{-# LANGUAGE LambdaCase #-}

-- | Generic mixfix operator processing infrastructure.
-- This module consolidates all the duplicated mixfix parsing logic across
-- Terms, RTypes, and Proofs into a single, extensible implementation.

module Operations.Generic.Mixfix
  ( -- | Typeclass for mixfix-capable AST nodes
    MixfixAst(..)
    -- | Generic reduction passes
  , reduceLevelG
  , reducePrefixG
  , reduceClosedG
  , reducePostfixG
    -- | Full processing pipeline
  , fullPassG
  , runLevelsG
  , reparseG
    -- | Re-exported types and functions
  , Assoc(..)
  , fixM
  ) where

import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Data.Foldable (asum)
import Control.Monad.Reader
import Control.Monad.Except (throwError)

import Core.Syntax
import Core.Raw
import Core.Errors
import Core.Context
import Parser.Mixfix (splitMixfix, mixfixKeywords)
import Operations.Generic.Token (ToTokenAst, toTok, Tok(..))

--------------------------------------------------------------------------------
-- | Types and data structures
--------------------------------------------------------------------------------

-- | Associativity for operators
data Assoc = ALeft | ARight | ANon deriving Eq

-- | Build precedence table from macro environment
type PrecTable = IntMap.IntMap [(String, Assoc)]

-- | Monadic fixpoint helper for iterating until convergence
fixM :: (Monad m, Eq a) => (a -> m a) -> a -> m a
fixM f x = do
  x' <- f x
  if x' == x then pure x else fixM f x'

--------------------------------------------------------------------------------
-- | Typeclass for AST nodes that support mixfix operator processing  
--------------------------------------------------------------------------------

class ToTokenAst a => MixfixAst a where
  -- | Flatten left-nested applications into a list
  flattenApps :: a -> [a]
  -- | Construct a macro application node
  makeMacro :: Name -> [a] -> SourcePos -> a

--------------------------------------------------------------------------------
-- | AST instances
--------------------------------------------------------------------------------

instance MixfixAst RawTerm where
  flattenApps = go []
    where
      go acc (RTApp f x _) = go (x:acc) f
      go acc t = t:acc

  makeMacro name args pos = RTMacro name args pos

instance MixfixAst RawRType where
  flattenApps = go []
    where
      go acc (RRApp f x _)  = go (x:acc) f
      go acc (RRComp f x _) = go (x:acc) f  -- Keep composition flattening
      go acc r              = r:acc

  makeMacro name args pos = RRMacro name args pos

instance MixfixAst RawProof where
  flattenApps = go []
    where
      go acc (RPApp f x _) = go (x:acc) f
      go acc p = p:acc

  makeMacro name args pos = RPMixfix name args pos

--------------------------------------------------------------------------------
-- | Helper functions extracted from Elaborate.hs
--------------------------------------------------------------------------------

-- | Build precedence table from macro environment
precTable :: Context -> PrecTable
precTable env = IntMap.fromListWith (++)
  [ (p, [(keyword, assoc)])
  | (macroName, fixity) <- Map.toList (macroFixities env)
  , keyword <- splitMixfix macroName
  , let (assoc, p) = case fixity of
          Infixl  n -> (ALeft , n)
          Infixr  n -> (ARight, n)
          InfixN  n -> (ANon  , n)
          Prefix  n -> (ARight, n)
          Postfix n -> (ALeft , n)
          Closed  n -> (ANon  , n)
  ]

-- | Collect prefix macros at precedence level k
prefixMacros :: Int -> Context -> [(String, [String])]
prefixMacros k env =
  [ (m, splitMixfix m)
  | (m, Prefix p) <- Map.toList (macroFixities env)
  , p == k
  ]

-- | Collect postfix macros at precedence level k  
postfixMacros :: Int -> Context -> [(String, [String])]
postfixMacros k env =
  [ (m, splitMixfix m)
  | (m, Postfix p) <- Map.toList (macroFixities env)
  , p == k
  ]

-- | Collect closed macros at precedence level k
closedMacros :: Int -> Context -> [(String, [String])]
closedMacros k env =
  [ (m, splitMixfix m)
  | (m, Closed p) <- Map.toList (macroFixities env)
  , p == k
  ]

-- | Try to match a prefix pattern at the head of token stream
matchPrefix :: (String, [String]) -> [Tok a] -> Maybe (String, [a], [Tok a], SourcePos)
matchPrefix (mName, lits) toks = go lits toks [] Nothing
  where
    go :: [String] -> [Tok a] -> [a] -> Maybe SourcePos -> Maybe (String, [a], [Tok a], SourcePos)
    go (l:ls) (TOP lit pos : TV arg : rest) acc start
      | lit == l = go ls rest (acc ++ [arg]) (Just (maybe pos id start))
    go [] rest acc (Just sp) = Just (mName, acc, rest, sp)
    go _ _ _ _ = Nothing

-- | Try to match a postfix pattern after head operand  
matchPostfix :: (String, [String]) -> [Tok a] -> Maybe (String, [a], [Tok a], SourcePos)
matchPostfix (mName, lits) toks0 = go lits toks0 [] Nothing
  where
    go :: [String] -> [Tok a] -> [a] -> Maybe SourcePos -> Maybe (String, [a], [Tok a], SourcePos)
    go (l:ls@(_:_)) (TOP lit pos : TV arg : rest) acc start
      | lit == l = go ls rest (acc ++ [arg]) (Just (maybe pos id start))
    go [l] (TOP lit pos : rest) acc start
      | lit == l = Just (mName, acc, rest, maybe pos id start)
    go _ _ _ _ = Nothing

-- | Try to match a closed pattern
matchClosed :: (String, [String]) -> [Tok a] -> Maybe (String, [a], [Tok a], SourcePos)
matchClosed (mName, lits) toks0 = go lits toks0 [] Nothing
  where
    go :: [String] -> [Tok a] -> [a] -> Maybe SourcePos -> Maybe (String, [a], [Tok a], SourcePos)
    go (l:ls@(_:_)) (TOP lit pos : TV arg : rest) acc start
      | lit == l = go ls rest (acc ++ [arg]) (Just (maybe pos id start))
    go [l] (TOP lit pos : rest) acc start
      | lit == l = Just (mName, acc, rest, maybe pos id start)
    go [] rest acc (Just sp) = Just (mName, acc, rest, sp)
    go _ _ _ _ = Nothing

--------------------------------------------------------------------------------
-- | Generic helper functions
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | Generic reduction passes
--------------------------------------------------------------------------------

-- | Generic binary infix operator reduction (shunting-yard algorithm)
reduceLevelG :: MixfixAst a => Int -> [Tok a] -> ElaborateM [Tok a]
reduceLevelG k toks = do
  ctx <- ask
  let lits = fromMaybe [] (IntMap.lookup k (precTable ctx))
  go ctx lits toks
  where
    go ctx lits (TV a : TOP op pos : TV b : rest)
      | Just _assoc <- lookup op lits = do
          let (args, rest') = collect op [a, b] rest
              macroName = "_" ++ intercalate "_" (replicate (length args - 1) op) ++ "_"
          case Map.lookup macroName (macroDefinitions ctx) of
            Just (params, _) | length params == length args -> do
              let rawNode = makeMacro (Name macroName) args pos
              go ctx lits (TV rawNode : rest')
            _ -> do -- No synthetic macro creation - fail if not in context
              (TV a :) <$> go ctx lits (TOP op pos : TV b : rest)
      | otherwise = (TV a :) <$> go ctx lits (TOP op pos : TV b : rest)
    go ctx lits (x:xs) = (x:) <$> go ctx lits xs
    go _ _ [] = return []

    -- Collect consecutive occurrences of the same operator
    collect op acc (TOP op' _ : TV c : rest) | op' == op =
      collect op (acc ++ [c]) rest
    collect _ acc rest = (acc, rest)

-- | Generic prefix operator reduction
reducePrefixG :: MixfixAst a => Int -> [Tok a] -> ElaborateM [Tok a]
reducePrefixG k toks = do
  env <- ask
  let pms = prefixMacros k env
  pure (loop toks pms)
  where
    loop [] _ = []
    loop ts@(TOP _lit _ : _) pms =
      case asum (map (`matchPrefix` ts) pms) of
        Just (mName, args, rest, sp) ->
          TV (makeMacro (Name mName) args sp) : loop rest pms
        _ -> let (x:xs) = ts in x : loop xs pms
    loop (x:xs) pms = x : loop xs pms

-- | Generic closed operator reduction
reduceClosedG :: MixfixAst a => Int -> [Tok a] -> ElaborateM [Tok a]
reduceClosedG k toks = do
  env <- ask
  let cms = closedMacros k env
  pure (loop toks cms)
  where
    loop [] _ = []
    loop ts@(TOP _lit _ : _) cms =
      case asum (map (`matchClosed` ts) cms) of
        Just (mName, args, rest, sp) ->
          TV (makeMacro (Name mName) args sp) : loop rest cms
        _ -> let (x:xs) = ts in x : loop xs cms
    loop (x:xs) cms = x : loop xs cms

-- | Generic postfix operator reduction
reducePostfixG :: MixfixAst a => Int -> [Tok a] -> ElaborateM [Tok a]
reducePostfixG k toks = do
  env <- ask
  let pms = postfixMacros k env
      loop [] = []
      loop ts@(TV a : rest) =
        case asum (map (`matchPostfix` rest) pms) of
          Just (mName, args, rest', sp) ->
            let node = makeMacro (Name mName) (a:args) sp
             in loop (TV node : rest')
          _ -> TV a : loop rest
      loop (x:xs) = x : loop xs
  pure (loop toks)

--------------------------------------------------------------------------------
-- | Full processing pipeline
--------------------------------------------------------------------------------

-- | One complete pass through all reduction phases
fullPassG :: MixfixAst a => Int -> [Tok a] -> ElaborateM [Tok a]
fullPassG k toks = do
  toks1 <- reducePrefixG k toks
  toks2 <- reduceClosedG k toks1  
  toks3 <- reducePostfixG k toks2
  reduceLevelG k toks3

-- | Run all precedence levels with fixpoint iteration
runLevelsG :: (MixfixAst a, Eq a) => [Int] -> [Tok a] -> ElaborateM [Tok a]
runLevelsG ks toks = foldM (\acc k -> fixM (fullPassG k) acc) toks ks

-- | Generic reparsing function that handles mixfix operators for any AST type
reparseG :: (MixfixAst a, Eq a, Show a) => (a -> ElaborateM b) -> SourcePos -> [a] -> ElaborateM b
reparseG elaborateFunc pos rawList = do
  ctx <- ask
  let ops = mixfixKeywords ctx
      toks0 = map (toTok ops) rawList
      precs = reverse (IntMap.keys (precTable ctx))
  toks1 <- runLevelsG precs toks0
  case toks1 of
    [TV raw] -> elaborateFunc raw
    _ -> throwError $ InvalidMixfixPattern 
           ("cannot resolve operators in reparseG - toks0=" ++ show toks0 ++ ", toks1=" ++ show toks1) 
           (ErrorContext pos "variable lookup")

