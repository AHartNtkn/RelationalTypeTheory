{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module Elaborate
  ( elaborate
  , elaborateDeclaration
  , elaborateTerm
  , elaborateRType
  , elaborateProof
  , emptyCtxWithBuiltins
  , isPostfixOperator
  , expandProofMacroOneStep
  , elaborateDeclarations
  , matchPrefix
  , Tok(..)
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad (when, foldM)
import qualified Data.Map as Map
import           Data.List       (foldl')
import           Data.Foldable   (asum)
import qualified Data.IntMap as IntMap
import qualified Data.Set as S
import           Data.List  (intercalate)     -- NEW
import Text.Megaparsec (SourcePos, ParseErrorBundle)
import Data.Void
import Data.Bifunctor (first)
import Data.Maybe (fromMaybe)

import Lib hiding (splitMixfix, mixfixKeywords)
import RawAst
import AST.Mixfix (splitMixfix, mixfixKeywords, defaultFixity)
import Generic.Shift (shift)
import Generic.FreeVars (freeVarsInTerm, freeVarsInRType, freeVarsInProof)
import Generic.Macro (elabMacroAppG)
import Errors (RelTTError(..), ErrorContext(..))
import ElaborateTypes
import Environment (extendMacroEnvironment, noMacros)
import Builtins (builtinFixities, builtinMacroBodies, macroEnvWithBuiltins)

-- | Monadic fixpoint helper for iterating until convergence
fixM :: (Monad m, Eq a) => (a -> m a) -> a -> m a
fixM f x = do
  x' <- f x
  if x' == x then pure x else fixM f x'


shiftIntMap :: Map.Map k Int -> Map.Map k Int
shiftIntMap = Map.map (+1)

shiftProofMap :: Map.Map String (Int,RelJudgment)
              -> Map.Map String (Int,RelJudgment)
shiftProofMap = Map.map (\(i,j) -> (i+1,j))

bindTermVar :: String -> ElaborateContext -> ElaborateContext
bindTermVar x ctx =
  ctx { boundVars = Map.insert x 0 (shiftIntMap (boundVars ctx))
      , termDepth = termDepth ctx + 1 }

bindRelVar :: String -> ElaborateContext -> ElaborateContext
bindRelVar r ctx =
  ctx { boundRelVars = Map.insert r 0 (shiftIntMap (boundRelVars ctx))
      , relDepth  = relDepth  ctx + 1 }

bindProofVar :: String -> RelJudgment -> ElaborateContext -> ElaborateContext
bindProofVar p j ctx =
  ctx { boundProofVars = Map.insert p (0,j) (shiftProofMap (boundProofVars ctx))
      , proofDepth = proofDepth ctx + 1 }



emptyCtxWithBuiltins :: ElaborateContext  
emptyCtxWithBuiltins = ElaborateContext
  { macroEnv = macroEnvWithBuiltins
  , theoremEnv = Lib.TheoremEnvironment Map.empty
  , termDepth = 0
  , relDepth = 0
  , proofDepth = 0
  , boundVars = Map.empty
  , boundRelVars = Map.empty
  , boundProofVars = Map.empty
  }





-- Helper to convert simple RawProof to RawTerm (for cross-category patterns)
proofToTerm :: RawProof -> Maybe RawTerm
proofToTerm (RPVar (Name n) pos) = Just (RTVar (Name n) pos)
proofToTerm _ = Nothing

-- Helper to convert simple RawProof to RawRType (for cross-category patterns)  
proofToRType :: RawProof -> Maybe RawRType
proofToRType (RPVar (Name n) pos) = Just (RRVar (Name n) pos)
proofToRType _ = Nothing

-- Expand a Proof‑macro one step.  Fails only on arity mismatch.
expandProofMacroOneStep
  :: MacroEnvironment -> String -> [Proof] -> SourcePos
  -> Either RelTTError Proof
expandProofMacroOneStep env name args pos =
  case Map.lookup name (macroDefinitions env) of
    Nothing           -> Left (UnknownMacro name (ErrorContext pos "proof macro lookup"))
    Just (params, mb) ->
      case mb of
        TermMacro  _ -> Left (InvalidMixfixPattern "term macro in proof context" (ErrorContext pos "proof macro application"))
        RelMacro   _ -> Left (InvalidMixfixPattern "rel macro in proof context" (ErrorContext pos "proof macro application"))
        ProofMacro pBody ->
          if length params /= length args
            then Left (MacroArityMismatch name (length params) (length args) (ErrorContext pos "variable lookup"))
            else
              -- substitute like you do in Normalize.Term  
              Right (foldl' (\acc arg -> AppP acc arg pos) (shift (length args) pBody) args)

----------------------------------------------------------------------
-- Mixfix re-parsing after the grammar parser
----------------------------------------------------------------------

data Tok a = TV a                        -- operand
           | TOP String SourcePos          -- operator literal token
  deriving (Show, Eq)

data Assoc = ALeft | ARight | ANon deriving Eq

toTokT :: S.Set String -> RawTerm -> Tok RawTerm
toTokT ops t@(RTVar (Name nm) pos)
  | nm `S.member` ops             = TOP nm pos
  | otherwise                     = TV  t
toTokT _   t                      = TV  t

toTokR :: S.Set String -> RawRType -> Tok RawRType
toTokR ops r@(RRVar (Name nm) pos)
  | nm `S.member` ops             = TOP nm pos
  | otherwise                     = TV  r
toTokR _   r                      = TV  r

toTokP :: S.Set String -> RawProof -> Tok RawProof
toTokP ops p@(RPVar (Name nm) pos)
  | nm `S.member` ops             = TOP nm pos
  | otherwise                     = TV  p
toTokP _   p                      = TV  p

-- Build one precedence table   Int -> [(literal, assoc)]
type PrecTable = IntMap.IntMap [(String, Assoc)]

-- Check if an operator is postfix in the macro environment
isPostfixOperator :: String -> MacroEnvironment -> Bool
isPostfixOperator op env = 
  any (\(macroName, fixity) -> 
    case fixity of
      Postfix _ -> op `elem` splitMixfix macroName
      _ -> False
  ) (Map.toList (macroFixities env))

precTable :: MacroEnvironment -> PrecTable
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

-- Flatten a left-nested application
flattenAppsT :: RawTerm -> [RawTerm]
flattenAppsT = go []
  where
    go acc (RTApp f x _) = go (x:acc) f
    go acc t = t:acc

flattenAppsR :: RawRType -> [RawRType]
flattenAppsR = go []
  where
    -- NEW: collapse R S T …   (left‑nested)
    go acc (RRApp f x _)  = go (x:acc) f
    -- keep the old composition flattening – harmless and still useful
    go acc (RRComp f x _) = go (x:acc) f
    go acc r                  = r:acc

flattenAppsP :: RawProof -> [RawProof]
flattenAppsP = go []
  where
    go acc (RPApp f x _) = go (x:acc) f
    go acc p = p:acc


-- Simple shunting-yard for binary infix operators
reduceLevelT :: Int -> [Tok RawTerm] -> ElaborateM [Tok RawTerm]
reduceLevelT k toks = do
  ctx <- ask
  let lits = fromMaybe [] (IntMap.lookup k (precTable (macroEnv ctx)))
  go ctx lits toks
  where
    -- gather as many  (TOP op TV arg)  pairs as we can to build one n‑ary node
    go ctx lits (TV a : TOP op pos : TV b : rest)
      | Just assoc <- lookup op lits = do
          let (args, rest') = collect op [a, b] rest
              macroName     = "_" ++ intercalate "_" (replicate (length args - 1) op) ++ "_"
          case Map.lookup macroName (macroDefinitions (macroEnv ctx)) of
            Just (params, _) | length params == length args -> do
              let rawNode = RTMacro (Name macroName) args pos
              go ctx lits (TV rawNode : rest')
            _ -> do -- no synthetic macro creation - fail if not in context
              (TV a :) <$> go ctx lits (TOP op pos : TV b : rest)
      | otherwise = (TV a :) <$> go ctx lits (TOP op pos : TV b : rest)
    go ctx lits (x:xs) = (x:) <$> go ctx lits xs
    go _ _ [] = return []

    -- keep swallowing   TOP op TV arg
    collect op acc (TOP op' _ : TV c : rest) | op' == op =
      collect op (acc ++ [c]) rest
    collect _  acc rest = (acc, rest)

-- **exact copy** for relational types ----------------------------------------
reduceLevelR :: Int -> [Tok RawRType] -> ElaborateM [Tok RawRType]
reduceLevelR k toks = do
  ctx <- ask
  let lits = fromMaybe [] (IntMap.lookup k (precTable (macroEnv ctx)))
  go ctx lits toks
  where
    go ctx lits (TV a : TOP op pos : TV b : rest)
      | Just assoc <- lookup op lits = do
          let (args, rest') = collect op [a, b] rest
              macroName     = "_" ++ intercalate "_" (replicate (length args - 1) op) ++ "_"
          case Map.lookup macroName (macroDefinitions (macroEnv ctx)) of
            Just (params, _) | length params == length args -> do
              let rawNode = RRMacro (Name macroName) args pos
              go ctx lits (TV rawNode : rest')
            _ -> do -- no synthetic macro creation - fail if not in context
              (TV a :) <$> go ctx lits (TOP op pos : TV b : rest)
      | otherwise = (TV a :) <$> go ctx lits (TOP op pos : TV b : rest)
    go ctx lits (x:xs) = (x:) <$> go ctx lits xs
    go _ _ [] = return []

    collect op acc (TOP op' _ : TV c : rest) | op' == op =
      collect op (acc ++ [c]) rest
    collect _  acc rest = (acc, rest)

-- **exact copy** for proof types ----------------------------------------
reduceLevelP :: Int -> [Tok RawProof] -> ElaborateM [Tok RawProof]
reduceLevelP k toks = do
  ctx <- ask
  let lits = fromMaybe [] (IntMap.lookup k (precTable (macroEnv ctx)))
  go ctx lits toks
  where
    go ctx lits (TV a : TOP op pos : TV b : rest)
      | Just assoc <- lookup op lits = do
          let (args, rest') = collect op [a, b] rest
              macroName     = "_" ++ intercalate "_" (replicate (length args - 1) op) ++ "_"
          case Map.lookup macroName (macroDefinitions (macroEnv ctx)) of
            Just (params, _) | length params == length args -> do
              let rawNode = RPMixfix (Name macroName) args pos
              go ctx lits (TV rawNode : rest')
            _ -> do -- no synthetic macro creation - fail if not in context
              (TV a :) <$> go ctx lits (TOP op pos : TV b : rest)
      | otherwise = (TV a :) <$> go ctx lits (TOP op pos : TV b : rest)
    go ctx lits (x:xs) = (x:) <$> go ctx lits xs
    go _ _ [] = return []

    collect op acc (TOP op' _ : TV c : rest) | op' == op =
      collect op (acc ++ [c]) rest
    collect _  acc rest = (acc, rest)

runLevelsT :: [Int] -> [Tok RawTerm] -> ElaborateM [Tok RawTerm]
-- | One "full pass" = prefix then infix for each type
fullPassT :: Int -> [Tok RawTerm] -> ElaborateM [Tok RawTerm]
fullPassT k ts = reducePrefixT k ts >>= reduceClosedT k >>= reducePostfixT k >>= reduceLevelT k

fullPassR :: Int -> [Tok RawRType] -> ElaborateM [Tok RawRType]
fullPassR k ts = reducePrefixR k ts >>= reduceClosedR k >>= reducePostfixR k >>= reduceLevelR k

fullPassP :: Int -> [Tok RawProof] -> ElaborateM [Tok RawProof]
fullPassP k ts = reducePrefixP k ts >>= reduceClosedP k >>= reducePostfixP k >>= reduceLevelP k

-- We now run *four* passes per precedence level:
--   1. reducePrefixT  – handles n‑ary **prefix** patterns such as
--      "if _ then _ else _"
--   2. reduceClosedT  – handles **closed/delimited** patterns such as
--      "ι⟨_,_⟩"
--   3. reducePostfixT – handles n‑ary **postfix** patterns such as
--      "_{_}" or "_˘"
--   4. reduceLevelT   – existing binary infix handling
runLevelsT ks toks = foldM (\acc k -> fixM (fullPassT k) acc) toks ks

runLevelsR :: [Int] -> [Tok RawRType] -> ElaborateM [Tok RawRType]
runLevelsR ks toks = foldM (\acc k -> fixM (fullPassR k) acc) toks ks

runLevelsP :: [Int] -> [Tok RawProof] -> ElaborateM [Tok RawProof]
runLevelsP ks toks = foldM (\acc k -> fixM (fullPassP k) acc) toks ks

-- ---------------------------------------------------------------------------
--  NEW  :  proof‑level tokenisation & reduction (exactly parallel to Term/RType)
-- ---------------------------------------------------------------------------


----------------------------------------------------------------------
-- NEW CODE:  generic *prefix*‑mixfix reduction (any arity ≥ 1)
----------------------------------------------------------------------

-- | Collect (macro‑name , literal pieces) for every *prefix* operator
--   that lives on precedence @k@.
prefixMacros
  :: Int
  -> MacroEnvironment
  -> [(String,[String])]   -- (canonicalName , ["if","then","else"])
prefixMacros k env =
  [ (m , splitMixfix m)
  | (m,Prefix p) <- Map.toList (macroFixities env)
  , p == k
  ]

-- | Collect (macro‑name , literal pieces) for every *postfix* operator
--   that lives on precedence @k@.
postfixMacros
  :: Int
  -> MacroEnvironment
  -> [(String,[String])]   -- (canonicalName , ["{","}"])
postfixMacros k env =
  [ (m , splitMixfix m)
  | (m,Postfix p) <- Map.toList (macroFixities env)
  , p == k
  ]

-- | Collect (macro‑name , literal pieces) for every *closed* operator
--   that lives on precedence @k@.
closedMacros
  :: Int
  -> MacroEnvironment
  -> [(String,[String])]   -- (canonicalName , ["ι⟨",",","⟩"])
closedMacros k env =
  [ (m , splitMixfix m)
  | (m,Closed p) <- Map.toList (macroFixities env)
  , p == k
  ]

-- | Try to match a single prefix pattern at the head of the token stream.
--   Return @(macroName , args , rest)@ on success.
matchPrefix
  :: (String,[String])
  -> [Tok a]
  -> Maybe (String,[a],[Tok a], SourcePos)
matchPrefix (mName,lits) toks = go lits toks [] Nothing
  where
    -- After *every* literal we demand one argument.
    -- The list of literals is never empty for a Prefix macro.
    go :: [String]           -- literals still to match
       -> [Tok a]            -- remaining stream
       -> [a]                -- arguments accumulated
       -> Maybe SourcePos    -- position of first literal
       -> Maybe (String,[a],[Tok a],SourcePos)

    -- general case: literal + argument, then continue
    go (l:ls) (TOP lit pos : TV arg : rest) acc start
      | lit == l  = go ls rest (acc ++ [arg])
                           (Just (maybe pos id start))

    -- **all literals consumed** → success
    go [] rest acc (Just sp) = Just (mName,acc,rest,sp)

    -- any other shape        → failure
    go _ _ _ _               = Nothing

-- | Try to match a postfix macro right after the head operand.
--   Return (name, extraArgs, restTokens, startPos).
matchPostfix
  :: (String,[String]) -> [Tok a]
  -> Maybe (String,[a],[Tok a], SourcePos)
matchPostfix (mName,lits) toks0 = go lits toks0 [] Nothing
  where
    -- Every literal except the last one must be followed by a TV argument.
    go :: [String] -> [Tok a] -> [a] -> Maybe SourcePos
       -> Maybe (String,[a],[Tok a], SourcePos)

    -- literal • arg
    go (l:ls@( _:_ )) (TOP lit pos : TV arg : rest) acc start
      | lit == l = go ls rest (acc ++ [arg]) (Just (maybe pos id start))

    -- final literal – no argument afterwards
    go [l] (TOP lit pos : rest) acc start
      | lit == l = Just (mName, acc, rest, maybe pos id start)

    go _ _ _ _ = Nothing

-- | Try to match a closed/delimited macro pattern.
--   Return (name, args, restTokens, startPos).
--   Closed patterns can end with either an argument or a literal.
matchClosed
  :: (String,[String]) -> [Tok a]
  -> Maybe (String,[a],[Tok a], SourcePos)
matchClosed (mName,lits) toks0 = go lits toks0 [] Nothing
  where
    go :: [String] -> [Tok a] -> [a] -> Maybe SourcePos
       -> Maybe (String,[a],[Tok a], SourcePos)

    -- literal • arg, then continue
    go (l:ls@(_:_)) (TOP lit pos : TV arg : rest) acc start
      | lit == l = go ls rest (acc ++ [arg]) (Just (maybe pos id start))

    -- final literal - can end without argument (this is the key difference from prefix)
    go [l] (TOP lit pos : rest) acc start
      | lit == l = Just (mName, acc, rest, maybe pos id start)

    -- all literals consumed → success
    go [] rest acc (Just sp) = Just (mName, acc, rest, sp)

    -- any other shape → failure
    go _ _ _ _ = Nothing

-- generic helper so we share code between T / R / P --------------------------
reducePrefixGeneric
  :: (S.Set String -> a -> Tok a)                 -- ^ toTok
  -> (Name -> [a] -> SourcePos -> a)          -- ^ macro constructor
  -> Int -> [Tok a] -> ElaborateM [Tok a]
reducePrefixGeneric toTok makeNode k toks = do
  env <- asks macroEnv
  let pms = prefixMacros k env
  pure (loop toks pms)
  where
    loop [] _ = []
    loop ts@(TOP lit _ : _) pms =
      case asum (map (`matchPrefix` ts) pms) of
        Just (mName,args,rest,sp) ->
          TV (makeNode (Name mName) args sp) : loop rest pms
        _ -> let (x:xs)=ts in x:loop xs pms
    loop (x:xs) pms = x:loop xs pms

-- | Reduce *prefix* mixfix operators of precedence @k@ inside a
--   token stream (terms).
reducePrefixT :: Int -> [Tok RawTerm] -> ElaborateM [Tok RawTerm]
reducePrefixT = reducePrefixGeneric toTokT RTMacro

-- | Same, but for relational‑types.
reducePrefixR :: Int -> [Tok RawRType] -> ElaborateM [Tok RawRType]
reducePrefixR = reducePrefixGeneric toTokR RRMacro

-- | Same, but for proofs.
reducePrefixP :: Int -> [Tok RawProof] -> ElaborateM [Tok RawProof]
reducePrefixP = reducePrefixGeneric toTokP RPMixfix

-- | Generic closed reducer (T / R / P all share it)
reduceClosedGeneric
  :: (S.Set String -> a -> Tok a)                 -- ^ toTok
  -> (Name -> [a] -> SourcePos -> a)          -- ^ macro constructor
  -> Int -> [Tok a] -> ElaborateM [Tok a]
reduceClosedGeneric toTok makeNode k toks = do
  env <- asks macroEnv
  let cms = closedMacros k env
  pure (loop toks cms)
  where
    loop [] _ = []
    loop ts@(TOP lit _ : _) cms =
      case asum (map (`matchClosed` ts) cms) of
        Just (mName,args,rest,sp) ->
          TV (makeNode (Name mName) args sp) : loop rest cms
        _ -> let (x:xs)=ts in x:loop xs cms
    loop (x:xs) cms = x:loop xs cms

-- | Reduce *closed* mixfix operators of precedence @k@ inside a
--   token stream (terms).
reduceClosedT :: Int -> [Tok RawTerm] -> ElaborateM [Tok RawTerm]
reduceClosedT = reduceClosedGeneric toTokT RTMacro

-- | Same, but for relational‑types.
reduceClosedR :: Int -> [Tok RawRType] -> ElaborateM [Tok RawRType]
reduceClosedR = reduceClosedGeneric toTokR RRMacro

-- | Same, but for proofs.
reduceClosedP :: Int -> [Tok RawProof] -> ElaborateM [Tok RawProof]
reduceClosedP = reduceClosedGeneric toTokP RPMixfix

-- | Generic postfix reducer (T / R / P all share it)
reducePostfixGeneric
  :: (S.Set String -> a -> Tok a)            -- toTok  (TV wrapper)
  -> (Name -> [a] -> SourcePos -> a)         -- node constructor
  -> Int -> [Tok a] -> ElaborateM [Tok a]
reducePostfixGeneric toTok makeNode k toks = do
  env <- asks macroEnv
  let pms  = postfixMacros k env             -- candidate macros
      loop [] = []
      loop ts@(TV a : rest) =
        case asum (map (`matchPostfix` rest) pms) of
          Just (mName,args,rest',sp) ->
            let node   = makeNode (Name mName) (a:args) sp
            in  loop (TV node : rest')
          _ -> TV a : loop rest
      loop (x:xs) = x : loop xs
  pure (loop toks)

-- | Reduce *postfix* mixfix operators of precedence @k@ inside a
--   token stream (terms).
reducePostfixT :: Int -> [Tok RawTerm] -> ElaborateM [Tok RawTerm]
reducePostfixT = reducePostfixGeneric toTokT RTMacro

-- | Same, but for relational‑types.
reducePostfixR :: Int -> [Tok RawRType] -> ElaborateM [Tok RawRType]
reducePostfixR = reducePostfixGeneric toTokR RRMacro

-- | Same, but for proofs.
reducePostfixP :: Int -> [Tok RawProof] -> ElaborateM [Tok RawProof]
reducePostfixP = reducePostfixGeneric toTokP RPMixfix

reparseTerms :: SourcePos -> [RawTerm] -> ElaborateM Term
reparseTerms pos rawList = do
  ctx <- ask
  let ops = mixfixKeywords (macroEnv ctx)
      toks0 = map (toTokT ops) rawList
      precs = reverse (IntMap.keys (precTable (macroEnv ctx)))
  toks1 <- runLevelsT precs toks0
  case toks1 of
    [TV raw] -> elaborateTerm raw
    _ -> throwError $ InvalidMixfixPattern ("cannot resolve operators in reparseTerms - toks0=" ++ show toks0 ++ ", toks1=" ++ show toks1) (ErrorContext pos "variable lookup")

reparseRTypes :: SourcePos -> [RawRType] -> ElaborateM RType
reparseRTypes pos rawList = do
  ctx <- ask
  let ops = mixfixKeywords (macroEnv ctx)
      toks0 = map (toTokR ops) rawList
      precs = reverse (IntMap.keys (precTable (macroEnv ctx)))
  toks1 <- runLevelsR precs toks0
  case toks1 of
    [TV raw] -> elaborateRType raw
    _ -> do
      let debugMsg = "Debug: rawList=" ++ show rawList ++ ", toks0=" ++ show toks0 ++ ", toks1=" ++ show toks1
      throwError $ InvalidMixfixPattern ("cannot resolve operators - " ++ debugMsg) (ErrorContext pos "variable lookup")

reparseProofs :: SourcePos -> [RawProof] -> ElaborateM Proof
reparseProofs pos rawList = do
  ctx <- ask
  let ops = mixfixKeywords (macroEnv ctx)
      toks0 = map (toTokP ops) rawList
      precs = reverse (IntMap.keys (precTable (macroEnv ctx)))
  toks1 <- runLevelsP precs toks0
  case toks1 of
    [TV raw] -> elaborateProof raw
    _ -> throwError $ InvalidMixfixPattern ("cannot resolve operators in reparseProofs - toks0=" ++ show toks0 ++ ", toks1=" ++ show toks1) (ErrorContext pos "variable lookup")


-- Check if there are any operator tokens in the list
hasOperatorT :: [Tok RawTerm] -> Bool
hasOperatorT = any isOp
  where
    isOp (TOP _ _) = True
    isOp _ = False

hasOperatorR :: [Tok RawRType] -> Bool
hasOperatorR = any isOp
  where
    isOp (TOP _ _) = True
    isOp _ = False

hasOperatorP :: [Tok RawProof] -> Bool
hasOperatorP = any isOp
  where
    isOp (TOP _ _) = True
    isOp _ = False

-- Main elaboration function
elaborate :: ElaborateContext -> RawDeclaration
          -> Either RelTTError           Declaration
elaborate ctx rawDecl =
  runExcept (runReaderT (elaborateDeclaration rawDecl) ctx)

elaborateDeclaration :: RawDeclaration -> ElaborateM Declaration
elaborateDeclaration (RawMacro name params body) = do
  ctx <- ask
  let pNames = map nameString params

      -- Using the centralized binder functions

      ctxTerm  = foldl (flip bindTermVar) ctx pNames   -- last parameter = index 0
      ctxRel   = foldl (flip bindRelVar ) ctx pNames
      ctxProof = ctx  -- proof macros can reference any variables
  -------------------------------------------------------------------------
  elaboratedBody <- case body of
    RawTermBody _ -> local (const ctxTerm) (elaborateMacroBody body)
    RawRelBody  _ -> local (const ctxRel ) (elaborateMacroBody body)
    RawProofBody _ -> local (const ctxProof) (elaborateMacroBody body)

  pure $ MacroDef (nameString name) pNames elaboratedBody
  
elaborateDeclaration (RawTheorem name bindings judgment proof) = do
  -- Elaborate bindings and extend context
  (elaboratedBindings, newCtx) <- elaborateBindings bindings
  -- Elaborate judgment and proof in extended context
  elaboratedJudgment <- local (const newCtx) (elaborateJudgment judgment)
  elaboratedProof <- local (const newCtx) (elaborateProof proof)
  return $ TheoremDef (nameString name) elaboratedBindings elaboratedJudgment elaboratedProof

elaborateDeclaration (RawFixityDecl fixity name) = do
  ctx <- ask
  let env0 = macroEnv ctx
      env1 = env0 { macroFixities = Map.insert (nameString name) fixity
                                         (macroFixities env0) }
  local (\c -> c { macroEnv = env1 })
        (pure (FixityDecl fixity (nameString name)))

elaborateDeclaration (RawImportDecl (RawImportModule path)) = do
  pure (ImportDecl (ImportModule path))

-- | Elaborate a list of raw declarations
elaborateDeclarations :: ElaborateContext -> [RawDeclaration] -> Either RelTTError [Declaration]
elaborateDeclarations ctx rawDecls = runExcept (runReaderT (mapM elaborateDeclaration rawDecls) ctx)

elaborateMacroBody :: RawMacroBody -> ElaborateM Lib.MacroBody
elaborateMacroBody (RawTermBody rawTerm) = do
  elaboratedTerm <- elaborateTerm rawTerm
  return $ Lib.TermMacro elaboratedTerm
elaborateMacroBody (RawRelBody rawRType) = do
  elaboratedRType <- elaborateRType rawRType
  return $ Lib.RelMacro elaboratedRType
elaborateMacroBody (RawProofBody rawProof) = do
  elaboratedProof <- elaborateProof rawProof
  return $ Lib.ProofMacro elaboratedProof

elaborateBindings :: [RawBinding] -> ElaborateM ([Binding], ElaborateContext)
elaborateBindings bindings = do
  ctx <- ask
  foldM elaborateBinding ([], ctx) bindings
  where
    elaborateBinding (acc, ctx) (RawTermBinding name) = do
      let binding = TermBinding (nameString name)
      let newCtx = bindTermVar (nameString name) ctx
      return (acc ++ [binding], newCtx)
    
    elaborateBinding (acc, ctx) (RawRelBinding name) = do
      let binding = RelBinding (nameString name)
      -- Theorem parameters should NOT increment relDepth - they're just added to lookup context
      let newCtx = ctx { boundRelVars = Map.insert (nameString name) (relDepth ctx) (boundRelVars ctx) }
      return (acc ++ [binding], newCtx)
    
    elaborateBinding (acc, ctx) (RawProofBinding name rawJudgment) = do
      elaboratedJudgment <- local (const ctx) (elaborateJudgment rawJudgment)
      let binding = ProofBinding (nameString name) elaboratedJudgment
      let newCtx = bindProofVar (nameString name) elaboratedJudgment ctx
      return (acc ++ [binding], newCtx)

elaborateJudgment :: RawJudgment -> ElaborateM RelJudgment
elaborateJudgment (RawJudgment rawTerm1 rawRType rawTerm2) = do
  term1 <- elaborateTerm rawTerm1
  rtype <- elaborateRType rawRType
  term2 <- elaborateTerm rawTerm2
  return $ RelJudgment term1 rtype term2

----------------------------------------------------------------------
--  Generic smart application consolidation
----------------------------------------------------------------------

-- | Generic smart application that consolidates smartAppT/R/P logic
smartAppGeneric
  :: (raw -> ElaborateM elaborated)                      -- ^ elaboration function
  -> (String -> [elaborated] -> SourcePos -> elaborated) -- ^ macro constructor
  -> (elaborated -> elaborated -> SourcePos -> elaborated) -- ^ application constructor (for over-app)
  -> Bool                                                 -- ^ allows over-application?
  -> String                                               -- ^ macro name
  -> [ParamInfo]                                          -- ^ macro parameters
  -> [raw]                                                -- ^ raw arguments
  -> SourcePos                                            -- ^ source position
  -> ElaborateM elaborated
smartAppGeneric elaborate makeMacroApp makeApp allowsOver macroName params rawArgs macroPos = do
  let paramCount = length params
      argCount = length rawArgs
      
  if allowsOver
    then do
      -- Terms and Proofs: allow over-application but not under-application
      when (argCount < paramCount) $
        throwError $ MacroArityMismatch macroName paramCount argCount 
                     (ErrorContext macroPos "macro application")
      
      -- Split arguments into macro args and extra args
      let (macroRawArgs, extraRawArgs) = splitAt paramCount rawArgs
      
      -- Elaborate macro arguments
      elaboratedMacroArgs <- mapM elaborate macroRawArgs
      let macroApp = makeMacroApp macroName elaboratedMacroArgs macroPos
      
      -- Apply any extra arguments via function application
      foldM (\acc rawArg -> do
        elaboratedArg <- elaborate rawArg
        return $ makeApp acc elaboratedArg macroPos) macroApp extraRawArgs
        
    else do
      -- Relations: require exact arity match
      when (paramCount /= argCount) $
        throwError $ MacroArityMismatch macroName paramCount argCount
                     (ErrorContext macroPos "relational macro application")
      
      -- Elaborate all arguments and create macro application
      elaboratedArgs <- mapM elaborate rawArgs
      return $ makeMacroApp macroName elaboratedArgs macroPos

----------------------------------------------------------------------
--  Elaborate one macro application while honouring ParamInfo
----------------------------------------------------------------------

elabMacroAppT
  :: String -> [ParamInfo] -> [RawTerm] -> SourcePos -> ElaborateM Term
elabMacroAppT name sig raws pos = do
  ctx <- ask
  -- Elaborate arguments to terms
  elaborated <- mapM elaborateTerm raws
  -- Look up macro body from environment
  case Map.lookup name (macroDefinitions (macroEnv ctx)) of
    Nothing -> throwError $ UnknownMacro name (ErrorContext pos "term macro lookup")
    Just (_, TermMacro body) -> 
      case elabMacroAppG (macroEnv ctx) name sig body elaborated of
        Right result -> return result
        Left _ -> throwError $ InvalidMixfixPattern ("Term macro application failed for " ++ name) (ErrorContext pos "term macro application")
    Just (_, RelMacro _) -> throwError $ InvalidMixfixPattern ("Relational macro " ++ name ++ " used in term context") (ErrorContext pos "term macro application")
    Just (_, ProofMacro _) -> throwError $ InvalidMixfixPattern ("Proof macro " ++ name ++ " used in term context") (ErrorContext pos "term macro application")

elabMacroAppR
  :: String -> [ParamInfo] -> [RawRType] -> SourcePos -> ElaborateM RType
elabMacroAppR name sig raws pos = do
  ctx <- ask
  -- Elaborate arguments to relational types
  elaborated <- mapM elaborateRType raws
  -- Look up macro body from environment
  case Map.lookup name (macroDefinitions (macroEnv ctx)) of
    Nothing -> throwError $ UnknownMacro name (ErrorContext pos "relational macro lookup")
    Just (_, RelMacro body) -> 
      case elabMacroAppG (macroEnv ctx) name sig body elaborated of
        Right result -> return result
        Left _ -> throwError $ InvalidMixfixPattern ("Relational macro application failed for " ++ name) (ErrorContext pos "relational macro application")
    Just (_, TermMacro _) -> throwError $ InvalidMixfixPattern ("Term macro " ++ name ++ " used in relational context") (ErrorContext pos "relational macro application")
    Just (_, ProofMacro _) -> throwError $ InvalidMixfixPattern ("Proof macro " ++ name ++ " used in relational context") (ErrorContext pos "relational macro application")

elabMacroAppP
  :: String -> [ParamInfo] -> [RawProof] -> SourcePos -> ElaborateM Proof
elabMacroAppP name sig raws pos = do
  ctx <- ask
  -- Elaborate arguments to proofs
  elaborated <- mapM elaborateProof raws
  -- Look up macro body from environment
  case Map.lookup name (macroDefinitions (macroEnv ctx)) of
    Nothing -> throwError $ UnknownMacro name (ErrorContext pos "proof macro lookup")
    Just (_, ProofMacro body) -> 
      case elabMacroAppG (macroEnv ctx) name sig body elaborated of
        Right result -> return result
        Left _ -> throwError $ InvalidMixfixPattern ("Proof macro application failed for " ++ name) (ErrorContext pos "proof macro application")
    Just (_, TermMacro _) -> throwError $ InvalidMixfixPattern ("Term macro " ++ name ++ " used in proof context") (ErrorContext pos "proof macro application")
    Just (_, RelMacro _) -> throwError $ InvalidMixfixPattern ("Relational macro " ++ name ++ " used in proof context") (ErrorContext pos "proof macro application")


elaborateTerm :: RawTerm -> ElaborateM Term
elaborateTerm (RTVar name pos) = do
  ctx <- ask
  let varName = nameString name
  case Map.lookup (nameString name) (boundVars ctx) of
    Just bindingDepth ->
      return $ Var (nameString name) bindingDepth pos
    Nothing -> 
      -- Try looking up as a macro with zero arguments
      case Map.lookup (nameString name) (Lib.macroDefinitions (macroEnv ctx)) of
        Just ([], macroBody) -> 
          -- Macro with zero arguments - create TMacro node
          case macroBody of
            Lib.TermMacro _ -> return $ TMacro (nameString name) [] pos
            Lib.RelMacro _ -> throwError $ UnboundVariable ("Relational macro " ++ nameString name ++ " used in term context") (ErrorContext pos "variable lookup")
            Lib.ProofMacro _ -> throwError $ UnboundVariable ("Proof macro " ++ nameString name ++ " used in term context") (ErrorContext pos "variable lookup")
        Just (params, _) -> 
          -- Macro exists but requires arguments
          throwError $ MacroArityMismatch (nameString name) (length params) 0 (ErrorContext pos "macro arity check")
        Nothing -> throwError $ UnboundVariable ("Unknown term variable: " ++ nameString name) (ErrorContext pos "variable lookup")

elaborateTerm (RTLam name rawBody pos) = do
  ctx <- ask
  let varName = nameString name
  let newCtx = bindTermVar varName ctx
  body <- local (const newCtx) (elaborateTerm rawBody)
  return $ Lam varName body pos

elaborateTerm raw@(RTApp _ _ pos) = do
  ctx <- ask
  let flattened = flattenAppsT raw
      ops = mixfixKeywords (macroEnv ctx)
      toks = map (toTokT ops) flattened
  -- Check if this contains mixfix operators
  if hasOperatorT toks
    then -- Contains mixfix operators - use mixfix parsing
      reparseTerms pos flattened
    else -- No mixfix operators - check for simple macro application
      case flattened of
        (RTVar name _ : args) -> do
          let macroName = nameString name
          -- First check if this name is bound as a variable - bound variables take precedence
          case Map.lookup macroName (boundVars ctx) of
            Just _ -> elaborateAppLeft raw  -- Bound variable - regular function application
            Nothing -> 
              case Map.lookup macroName (Lib.macroDefinitions (macroEnv ctx)) of
                Nothing -> elaborateAppLeft raw  -- Not a macro - regular function application
                Just (params, _) -> smartAppT macroName params args pos  -- Macro application
        _ -> elaborateAppLeft raw  -- Not a simple application - regular function application
  where
    elaborateAppLeft (RTApp rawFunc rawArg _) = do
      func <- elaborateTerm rawFunc
      arg <- elaborateTerm rawArg
      return $ App func arg pos
    elaborateAppLeft other = elaborateTerm other
    
    smartAppT macroName params args macroPos = 
      smartAppGeneric elaborateTerm TMacro App True macroName params args macroPos

elaborateTerm (RTMacro nm args pos) = do
  let name = nameString nm
  ctx <- ask
  case Map.lookup name (Lib.macroDefinitions (macroEnv ctx)) of
    Nothing -> throwError $ UnknownMacro name (ErrorContext pos "macro lookup")
    Just (sig, _) -> elabMacroAppT name sig args pos

elaborateRType :: RawRType -> ElaborateM RType
elaborateRType (RRVar name pos) = do
  ctx <- ask
  let varName = nameString name
  case Map.lookup (nameString name) (boundRelVars ctx) of
    Just bindingDepth -> 
      return $ RVar (nameString name) bindingDepth pos
    Nothing -> 
      -- Try looking up as a term variable (which can be promoted to relation)
      case Map.lookup (nameString name) (boundVars ctx) of
        Just bindingDepth ->
          return $ Prom (Var (nameString name) bindingDepth pos) pos
        Nothing -> 
          -- Try looking up as a macro with zero arguments
          case Map.lookup (nameString name) (Lib.macroDefinitions (macroEnv ctx)) of
            Just ([], macroBody) -> 
              -- Macro with zero arguments - create RMacro node or promote TMacro
              case macroBody of
                Lib.TermMacro _ -> return $ Prom (TMacro (nameString name) [] pos) pos
                Lib.RelMacro _ -> return $ RMacro (nameString name) [] pos
                Lib.ProofMacro _ -> throwError $ UnboundVariable ("Proof macro " ++ nameString name ++ " used in relational type context") (ErrorContext pos "variable lookup")
            Just (params, _) -> 
              -- Macro exists but requires arguments
              throwError $ MacroArityMismatch (nameString name) (length params) 0 (ErrorContext pos "macro arity check")
            Nothing -> throwError $ UnboundVariable ("Unknown relational variable: " ++ nameString name) (ErrorContext pos "variable lookup")

elaborateRType (RRArr rawLeft rawRight pos) = do
  left <- elaborateRType rawLeft
  right <- elaborateRType rawRight
  return $ Arr left right pos

elaborateRType (RRAll name rawBody pos) = do
  ctx <- ask
  let varName = nameString name
  let newCtx = bindRelVar varName ctx
  body <- local (const newCtx) (elaborateRType rawBody)
  return $ All varName body pos

-- | Juxtaposition in relational types is *only* allowed to form a
--   (prefix or infix) macro application.  Anything left over after
--   re‑parsing is therefore an error.
elaborateRType raw@(RRApp _ _ pos) = do
  ctx  <- ask
  let flattened = flattenAppsR raw
      ops = mixfixKeywords (macroEnv ctx)
      toks = map (toTokR ops) flattened
  -- Check if this contains mixfix operators
  if hasOperatorR toks
    then -- Contains mixfix operators - use mixfix parsing
      reparseRTypes pos flattened
    else -- No mixfix operators - check for simple macro application
      case flattened of
        (RRVar name _ : args) -> do
          let macroName = nameString name
          case Map.lookup macroName (Lib.macroDefinitions (macroEnv ctx)) of
            Nothing -> throwError $ InvalidMixfixPattern "bare application is illegal for Rel" (ErrorContext pos "relational macro application")
            Just (params, _) -> smartAppR macroName params args pos
        _ -> throwError $ InvalidMixfixPattern "bare application is illegal for Rel" (ErrorContext pos "relational macro application")
  where
    smartAppR macroName params args macroPos = 
      smartAppGeneric elaborateRType RMacro (\_ _ _ -> error "Relations don't support application") False macroName params args macroPos

elaborateRType raw@(RRComp _ _ pos) = do
  ctx <- ask
  let ops = mixfixKeywords (macroEnv ctx)
      toks = map (toTokR ops) (flattenAppsR raw)
  case hasOperatorR toks of
    False -> elaborateCompLeft raw
    True  -> reparseRTypes pos (flattenAppsR raw)
  where
    elaborateCompLeft (RRComp rawLeft rawRight _) = do
      left <- elaborateRType rawLeft
      right <- elaborateRType rawRight
      return $ Comp left right pos
    elaborateCompLeft other = elaborateRType other

elaborateRType (RRConv rawRType pos) = do
  rtype <- elaborateRType rawRType
  return $ Conv rtype pos

elaborateRType (RRMacro nm args pos) = do
  let name = nameString nm
  ctx <- ask
  case Map.lookup name (Lib.macroDefinitions (macroEnv ctx)) of
    Nothing -> throwError $ UnknownMacro name (ErrorContext pos "macro lookup")
    Just (sig, _) -> elabMacroAppR name sig args pos

elaborateRType (RRProm rawTerm pos) = do
  term <- elaborateTerm rawTerm
  return $ Prom term pos

elaborateProof :: RawProof -> ElaborateM Proof
elaborateProof (RPVar name pos) = do
  ctx <- ask
  case Map.lookup (nameString name) (boundProofVars ctx) of
    Just (bindingDepth, _) ->
      return $ PVar (nameString name) bindingDepth pos
    Nothing -> throwError $ UnboundVariable ("Unknown proof variable: " ++ nameString name) (ErrorContext pos "variable lookup")

elaborateProof raw@(RPApp _ _ pos) = do
  ctx  <- ask
  let flattened = flattenAppsP raw
      ops = mixfixKeywords (macroEnv ctx)
      toks = map (toTokP ops) flattened
  -- Check if this contains mixfix operators
  if hasOperatorP toks
    then -- Contains mixfix operators - use mixfix parsing
      reparseProofs pos flattened
    else -- No mixfix operators - check for simple macro application or regular application
      case flattened of
        [rawFunc, rawArg] -> do
          -- Simple binary application - handle directly
          func <- elaborateProof rawFunc
          arg <- elaborateProof rawArg
          return $ AppP func arg pos
        (RPVar name _ : args) -> do
          let macroName = nameString name
          case Map.lookup macroName (Lib.macroDefinitions (macroEnv ctx)) of
            Nothing -> throwError $ InvalidMixfixPattern "bare application is illegal for Proof" (ErrorContext pos "proof macro application")
            Just (params, _) -> smartAppP macroName params args pos
        _ -> throwError $ InvalidMixfixPattern "bare application is illegal for Proof" (ErrorContext pos "proof macro application")
  where
    smartAppP macroName params args macroPos = 
      smartAppGeneric elaborateProof PMacro AppP True macroName params args macroPos

elaborateProof (RPTheorem name rawArgs pos) = do
  ctx <- ask
  let theoremName = nameString name
  case Map.lookup theoremName (Lib.theoremDefinitions (theoremEnv ctx)) of
    Nothing -> throwError $ UnknownTheorem theoremName (ErrorContext pos "theorem lookup")
    Just (bindings, _, _) -> do
      when (length bindings /= length rawArgs) $
        throwError $ TheoremArityMismatch theoremName (length bindings) (length rawArgs) (ErrorContext pos "variable lookup")
      args <- mapM elaborateArg rawArgs
      return $ PTheoremApp theoremName args pos

elaborateProof (RPLamP name rawRType rawBody pos) = do
  ctx <- ask
  elaboratedRType <- elaborateRType rawRType
  let varName = nameString name
  -- Create a dummy judgment for the proof variable
  let judgment = RelJudgment (Var "dummy" 0 pos) elaboratedRType (Var "dummy" 0 pos)
  let newCtx = bindProofVar varName judgment ctx
  body <- local (const newCtx) (elaborateProof rawBody)
  return $ LamP varName elaboratedRType body pos

elaborateProof (RPLamT name rawBody pos) = do
  ctx <- ask
  let varName = nameString name
  let newCtx = bindRelVar varName ctx
  body <- local (const newCtx) (elaborateProof rawBody)
  return $ TyLam varName body pos

elaborateProof (RPAppT rawProof rawRType pos) = do
  proof <- elaborateProof rawProof
  rtype <- elaborateRType rawRType
  return $ TyApp proof rtype pos

elaborateProof (RPConv rawTerm1 rawProof rawTerm2 pos) = do
  term1 <- elaborateTerm rawTerm1
  proof <- elaborateProof rawProof
  term2 <- elaborateTerm rawTerm2
  return $ ConvProof term1 proof term2 pos

elaborateProof (RPIota rawTerm1 rawTerm2 pos) = do
  term1 <- elaborateTerm rawTerm1
  term2 <- elaborateTerm rawTerm2
  return $ Iota term1 term2 pos

elaborateProof (RPRho x rawT1 rawT2 rawP1 rawP2 pos) = do
  ctx <- ask
  let ctxWithX = bindTermVar (nameString x) ctx
  t1 <- local (const ctxWithX) (elaborateTerm rawT1)
  t2 <- local (const ctxWithX) (elaborateTerm rawT2)
  p1 <- elaborateProof rawP1     --  x NOT in scope here
  p2 <- elaborateProof rawP2
  return $ RhoElim (nameString x) t1 t2 p1 p2 pos

elaborateProof (RPPi rawProof x u v rawQ pos) = do
  p <- elaborateProof rawProof
  ctx <- ask
  -- Bind x as a term variable
  let xName = nameString x
      uName = nameString u
      vName = nameString v
      dummyJudgment = RelJudgment (Var "dummy" 0 pos) (RVar "dummy" 0 pos) (Var "dummy" 0 pos)
      ctxWithX  = bindTermVar  xName ctx
      ctxWithU  = bindProofVar uName dummyJudgment ctxWithX
      ctxWithUV = bindProofVar vName dummyJudgment ctxWithU
  -- Elaborate q in the extended context
  q <- local (const ctxWithUV) (elaborateProof rawQ)
  return $ Pi p xName uName vName q pos

elaborateProof (RPConvIntro rawProof pos) = do
  proof <- elaborateProof rawProof
  return $ ConvIntro proof pos

elaborateProof (RPConvElim rawProof pos) = do
  proof <- elaborateProof rawProof
  return $ ConvElim proof pos

elaborateProof (RPPair rawProof1 rawProof2 pos) = do
  proof1 <- elaborateProof rawProof1
  proof2 <- elaborateProof rawProof2
  return $ Pair proof1 proof2 pos

elaborateProof (RPMixfix nm args pos) = do
  let name = nameString nm
  ctx <- ask
  case Map.lookup name (Lib.macroDefinitions (macroEnv ctx)) of
    Nothing -> throwError $ UnknownMacro name (ErrorContext pos "macro lookup")
    Just (sig, _) -> elabMacroAppP name sig args pos

elaborateArg :: RawArg -> ElaborateM TheoremArg
elaborateArg (RawTermArg rawTerm) = do
  term <- elaborateTerm rawTerm
  return $ TermArg term
elaborateArg (RawRelArg rawRType) = do
  rtype <- elaborateRType rawRType
  return $ RelArg rtype
elaborateArg (RawProofArg rawProof) = do
  proof <- elaborateProof rawProof
  return $ ProofArg proof