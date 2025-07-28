{-# LANGUAGE RankNTypes #-}

module Parser.Mixfix
  ( MixfixSpec (..),
    generalMixfix,
    buildMixfixOps,
    HasMacroEnv (..),
  )
where

import qualified Control.Monad.Combinators.Expr as Expr
import Control.Monad.Reader (MonadReader, ask, local)
import qualified Data.List as L
import qualified Data.Map as M
import Data.Ord (comparing)
import Debug.Trace
import Lib (MacroEnvironment(..), MacroBody(..), Fixity(..), MixfixPart(..), parseMixfixPattern, splitMixfix, holes)
import Text.Megaparsec hiding (getSourcePos)

-- | Everything that changes between terms vs. relations.
data MixfixSpec m expr = MixfixSpec
  { -- | how to parse an argument
    holeParser :: m expr,
    -- | constructor  (TMacro / RMacro)
    mkMacroNode ::
      String ->
      [expr] ->
      SourcePos ->
      expr,
    -- | TermMacro ?  RelMacro ?
    isRightBody :: MacroBody -> Bool,
    -- | fixed, non‑macro ops
    extraOps :: [[Expr.Operator m expr]],
    -- | term‑only 'smart application'
    smartAppOp :: Maybe [Expr.Operator m expr],
    -- | lexeme parser
    symbolParser :: String -> m String,
    -- | position parser
    posParser :: m SourcePos
  }

----------------------------------------------------------------------
-- 1.1  Generic "≥3‑hole / prefix / postfix" parser
----------------------------------------------------------------------
generalMixfix :: (MonadReader ctx m, HasMacroEnv ctx, MonadParsec e s m) => MixfixSpec m expr -> m expr
generalMixfix spec = do
  ctx <- ask
  -- Check if mixfix is allowed (to prevent left-recursion)
  case getAllowMixfix ctx of
    False -> empty  -- Skip mixfix parsing when disabled
    True -> do
      let env = getMacroEnv ctx
          defs = macroDefinitions env
          good name = maybe False (isRightBody spec . snd) (M.lookup name defs)
          
          pat n = parseMixfixPattern n
          isPost n = pat n == [Hole, Literal (last (splitMixfix n))]
          isGen n = '_' `elem` n && holes n /= 2 && not (isPost n) && good n
          
          cands = filter isGen (M.keys defs)
          sorted = L.sortBy (comparing (negate . length . splitMixfix)) cands
          
      choice (map (try . parseName) sorted)
  where
    parseName n = do
      pos <- posParser spec
      -- Special handling for first hole to prevent left-recursion
      args <- case parseMixfixPattern n of
        Hole : rest -> do
          -- Parse first hole with mixfix disabled
          h <- local (disableMixfix) (holeParser spec)
          others <- walkPattern rest []
          pure (h : reverse others)
        pat -> do
          -- Pattern starts with literal, proceed normally
          args' <- walkPattern pat []
          pure (reverse args')
      pure $ mkMacroNode spec n args pos
    
    walkPattern [] acc = pure acc
    walkPattern (Hole : rest) acc = do
      a <- holeParser spec
      walkPattern rest (a : acc)
    walkPattern (Literal lit : rest) acc = do
      _ <- symbolParser spec lit
      walkPattern rest acc
    
    -- Helper to disable mixfix in context
    disableMixfix = setAllowMixfix False

-- Helper typeclass to extract MacroEnvironment from context
class HasMacroEnv ctx where
  getMacroEnv :: ctx -> MacroEnvironment
  getAllowMixfix :: ctx -> Bool
  getAllowMixfix _ = True  -- Default to true for backward compatibility
  setAllowMixfix :: Bool -> ctx -> ctx

----------------------------------------------------------------------
-- 1.2  Fixity‑table builder (prefix / postfix / infix)
----------------------------------------------------------------------
buildMixfixOps :: (Monad m) => MixfixSpec m expr -> MacroEnvironment -> [[Expr.Operator m expr]]
buildMixfixOps spec env =
  map bucket [9, 8 .. 0]
    ++ maybe [] id (smartAppOp spec)
    : []
    ++ extraOps spec
  where
    table = M.toList (macroFixities env)
    bucket lvl =
      [ op
        | (name, fx) <- table,
          getLvl fx == lvl,
          '_' `elem` name, -- Only actual mixfix macros (with underscores) - check this first
          length (splitMixfix name) == 1, -- Only simple single-segment operators
          name `M.member` macroDefinitions env, -- Skip if macro definition doesn't exist
          trace ("DEBUG MIXFIX: Checking " ++ name ++ " for body type") True,
          isRightBody spec (snd (macroDefinitions env M.! name)),
          trace ("DEBUG MIXFIX: " ++ name ++ " passed isRightBody check") True,
          op <- fixityToOp name fx
      ]
    getLvl (Lib.Infixl n) = n
    getLvl (Lib.Infixr n) = n
    getLvl (Lib.InfixN n) = n
    getLvl (Lib.Prefix n) = n
    getLvl (Lib.Postfix n) = n
    getLvl (Lib.Closed n) = n
    fixityToOp n (Lib.Infixl _) = [Expr.InfixL (bin n)]
    fixityToOp n (Lib.Infixr _) = [Expr.InfixR (bin n)]
    fixityToOp n (Lib.InfixN _) = [Expr.InfixN (bin n)]
    fixityToOp n (Lib.Prefix _) = [Expr.Prefix (pre n)]
    fixityToOp n (Lib.Postfix _) = [Expr.Postfix (post n)]
    fixityToOp n (Lib.Closed _) = [] -- Closed patterns handled by generalMixfix, not buildMixfixOps
    bin n = do
      pos <- (posParser spec)
      _ <- symbolParser spec (extractLit n)
      pure $ \x y -> mkMacroNode spec n [x, y] pos
    pre n = do
      pos <- (posParser spec)
      _ <- symbolParser spec (head (splitMixfix n))
      pure $ \y -> mkMacroNode spec n [y] pos
    post n = do
      pos <- (posParser spec)
      _ <- symbolParser spec (last (splitMixfix n))
      pure $ \x -> mkMacroNode spec n [x] pos
    extractLit n = head (splitMixfix n) -- For binary infix: "_+_" -> "+"
