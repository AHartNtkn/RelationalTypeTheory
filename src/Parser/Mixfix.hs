{-# LANGUAGE RankNTypes #-}

module Parser.Mixfix
  ( MixfixSpec (..)
  , generalMixfix
  , buildMixfixOps
  , HasMacroEnv (..)
  ) where

import           Control.Monad
import qualified Control.Monad.Combinators.Expr as Expr
import           Control.Monad.Combinators.Expr (makeExprParser)
import           Control.Monad.Reader           (MonadReader, ask)
import           Control.Applicative            (Alternative)
import           Data.Function                  (on)
import qualified Data.List                      as L
import qualified Data.Map                       as M
import qualified Data.Set                       as S
import           Data.Ord                       (comparing)
import           Data.Void
import           Lib
import           Text.Megaparsec hiding (getSourcePos)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lexer

-- | Everything that changes between terms vs. relations.
data MixfixSpec m expr = MixfixSpec
  { holeParser   :: m expr                            -- ^ how to parse an argument
  , mkMacroNode  :: String -> [expr] -> SourcePos
                 -> expr                              -- ^ constructor  (TMacro / RMacro)
  , isRightBody  :: MacroBody -> Bool                 -- ^ TermMacro ?  RelMacro ?
  , extraOps     :: [[Expr.Operator m expr]]          -- ^ fixed, non‑macro ops
  , smartAppOp   :: Maybe [Expr.Operator m expr]      -- ^ term‑only 'smart application'
  , symbolParser :: String -> m String                -- ^ lexeme parser
  , posParser    :: m SourcePos                       -- ^ position parser
  }

----------------------------------------------------------------------  
-- 1.1  Generic "≥3‑hole / prefix / postfix" parser
----------------------------------------------------------------------
generalMixfix :: (MonadReader ctx m, HasMacroEnv ctx, MonadParsec e s m, Alternative m) => MixfixSpec m expr -> m expr
generalMixfix spec = do
  ctx <- ask
  let env        = getMacroEnv ctx
      defs       = macroDefinitions env
      good name  = maybe False (isRightBody spec . snd) (M.lookup name defs)
      isPost n   = parseMixfixPattern n == [Hole, Literal (last (splitMixfix n))]
      isGen  n   = '_' `elem` n && holes n /= 2 && not (isPost n) && good n
      cand       = filter isGen (M.keys defs)
      sorted     = L.sortBy (comparing (negate . length . splitMixfix)) cand
  choice $ map (try . parseName) sorted
  where
    parseName n = do
      let segs = splitMixfix n
      pos  <- (posParser spec)
      args <- go segs []
      pure $ mkMacroNode spec n (reverse args) pos
    go []       acc = pure acc
    go (l:ls)   acc = symbolParser spec l *> (holeParser spec >>= \a -> go ls (a:acc))

-- Helper typeclass to extract MacroEnvironment from context
class HasMacroEnv ctx where
  getMacroEnv :: ctx -> MacroEnvironment

----------------------------------------------------------------------
-- 1.2  Fixity‑table builder (prefix / postfix / infix)
----------------------------------------------------------------------
buildMixfixOps :: (Monad m, Applicative m) => MixfixSpec m expr -> MacroEnvironment -> [[Expr.Operator m expr]]
buildMixfixOps spec env =
        map bucket [9,8..0]
     ++ maybe [] id (smartAppOp spec) : []
     ++ extraOps spec
  where
    table = M.toList (macroFixities env)
    bucket lvl = [ op
                 | (name, fx) <- table
                 , getLvl fx == lvl
                 , '_' `elem` name  -- Only actual mixfix macros (with underscores) - check this first
                 , length (splitMixfix name) == 1  -- Only simple single-segment operators
                 , name `M.member` macroDefinitions env  -- Skip if macro definition doesn't exist
                 , isRightBody spec (snd (macroDefinitions env M.! name))
                 , op <- fixityToOp name fx
                 ]
    getLvl (Lib.Infixl n)  = n
    getLvl (Lib.Infixr n)  = n
    getLvl (Lib.InfixN n)  = n
    getLvl (Lib.Prefix n)  = n
    getLvl (Lib.Postfix n) = n
    fixityToOp n (Lib.Infixl _)  = [Expr.InfixL  (bin n)]
    fixityToOp n (Lib.Infixr _)  = [Expr.InfixR  (bin n)]
    fixityToOp n (Lib.InfixN _)  = [Expr.InfixN  (bin n)]
    fixityToOp n (Lib.Prefix _)  = [Expr.Prefix  (pre n)]
    fixityToOp n (Lib.Postfix _) = [Expr.Postfix (post n)]
    bin  n = do pos <- (posParser spec)
                _   <- symbolParser spec (extractLit n)
                pure $ \x y -> mkMacroNode spec n [x,y] pos
    pre  n = do pos <- (posParser spec)
                _   <- symbolParser spec (head (splitMixfix n))
                pure $ \y   -> mkMacroNode spec n [y]   pos
    post n = do pos <- (posParser spec)
                _   <- symbolParser spec (last (splitMixfix n))
                pure $ \x   -> mkMacroNode spec n [x]   pos
    extractLit n = head (splitMixfix n)  -- For binary infix: "_+_" -> "+"