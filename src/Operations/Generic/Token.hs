{-# LANGUAGE LambdaCase #-}

-- | Generic token conversion for mixfix parsing.
-- This module eliminates the duplication between toTokT, toTokR, and toTokP functions.

module Operations.Generic.Token
  ( -- * Typeclass
    ToTokenAst(..)
    -- * Generic operations  
  , toTok
  , hasOperatorG
  , Tok(..)
  ) where

import qualified Data.Set as S
import Text.Megaparsec (SourcePos)
import Core.Raw (Name(..), RawTerm(..), RawRType(..), RawProof(..))

-- | Token type for mixfix parsing
data Tok a = TV a                        -- operand
           | TOP String SourcePos          -- operator literal token
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- | Core typeclass for token conversion
--------------------------------------------------------------------------------

class ToTokenAst a where
  -- | Extract variable information if this is a variable node
  extractVarInfo :: a -> Maybe (Name, SourcePos)

--------------------------------------------------------------------------------
-- | Generic token conversion
--------------------------------------------------------------------------------

-- | Convert AST node to token, checking if it's an operator
toTok :: ToTokenAst a => S.Set String -> a -> Tok a
toTok ops ast = 
  case extractVarInfo ast of
    Just (Name nm, pos) 
      | nm `S.member` ops -> TOP nm pos
      | otherwise -> TV ast
    Nothing -> TV ast

-- | Check if there are any operator tokens in the list
hasOperatorG :: [Tok a] -> Bool
hasOperatorG = any isOp
  where
    isOp (TOP _ _) = True
    isOp _ = False

--------------------------------------------------------------------------------
-- | Instances for Raw AST types
--------------------------------------------------------------------------------

instance ToTokenAst RawTerm where
  extractVarInfo = \case
    RTVar name pos -> Just (name, pos)
    _ -> Nothing

instance ToTokenAst RawRType where  
  extractVarInfo = \case
    RRVar name pos -> Just (name, pos)
    _ -> Nothing

instance ToTokenAst RawProof where
  extractVarInfo = \case
    RPVar name pos -> Just (name, pos)
    _ -> Nothing