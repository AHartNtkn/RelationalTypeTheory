{-# LANGUAGE LambdaCase #-}

-- | Generic token conversion for mixfix parsing.
-- This module uses the unified Raw type instead of separate raw types.

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
import Core.Raw (Name(..), Raw(..))

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
-- | Instance for unified Raw AST type
--------------------------------------------------------------------------------

instance ToTokenAst Raw where
  extractVarInfo = \case
    RawVar name pos -> Just (name, pos)
    _ -> Nothing