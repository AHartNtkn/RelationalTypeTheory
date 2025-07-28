-- | Mixfix pattern parsing and analysis utilities
-- This module handles the parsing and analysis of mixfix operators,
-- extracting holes, literals, and determining default fixities.
module Parser.Mixfix
  ( MixfixPart(..)
  , parseMixfixPattern
  , splitMixfix
  , holes
  , defaultFixity
  , mixfixKeywords
  ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Core.Syntax (MacroEnvironment(..), Fixity(..))

-- | Principled representation of mixfix pattern parts
data MixfixPart = Hole | Literal String
  deriving (Show, Eq)

-- | Parse a mixfix identifier into its constituent parts
-- "_+_" -> [Hole, Literal "+", Hole]
-- "if_then_else_" -> [Literal "if", Hole, Literal "then", Hole, Literal "else", Hole]
-- "not_" -> [Literal "not", Hole]
-- "_!" -> [Hole, Literal "!"]
-- "regular" -> [Literal "regular"]
parseMixfixPattern :: String -> [MixfixPart]
parseMixfixPattern = go
  where
    go [] = []
    go ('_' : rest) = Hole : go rest
    go str =
      let (literal, rest) = span (/= '_') str
       in if null literal
            then go rest
            else Literal literal : go rest

-- | Count the number of holes in a mixfix pattern
holes :: String -> Int
holes = length . filter isHole . parseMixfixPattern
  where
    isHole Hole = True
    isHole _ = False

-- | Extract just the literal parts from a mixfix pattern (for backward compatibility)
splitMixfix :: String -> [String]
splitMixfix = map extractLiteral . filter isLiteral . parseMixfixPattern
  where
    isLiteral (Literal _) = True
    isLiteral _ = False
    extractLiteral (Literal s) = s
    extractLiteral _ = error "extractLiteral called on non-literal"

-- | Default fixity for macros based on hole count and position
defaultFixity :: String -> Fixity
defaultFixity name = case holes name of
  2 -> Infixl 6   -- Haskell's default for binary infix
  1 | head name == '_' -> Postfix 8
    | last name == '_' -> Prefix  9
  _ -> Prefix 9

-- | Extract all mixfix keywords (literal segments) from macro definitions
mixfixKeywords :: MacroEnvironment -> Set.Set String
mixfixKeywords env =
  Set.fromList
    . filter (not . null)
    . concatMap splitMixfix
    . filter ('_' `elem`) -- Only process mixfix patterns (containing underscores)
    . Map.keys
    $ macroDefinitions env