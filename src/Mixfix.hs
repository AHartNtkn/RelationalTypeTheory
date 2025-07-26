{-# LANGUAGE OverloadedStrings #-}
module Mixfix
  ( holes, splitMixfix, parseMixfixPattern, MixfixPiece(..)
  , mixfixKeywords
  ) where

import qualified Data.Text as T
import qualified Data.Set  as S
import qualified Data.Map as Map
import           Lib (MacroEnvironment(..))

holes :: String -> Int
holes = length . filter (== '_')

splitMixfix :: String -> [String]
splitMixfix = filter (not . null) . splitOn '_'
  where splitOn c = map T.unpack . T.split (==c) . T.pack

data MixfixPiece = Hole | Literal String deriving (Show, Eq)

parseMixfixPattern :: String -> [MixfixPiece]
parseMixfixPattern s =
  go False (s)
  where
    go _      []       = []
    go False ('_':cs)  = Hole : go False cs
    go False (c : cs)  = let (lit,rest) = span (/= '_') (c:cs)
                         in Literal lit : go False rest
    go True  _         = error "impossible"

mixfixKeywords :: MacroEnvironment -> S.Set String
mixfixKeywords env =
  S.fromList [ lit
             | (k,_) <- Map.toList (macroDefinitions env)
             , '_' `elem` k  -- Only process mixfix patterns containing underscores
             , Literal lit <- parseMixfixPattern k ]