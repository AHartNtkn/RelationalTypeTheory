-- | Generic utility functions used throughout the RelTT system
module Utils
  ( updateAt
  ) where

-- | Safe list update at a given index
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt i f xs = zipWith (\j x -> if j == i then f x else x) [0..] xs