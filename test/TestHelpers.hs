{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module TestHelpers
  ( PositionInsensitive (..),
    shouldBeEqualProof,
    shouldBeEqualDeclaration,
    simpleParamInfo,
    simpleTermMacro,
    simpleRelMacro,
  )
where

import Core.Syntax
import Control.Monad (unless)
import Test.Hspec ( expectationFailure, Expectation )


shouldBeEqualProof :: Proof -> Proof -> Expectation
shouldBeEqualProof actual expected =
  unless (actual == expected) $
    expectationFailure $
      "Proofs not structurally equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

shouldBeEqualDeclaration :: Declaration -> Declaration -> Expectation  
shouldBeEqualDeclaration actual expected =
  unless (actual == expected) $
    expectationFailure $
      "Declarations not structurally equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

-- Helper type class for position-insensitive comparison
class PositionInsensitive a where
  shouldBeEqual :: a -> a -> Expectation

instance PositionInsensitive Term where
  shouldBeEqual actual expected = 
    unless (actual == expected) $
      expectationFailure $
        "Terms not equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

instance PositionInsensitive RType where
  shouldBeEqual actual expected = 
    unless (actual == expected) $
      expectationFailure $
        "RTypes not equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

instance PositionInsensitive Proof where
  shouldBeEqual = shouldBeEqualProof

instance PositionInsensitive Declaration where
  shouldBeEqual = shouldBeEqualDeclaration

instance PositionInsensitive RelJudgment where
  shouldBeEqual rj1 rj2 =
    unless (rj1 == rj2) $
      expectationFailure $
        "RelJudgments not equal:\nExpected: " ++ show rj2 ++ "\nActual: " ++ show rj1

instance (PositionInsensitive a) => PositionInsensitive [a] where
  shouldBeEqual [] [] = return ()
  shouldBeEqual (x : xs) (y : ys) = do
    shouldBeEqual x y
    shouldBeEqual xs ys
  shouldBeEqual actual expected =
    expectationFailure $ "Lists have different lengths:\nExpected: " ++ show (length expected) ++ " elements\nActual: " ++ show (length actual) ++ " elements"



-- | Helper functions for creating test macro signatures
simpleParamInfo :: String -> VarKind -> ParamInfo
simpleParamInfo name kind = ParamInfo name kind False []

-- | Create a simple term macro sig for testing
simpleTermMacro :: [String] -> Term -> MacroSig
simpleTermMacro params body = ([simpleParamInfo p TermK | p <- params], TermMacro body)

-- | Create a simple rel macro sig for testing
simpleRelMacro :: [String] -> RType -> MacroSig
simpleRelMacro params body = ([simpleParamInfo p RelK | p <- params], RelMacro body)

-- | Create a simple proof macro sig for testing
simpleProofMacro :: [String] -> Proof -> MacroSig
simpleProofMacro params body = ([simpleParamInfo p ProofK | p <- params], ProofMacro body)
