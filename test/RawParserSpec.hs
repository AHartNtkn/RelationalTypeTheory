{-# LANGUAGE OverloadedStrings #-}

module RawParserSpec (spec) where

import Core.Raw
import Parser.Raw
import Test.Hspec
import Text.Megaparsec

spec :: Spec
spec = do
  describe "Raw Term Parsing" $ do
    it "parses simple variable" $ do
      case runParser rawTerm "test" "x" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RTVar (Name "x") _) -> return ()
        Right other -> expectationFailure $ "Expected RTVar, got: " ++ show other

    it "parses lambda expression" $ do
      case runParser rawTerm "test" "λ x . x" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RTLam (Name "x") (RTVar (Name "x") _) _) -> return ()
        Right other -> expectationFailure $ "Expected RTLam, got: " ++ show other

    it "parses function application" $ do
      case runParser rawTerm "test" "f x" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RTApp (RTVar (Name "f") _) (RTVar (Name "x") _) _) -> return ()
        Right other -> expectationFailure $ "Expected RTApp, got: " ++ show other

  describe "Raw RType Parsing" $ do
    it "parses relational variable" $ do
      case runParser rawRType "test" "R" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RRVar (Name "R") _) -> return ()
        Right other -> expectationFailure $ "Expected RRVar, got: " ++ show other

    it "parses arrow type" $ do
      case runParser rawRType "test" "A → B" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RRArr (RRVar (Name "A") _) (RRVar (Name "B") _) _) -> return ()
        Right other -> expectationFailure $ "Expected RRArr, got: " ++ show other

  describe "Raw Proof Parsing" $ do
    it "parses proof variable" $ do
      case runParser rawProof "test" "p" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RPVar (Name "p") _) -> return ()
        Right other -> expectationFailure $ "Expected RPVar, got: " ++ show other

    it "parses iota proof" $ do
      case runParser rawProof "test" "ι⟨ x , y⟩" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RPIota (RTVar (Name "x") _) (RTVar (Name "y") _) _) -> return ()
        Right other -> expectationFailure $ "Expected RPIota, got: " ++ show other

  describe "Raw Declaration Parsing" $ do
    it "parses simple macro" $ do
      case runParser rawDeclaration "test" "id ≔ λ x . x;" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RawMacro (Name "id") [] _) -> return ()
        Right other -> expectationFailure $ "Expected RawMacro, got: " ++ show other

    it "parses theorem" $ do
      case runParser rawDeclaration "test" "⊢ test (x : term) : x [R] x ≔ p;" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RawTheorem (Name "test") _ _ _) -> return ()
        Right other -> expectationFailure $ "Expected RawTheorem, got: " ++ show other