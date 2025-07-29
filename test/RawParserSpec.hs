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

    it "parses relational application" $ do
      case runParser rawRType "test" "R S" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RRApp (RRVar (Name "R") _) (RRVar (Name "S") _) _) -> return ()
        Right other -> expectationFailure $ "Expected RRApp, got: " ++ show other

  describe "Raw Proof Parsing" $ do
    it "parses proof variable" $ do
      case runParser rawProof "test" "p" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RPVar (Name "p") _) -> return ()
        Right other -> expectationFailure $ "Expected RPVar, got: " ++ show other

    it "parses proof application" $ do
      case runParser rawProof "test" "p q" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RPApp (RPVar (Name "p") _) (RPVar (Name "q") _) _) -> return ()
        Right other -> expectationFailure $ "Expected RPApp, got: " ++ show other

  describe "Raw Declaration Parsing" $ do
    it "parses simple macro" $ do
      case runParser rawDeclaration "test" "id ≔ λ x . x;" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RawMacro (Name "id") [] _) -> return ()
        Right other -> expectationFailure $ "Expected RawMacro, got: " ++ show other