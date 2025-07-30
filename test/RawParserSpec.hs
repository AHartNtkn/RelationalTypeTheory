{-# LANGUAGE OverloadedStrings #-}

module RawParserSpec (spec) where

import Core.Raw
import Parser.Raw
import Test.Hspec
import Text.Megaparsec

spec :: Spec
spec = do
  describe "Unified Raw Parsing" $ do
    it "parses simple variable" $ do
      case runParser raw "test" "x" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RawVar (Name "x") _) -> return ()
        Right other -> expectationFailure $ "Expected RawVar, got: " ++ show other

    it "parses function application" $ do
      case runParser raw "test" "f x" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RawApp (RawVar (Name "f") _) (RawVar (Name "x") _) _) -> return ()
        Right other -> expectationFailure $ "Expected RawApp, got: " ++ show other

    it "parses parenthesized expression" $ do
      case runParser raw "test" "(x)" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RawParens (RawVar (Name "x") _) _) -> return ()
        Right other -> expectationFailure $ "Expected RawParens, got: " ++ show other

    it "parses macro applications" $ do
      case runParser raw "test" "_+_ x y" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RawApp (RawApp (RawVar (Name "_+_") _) (RawVar (Name "x") _) _) (RawVar (Name "y") _) _) -> return ()
        Right other -> expectationFailure $ "Expected RawApp structure, got: " ++ show other

  describe "Raw Declaration Parsing" $ do
    it "parses simple macro definition" $ do
      case runParser rawDeclaration "test" "id ≔ λ x . x;" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RawMacroDef (Name "id") [] _) -> return ()
        Right other -> expectationFailure $ "Expected RawMacroDef, got: " ++ show other

    it "parses parameterized macro definition" $ do
      case runParser rawDeclaration "test" "const x y ≔ x;" of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right (RawMacroDef (Name "const") [Name "x", Name "y"] _) -> return ()
        Right other -> expectationFailure $ "Expected RawMacroDef with params, got: " ++ show other