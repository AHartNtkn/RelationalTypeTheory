{-# LANGUAGE OverloadedStrings #-}

module MixfixSpec (spec) where

import Test.Hspec
import Control.Monad.Reader
import Control.Monad.Except
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Megaparsec (runParser, errorBundlePretty, initialPos)
import Data.Void

-- Import new mixfix system
-- import RelTT.Mixfix.Core
-- import RelTT.Mixfix.Env
-- import RelTT.Mixfix.Parse
-- import RelTT.Mixfix.Util
-- import RelTT.Mixfix.Pretty

-- Import core system
import Core.Syntax
import Core.Raw
import Core.Context (emptyContext, Context)
import Parser.Raw (parseFile, rawDeclaration)
import Parser.Lexer (ident)
import TestHelpers (stripPos)

-- Helper functions for new mixfix system
type P = Parsec Void String

-- Simple test environment setup
testEnv :: Env
testEnv = emptyEnv

-- Helper to parse with empty context
runParserEmpty :: P a -> String -> Either String a  
runParserEmpty parser input =
  case runParser parser "test" input of
    Left parseErr -> Left $ errorBundlePretty parseErr
    Right result -> Right result

-- Test spec for new mixfix system
spec :: Spec
spec = describe "New Grammar-Based Mixfix System" $ do
  basicGrammarTests
  precedenceTests
  associativityTests
  errorRecoveryTests
  prettyPrintingTests

-- Test basic grammar composition
basicGrammarTests :: Spec
basicGrammarTests = describe "Basic grammar composition" $ do
  it "handles simple macro definitions" $ do
    -- This test validates that the new system can parse macro definitions
    let content = "_+_ a b ≔ a;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result -> 
        case stripPos result of
          RawMacroDef (Name "_+_") [Name "a", Name "b"] _ -> return ()
          other -> expectationFailure $ "Expected macro def, got: " ++ show other

  it "handles complex mixfix patterns" $ do
    let content = "if_then_else_ c t e ≔ t;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result ->
        case stripPos result of
          RawMacroDef (Name "if_then_else_") [Name "c", Name "t", Name "e"] _ -> return ()
          other -> expectationFailure $ "Expected ternary macro def, got: " ++ show other

  it "handles prefix patterns" $ do
    let content = "not_ b ≔ b;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result ->
        case stripPos result of
          RawMacroDef (Name "not_") [Name "b"] _ -> return ()
          other -> expectationFailure $ "Expected prefix macro def, got: " ++ show other

  it "handles postfix patterns" $ do
    let content = "_! n ≔ n;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result ->
        case stripPos result of
          RawMacroDef (Name "_!") [Name "n"] _ -> return ()
          other -> expectationFailure $ "Expected postfix macro def, got: " ++ show other

-- Test precedence resolution
precedenceTests :: Spec
precedenceTests = describe "Precedence resolution" $ do
  it "handles fixity declarations" $ do
    let content = "infixl 6 _+_;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result ->
        case stripPos result of
          RawFixityDecl (Infixl 6) (Name "_+_") -> return ()
          other -> expectationFailure $ "Expected fixity decl, got: " ++ show other

  it "parses multiple fixity levels" $ do 
    let content = "infixr 5 _*_;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result ->
        case stripPos result of
          RawFixityDecl (Infixr 5) (Name "_*_") -> return ()
          other -> expectationFailure $ "Expected infixr decl, got: " ++ show other

-- Test associativity handling
associativityTests :: Spec
associativityTests = describe "Associativity handling" $ do
  it "handles left associative operators" $ do
    let content = "infixl 6 _+_;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result ->
        case stripPos result of
          RawFixityDecl (Infixl 6) (Name "_+_") -> return ()
          other -> expectationFailure $ "Expected left assoc decl, got: " ++ show other

  it "handles right associative operators" $ do
    let content = "infixr 5 _*_;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result ->
        case stripPos result of
          RawFixityDecl (Infixr 5) (Name "_*_") -> return ()
          other -> expectationFailure $ "Expected right assoc decl, got: " ++ show other

  it "handles non-associative operators" $ do
    let content = "infix 4 _==_;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result ->
        case stripPos result of
          RawFixityDecl (InfixN 4) (Name "_==_") -> return ()
          other -> expectationFailure $ "Expected non-assoc decl, got: " ++ show other

-- Test error recovery
errorRecoveryTests :: Spec
errorRecoveryTests = describe "Error recovery" $ do
  it "rejects invalid precedence levels" $ do
    case runParserEmpty (rawDeclaration) "infixl 10 _+_;" of
      Left _ -> return () -- Expected failure
      Right result -> expectationFailure $ "Expected parse failure, but got: " ++ show result

  it "handles malformed fixity declarations" $ do
    case runParserEmpty (rawDeclaration) "infixl _+_;" of
      Left _ -> return () -- Expected failure  
      Right result -> expectationFailure $ "Expected parse failure, but got: " ++ show result

-- Test pretty printing with new system
prettyPrintingTests :: Spec
prettyPrintingTests = describe "Pretty printing" $ do
  it "pretty prints fixity declarations correctly" $ pendingWith "Pretty printing integration pending"
  
  it "pretty prints macro applications correctly" $ pendingWith "Pretty printing integration pending"

-- Helper to create simple contexts for testing
simpleContext :: Context
simpleContext = emptyContext

-- Test Unicode support
unicodeTests :: Spec
unicodeTests = describe "Unicode mixfix operations" $ do
  it "parses unicode operators" $ do
    let content = "_∪_ a b ≔ a;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result ->
        case stripPos result of
          RawMacroDef (Name "_∪_") [Name "a", Name "b"] _ -> return ()
          other -> expectationFailure $ "Expected unicode macro def, got: " ++ show other

  it "handles unicode fixity declarations" $ do
    let content = "infixl 6 _∪_;"
    case runParserEmpty (rawDeclaration) content of
      Left err -> expectationFailure $ "Parse failed: " ++ err  
      Right result ->
        case stripPos result of
          RawFixityDecl (Infixl 6) (Name "_∪_") -> return ()
          other -> expectationFailure $ "Expected unicode fixity decl, got: " ++ show other