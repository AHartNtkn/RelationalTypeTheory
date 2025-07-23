{-# LANGUAGE OverloadedStrings #-}

module TermOpsSpec (spec) where

import Context (extendMacroEnvironment, noMacros)
import Errors
import Lib
import Normalize
import Test.Hspec
import Text.Megaparsec (initialPos)
import TypeOps

spec :: Spec
spec = do
  termExpansionSpec
  termExpansionErrorSpec
  termExpansionEdgeCasesSpec

-- | Test basic TMacro expansion functionality
termExpansionSpec :: Spec
termExpansionSpec = describe "TMacro expansion" $ do
  it "expands simple TMacro with no parameters" $ do
    let macroEnv = extendMacroEnvironment "true" [] (TermMacro (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
        term = TMacro "true" [] (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasTermExpanded result `shouldBe` True
        termExpansionSteps result `shouldBe` 1
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands TMacro with single parameter" $ do
    let macroEnv = extendMacroEnvironment "id" ["x"] (TermMacro (Var "x" 0 (initialPos "test"))) defaultFixity noMacros
        term = TMacro "id" [Var "a" (-1) (initialPos "test")] (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` Var "a" (-1) (initialPos "test")
        wasTermExpanded result `shouldBe` True
        termExpansionSteps result `shouldBe` 1
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands TMacro with multiple parameters" $ do
    let macroEnv = extendMacroEnvironment "app" ["f", "x"] (TermMacro (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
        term = TMacro "app" [Var "g" (-1) (initialPos "test"), Var "y" (-1) (initialPos "test")] (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` App (Var "g" (-1) (initialPos "test")) (Var "y" (-1) (initialPos "test")) (initialPos "test")
        wasTermExpanded result `shouldBe` True
        termExpansionSteps result `shouldBe` 1
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands nested TMacros" $ do
    let macroEnv =
          extendMacroEnvironment "id" ["x"] (TermMacro (Var "x" 0 (initialPos "test"))) defaultFixity $
            extendMacroEnvironment "twice" ["f", "x"] (TermMacro (App (Var "f" 1 (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
        term = TMacro "twice" [TMacro "id" [Var "f" (-1) (initialPos "test")] (initialPos "test"), Var "x" (-1) (initialPos "test")] (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` App (Var "f" (-1) (initialPos "test")) (App (Var "f" (-1) (initialPos "test")) (Var "x" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasTermExpanded result `shouldBe` True
        termExpansionSteps result `shouldSatisfy` (> 1)
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands TMacros in complex terms" $ do
    let macroEnv = extendMacroEnvironment "const" ["x", "y"] (TermMacro (Var "x" 1 (initialPos "test"))) defaultFixity noMacros
        term = Lam "z" (App (TMacro "const" [Var "z" 0 (initialPos "test"), Var "w" (-1) (initialPos "test")] (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` Lam "z" (App (Var "z" 0 (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasTermExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "does not expand when no TMacros present" $ do
    let macroEnv = noMacros
        term = Lam "x" (App (Var "f" (-1) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` term
        wasTermExpanded result `shouldBe` False
        termExpansionSteps result `shouldBe` 0
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

-- | Test TMacro expansion error cases
termExpansionErrorSpec :: Spec
termExpansionErrorSpec = describe "TMacro expansion errors" $ do
  it "fails on undefined macro" $ do
    let macroEnv = noMacros
        term = TMacro "undefined" [Var "x" 0 (initialPos "test")] (initialPos "test")
    case expandTermMacros macroEnv term of
      Left (UnboundMacro name _) -> name `shouldBe` "undefined"
      Left err -> expectationFailure $ "Expected UnboundMacro error, got: " ++ show err
      Right _ -> expectationFailure "Expected error for undefined macro"

  it "fails on macro arity mismatch - too few arguments" $ do
    let macroEnv = extendMacroEnvironment "binary" ["x", "y"] (TermMacro (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
        term = TMacro "binary" [Var "a" 0 (initialPos "test")] (initialPos "test") -- Missing second argument
    case expandTermMacros macroEnv term of
      Left (MacroArityMismatch name expected actual _) -> do
        name `shouldBe` "binary"
        expected `shouldBe` 2
        actual `shouldBe` 1
      Left err -> expectationFailure $ "Expected MacroArityMismatch error, got: " ++ show err
      Right _ -> expectationFailure "Expected error for arity mismatch"

  it "fails on macro arity mismatch - too many arguments" $ do
    let macroEnv = extendMacroEnvironment "unary" ["x"] (TermMacro (Var "x" 0 (initialPos "test"))) defaultFixity noMacros
        term = TMacro "unary" [Var "a" 0 (initialPos "test"), Var "b" 0 (initialPos "test")] (initialPos "test") -- Extra argument
    case expandTermMacros macroEnv term of
      Left (MacroArityMismatch name expected actual _) -> do
        name `shouldBe` "unary"
        expected `shouldBe` 1
        actual `shouldBe` 2
      Left err -> expectationFailure $ "Expected MacroArityMismatch error, got: " ++ show err
      Right _ -> expectationFailure "Expected error for arity mismatch"

  it "fails when trying to use relational macro as term macro" $ do
    let macroEnv = extendMacroEnvironment "relMacro" ["X"] (RelMacro (RVar "X" 0 (initialPos "test"))) defaultFixity noMacros
        term = TMacro "relMacro" [Var "x" 0 (initialPos "test")] (initialPos "test")
    case expandTermMacros macroEnv term of
      Left (UnboundMacro name _) -> name `shouldBe` "relMacro"
      Left err -> expectationFailure $ "Expected UnboundMacro error, got: " ++ show err
      Right _ -> expectationFailure "Expected error when using relational macro as term macro"

-- | Test edge cases and special scenarios
termExpansionEdgeCasesSpec :: Spec
termExpansionEdgeCasesSpec = describe "TMacro expansion edge cases" $ do
  it "handles deeply nested macro expansions within step limit" $ do
    -- Test legitimate deep nesting that stays within reasonable bounds
    let macroEnv = extendMacroEnvironment "wrap" ["x"] (TermMacro (Lam "f" (App (Var "f" 0 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
        term = TMacro "wrap" [TMacro "wrap" [TMacro "wrap" [Var "base" (-1) (initialPos "test")] (initialPos "test")] (initialPos "test")] (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        wasTermExpanded result `shouldBe` True
        termExpansionSteps result `shouldSatisfy` (>= 3)
      Left err -> expectationFailure $ "Unexpected error in valid nested expansion: " ++ show err

  it "expands TMacros in WHNF mode" $ do
    let macroEnv = extendMacroEnvironment "id" ["x"] (TermMacro (Var "x" 0 (initialPos "test"))) defaultFixity noMacros
        term = TMacro "id" [Var "a" (-1) (initialPos "test")] (initialPos "test")
    case expandTermMacrosWHNF macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` Var "a" (-1) (initialPos "test")
        wasTermExpanded result `shouldBe` True
        termExpansionSteps result `shouldBe` 1
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "handles TMacros with complex argument expressions" $ do
    let macroEnv = extendMacroEnvironment "apply" ["f", "x"] (TermMacro (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
        complexArg = Lam "y" (App (Var "g" (-1) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        term = TMacro "apply" [complexArg, Var "z" (-1) (initialPos "test")] (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` App complexArg (Var "z" (-1) (initialPos "test")) (initialPos "test")
        wasTermExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "preserves variable scoping during expansion" $ do
    let macroEnv = extendMacroEnvironment "test" ["x"] (TermMacro (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
        term = TMacro "test" [Var "a" (-1) (initialPos "test")] (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` Lam "y" (App (Var "a" (-1) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasTermExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "handles empty argument lists correctly" $ do
    let macroEnv = extendMacroEnvironment "unit" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
        term = TMacro "unit" [] (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")
        wasTermExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "correctly substitutes multiple occurrences of parameters" $ do
    let macroEnv = extendMacroEnvironment "dup" ["x"] (TermMacro (App (Var "x" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
        term = TMacro "dup" [Var "f" (-1) (initialPos "test")] (initialPos "test")
    case expandTermMacros macroEnv term of
      Right result -> do
        expandedTerm result `shouldBe` App (Var "f" (-1) (initialPos "test")) (Var "f" (-1) (initialPos "test")) (initialPos "test")
        wasTermExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands term macros within promotions in relational contexts" $ do
    let macroEnv = extendMacroEnvironment "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
        promotedMacro = Prom (TMacro "Id" [] (initialPos "test")) (initialPos "test")
    -- This tests that term macros can be expanded within promotions
    case expandMacros macroEnv promotedMacro of
      Right result -> do
        expandedType result `shouldBe` Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err
