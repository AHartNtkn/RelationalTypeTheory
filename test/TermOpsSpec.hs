{-# LANGUAGE OverloadedStrings #-}

module TermOpsSpec (spec) where

import Core.Errors
import Core.Syntax
import Core.Context (extendMacroContext, emptyContext)
import Operations.Generic.Expansion (expandFully, expandWHNF, ExpansionResult(..))
import Operations.Generic.Mixfix (defaultFixity)
import Test.Hspec
import Text.Megaparsec (initialPos)

-- Helper to create ParamInfo for tests
testParamInfo :: String -> ParamInfo
testParamInfo name = ParamInfo name TermK False []

-- Helper to create ParamInfo for relational tests
testRelParamInfo :: String -> ParamInfo
testRelParamInfo name = ParamInfo name RelK False []

spec :: Spec
spec = do
  termExpansionSpec
  termExpansionErrorSpec
  termExpansionEdgeCasesSpec

-- | Test basic TMacro expansion functionality
termExpansionSpec :: Spec
termExpansionSpec = describe "TMacro expansion" $ do
  it "expands simple TMacro with no parameters" $ do
    let macroEnv = extendMacroContext "true" [] (TermMacro (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "true" [] (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
        expansionSteps result `shouldBe` 1
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands TMacro with single parameter" $ do
    let macroEnv = extendMacroContext "id" [testParamInfo "x"] (TermMacro (Var "x" 0 (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "id" [MTerm (Var "a" (-1) (initialPos "test"))] (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` Var "a" (-1) (initialPos "test")
        wasExpanded result `shouldBe` True
        expansionSteps result `shouldBe` 1
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands TMacro with multiple parameters" $ do
    let macroEnv = extendMacroContext "app" [testParamInfo "f", testParamInfo "x"] (TermMacro (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "app" [MTerm (Var "g" (-1) (initialPos "test")), MTerm (Var "y" (-1) (initialPos "test"))] (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` App (Var "g" (-1) (initialPos "test")) (Var "y" (-1) (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
        expansionSteps result `shouldBe` 1
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands nested TMacros" $ do
    let macroEnv =
          extendMacroContext "id" [testParamInfo "x"] (TermMacro (Var "x" 0 (initialPos "test"))) (defaultFixity "TEST") $
            extendMacroContext "twice" [testParamInfo "f", testParamInfo "x"] (TermMacro (App (Var "f" 1 (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "twice" [MTerm (TMacro "id" [MTerm (Var "f" (-1) (initialPos "test"))] (initialPos "test")), MTerm (Var "x" (-1) (initialPos "test"))] (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` App (Var "f" (-1) (initialPos "test")) (App (Var "f" (-1) (initialPos "test")) (Var "x" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
        expansionSteps result `shouldSatisfy` (> 1)
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands TMacros in complex terms" $ do
    let macroEnv = extendMacroContext "const" [testParamInfo "x", testParamInfo "y"] (TermMacro (Var "x" 1 (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = Lam "z" (App (TMacro "const" [MTerm (Var "z" 0 (initialPos "test")), MTerm (Var "w" (-1) (initialPos "test"))] (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` Lam "z" (App (Var "z" 0 (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "does not expand when no TMacros present" $ do
    let macroEnv = emptyContext
        term = Lam "x" (App (Var "f" (-1) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` term
        wasExpanded result `shouldBe` False
        expansionSteps result `shouldBe` 0
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

-- | Test TMacro expansion error cases
termExpansionErrorSpec :: Spec
termExpansionErrorSpec = describe "TMacro expansion errors" $ do
  it "fails on undefined macro" $ do
    let macroEnv = emptyContext
        term = TMacro "undefined" [MTerm (Var "x" 0 (initialPos "test"))] (initialPos "test")
    case expandFully macroEnv term of
      Left (UnboundMacro name _) -> name `shouldBe` "undefined"
      Left err -> expectationFailure $ "Expected UnboundMacro error, got: " ++ show err
      Right _ -> expectationFailure "Expected error for undefined macro"

  it "fails on macro arity mismatch - too few arguments" $ do
    let macroEnv = extendMacroContext "binary" [testParamInfo "x", testParamInfo "y"] (TermMacro (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "binary" [MTerm (Var "a" 0 (initialPos "test"))] (initialPos "test") -- Missing second argument
    case expandFully macroEnv term of
      Left (MacroArityMismatch name expected actual _) -> do
        name `shouldBe` "binary"
        expected `shouldBe` 2
        actual `shouldBe` 1
      Left err -> expectationFailure $ "Expected MacroArityMismatch error, got: " ++ show err
      Right _ -> expectationFailure "Expected error for arity mismatch"

  it "fails on macro arity mismatch - too many arguments" $ do
    let macroEnv = extendMacroContext "unary" [testParamInfo "x"] (TermMacro (Var "x" 0 (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "unary" [MTerm (Var "a" 0 (initialPos "test")), MTerm (Var "b" 0 (initialPos "test"))] (initialPos "test") -- Extra argument
    case expandFully macroEnv term of
      Left (MacroArityMismatch name expected actual _) -> do
        name `shouldBe` "unary"
        expected `shouldBe` 1
        actual `shouldBe` 2
      Left err -> expectationFailure $ "Expected MacroArityMismatch error, got: " ++ show err
      Right _ -> expectationFailure "Expected error for arity mismatch"

  it "fails when trying to use relational macro as term macro" $ do
    let macroEnv = extendMacroContext "relMacro" [testRelParamInfo "X"] (RelMacro (RVar "X" 0 (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "relMacro" [MTerm (Var "x" 0 (initialPos "test"))] (initialPos "test")
    case expandFully macroEnv term of
      Left (UnboundMacro name _) -> name `shouldBe` "relMacro"
      Left err -> expectationFailure $ "Expected UnboundMacro error, got: " ++ show err
      Right _ -> expectationFailure "Expected error when using relational macro as term macro"

-- | Test edge cases and special scenarios
termExpansionEdgeCasesSpec :: Spec
termExpansionEdgeCasesSpec = describe "TMacro expansion edge cases" $ do
  it "handles deeply nested macro expansions within step limit" $ do
    -- Test legitimate deep nesting that stays within reasonable bounds
    let macroEnv = extendMacroContext "wrap" [testParamInfo "x"] (TermMacro (Lam "f" (App (Var "f" 0 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "wrap" [MTerm (TMacro "wrap" [MTerm (TMacro "wrap" [MTerm (Var "base" (-1) (initialPos "test"))] (initialPos "test"))] (initialPos "test"))] (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        wasExpanded result `shouldBe` True
        expansionSteps result `shouldSatisfy` (>= 3)
      Left err -> expectationFailure $ "Unexpected error in valid nested expansion: " ++ show err

  it "expands TMacros in WHNF mode" $ do
    let macroEnv = extendMacroContext "id" [testParamInfo "x"] (TermMacro (Var "x" 0 (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "id" [MTerm (Var "a" (-1) (initialPos "test"))] (initialPos "test")
    case expandWHNF macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` Var "a" (-1) (initialPos "test")
        wasExpanded result `shouldBe` True
        expansionSteps result `shouldBe` 1
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "handles TMacros with complex argument expressions" $ do
    let macroEnv = extendMacroContext "apply" [testParamInfo "f", testParamInfo "x"] (TermMacro (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") emptyContext
        complexArg = Lam "y" (App (Var "g" (-1) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        term = TMacro "apply" [MTerm complexArg, MTerm (Var "z" (-1) (initialPos "test"))] (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` App complexArg (Var "z" (-1) (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "preserves variable scoping during expansion" $ do
    let macroEnv = extendMacroContext "test" [testParamInfo "x"] (TermMacro (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "test" [MTerm (Var "a" (-1) (initialPos "test"))] (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` Lam "y" (App (Var "a" (-1) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "handles empty argument lists correctly" $ do
    let macroEnv = extendMacroContext "unit" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "unit" [] (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "correctly substitutes multiple occurrences of parameters" $ do
    let macroEnv = extendMacroContext "dup" [testParamInfo "x"] (TermMacro (App (Var "x" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") emptyContext
        term = TMacro "dup" [MTerm (Var "f" (-1) (initialPos "test"))] (initialPos "test")
    case expandFully macroEnv term of
      Right result -> do
        expandedValue result `shouldBe` App (Var "f" (-1) (initialPos "test")) (Var "f" (-1) (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands term macros within promotions in relational contexts" $ do
    let macroEnv = extendMacroContext "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") emptyContext
        promotedMacro = Prom (TMacro "Id" [] (initialPos "test")) (initialPos "test")
    -- This tests that term macros can be expanded within promotions
    case expandFully macroEnv promotedMacro of
      Right result -> do
        expandedValue result `shouldBe` Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err
