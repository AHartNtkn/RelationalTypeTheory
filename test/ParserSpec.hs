{-# LANGUAGE OverloadedStrings #-}

module ParserSpec (spec) where

import Control.Monad.Reader
import Control.Monad.Except
import qualified Data.Map as Map
import Lib
import RawParser
import Elaborate
import Test.Hspec
import TestHelpers
import Text.Megaparsec (errorBundlePretty, initialPos, runParser)

spec :: Spec
spec = do
  termParserSpec
  termMacroParserSpec
  contextAwareMacroParserSpec
  advancedTermMacroScenarioSpec
  macroBodyDisambiguationSpec
  rtypeParserSpec
  proofParserSpec
  declarationParserSpec
  declarationComplexCasesSpec
  theoremReferencingSpec
  deBruijnEdgeCasesSpec
  parserErrorSpec

-- Test helper for terms using new parser pipeline (Raw + Elaborate)
testParseTerm :: [String] -> [String] -> [String] -> MacroEnvironment -> String -> Term -> Expectation
testParseTerm tVars rVars pVars env input expected =
  let boundVarMap = Map.fromList (zip tVars (reverse [0 .. length tVars - 1]))
      boundRelVarMap = Map.fromList (zip rVars (reverse [0 .. length rVars - 1]))
      boundProofVarMap = Map.fromList [(pVar, (i, RelJudgment (Var "dummy" 0 (initialPos "test")) (RVar "dummy" 0 (initialPos "test")) (Var "dummy" 0 (initialPos "test")))) | (pVar, i) <- zip pVars (reverse [0 .. length pVars - 1])]
      elabCtx = ElaborateContext env noTheorems (length tVars) (length rVars) (length pVars) boundVarMap boundRelVarMap boundProofVarMap
   in case runParser rawTerm "test" (input) of
        Left err -> expectationFailure $ "Raw parse failed: " ++ errorBundlePretty err
        Right rawResult -> 
          case runExcept (runReaderT (elaborateTerm rawResult) elabCtx) of
            Left elabErr -> expectationFailure $ "Elaboration failed: " ++ show elabErr
            Right result -> result `shouldBeEqual` expected

-- Test helper for relational types using new parser pipeline
testParseRType :: [String] -> [String] -> [String] -> MacroEnvironment -> String -> RType -> Expectation
testParseRType tVars rVars pVars env input expected =
  let boundVarMap = Map.fromList (zip tVars (reverse [0 .. length tVars - 1]))
      boundRelVarMap = Map.fromList (zip rVars (reverse [0 .. length rVars - 1]))
      boundProofVarMap = Map.fromList [(pVar, (i, RelJudgment (Var "dummy" 0 (initialPos "test")) (RVar "dummy" 0 (initialPos "test")) (Var "dummy" 0 (initialPos "test")))) | (pVar, i) <- zip pVars (reverse [0 .. length pVars - 1])]
      elabCtx = ElaborateContext env noTheorems (length tVars) (length rVars) (length pVars) boundVarMap boundRelVarMap boundProofVarMap
   in case runParser rawRType "test" (input) of
        Left err -> expectationFailure $ "Raw parse failed: " ++ errorBundlePretty err
        Right rawResult -> 
          case runExcept (runReaderT (elaborateRType rawResult) elabCtx) of
            Left elabErr -> expectationFailure $ "Elaboration failed: " ++ show elabErr
            Right result -> result `shouldBeEqual` expected

-- Test helper for proofs using new parser pipeline
testParseProof :: [String] -> [String] -> [String] -> MacroEnvironment -> String -> Proof -> Expectation
testParseProof tVars rVars pVars env input expected =
  let boundVarMap = Map.fromList (zip tVars (reverse [0 .. length tVars - 1]))
      boundRelVarMap = Map.fromList (zip rVars (reverse [0 .. length rVars - 1]))
      boundProofVarMap = Map.fromList [(pVar, (i, RelJudgment (Var "dummy" 0 (initialPos "test")) (RVar "dummy" 0 (initialPos "test")) (Var "dummy" 0 (initialPos "test")))) | (pVar, i) <- zip pVars (reverse [0 .. length pVars - 1])]
      elabCtx = ElaborateContext env noTheorems (length tVars) (length rVars) (length pVars) boundVarMap boundRelVarMap boundProofVarMap
   in case runParser rawProof "test" (input) of
        Left err -> expectationFailure $ "Raw parse failed: " ++ errorBundlePretty err
        Right rawResult -> 
          case runExcept (runReaderT (elaborateProof rawResult) elabCtx) of
            Left elabErr -> expectationFailure $ "Elaboration failed: " ++ show elabErr
            Right result -> result `shouldBeEqual` expected

-- Test helper for declarations using new parser pipeline
testParseDeclaration :: [String] -> [String] -> [String] -> MacroEnvironment -> String -> Declaration -> Expectation
testParseDeclaration tVars rVars pVars env input expected =
  let boundVarMap = Map.fromList (zip tVars (reverse [0 .. length tVars - 1]))
      boundRelVarMap = Map.fromList (zip rVars (reverse [0 .. length rVars - 1]))
      boundProofVarMap = Map.fromList [(pVar, (i, RelJudgment (Var "dummy" 0 (initialPos "test")) (RVar "dummy" 0 (initialPos "test")) (Var "dummy" 0 (initialPos "test")))) | (pVar, i) <- zip pVars (reverse [0 .. length pVars - 1])]
      elabCtx = ElaborateContext env noTheorems (length tVars) (length rVars) (length pVars) boundVarMap boundRelVarMap boundProofVarMap
   in case runParser rawDeclaration "test" (input) of
        Left err -> expectationFailure $ "Raw parse failed: " ++ errorBundlePretty err
        Right rawResult -> 
          case elaborate elabCtx rawResult of
            Left frontEndErr -> expectationFailure $ "Elaboration failed: " ++ show frontEndErr
            Right result -> result `shouldBeEqual` expected

-- Test helper for parsing files using new parser pipeline
testParseFile :: [String] -> [String] -> [String] -> MacroEnvironment -> String -> [Declaration] -> Expectation
testParseFile tVars rVars pVars env input expected =
  let boundVarMap = Map.fromList (zip tVars (reverse [0 .. length tVars - 1]))
      boundRelVarMap = Map.fromList (zip rVars (reverse [0 .. length rVars - 1]))
      boundProofVarMap = Map.fromList [(pVar, (i, RelJudgment (Var "dummy" 0 (initialPos "test")) (RVar "dummy" 0 (initialPos "test")) (Var "dummy" 0 (initialPos "test")))) | (pVar, i) <- zip pVars (reverse [0 .. length pVars - 1])]
      elabCtx = ElaborateContext env noTheorems (length tVars) (length rVars) (length pVars) boundVarMap boundRelVarMap boundProofVarMap
   in case runParser parseFile "test" (input) of
        Left err -> expectationFailure $ "Raw parse failed: " ++ errorBundlePretty err
        Right rawResults -> 
          case mapM (elaborate elabCtx) rawResults of
            Left frontEndErr -> expectationFailure $ "Elaboration failed: " ++ show frontEndErr
            Right results -> results `shouldBeEqual` expected

-- Helper functions to test parsing failures for different syntactic categories
testParseTermFailure :: String -> Expectation
testParseTermFailure input =
  case runParser rawTerm "test" input of
    Left _ -> return () -- Expected failure
    Right result -> expectationFailure $ "Expected parse failure, but got: " ++ show result

testParseRTypeFailure :: String -> Expectation
testParseRTypeFailure input =
  case runParser rawRType "test" (input) of
    Left _ -> return () -- Expected failure
    Right result -> expectationFailure $ "Expected parse failure, but got: " ++ show result

-- Test helper for RType elaboration failures
testParseRTypeElaborationFailure :: [String] -> [String] -> [String] -> MacroEnvironment -> String -> Expectation
testParseRTypeElaborationFailure tVars rVars pVars env input =
  let boundVarMap = Map.fromList (zip tVars (reverse [0 .. length tVars - 1]))
      boundRelVarMap = Map.fromList (zip rVars (reverse [0 .. length rVars - 1]))
      boundProofVarMap = Map.fromList [(pVar, (i, RelJudgment (Var "dummy" 0 (initialPos "test")) (RVar "dummy" 0 (initialPos "test")) (Var "dummy" 0 (initialPos "test")))) | (pVar, i) <- zip pVars (reverse [0 .. length pVars - 1])]
      elabCtx = ElaborateContext env noTheorems (length tVars) (length rVars) (length pVars) boundVarMap boundRelVarMap boundProofVarMap
   in case runParser rawRType "test" (input) of
        Left err -> expectationFailure $ "Raw parse failed: " ++ errorBundlePretty err
        Right rawResult -> 
          case runExcept (runReaderT (elaborateRType rawResult) elabCtx) of
            Left _ -> return () -- Expected elaboration failure
            Right result -> expectationFailure $ "Expected elaboration failure, but got: " ++ show result

testParseProofFailure :: String -> Expectation
testParseProofFailure input =
  case runParser rawProof "test" (input) of
    Left _ -> return () -- Expected failure
    Right result -> expectationFailure $ "Expected parse failure, but got: " ++ show result

testParseDeclarationFailure :: String -> Expectation
testParseDeclarationFailure input =
  case runParser rawDeclaration "test" (input) of
    Left _ -> return () -- Expected failure
    Right result -> expectationFailure $ "Expected parse failure, but got: " ++ show result

termParserSpec :: Spec
termParserSpec = describe "Term parser" $ do
  it "parses variables" $ do
    testParseTerm ["x"] [] [] noMacros "x" (Var "x" 0 (initialPos "test")) -- bound variable
    testParseTerm ["foo"] [] [] noMacros "foo" (Var "foo" 0 (initialPos "test")) -- bound variable
    testParseTerm ["x123"] [] [] noMacros "x123" (Var "x123" 0 (initialPos "test")) -- bound variable
    testParseTerm ["foo_bar"] [] [] noMacros "foo_bar" (Var "foo_bar" 0 (initialPos "test")) -- with underscore
    testParseTerm ["test_123"] [] [] noMacros "test_123" (Var "test_123" 0 (initialPos "test")) -- underscore and numbers
    testParseTerm ["a_b_c"] [] [] noMacros "a_b_c" (Var "a_b_c" 0 (initialPos "test")) -- multiple underscores
    testParseTerm ["x'"] [] [] noMacros "x'" (Var "x'" 0 (initialPos "test")) -- with apostrophe
    testParseTerm ["foo'"] [] [] noMacros "foo'" (Var "foo'" 0 (initialPos "test")) -- with apostrophe
    testParseTerm ["x''"] [] [] noMacros "x''" (Var "x''" 0 (initialPos "test")) -- multiple apostrophes
  it "parses lambda abstractions" $ do
    testParseTerm [] [] [] noMacros "λ x . x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) -- x bound at index 0
    testParseTerm [] [] [] noMacros "\\x . x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) -- x bound at index 0
    testParseTerm [] [] [] noMacros "λ x . λ y . x" (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) -- x bound at index 1 (distance from binding)
    testParseTerm [] [] [] noMacros "λ x_1. x_1" (Lam "x_1" (Var "x_1" 0 (initialPos "test")) (initialPos "test")) -- lambda with underscore in variable name
  it "parses complex nested lambda abstractions" $ do
    testParseTerm [] [] [] noMacros "λ x . λ y . λ z . x" (Lam "x" (Lam "y" (Lam "z" (Var "x" 2 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) -- x at distance 2
    testParseTerm [] [] [] noMacros "λ x . λ y . λ z . y" (Lam "x" (Lam "y" (Lam "z" (Var "y" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) -- y at distance 1
    testParseTerm [] [] [] noMacros "λ x . λ y . λ z . z" (Lam "x" (Lam "y" (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) -- z at distance 0
  it "parses variable shadowing scenarios" $ do
    testParseTerm [] [] [] noMacros "λ x . λ x . x" (Lam "x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) -- inner x shadows outer x
  it "parses applications" $ do
    testParseTerm ["f", "x"] [] [] noMacros "f x" (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["f", "x", "y"] [] [] noMacros "f x y" (App (App (Var "f" 2 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))

  it "parses parentheses correctly" $ do
    testParseTerm [] [] [] noMacros "(λ x . x)" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["f", "x", "y"] [] [] noMacros "(f x) y" (App (App (Var "f" 2 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["f", "x", "y"] [] [] noMacros "f (x y)" (App (Var "f" 2 (initialPos "test")) (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

-- Helper to create dummy term macros for parsing tests (body doesn't matter for parsing)
createTermMacroEnv :: [(String, [String])] -> MacroEnvironment
createTermMacroEnv macroDefs =
  foldr
    ( \(name, params) env ->
        let dummyBody = TermMacro (Var "dummy" 0 (initialPos "test")) -- Dummy body for parsing tests
         in extendMacroEnvironment name params dummyBody (defaultFixity "TEST") env
    )
    noMacros
    macroDefs

termMacroParserSpec :: Spec
termMacroParserSpec = describe "Term macro parser (TMacro)" $ do
  it "parses regular applications without macro context" $ do
    testParseTerm ["f", "x"] [] [] noMacros "f x" (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["f", "x", "y"] [] [] noMacros "f x y" (App (App (Var "f" 2 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["g", "a", "b", "c"] [] [] noMacros "g a b c" (App (App (App (Var "g" 3 (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test")) (Var "b" 1 (initialPos "test")) (initialPos "test")) (Var "c" 0 (initialPos "test")) (initialPos "test"))

  it "parses term macros with single argument" $ do
    let env = createTermMacroEnv [("f", ["x"])]
    testParseTerm ["x"] [] [] env "f x" (TMacro "f" [Var "x" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["y", "z"] [] [] env "f (y z)" (TMacro "f" [App (Var "y" 1 (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test")] (initialPos "test"))

  it "parses term macros with multiple arguments" $ do
    let env = createTermMacroEnv [("add", ["x", "y"])]
    testParseTerm ["x", "y"] [] [] env "add x y" (TMacro "add" [Var "x" 1 (initialPos "test"), Var "y" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["f", "a", "g", "b"] [] [] env "add (f a) (g b)" (TMacro "add" [App (Var "f" 3 (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test"), App (Var "g" 1 (initialPos "test")) (Var "b" 0 (initialPos "test")) (initialPos "test")] (initialPos "test"))

  it "parses term macros with zero arguments" $ do
    let env = createTermMacroEnv [("unit", [])]
    testParseTerm [] [] [] env "unit" (TMacro "unit" [] (initialPos "test"))

  it "parses macro with proper argument binding" $ do
    let env = createTermMacroEnv [("unary", ["x"])]
    testParseTerm ["x"] [] [] env "unary x" (TMacro "unary" [Var "x" 0 (initialPos "test")] (initialPos "test"))

  it "parses term macros with complex arguments" $ do
    let env = createTermMacroEnv [("compose", ["f", "g", "x"])]
    testParseTerm ["f", "g", "x"] [] [] env "compose f g x" (TMacro "compose" [Var "f" 2 (initialPos "test"), Var "g" 1 (initialPos "test"), Var "x" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["g", "h", "y"] [] [] env "compose (λ x . x) g (h y)" (TMacro "compose" [Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"), Var "g" 2 (initialPos "test"), App (Var "h" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")] (initialPos "test"))

  it "parses nested term macro applications" $ do
    let env = createTermMacroEnv [("f", ["x"]), ("g", ["y"])]
    testParseTerm ["x"] [] [] env "f (g x)" (TMacro "f" [TMacro "g" [Var "x" 0 (initialPos "test")] (initialPos "test")] (initialPos "test"))

  it "parses term macro accumulation (multiple arguments)" $ do
    let env = createTermMacroEnv [("f", ["x", "y", "z"])]
    testParseTerm ["a", "b", "c"] [] [] env "f a b c" (TMacro "f" [Var "a" 2 (initialPos "test"), Var "b" 1 (initialPos "test"), Var "c" 0 (initialPos "test")] (initialPos "test"))

  it "handles mixed term macros and regular applications" $ do
    let env = createTermMacroEnv [("macro", ["x"])]
    testParseTerm ["regular", "x"] [] [] env "regular (macro x)" (App (Var "regular" 1 (initialPos "test")) (TMacro "macro" [Var "x" 0 (initialPos "test")] (initialPos "test")) (initialPos "test"))
    testParseTerm ["regular", "x"] [] [] env "macro (regular x)" (TMacro "macro" [App (Var "regular" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")] (initialPos "test"))

contextAwareMacroParserSpec :: Spec
contextAwareMacroParserSpec = describe "Context-aware macro detection" $ do
  it "distinguishes between macro and regular application based on context" $ do
    let emptyCtx = createTermMacroEnv []
    let env = createTermMacroEnv [("f", ["x"])]

    -- Same input, different results based on context
    testParseTerm ["f", "x"] [] [] emptyCtx "f x" (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["x"] [] [] env "f x" (TMacro "f" [Var "x" 0 (initialPos "test")] (initialPos "test"))

  it "handles context with multiple macros" $ do
    let env = createTermMacroEnv [("add", ["x", "y"]), ("mul", ["x", "y"]), ("id", ["x"])]
    testParseTerm ["unknown", "z", "a", "b", "x", "y"] [] [] env "add x y" (TMacro "add" [Var "x" 1 (initialPos "test"), Var "y" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["unknown", "z", "a", "b", "x", "y"] [] [] env "mul a b" (TMacro "mul" [Var "a" 3 (initialPos "test"), Var "b" 2 (initialPos "test")] (initialPos "test"))
    testParseTerm ["unknown", "z", "a", "b", "x", "y"] [] [] env "id z" (TMacro "id" [Var "z" 4 (initialPos "test")] (initialPos "test"))
    testParseTerm ["unknown", "z", "a", "b", "x", "y"] [] [] env "unknown x" (App (Var "unknown" 5 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test"))

  it "parses macro calls with bound variables" $ do
    let env = createTermMacroEnv [("known", ["x"])]
    testParseTerm ["x"] [] [] env "known x" (TMacro "known" [Var "x" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["x", "unknown"] [] [] env "unknown x" (App (Var "unknown" 0 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test"))

  it "handles macro detection with bound variables" $ do
    let env = createTermMacroEnv [("f", ["x"]), ("g", [])]
    testParseTerm ["x"] [] [] env "f x" (TMacro "f" [Var "x" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["h"] [] [] env "h g" (App (Var "h" 0 (initialPos "test")) (TMacro "g" [] (initialPos "test")) (initialPos "test"))

  it "handles macro detection in complex expressions" $ do
    let env = createTermMacroEnv [("f", ["x"]), ("g", ["y"])]
    testParseTerm ["x", "y"] [] [] env "(f x) (g y)" (App (TMacro "f" [Var "x" 1 (initialPos "test")] (initialPos "test")) (TMacro "g" [Var "y" 0 (initialPos "test")] (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] env "λ z . f z" (Lam "z" (TMacro "f" [Var "z" 0 (initialPos "test")] (initialPos "test")) (initialPos "test"))

  it "rejects partial macro applications" $ do
    let env = createTermMacroEnv [("f", ["x", "y"])]
    -- When macro expects 2 args but gets 1, it should error in elaboration
    let elabCtx = ElaborateContext env noTheorems 1 0 0 (Map.fromList [("x", 0)]) Map.empty Map.empty
    case runParser rawTerm "test" "f x" of
      Left err -> expectationFailure $ "Raw parse failed: " ++ errorBundlePretty err
      Right rawResult -> 
        case runExcept (runReaderT (elaborateTerm rawResult) elabCtx) of
          Left elabErr -> show elabErr `shouldContain` "MacroArityMismatch"
          Right result -> expectationFailure $ "Expected elaboration error for under-applied macro, but got: " ++ show result
    -- Full application should still work
    testParseTerm ["x", "y"] [] [] env "f x y" (TMacro "f" [Var "x" 1 (initialPos "test"), Var "y" 0 (initialPos "test")] (initialPos "test"))

  it "respects macro arity limits" $ do
    let env = createTermMacroEnv [("unary", ["x"]), ("binary", ["x", "y"])]
    -- Exact arity - should be TMacro
    testParseTerm ["a", "b", "c", "dummy"] [] [] env "unary a" (TMacro "unary" [Var "a" 3 (initialPos "test")] (initialPos "test"))
    testParseTerm ["a", "b", "c", "dummy"] [] [] env "binary a b" (TMacro "binary" [Var "a" 3 (initialPos "test"), Var "b" 2 (initialPos "test")] (initialPos "test"))
    -- Over-arity - should stop at arity limit and App the rest
    testParseTerm ["a", "b", "c", "dummy"] [] [] env "unary a b" (App (TMacro "unary" [Var "a" 3 (initialPos "test")] (initialPos "test")) (Var "b" 2 (initialPos "test")) (initialPos "test"))
    testParseTerm ["a", "b", "c", "dummy"] [] [] env "binary a b c" (App (TMacro "binary" [Var "a" 3 (initialPos "test"), Var "b" 2 (initialPos "test")] (initialPos "test")) (Var "c" 1 (initialPos "test")) (initialPos "test"))
    -- Parentheses should force boundaries
    testParseTerm ["a", "b", "c", "dummy"] [] [] env "(unary a) b" (App (TMacro "unary" [Var "a" 3 (initialPos "test")] (initialPos "test")) (Var "b" 2 (initialPos "test")) (initialPos "test"))
    testParseTerm ["a", "b", "c", "dummy"] [] [] env "(binary a b) c" (App (TMacro "binary" [Var "a" 3 (initialPos "test"), Var "b" 2 (initialPos "test")] (initialPos "test")) (Var "c" 1 (initialPos "test")) (initialPos "test"))

advancedTermMacroScenarioSpec :: Spec
advancedTermMacroScenarioSpec = describe "Advanced term macro scenarios" $ do
  it "handles deeply nested TMacro applications" $ do
    let env = createTermMacroEnv [("f", ["x"]), ("g", ["y"]), ("h", ["z"])]
    -- Test deeply nested: f (g (h x))
    testParseTerm ["x"] [] [] env "f (g (h x))" (TMacro "f" [TMacro "g" [TMacro "h" [Var "x" 0 (initialPos "test")] (initialPos "test")] (initialPos "test")] (initialPos "test"))
    -- Test complex nesting with mixed regular terms: f (g (x y))
    testParseTerm ["x", "y"] [] [] env "f (g (x y))" (TMacro "f" [TMacro "g" [App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")] (initialPos "test")] (initialPos "test"))

  it "handles TMacro in lambda abstractions with variable capture" $ do
    let env = createTermMacroEnv [("apply", ["f", "x"])]
    -- Lambda with TMacro using bound variable x
    testParseTerm ["x"] [] [] env "λ f . apply f x" (Lam "f" (TMacro "apply" [Var "f" 0 (initialPos "test"), Var "x" 1 (initialPos "test")] (initialPos "test")) (initialPos "test"))
    -- Nested lambda with TMacro using bound variables - should work
    testParseTerm [] [] [] env "λ x . λ y . apply x y" (Lam "x" (Lam "y" (TMacro "apply" [Var "x" 1 (initialPos "test"), Var "y" 0 (initialPos "test")] (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles mixed macro patterns with bound variables" $ do
    let env = createTermMacroEnv [("compose", ["f", "g"]), ("id", [])]
    -- Complex expression with bound variables f, g
    testParseTerm ["f", "g"] [] [] env "compose (compose id f) g" (TMacro "compose" [TMacro "compose" [TMacro "id" [] (initialPos "test"), Var "f" 1 (initialPos "test")] (initialPos "test"), Var "g" 0 (initialPos "test")] (initialPos "test"))

  it "handles TMacro with complex argument patterns" $ do
    let env = createTermMacroEnv [("curry", ["f", "x", "y"]), ("uncurry", ["f"])]
    -- TMacro with lambda argument: curry (λ x . λ y . x y) a b
    testParseTerm ["a", "b"] [] [] env "curry (λ x . λ y . x y) a b" (TMacro "curry" [Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"), Var "a" 1 (initialPos "test"), Var "b" 0 (initialPos "test")] (initialPos "test"))
    -- TMacro with nested TMacro argument: uncurry (curry f x)
    testParseTerm ["f", "x", "y"] [] [] env "uncurry (curry f x y)" (TMacro "uncurry" [TMacro "curry" [Var "f" 2 (initialPos "test"), Var "x" 1 (initialPos "test"), Var "y" 0 (initialPos "test")] (initialPos "test")] (initialPos "test"))

  it "handles variable shadowing with TMacros" $ do
    let env = createTermMacroEnv [("bind", ["x", "f"])]
    -- Variable shadowing: λ x . bind x (λ x . x) where inner x shadows outer x
    testParseTerm [] [] [] env "λ x . bind x (λ x . x)" (Lam "x" (TMacro "bind" [Var "x" 0 (initialPos "test"), Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")] (initialPos "test")) (initialPos "test"))
    -- Complex shadowing: λ f . λ x . bind (f x) (λ f . f)
    testParseTerm [] [] [] env "λ f . λ x . bind (f x) (λ f . f)" (Lam "f" (Lam "x" (TMacro "bind" [App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"), Lam "f" (Var "f" 0 (initialPos "test")) (initialPos "test")] (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "rejects TMacro arity edge cases" $ do
    let env = createTermMacroEnv [("binary", ["x", "y"]), ("ternary", ["x", "y", "z"])]
    -- Under-application (partial application) should error in elaboration
    let elabCtx = ElaborateContext env noTheorems 3 0 0 (Map.fromList [("x", 2), ("y", 1), ("z", 0)]) Map.empty Map.empty
    case runParser rawTerm "test" "binary x" of
      Left err -> expectationFailure $ "Raw parse failed: " ++ errorBundlePretty err
      Right rawResult -> 
        case runExcept (runReaderT (elaborateTerm rawResult) elabCtx) of
          Left elabErr -> show elabErr `shouldContain` "MacroArityMismatch"
          Right result -> expectationFailure $ "Expected elaboration error for under-applied macro, but got: " ++ show result
    -- Exact application
    testParseTerm ["x", "y", "z"] [] [] env "binary x y" (TMacro "binary" [Var "x" 2 (initialPos "test"), Var "y" 1 (initialPos "test")] (initialPos "test"))

    -- Over-application (should switch to App after arity limit (initialPos "test"))
    testParseTerm ["x", "y", "z"] [] [] env "binary x y z" (App (TMacro "binary" [Var "x" 2 (initialPos "test"), Var "y" 1 (initialPos "test")] (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test"))

  it "handles TMacro in complex application chains" $ do
    let env = createTermMacroEnv [("map", ["f", "xs"]), ("filter", ["p", "xs"])]
    -- Chain: map f (filter p xs)
    testParseTerm ["f", "p", "xs"] [] [] env "map f (filter p xs)" (TMacro "map" [Var "f" 2 (initialPos "test"), TMacro "filter" [Var "p" 1 (initialPos "test"), Var "xs" 0 (initialPos "test")] (initialPos "test")] (initialPos "test"))
    -- Left-associative application chain: map stops at arity, uses App for extra
    testParseTerm ["f", "xs", "ys"] [] [] env "map f xs ys" (App (TMacro "map" [Var "f" 2 (initialPos "test"), Var "xs" 1 (initialPos "test")] (initialPos "test")) (Var "ys" 0 (initialPos "test")) (initialPos "test"))

  it "handles TMacro with parentheses and precedence" $ do
    let env = createTermMacroEnv [("add", ["x", "y"]), ("mul", ["x", "y"])]
    -- Parentheses affecting parsing: add (mul x y) z
    testParseTerm ["x", "y", "z"] [] [] env "add (mul x y) z" (TMacro "add" [TMacro "mul" [Var "x" 2 (initialPos "test"), Var "y" 1 (initialPos "test")] (initialPos "test"), Var "z" 0 (initialPos "test")] (initialPos "test"))
    -- Different grouping: (add x y) z - arity limit forces App after completion
    testParseTerm ["x", "y", "z"] [] [] env "(add x y) z" (App (TMacro "add" [Var "x" 2 (initialPos "test"), Var "y" 1 (initialPos "test")] (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test"))

  it "handles large argument lists for TMacros" $ do
    let env = createTermMacroEnv [("manyArgs", ["a", "b", "c", "d", "e", "f", "g", "h"])]
    testParseTerm
      ["a", "b", "c", "d", "e", "f", "g", "h"]
      []
      []
      env
      "manyArgs a b c d e f g h"
      ( TMacro
          "manyArgs"
          [ Var "a" 7 (initialPos "test"),
            Var "b" 6 (initialPos "test"),
            Var "c" 5 (initialPos "test"),
            Var "d" 4 (initialPos "test"),
            Var "e" 3 (initialPos "test"),
            Var "f" 2 (initialPos "test"),
            Var "g" 1 (initialPos "test"),
            Var "h" 0 (initialPos "test")
          ]
          (initialPos "test")
      )

  it "handles TMacro names that are also variable names" $ do
    let env = createTermMacroEnv [("f", ["x"])]
    -- When 'f' is both a macro name and used as a variable
    -- In head position with correct arity, it should be TMacro
    testParseTerm ["x"] [] [] env "f x" (TMacro "f" [Var "x" 0 (initialPos "test")] (initialPos "test"))
    -- In lambda binding: λ f . f x (here f is bound, shadowing the macro)
    testParseTerm ["x"] [] [] env "λ f . f x" (Lam "f" (App (Var "f" 0 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
    -- Complex case: λg. g (f y) - f is still the macro since it's not bound
    testParseTerm ["y"] [] [] env "λg. g (f y)" (Lam "g" (App (Var "g" 0 (initialPos "test")) (TMacro "f" [Var "y" 1 (initialPos "test")] (initialPos "test")) (initialPos "test")) (initialPos "test"))

macroBodyDisambiguationSpec :: Spec
macroBodyDisambiguationSpec = describe "MacroBody disambiguation" $ do
  it "parses macro definitions with term bodies" $ do
    testParseDeclaration [] [] [] noMacros "TermMacro x ≔ x;" (MacroDef "TermMacro" ["x"] (TermMacro (Var "x" 0 (initialPos "test"))))
    testParseDeclaration [] [] [] noMacros "Lambda ≔ λ x . x;" (MacroDef "Lambda" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration [] [] [] noMacros "AppMacro f x ≔ f x;" (MacroDef "AppMacro" ["f", "x"] (TermMacro (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))))

  it "parses macro definitions with relational type bodies" $ do
    testParseDeclaration [] [] [] noMacros "Arrow A B ≔ A -> B;" (MacroDef "Arrow" ["A", "B"] (RelMacro (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration [] [] [] noMacros "Composition R S ≔ R ∘ S;" (MacroDef "Composition" ["R", "S"] (RelMacro (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration [] [] [] noMacros "Universal X ≔ ∀ Y . X -> Y;" (MacroDef "Universal" ["X"] (RelMacro (All "Y" (Arr (RVar "X" 1 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))))

  it "parses parenthesized terms as term macros" $ do
    testParseDeclaration [] [] [] noMacros "ParenId ≔ (λ x . x);" (MacroDef "ParenId" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration [] [] [] noMacros "ParenApp f x ≔ (f x);" (MacroDef "ParenApp" ["f", "x"] (TermMacro (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))))

  it "tries term parsing first, then falls back to relational" $ do
    -- Lambda terms should parse as terms
    testParseDeclaration [] [] [] noMacros "TermFirst x ≔ λ y . x y;" (MacroDef "TermFirst" ["x"] (TermMacro (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))))
    -- Relational operators should parse as relational
    testParseDeclaration [] [] [] noMacros "RelSecond R ≔ R -> R;" (MacroDef "RelSecond" ["R"] (RelMacro (Arr (RVar "R" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test"))))

  it "handles complex macro body disambiguation" $ do
    -- Lambda terms should parse as terms
    testParseDeclaration [] [] []
      noMacros
      "LambdaBody ≔ λ x . λ y . x y;"
      (MacroDef "LambdaBody" [] (TermMacro (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))))

    -- Compositions should parse as relational types
    testParseDeclaration [] [] [] noMacros "CompBody R S ≔ R ∘ S;" (MacroDef "CompBody" ["R", "S"] (RelMacro (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))))
    -- Arrows should parse as relational types
    testParseDeclaration [] [] [] noMacros "ArrowBody A B ≔ A -> B;" (MacroDef "ArrowBody" ["A", "B"] (RelMacro (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))))

  it "handles macro body with quantifiers" $ do
    testParseDeclaration [] [] [] noMacros "ForallBody ≔ ∀ X . X;" (MacroDef "ForallBody" [] (RelMacro (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration [] [] [] noMacros "ForallComp R ≔ ∀ X . R ∘ X;" (MacroDef "ForallComp" ["R"] (RelMacro (All "X" (Comp (RVar "R" 1 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))))

  it "handles macro body with converse operations" $ do
    testParseDeclaration [] [] [] noMacros "ConvBody R ≔ R ˘;" (MacroDef "ConvBody" ["R"] (RelMacro (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration [] [] [] noMacros "ConvComp R S ≔ (R ∘ S)˘;" (MacroDef "ConvComp" ["R", "S"] (RelMacro (Conv (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))))

  it "handles nested disambiguation in complex expressions" $ do
    -- Complex term with applications
    testParseDeclaration [] [] [] noMacros "ComplexTerm f g x ≔ (λh. h (f x)) g;" ( MacroDef "ComplexTerm" ["f", "g", "x"] (TermMacro (App (Lam "h" (App (Var "h" 0 (initialPos "test")) (App (Var "f" 3 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "g" 1 (initialPos "test")) (initialPos "test")))  )

    -- Complex relational type with nested structure
    testParseDeclaration [] [] []
      noMacros
      "ComplexRel R S T ≔ ∀ X . (R ∘ X) -> (S ˘ ∘ T);"
      ( MacroDef
          "ComplexRel"
          ["R", "S", "T"]
          (RelMacro (All "X" (Arr (Comp (RVar "R" 3 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (Comp (Conv (RVar "S" 2 (initialPos "test")) (initialPos "test")) (RVar "T" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")))
      )

rtypeParserSpec :: Spec
rtypeParserSpec = describe "RType parser" $ do
  it "parses Unicode and ASCII alternatives consistently" $ do
    -- Arrow types
    testParseRType [] ["A", "B"] [] noMacros "A -> B" (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A", "B"] [] noMacros "A → B" (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
    -- Universal quantification
    testParseRType [] ["A"] [] noMacros "∀x . A" (All "x" (RVar "A" 1 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A"] [] noMacros "forall x . A" (All "x" (RVar "A" 1 (initialPos "test")) (initialPos "test"))
    -- Converse operations
    testParseRType [] ["R"] [] noMacros "R ˘" (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test"))
    -- Composition
    testParseRType [] ["R", "S"] [] noMacros "R ∘ S" (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))
  it "parses relation variables with bound context" $ do
    testParseRType [] ["A"] [] noMacros "A" (RVar "A" 0 (initialPos "test"))
    testParseRType [] ["R"] [] noMacros "R" (RVar "R" 0 (initialPos "test"))

  it "parses arrow types with bound variables" $ do
    testParseRType [] ["A", "B"] [] noMacros "A -> B" (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A", "B"] [] noMacros "A → B" (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A", "B", "C"] [] noMacros "A -> B -> C" (Arr (RVar "A" 2 (initialPos "test")) (Arr (RVar "B" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses universal quantification with mixed bound variables" $ do
    testParseRType [] ["A"] [] noMacros "∀x . A" (All "x" (RVar "A" 1 (initialPos "test")) (initialPos "test")) -- A bound in context, x bound by quantifier
    testParseRType [] ["A"] [] noMacros "forall x . A" (All "x" (RVar "A" 1 (initialPos "test")) (initialPos "test"))

  it "parses bound variables correctly in quantifier scope" $ do
    testParseRType [] [] [] noMacros "∀x . x" (All "x" (RVar "x" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["S"] [] noMacros "∀R . R ∘ S" (All "R" (Comp (RVar "R" 0 (initialPos "test")) (RVar "S" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses nested quantification with multiple bound variables" $ do
    testParseRType [] [] [] noMacros "∀x . ∀y . x ∘ y" (All "x" (All "y" (Comp (RVar "x" 1 (initialPos "test")) (RVar "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseRType [] [] [] noMacros "∀R . ∀S. R ∘ S ˘" (All "R" (All "S" (Comp (RVar "R" 1 (initialPos "test")) (Conv (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses deeply nested quantification" $ do
    testParseRType [] [] [] noMacros "∀A. ∀B. ∀C. A ∘ B ∘ C" (All "A" (All "B" (All "C" (Comp (Comp (RVar "A" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses relation variable shadowing" $ do
    testParseRType [] [] [] noMacros "∀R . ∀R . R" (All "R" (All "R" (RVar "R" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) -- inner R shadows outer R
  it "parses mixed bound and unbound variables" $ do
    testParseRType [] ["Unbound"] [] noMacros "∀x . x ∘ Unbound" (All "x" (Comp (RVar "x" 0 (initialPos "test")) (RVar "Unbound" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseRType [] ["Unbound"] [] noMacros "∀R . Unbound ∘ R" (All "R" (Comp (RVar "Unbound" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses composition" $ do
    testParseRType [] ["R", "S"] [] noMacros "R ∘ S" (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["R", "S", "T"] [] noMacros "R ∘ S ∘ T" (Comp (Comp (RVar "R" 2 (initialPos "test")) (RVar "S" 1 (initialPos "test")) (initialPos "test")) (RVar "T" 0 (initialPos "test")) (initialPos "test"))

  it "parses converse" $ do
    testParseRType [] ["R"] [] noMacros "R ˘" (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["R", "S"] [] noMacros "(R ∘ S)˘" (Conv (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses promotion" $ do
    testParseRType [] [] [] noMacros "λ x . x" (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses promotion (parens)" $ do
    testParseRType [] [] [] noMacros "(λ x . x)" (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "distinguishes between promotion and macro applications" $ do
    -- Test with a context that has no macros - should parse as promotion
    testParseRType ["y"] [] [] noMacros "(λ x . x y)" (Prom (Lam "x" (App (Var "x" 0 (initialPos "test")) (Var "y" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    -- Test basic bound identifier - should parse as RVar
    testParseRType [] ["SomeType"] [] noMacros "SomeType" (RVar "SomeType" 0 (initialPos "test"))

  it "parses type application" $ do
    let listEnv = extendMacroEnvironment "List" ["A"] (RelMacro (RVar "A" 0 (initialPos "test"))) (defaultFixity "TEST") noMacros
    testParseRType [] ["A"] [] listEnv "List A" (RMacro "List" [RVar "A" 0 (initialPos "test")] (initialPos "test"))
    let pairEnv = extendMacroEnvironment "Pair" ["A", "B"] (RelMacro (RVar "A" 1 (initialPos "test"))) (defaultFixity "TEST") noMacros
    testParseRType [] ["A", "B"] [] pairEnv "Pair A B" (RMacro "Pair" [RVar "A" 1 (initialPos "test"), RVar "B" 0 (initialPos "test")] (initialPos "test"))

  it "rejects unknown macros in type applications" $ do
    -- These should fail during elaboration, not parsing
    testParseRTypeElaborationFailure [] ["A"] [] noMacros "List A"  
    testParseRTypeElaborationFailure [] ["A", "B"] [] noMacros "Pair A B"

  it "respects operator precedence" $ do
    testParseRType [] ["A", "B", "C"] [] noMacros "A -> B ∘ C" (Arr (RVar "A" 2 (initialPos "test")) (Comp (RVar "B" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseRType [] ["R", "S"] [] noMacros "R ∘ S ˘" (Comp (RVar "R" 1 (initialPos "test")) (Conv (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "respects complex operator precedence and associativity" $ do
    -- Converse has highest precedence
    testParseRType [] ["A", "B", "C"] [] noMacros "A ∘ B˘ ∘ C" (Comp (Comp (RVar "A" 2 (initialPos "test")) (Conv (RVar "B" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test"))
    -- Composition is left-associative
    testParseRType [] ["A", "B", "C", "D"] [] noMacros "A ∘ B ∘ C ∘ D" (Comp (Comp (Comp (RVar "A" 3 (initialPos "test")) (RVar "B" 2 (initialPos "test")) (initialPos "test")) (RVar "C" 1 (initialPos "test")) (initialPos "test")) (RVar "D" 0 (initialPos "test")) (initialPos "test"))
    -- Arrow is right-associative
    testParseRType [] ["A", "B", "C", "D"] [] noMacros "A -> B -> C -> D" (Arr (RVar "A" 3 (initialPos "test")) (Arr (RVar "B" 2 (initialPos "test")) (Arr (RVar "C" 1 (initialPos "test")) (RVar "D" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    -- Mixed precedence: converse > composition > arrow
    testParseRType [] ["A", "B", "C", "D"] [] noMacros "A -> B ∘ C˘ -> D" (Arr (RVar "A" 3 (initialPos "test")) (Arr (Comp (RVar "B" 2 (initialPos "test")) (Conv (RVar "C" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (RVar "D" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

proofParserSpec :: Spec
proofParserSpec = describe "Proof parser" $ do
  it "parses Unicode and ASCII alternatives for proofs" $ do
    -- Lambda abstractions
    testParseProof [] ["A"] ["p"] noMacros "λ x: A. p" (LamP "x" (RVar "A" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test"))
    testParseProof [] ["A"] ["p"] noMacros "\\x: A. p" (LamP "x" (RVar "A" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test"))
    -- Type lambda
    testParseProof [] [] ["p"] noMacros "Λα. p" (TyLam "α" (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "/\\ α. p" (TyLam "α" (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    -- Iota (term promotion introduction)
    testParseProof ["x", "y"] [] [] noMacros "ι⟨ x , y⟩" (Iota (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["x", "y"] [] [] noMacros "ι<x, y>" (Iota (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["x", "y"] [] [] noMacros "iota<x, y>" (Iota (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))
    -- Converse operations
    testParseProof [] [] ["p"] noMacros "∪ᵢ p" (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "convIntro p" (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "∪ₑ p" (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "convElim p" (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    -- Pi elimination
    testParseProof [] [] ["p", "q"] noMacros "π p - x . y . z .q" (Pi (PVar "p" 1 (initialPos "test")) "x" "y" "z" (PVar "q" 2 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p", "q"] noMacros "pi p - x . y . z .q" (Pi (PVar "p" 1 (initialPos "test")) "x" "y" "z" (PVar "q" 2 (initialPos "test")) (initialPos "test"))
    -- Rho elimination
    testParseProof ["t1", "t2"] [] ["p", "q"] noMacros "ρ{ x . t1, t2} p - q" (RhoElim "x" (Var "t1" 2 (initialPos "test")) (Var "t2" 1 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["t1", "t2"] [] ["p", "q"] noMacros "rho{x . t1, t2} p - q" (RhoElim "x" (Var "t1" 2 (initialPos "test")) (Var "t2" 1 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
  it "parses proof variables and constants" $ do
    testParseProof [] [] ["p"] noMacros "p" (PVar "p" 0 (initialPos "test"))
    testParseProof [] [] ["axiom"] noMacros "axiom" (PVar "axiom" 0 (initialPos "test"))

  it "parses proof lambda abstractions" $ do
    testParseProof [] ["A"] ["p"] noMacros "λ x: A. p" (LamP "x" (RVar "A" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test"))
    testParseProof [] ["A", "B"] ["p"] noMacros "\\x: A -> B. p" (LamP "x" (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test"))

  it "parses type lambda abstractions" $ do
    testParseProof [] [] ["p"] noMacros "Λα. p" (TyLam "α" (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "/\\ α. p" (TyLam "α" (PVar "p" 0 (initialPos "test")) (initialPos "test"))

  it "parses type applications" $ do
    testParseProof [] ["A"] ["p"] noMacros "p{A}" (TyApp (PVar "p" 0 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] ["B"] ["q"] noMacros "(Λα. q){B}" (TyApp (TyLam "α" (PVar "q" 0 (initialPos "test")) (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))

  it "parses proof applications" $ do
    testParseProof [] [] ["p", "q"] noMacros "p q" (AppP (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p", "q", "r"] noMacros "p q r" (AppP (AppP (PVar "p" 2 (initialPos "test")) (PVar "q" 1 (initialPos "test")) (initialPos "test")) (PVar "r" 0 (initialPos "test")) (initialPos "test"))

  it "parses conversion proofs" $ do
    testParseProof ["t", "u"] [] ["p"] noMacros "t ⇃ p ⇂ u" (ConvProof (Var "t" 1 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")) (initialPos "test"))
    -- Test the specific case that was failing: parenthesized lambda applications
    testParseProof
      ["f", "a"]
      []
      ["p"]
      noMacros
      "((λ z . z) (f a)) ⇃ p ⇂ (f ((λ w . w) a))"
      ( ConvProof
          (App (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
          (PVar "p" 0 (initialPos "test"))
          (App (Var "f" 1 (initialPos "test")) (App (Lam "w" (Var "w" 0 (initialPos "test")) (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
          (initialPos "test")
      )
    -- Test nested parentheses with lambdas
    testParseProof
      ["x", "y"]
      []
      ["q"]
      noMacros
      "((λa. a) x) ⇃ q ⇂ ((λb.b) y)"
      ( ConvProof
          (App (Lam "a" (Var "a" 0 (initialPos "test")) (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test"))
          (PVar "q" 0 (initialPos "test"))
          (App (Lam "b" (Var "b" 0 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))
          (initialPos "test")
      )
    -- Test complex nested applications
    testParseProof
      ["a", "g", "f"]
      []
      ["r"]
      noMacros
      "((λ x .f (g x)) a) ⇃ r ⇂ (f (g a))"
      ( ConvProof
          (App (Lam "x" (App (Var "f" 3 (initialPos "test")) (App (Var "g" 2 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test"))
          (PVar "r" 0 (initialPos "test"))
          (App (Var "f" 2 (initialPos "test")) (App (Var "g" 1 (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
          (initialPos "test")
      )

  it "parses rho elimination" $ do
    testParseProof
      ["t1", "t2"]
      []
      ["p", "q"]
      noMacros
      "ρ{ x . t1, t2} p - q"
      (RhoElim "x" (Var "t1" 2 (initialPos "test")) (Var "t2" 1 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof
      ["u", "v"]
      []
      ["r", "s"]
      noMacros
      "rho{y . u, v} r - s"
      (RhoElim "y" (Var "u" 2 (initialPos "test")) (Var "v" 1 (initialPos "test")) (PVar "r" 1 (initialPos "test")) (PVar "s" 0 (initialPos "test")) (initialPos "test"))

  it "parses rho elimination with bound variable usage" $ do
    -- Test the key bug fix: variables bound by rho (x, y) should be usable within the {x .t1,t2} terms
    testParseProof
      ["a"]
      []
      ["p", "q"]
      noMacros
      "ρ{ x . x, a} p - q"
      (RhoElim "x" (Var "x" 0 (initialPos "test")) (Var "a" 1 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof
      ["b"]
      []
      ["r", "s"]
      noMacros
      "rho{y . y, b} r - s"
      (RhoElim "y" (Var "y" 0 (initialPos "test")) (Var "b" 1 (initialPos "test")) (PVar "r" 1 (initialPos "test")) (PVar "s" 0 (initialPos "test")) (initialPos "test"))
    -- Both terms use the bound variable
    testParseProof
      []
      []
      ["p", "q"]
      noMacros
      "ρ{ z . z, z} p - q"
      (RhoElim "z" (Var "z" 0 (initialPos "test")) (Var "z" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    -- More complex terms with the bound variable
    testParseProof
      ["f"]
      []
      ["p", "q"]
      noMacros
      "ρ{ x . f x, x} p - q"
      (RhoElim "x" (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))

  it "parses pi elimination" $ do
    testParseProof
      []
      []
      ["p", "q"]
      noMacros
      "π p - x . y . z .q"
      (Pi (PVar "p" 1 (initialPos "test")) "x" "y" "z" (PVar "q" 2 (initialPos "test")) (initialPos "test"))
    testParseProof
      []
      []
      ["r", "s"]
      noMacros
      "pi r - a.b.c.s"
      (Pi (PVar "r" 1 (initialPos "test")) "a" "b" "c" (PVar "s" 2 (initialPos "test")) (initialPos "test"))

  it "parses pi elimination with bound variables used in proof" $ do
    -- Test the bug: variables bound by pi should be usable in the proof term
    testParseProof
      []
      []
      ["p"]
      noMacros
      "π p - x . u . v .(u,v)"
      (Pi (PVar "p" 0 (initialPos "test")) "x" "u" "v" (Pair (PVar "u" 1 (initialPos "test")) (PVar "v" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses converse operations" $ do
    testParseProof [] [] ["p"] noMacros "∪ᵢ p" (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "convIntro p" (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "∪ₑ p" (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "convElim p" (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test"))

  it "parses pairs" $ do
    testParseProof [] [] ["p", "q"] noMacros "(p, q)" (Pair (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p", "q", "r"] noMacros "(p, (q, r))" (Pair (PVar "p" 2 (initialPos "test")) (Pair (PVar "q" 1 (initialPos "test")) (PVar "r" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses complex proof lambda abstractions with nested types" $ do
    testParseProof
      []
      []
      ["p"]
      noMacros
      "λ x: ∀A. A -> A. p"
      (LamP "x" (All "A" (Arr (RVar "A" 0 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test"))
    testParseProof
      []
      ["A", "B"]
      ["q"]
      noMacros
      "λy: A ∘ B˘. q"
      (LamP "y" (Comp (RVar "A" 1 (initialPos "test")) (Conv (RVar "B" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (PVar "q" 1 (initialPos "test")) (initialPos "test"))

  it "parses nested type and proof lambda abstractions" $ do
    testParseProof
      []
      []
      ["q"]
      noMacros
      "Λα. λp: α. Λβ. q"
      (TyLam "α" (LamP "p" (RVar "α" 0 (initialPos "test")) (TyLam "β" (PVar "q" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses complex type applications with nested structures" $ do
    testParseProof
      []
      []
      ["p"]
      noMacros
      "p{∀A. A -> A}"
      (TyApp (PVar "p" 0 (initialPos "test")) (All "A" (Arr (RVar "A" 0 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseProof
      []
      ["A", "B", "C"]
      ["p"]
      noMacros
      "(p{A}){B ∘ C}"
      (TyApp (TyApp (PVar "p" 0 (initialPos "test")) (RVar "A" 2 (initialPos "test")) (initialPos "test")) (Comp (RVar "B" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

declarationParserSpec :: Spec
declarationParserSpec = describe "Declaration parser" $ do
  it "parses Unicode and ASCII alternatives for declarations" $ do
    -- Macro definition symbols
    testParseDeclaration [] [] [] noMacros "Id ≔ (λ x . x);" (MacroDef "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration [] [] [] noMacros "Id ≔ (λ x . x);" (MacroDef "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    -- Theorem definition symbols
    testParseDeclaration [] [] []
      noMacros
      "⊢ test (t : Term) (u : Term) (A : Rel) (p : t [A] u) : t [A] u ≔ p;"
      (TheoremDef "test" [TermBinding "t", TermBinding "u", RelBinding "A", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))] (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test"))) (PVar "p" 0 (initialPos "test")))
    testParseDeclaration [] [] []
      noMacros
      "theorem test (t : Term) (u : Term) (A : Rel) (p : t [A] u) : t [A] u ≔ p;"
      (TheoremDef "test" [TermBinding "t", TermBinding "u", RelBinding "A", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))] (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test"))) (PVar "p" 0 (initialPos "test")))
  it "parses macro definitions" $ do
    testParseDeclaration [] [] []
      noMacros
      "Id ≔ (λ x . x);"
      (MacroDef "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration [] [] []
      noMacros
      "Comp R S ≔ R ∘ S;"
      (MacroDef "Comp" ["R", "S"] (RelMacro (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration [] [] [] noMacros "Id ≔ (λ x . x);"
      (MacroDef "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    -- Test macro name with underscores
    testParseDeclaration [] [] [] noMacros "BoolEq ≔ ∀ X . X → X → X;"
      (MacroDef "BoolEq" [] (RelMacro (All "X" (Arr (RVar "X" 0 (initialPos "test")) (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))))

  it "parses theorem definitions" $ do
    let idMacroEnv = extendMacroEnvironment "Id" [] (RelMacro (RVar "dummy" 0 (initialPos "test"))) (defaultFixity "TEST") noMacros
    testParseDeclaration [] [] [] idMacroEnv "⊢ refl (t : Term) : t [Id] t ≔ ι⟨t, t⟩;"
      ( TheoremDef
          "refl"
          [TermBinding "t"]
          (RelJudgment (Var "t" 0 (initialPos "test")) (RMacro "Id" [] (initialPos "test")) (Var "t" 0 (initialPos "test"))) -- t bound at index 0, Id is macro
          (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test"))
      )

    let symMacroEnv = extendMacroEnvironment "Sym" ["R"] (RelMacro (RVar "dummy" 0 (initialPos "test"))) (defaultFixity "TEST") noMacros
    testParseDeclaration [] [] [] symMacroEnv "theorem sym (t : Term) (u : Term) (R : Rel) (p : t [R] u) : u [Sym R] t ≔ ∪ᵢ p;"
      ( TheoremDef
          "sym"
          [TermBinding "t", TermBinding "u", RelBinding "R", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))]
          (RelJudgment (Var "u" 0 (initialPos "test")) (RMacro "Sym" [RVar "R" 0 (initialPos "test")] (initialPos "test")) (Var "t" 1 (initialPos "test"))) -- t,u,R bound with correct indices
          (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test"))
      )

    -- Test theorem name with underscores
    testParseDeclaration [] [] [] noMacros "⊢ id_test : (λ x . x) [(λ x . x)] (λ x . x) ≔ ι⟨λ x . x, λ x . x⟩;"
      ( TheoremDef
          "id_test"
          []
          (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")))
          (Iota (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
      )

  it "parses relational judgments with complex terms" $ do
    -- Lambda terms in judgments
    let idMacroEnv2 = extendMacroEnvironment "Id" [] (RelMacro (RVar "dummy" 0 (initialPos "test"))) (defaultFixity "TEST") noMacros
    testParseDeclaration [] [] [] idMacroEnv2 "⊢ beta : (λ x . x) [Id] (λ y . y) ≔ ι⟨λ x . x, λ y . y⟩;"
      ( TheoremDef
          "beta"
          []
          (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (RMacro "Id" [] (initialPos "test")) (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")))
          (Iota (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
      )

    -- Application terms in judgments
    testParseDeclaration [] [] [] noMacros "⊢ app (f : Term) (x : Term) (R : Rel) (p : (f x) [R] (f x)) : (f x) [R] (f x) ≔ p;"
      ( TheoremDef
          "app"
          [TermBinding "f", TermBinding "x", RelBinding "R", ProofBinding "p" (RelJudgment (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (RVar "R" 0 (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")))]
          (RelJudgment (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (RVar "R" 0 (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")))
          (PVar "p" 0 (initialPos "test"))
      )

    -- Mixed bound and free variables
    testParseDeclaration [] [] [] noMacros "⊢ mixed (x : Term) (g : Term) (z : Term) (S : Rel) (p : (λ y . x) [S] (g z)) : (λ y . x) [S] (g z) ≔ p;"
      ( TheoremDef
          "mixed"
          [TermBinding "x", TermBinding "g", TermBinding "z", RelBinding "S", ProofBinding "p" (RelJudgment (Lam "y" (Var "x" 3 (initialPos "test")) (initialPos "test")) (RVar "S" 0 (initialPos "test")) (App (Var "g" 1 (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test")))]
          (RelJudgment (Lam "y" (Var "x" 3 (initialPos "test")) (initialPos "test")) (RVar "S" 0 (initialPos "test")) (App (Var "g" 1 (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test")))
          (PVar "p" 0 (initialPos "test"))
      )

    -- Nested lambda terms
    let compMacroEnv = extendMacroEnvironment "Comp" ["A", "B"] (RelMacro (Comp (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))) (defaultFixity "TEST") noMacros
    testParseDeclaration [] [] [] compMacroEnv "⊢ nested (A : Rel) (B : Rel) (p : (λ x . λ y . x y) [Comp A B] (λ z . z)) : (λ x . λ y . x y) [Comp A B] (λ z . z) ≔ p;"
      ( TheoremDef
          "nested"
          [ RelBinding "A",
            RelBinding "B",
            ProofBinding
              "p"
              ( RelJudgment
                  (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
                  (RMacro "Comp" [RVar "A" 1 (initialPos "test"), RVar "B" 0 (initialPos "test")] (initialPos "test"))
                  (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test"))
              )
          ]
          ( RelJudgment
              (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
              (RMacro "Comp" [RVar "A" 1 (initialPos "test"), RVar "B" 0 (initialPos "test")] (initialPos "test"))
              (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test"))
          )
          (PVar "p" 0 (initialPos "test"))
      )

  it "parses relation bindings" $ do
    testParseDeclaration [] [] [] noMacros "⊢ test (t : Term) (u : Term) (A : Rel) (p : t [A] u) : t [A] u ≔ p;"
      ( TheoremDef
          "test"
          [TermBinding "t", TermBinding "u", RelBinding "A", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))]
          (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test"))) -- proper bindings with correct indices
          (PVar "p" 0 (initialPos "test"))
      )

  it "parses files with multiple declarations" $ do
    let input =
          unlines
            [ "Id ≔ (λ x . x);",
              "Sym R ≔ R ˘;",
              "⊢ refl (t : Term) : t [Id] t ≔ ι⟨t, t⟩;"
            ]
    testParseFile [] [] [] noMacros input
      [ MacroDef "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))),
        MacroDef "Sym" ["R"] (RelMacro (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test"))),
        TheoremDef
          "refl"
          [TermBinding "t"]
          (RelJudgment (Var "t" 0 (initialPos "test")) (Prom (TMacro "Id" [] (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test")))
          (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test"))
      ]

  -- Add tests to verify macro vs variable context behavior
  it "correctly distinguishes macros vs variables based on context" $ do
    -- Test without macro context - should parse as RVar
    testParseDeclaration [] [] [] noMacros "⊢ test (t : Term) (u : Term) (Unbound : Rel) (p : t [Unbound] u) : t [Unbound] u ≔ p;"
      (TheoremDef "test" [TermBinding "t", TermBinding "u", RelBinding "Unbound", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "Unbound" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))] (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "Unbound" 0 (initialPos "test")) (Var "u" 0 (initialPos "test"))) (PVar "p" 0 (initialPos "test")))

    -- Test with proper file context that defines 0-arity macro
    let macroFileInput0 =
          unlines
            [ "Rel0 ≔ ∀ X . X;",
              "⊢ test (t : Term) (u : Term) (p : t [Rel0] u) : t [Rel0] u ≔ p;"
            ]
    testParseFile [] [] [] noMacros macroFileInput0
      [ MacroDef "Rel0" [] (RelMacro (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test"))),
        TheoremDef "test" [TermBinding "t", TermBinding "u", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RMacro "Rel0" [] (initialPos "test")) (Var "u" 0 (initialPos "test")))] (RelJudgment (Var "t" 1 (initialPos "test")) (RMacro "Rel0" [] (initialPos "test")) (Var "u" 0 (initialPos "test"))) (PVar "p" 0 (initialPos "test"))
      ]

    -- Test with 1-arity macro application
    let macroFileInput1 =
          unlines
            [ "Sym R ≔ R ˘;",
              "⊢ test (t : Term) (u : Term) (A : Rel) (p : t [Sym A] u) : t [Sym A] u ≔ p;"
            ]
    testParseFile [] [] [] noMacros macroFileInput1
      [ MacroDef "Sym" ["R"] (RelMacro (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test"))),
        TheoremDef "test" [TermBinding "t", TermBinding "u", RelBinding "A", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RMacro "Sym" [RVar "A" 0 (initialPos "test")] (initialPos "test")) (Var "u" 0 (initialPos "test")))] (RelJudgment (Var "t" 1 (initialPos "test")) (RMacro "Sym" [RVar "A" 0 (initialPos "test")] (initialPos "test")) (Var "u" 0 (initialPos "test"))) (PVar "p" 0 (initialPos "test"))
      ]

  it "parses macro applications with arguments" $ do
    let input =
          unlines
            [ "Comp R S ≔ R ∘ S;",
              "Pair A B ≔ A -> B;",
              "⊢ test (t : Term) (u : Term) (X : Rel) (Y : Rel) (p : t [Comp X Y] u) : t [Comp X Y] u ≔ p;"
            ]
    testParseFile [] [] [] noMacros input
      [ MacroDef "Comp" ["R", "S"] (RelMacro (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))),
        MacroDef "Pair" ["A", "B"] (RelMacro (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))),
        TheoremDef
          "test"
          [TermBinding "t", TermBinding "u", RelBinding "X", RelBinding "Y", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RMacro "Comp" [RVar "X" 1 (initialPos "test"), RVar "Y" 0 (initialPos "test")] (initialPos "test")) (Var "u" 0 (initialPos "test")))]
          (RelJudgment (Var "t" 1 (initialPos "test")) (RMacro "Comp" [RVar "X" 1 (initialPos "test"), RVar "Y" 0 (initialPos "test")] (initialPos "test")) (Var "u" 0 (initialPos "test")))
          (PVar "p" 0 (initialPos "test"))
      ]

-- Parser error handling tests
parserErrorSpec :: Spec
parserErrorSpec = describe "Parser error handling" $ do
  it "handles empty input gracefully" $ do
    testParseTermFailure ""
    testParseRTypeFailure ""
    testParseProofFailure ""
    testParseDeclarationFailure ""

  it "handles malformed operators" $ do
    -- Operators without operands
    testParseRTypeFailure "∘"
    testParseRTypeFailure "->"
    testParseRTypeFailure "˘"

  it "handles incomplete constructs" $ do
    -- Incomplete quantifier
    testParseRTypeFailure "∀"
    -- Incomplete lambda
    testParseTermFailure "λ"
    -- Incomplete type application
    testParseProofFailure "p{"

  it "handles mismatched delimiters" $ do
    testParseTermFailure "("
    testParseTermFailure ")"
    testParseRTypeFailure "⟨"
    testParseProofFailure "⟨x"

  it "handles malformed lambda expressions" $ do
    -- Missing variable name
    testParseTermFailure "λ. x"
    -- Missing dot
    testParseTermFailure "λ x x"
    -- Missing body
    testParseTermFailure "λ x ."
    -- Malformed nested lambda
    testParseTermFailure "λ x . λ. y"

  it "handles malformed quantifiers" $ do
    -- Missing variable name
    testParseRTypeFailure "∀. A"
    -- Missing dot
    testParseRTypeFailure "∀x A"
    -- Missing body
    testParseRTypeFailure "∀x ."
    -- Invalid quantifier syntax
    testParseRTypeFailure "∀∀x . A"

  it "handles malformed proof terms" $ do
    -- Invalid iota syntax
    testParseProofFailure "ι< x"
    testParseProofFailure "ι< x , y"
    testParseProofFailure "ι< , y >"
    -- Invalid conversion syntax
    testParseProofFailure "x ⇃ p" -- Incomplete conversion (missing ⇂ y)
    testParseProofFailure "⇃ p ⇂ y" -- Missing first term
    testParseProofFailure "x ⇃ ⇂ y" -- Missing proof
    -- Invalid rho syntax
    testParseProofFailure "ρ{ x . t , t } p"
    testParseProofFailure "ρ{ x . t , t } p -"

  it "handles malformed type applications" $ do
    -- Incomplete type application
    testParseProofFailure "p {"
    testParseProofFailure "p { }"
    -- Missing proof term
    testParseProofFailure "{ R }"

  it "handles malformed macro definitions" $ do
    -- Missing assignment
    testParseDeclarationFailure "Id"
    -- Missing body
    testParseDeclarationFailure "Id ≔"
    -- Invalid parameter syntax
    testParseDeclarationFailure "Id [] ≔ R"

  it "handles malformed theorem definitions" $ do
    -- Missing judgment
    testParseDeclarationFailure "thm :"
    -- Missing proof
    testParseDeclarationFailure "thm : t[R]u ≔"
    -- Invalid binding syntax
    testParseDeclarationFailure "thm (x y) : t[R]u ≔ p"

  it "handles nested parsing errors in complex expressions" $ do
    -- Error in nested lambda
    testParseTermFailure "λ x . λ y . λ. z"
    -- Error in nested type
    testParseRTypeFailure "∀ X . ∀ Y . ∀. Z"
    -- Error in nested proof
    testParseProofFailure "λ u : R . λv:S. ι{x"

  it "handles operator precedence errors" $ do
    -- Missing operands in composition chain
    testParseRTypeFailure "R ∘ ∘ S"
    -- Invalid arrow chain
    testParseRTypeFailure "A → → B"
    -- Malformed promotion
    testParseRTypeFailure "^"

  it "handles Unicode vs ASCII inconsistencies" $ do
    -- Mixed syntax errors
    testParseRTypeFailure "∀x -> A" -- Should be ∀x . A or forall x -> A
    testParseProofFailure "∪i p" -- Should be ∪ᵢ p
    -- Invalid Unicode combinations
    testParseRTypeFailure "R ∘˘ S" -- Invalid operator combination
  it "validates successful mixed Unicode/ASCII parsing" $ do
    -- These should succeed
    testParseRType [] ["A", "B", "C"] [] noMacros "A → B -> C" (Arr (RVar "A" 2 (initialPos "test")) (Arr (RVar "B" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] noMacros "λ x . x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] noMacros "\\x . x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))

-- Complex declaration parsing tests
declarationComplexCasesSpec :: Spec
declarationComplexCasesSpec = describe "Declaration parser complex cases" $ do
  it "parses theorems with many bindings of different types" $ do
    let input = "⊢ complex (t : Term) (u : Term) (v : Term) (A : Rel) (B : Rel) (x : Term) (y : Term) (p : t [A] u) (q : u [B] v) (transProof : t [A ∘ B] v) : t [A ∘ B] v ≔ transProof;"
    testParseDeclaration [] [] [] noMacros input
      ( TheoremDef
          "complex"
          [ TermBinding "t",
            TermBinding "u",
            TermBinding "v",
            RelBinding "A",
            RelBinding "B",
            TermBinding "x",
            TermBinding "y",
            ProofBinding "p" (RelJudgment (Var "t" 4 (initialPos "test")) (RVar "A" 1 (initialPos "test")) (Var "u" 3 (initialPos "test"))),
            ProofBinding "q" (RelJudgment (Var "u" 3 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (Var "v" 2 (initialPos "test"))),
            ProofBinding "transProof" (RelJudgment (Var "t" 4 (initialPos "test")) (Comp (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")) (Var "v" 2 (initialPos "test")))
          ]
          (RelJudgment (Var "t" 4 (initialPos "test")) (Comp (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")) (Var "v" 2 (initialPos "test")))
          (PVar "transProof" 0 (initialPos "test"))
      )

  it "parses macro definitions with deeply nested bodies" $ do
    let input = "NestedComp R S T U ≔ ((R ∘ S) ∘ (T˘ ∘ U))˘;"
    testParseDeclaration [] [] [] noMacros input
      ( MacroDef
          "NestedComp"
          ["R", "S", "T", "U"]
          ( RelMacro
              ( Conv
                  ( Comp
                      (Comp (RVar "R" 3 (initialPos "test")) (RVar "S" 2 (initialPos "test")) (initialPos "test"))
                      (Comp (Conv (RVar "T" 1 (initialPos "test")) (initialPos "test")) (RVar "U" 0 (initialPos "test")) (initialPos "test"))
                      (initialPos "test")
                  )
                  (initialPos "test")
              )
          )
      )

  it "parses theorems with complex relational judgments" $ do
    let input = "⊢ complexRel (R : Rel) (S : Rel) (complexProof : (λ x . x) [(∀ X . R ∘ X ∘ S)] (λ y . y)) : (λ x . x) [(∀ X . R ∘ X ∘ S)] (λ y . y) ≔ complexProof;"
    testParseDeclaration [] [] [] noMacros input
      ( TheoremDef
          "complexRel"
          [ RelBinding "R",
            RelBinding "S",
            ProofBinding
              "complexProof"
              ( RelJudgment
                  (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
                  (All "X" (Comp (Comp (RVar "R" 2 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (RVar "S" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
                  (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test"))
              )
          ]
          ( RelJudgment
              (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
              (All "X" (Comp (Comp (RVar "R" 2 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (RVar "S" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
              (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test"))
          )
          (PVar "complexProof" 0 (initialPos "test"))
      )

  it "parses macro definitions with promoted lambda terms" $ do
    let input = "LambdaMacro A B ≔ (λ x . λ y . x y);"
    testParseDeclaration [] [] [] noMacros input
      ( MacroDef
          "LambdaMacro"
          ["A", "B"]
          (TermMacro (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")))
      )

  it "parses files with multiple complex declarations" $ do
    let input =
          unlines
            [ "DoubleComp R S ≔ R ∘ R ∘ S;",
              "TripleRel A B C ≔ A ∘ (B˘ ∘ C);",
              "⊢ composition (t : Term) (u : Term) (v : Term) (w : Term) (X : Rel) (Y : Rel) (Z : Rel) (p : t [X] u) (q : u [Y] v) (r : v [Z] w) (tripleComp : t [X ∘ Y ∘ Z] w) : t [X ∘ Y ∘ Z] w ≔ tripleComp;",
              "Identity ≔ (λ x . x);",
              "⊢ identity (t : Term) : t [Identity] t ≔ ι⟨t, t⟩;"
            ]
    testParseFile [] [] [] noMacros input
      [ MacroDef "DoubleComp" ["R", "S"] (RelMacro (Comp (Comp (RVar "R" 1 (initialPos "test")) (RVar "R" 1 (initialPos "test")) (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))),
        MacroDef "TripleRel" ["A", "B", "C"] (RelMacro (Comp (RVar "A" 2 (initialPos "test")) (Comp (Conv (RVar "B" 1 (initialPos "test")) (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))),
        TheoremDef
          "composition"
          [ TermBinding "t",
            TermBinding "u",
            TermBinding "v",
            TermBinding "w",
            RelBinding "X",
            RelBinding "Y",
            RelBinding "Z",
            ProofBinding "p" (RelJudgment (Var "t" 3 (initialPos "test")) (RVar "X" 2 (initialPos "test")) (Var "u" 2 (initialPos "test"))),
            ProofBinding "q" (RelJudgment (Var "u" 2 (initialPos "test")) (RVar "Y" 1 (initialPos "test")) (Var "v" 1 (initialPos "test"))),
            ProofBinding "r" (RelJudgment (Var "v" 1 (initialPos "test")) (RVar "Z" 0 (initialPos "test")) (Var "w" 0 (initialPos "test"))),
            ProofBinding "tripleComp" (RelJudgment (Var "t" 3 (initialPos "test")) (Comp (Comp (RVar "X" 2 (initialPos "test")) (RVar "Y" 1 (initialPos "test")) (initialPos "test")) (RVar "Z" 0 (initialPos "test")) (initialPos "test")) (Var "w" 0 (initialPos "test")))
          ]
          (RelJudgment (Var "t" 3 (initialPos "test")) (Comp (Comp (RVar "X" 2 (initialPos "test")) (RVar "Y" 1 (initialPos "test")) (initialPos "test")) (RVar "Z" 0 (initialPos "test")) (initialPos "test")) (Var "w" 0 (initialPos "test")))
          (PVar "tripleComp" 0 (initialPos "test")),
        MacroDef "Identity" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))),
        TheoremDef
          "identity"
          [TermBinding "t"]
          (RelJudgment (Var "t" 0 (initialPos "test")) (Prom (TMacro "Identity" [] (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test")))
          (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test"))
      ]

  it "parses theorems with nested quantified types in bindings" $ do
    let input = "⊢ quantified (t : Term) (u : Term) (p : t [∀ X . ∀ Y . X ∘ Y] u) (quantProof : u [∀Z. Z˘] t) : u [∀Z. Z˘] t ≔ quantProof;"
    testParseDeclaration [] [] [] noMacros input
      ( TheoremDef
          "quantified"
          [TermBinding "t", TermBinding "u", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (All "X" (All "Y" (Comp (RVar "X" 1 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "u" 0 (initialPos "test"))), ProofBinding "quantProof" (RelJudgment (Var "u" 0 (initialPos "test")) (All "Z" (Conv (RVar "Z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 1 (initialPos "test")))]
          (RelJudgment (Var "u" 0 (initialPos "test")) (All "Z" (Conv (RVar "Z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 1 (initialPos "test")))
          (PVar "quantProof" 0 (initialPos "test"))
      )

  it "parses macro definitions with variable shadowing" $ do
    let input = "ShadowMacro R ≔ ∀R . R ∘ R;"
    testParseDeclaration [] [] [] noMacros input
      ( MacroDef
          "ShadowMacro"
          ["R"]
          (RelMacro (All "R" (Comp (RVar "R" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))) -- Inner R shadows outer R
      )

  it "parses theorems with complex proof terms" $ do
    let input = "⊢ complexProof (R : Rel) (t : Term) (u : Term) : t [R] u ≔ ρ{ x . t, u} (Λα. λp: α. p { R }) - ι⟨t, u⟩;"
    testParseDeclaration [] [] [] noMacros input
      ( TheoremDef
          "complexProof"
          [RelBinding "R", TermBinding "t", TermBinding "u"]
          (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))
          ( RhoElim
              "x"
              (Var "t" 2 (initialPos "test"))
              (Var "u" 1 (initialPos "test"))
              (TyLam "α" (LamP "p" (RVar "α" 0 (initialPos "test")) (TyApp (PVar "p" 0 (initialPos "test")) (RVar "R" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
              (Iota (Var "t" 1 (initialPos "test")) (Var "u" 0 (initialPos "test")) (initialPos "test"))
              (initialPos "test")
          )
      )

  it "parses macro applications within macro definitions" $ do
    let input =
          unlines
            [ "Base A ≔ A ∘ A;",
              "Extended B C ≔ Base B ∘ C;"
            ]
    testParseFile [] [] [] noMacros input
      [ MacroDef "Base" ["A"] (RelMacro (Comp (RVar "A" 0 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test"))),
        MacroDef "Extended" ["B", "C"] (RelMacro (Comp (RMacro "Base" [RVar "B" 1 (initialPos "test")] (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")))
      ]

  it "parses extremely long macro parameter lists" $ do
    let params = ["A", "B", "C", "D", "E", "F", "G", "H", "I", "J"]
        paramStr = unwords params
        input = "ManyParams " ++ paramStr ++ " ≔ A ∘ B ∘ C ∘ D ∘ E ∘ F ∘ G ∘ H ∘ I ∘ J;"
        compWithPos x y = Comp x y (initialPos "test")
        expectedBody = foldl1 compWithPos (map (\(name, idx) -> RVar name idx (initialPos "test")) (zip params (reverse [0 .. length params - 1])))
    testParseDeclaration [] [] [] noMacros input
      (MacroDef "ManyParams" params (RelMacro expectedBody))

  it "parses theorems with deeply nested binding contexts" $ do
    let input = "⊢ deeplyNested (A : Rel) (B : Rel) (C : Rel) (x : Term) (y : Term) (z : Term) (p : x [A] y) (q : y [B] z) (r : x [C] z) (compositionElim : x [A ∘ B] z) : x [A ∘ B] z ≔ compositionElim;"
    testParseDeclaration [] [] [] noMacros input
      ( TheoremDef
          "deeplyNested"
          [ RelBinding "A",
            RelBinding "B",
            RelBinding "C",
            TermBinding "x",
            TermBinding "y",
            TermBinding "z",
            ProofBinding "p" (RelJudgment (Var "x" 2 (initialPos "test")) (RVar "A" 2 (initialPos "test")) (Var "y" 1 (initialPos "test"))),
            ProofBinding "q" (RelJudgment (Var "y" 1 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (Var "z" 0 (initialPos "test"))),
            ProofBinding "r" (RelJudgment (Var "x" 2 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (Var "z" 0 (initialPos "test"))),
            ProofBinding "compositionElim" (RelJudgment (Var "x" 2 (initialPos "test")) (Comp (RVar "A" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (Var "z" 0 (initialPos "test")))
          ]
          (RelJudgment (Var "x" 2 (initialPos "test")) (Comp (RVar "A" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (Var "z" 0 (initialPos "test")))
          (PVar "compositionElim" 0 (initialPos "test"))
      )

  it "handles mixed Unicode and ASCII in complex declarations" $ do
    let input = "MixedSyntax R S ≔ R ∘ S ˘ -> ∀ X . X;"
    testParseDeclaration [] [] [] noMacros input
      ( MacroDef
          "MixedSyntax"
          ["R", "S"]
          (RelMacro (Arr (Comp (RVar "R" 1 (initialPos "test")) (Conv (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")))
      )

-- De Bruijn index edge case tests
deBruijnEdgeCasesSpec :: Spec
deBruijnEdgeCasesSpec = describe "De Bruijn index edge cases" $ do
  it "handles deep nesting with correct index calculation" $ do
    -- Test λ x . λ y . λ z . λ w . λv. x (deeply nested, x at index 4)
    testParseTerm [] [] [] noMacros "λ x . λ y . λ z . λ w . λv. x"
      (Lam "x" (Lam "y" (Lam "z" (Lam "w" (Lam "v" (Var "x" 4 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles complex variable shadowing patterns" $ do
    -- Test λ x . λ y . λ x . λ y . x y (inner x shadows outer, inner y shadows outer)
    testParseTerm [] [] [] noMacros "λ x . λ y . λ x . λ y . x y"
      (Lam "x" (Lam "y" (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles variable references across multiple shadow levels" $ do
    -- Test λ x . λ y . λ x . λ z . λ x . λ y . x y z (multiple levels of shadowing)
    testParseTerm [] [] [] noMacros "λ x . λ y . λ x . λ z . λ x . λ y . x y z"
      ( Lam
          "x"
          ( Lam
              "y"
              ( Lam
                  "x"
                  ( Lam
                      "z"
                      ( Lam
                          "x"
                          ( Lam
                              "y"
                              (App (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (Var "z" 2 (initialPos "test")) (initialPos "test"))
                              (initialPos "test")
                          )
                          (initialPos "test")
                      )
                      (initialPos "test")
                  )
                  (initialPos "test")
              )
              (initialPos "test")
          )
          (initialPos "test")
      )

  it "handles boundary conditions with index 0" $ do
    -- Test immediately bound variables
    testParseTerm [] [] [] noMacros "λ x . x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] [] [] noMacros "∀x . x" (All "x" (RVar "x" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] ["A"] [] noMacros "λ x: A. x" (LamP "x" (RVar "A" 0 (initialPos "test")) (PVar "x" 0 (initialPos "test")) (initialPos "test"))

  it "handles free variables with index -1" $ do
    -- Test free variables in various contexts
    testParseTerm ["x"] [] [] noMacros "x" (Var "x" 0 (initialPos "test"))
    testParseRType [] ["R"] [] noMacros "R" (RVar "R" 0 (initialPos "test")) -- Free relation variables
    testParseProof [] [] ["p"] noMacros "p" (PVar "p" 0 (initialPos "test"))

  it "handles mixed free and bound variables" $ do
    -- Test λ x . x free_var (bound x at 0, free_var at index 1)
    testParseTerm ["free"] [] [] noMacros "λ x . x free"
      (Lam "x" (App (Var "x" 0 (initialPos "test")) (Var "free" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles quantifier nesting with correct indices" $ do
    -- Test ∀A. ∀B. ∀C. A ∘ B ∘ C (A at 2, B at 1, C at 0)
    testParseRType [] [] [] noMacros "∀A. ∀B. ∀C. A ∘ B ∘ C"
      (All "A" (All "B" (All "C" (Comp (Comp (RVar "A" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles extreme nesting depth" $ do
    -- Create a very deeply nested lambda term that references the outermost bound variable
    let depth = 20
        buildNestedLambda 0 = Var "x20" (depth - 1) (initialPos "test") -- Reference outermost lambda variable x20 (index 19)
        buildNestedLambda n = Lam ("x" ++ show n) (buildNestedLambda (n - 1)) (initialPos "test")
        expected = buildNestedLambda depth

        buildInput 0 = "x20" -- Reference the outermost variable
        buildInput n = "λ x" ++ show n ++ ". " ++ buildInput (n - 1)
        input = buildInput depth

    testParseTerm [] [] [] noMacros input expected

  it "handles complex proof binding contexts" $ do
    -- Test theorem with many bindings that create complex de Bruijn patterns
    let input = "⊢ multiBinding (x : Term) (y : Term) (z : Term) (R : Rel) (S : Rel) (p1 : x [R] y) (p2 : y [S] z) (p3 : x [R ∘ S] z) : x [R] z ≔ p1;"
    testParseDeclaration [] [] [] noMacros input
      ( TheoremDef
          "multiBinding"
          [ TermBinding "x",
            TermBinding "y",
            TermBinding "z",
            RelBinding "R",
            RelBinding "S",
            ProofBinding "p1" (RelJudgment (Var "x" 2 (initialPos "test")) (RVar "R" 1 (initialPos "test")) (Var "y" 1 (initialPos "test"))),
            ProofBinding "p2" (RelJudgment (Var "y" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (Var "z" 0 (initialPos "test"))),
            ProofBinding "p3" (RelJudgment (Var "x" 2 (initialPos "test")) (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) (Var "z" 0 (initialPos "test")))
          ]
          (RelJudgment (Var "x" 2 (initialPos "test")) (RVar "R" 1 (initialPos "test")) (Var "z" 0 (initialPos "test")))
          (PVar "p1" 2 (initialPos "test"))
      )

  it "handles variable capture avoidance in complex terms" $ do
    -- Test cases where variable names could conflict but indices prevent capture
    testParseTerm [] [] [] noMacros "λ x . (λ x . x) x"
      (Lam "x" (App (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) -- Inner x (index 0), outer x (index 0)
  it "handles index shifting in application contexts" $ do
    -- Test complex applications where index management is critical
    testParseTerm [] [] [] noMacros "(λ x . λ y . x) (λ z . z)"
      (App (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles binding in different syntactic contexts" $ do
    -- Test that binding works consistently across term, type, and proof contexts
    testParseTerm
      []
      []
      []
      noMacros
      "λ x . λ y . x y"
      (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseRType
      []
      []
      []
      noMacros
      "∀R . ∀S. R ∘ S"
      (All "R" (All "S" (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseProof
      []
      ["A", "B"]
      []
      noMacros
      "λp: A. λq: B. p"
      (LamP "p" (RVar "A" 1 (initialPos "test")) (LamP "q" (RVar "B" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles index boundary stress test" $ do
    -- Test with very high indices to ensure no overflow issues
    let buildDeepLambda 0 acc = acc
        buildDeepLambda n acc = buildDeepLambda (n - 1) (Lam ("x" ++ show n) acc (initialPos "test"))
        deepTerm = buildDeepLambda 50 (Var "x1" 49 (initialPos "test")) -- Reference the outermost variable
        buildDeepInput 0 acc = acc
        buildDeepInput n acc = buildDeepInput (n - 1) ("λ x" ++ show n ++ ". " ++ acc)
        deepInput = buildDeepInput 50 "x1"

    testParseTerm [] [] [] noMacros deepInput deepTerm

  it "handles interleaved binding types in complex declarations" $ do
    -- Test declarations with alternating term, relation, and proof bindings
    let input = "⊢ interleaved (R : Rel) (t : Term) (S : Rel) (u : Term) (p : t [R] u) (T : Rel) : t [R ∘ S ∘ T] u ≔ p;"
    testParseDeclaration [] [] [] noMacros input
      ( TheoremDef
          "interleaved"
          [ RelBinding "R",
            TermBinding "t",
            RelBinding "S",
            TermBinding "u",
            ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "R" 1 (initialPos "test")) (Var "u" 0 (initialPos "test"))),
            RelBinding "T"
          ]
          (RelJudgment (Var "t" 1 (initialPos "test")) (Comp (Comp (RVar "R" 2 (initialPos "test")) (RVar "S" 1 (initialPos "test")) (initialPos "test")) (RVar "T" 0 (initialPos "test")) (initialPos "test")) (Var "u" 0 (initialPos "test")))
          (PVar "p" 0 (initialPos "test"))
      )

  it "handles edge case of zero bindings" $ do
    -- Test that variables work correctly when there are no lambda bindings
    testParseTerm ["free1", "free2"] [] [] noMacros "free1 free2" (App (Var "free1" 1 (initialPos "test")) (Var "free2" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["FreeRel"] [] noMacros "FreeRel" (RVar "FreeRel" 0 (initialPos "test"))
    testParseProof [] [] ["freeProof"] noMacros "freeProof" (PVar "freeProof" 0 (initialPos "test"))

  it "handles maximum complexity binding scenario" $ do
    -- Test the most complex binding scenario we can create
    let input = "⊢ maxComplexity (A : Rel) (B : Rel) (C : Rel) (x : Term) (y : Term) (z : Term) (w : Term) (p1 : x [A] y) (p2 : y [B] z) (p3 : z [C] w) (p4 : x [A ∘ B] z) (p5 : y [B ∘ C] w) (p6 : x [A ∘ B ∘ C] w) : x [A] w ≔ p1;"
    -- This creates a complex binding context that tests the limits of de Bruijn index management
    testParseDeclaration [] [] [] noMacros input
      ( TheoremDef
          "maxComplexity"
          [ RelBinding "A",
            RelBinding "B",
            RelBinding "C",
            TermBinding "x",
            TermBinding "y",
            TermBinding "z",
            TermBinding "w",
            ProofBinding "p1" (RelJudgment (Var "x" 3 (initialPos "test")) (RVar "A" 2 (initialPos "test")) (Var "y" 2 (initialPos "test"))),
            ProofBinding "p2" (RelJudgment (Var "y" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (Var "z" 1 (initialPos "test"))),
            ProofBinding "p3" (RelJudgment (Var "z" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (Var "w" 0 (initialPos "test"))),
            ProofBinding "p4" (RelJudgment (Var "x" 3 (initialPos "test")) (Comp (RVar "A" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (Var "z" 1 (initialPos "test"))),
            ProofBinding "p5" (RelJudgment (Var "y" 2 (initialPos "test")) (Comp (RVar "B" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (Var "w" 0 (initialPos "test"))),
            ProofBinding "p6" (RelJudgment (Var "x" 3 (initialPos "test")) (Comp (Comp (RVar "A" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (Var "w" 0 (initialPos "test")))
          ]
          (RelJudgment (Var "x" 3 (initialPos "test")) (RVar "A" 2 (initialPos "test")) (Var "w" 0 (initialPos "test")))
          (PVar "p1" 5 (initialPos "test"))
      )

-- Theorem referencing tests
theoremReferencingSpec :: Spec
theoremReferencingSpec = describe "Theorem referencing" $ do
  it "parses theorem definitions and references in file context" $ do
    let input =
          unlines
            [ "⊢ identity_lemma (t : Term) : t [(λ x . x)] t ≔ ι⟨t, t⟩;",
              "⊢ test_ref (s : Term) : s [(λ x . x)] s ≔ identity_lemma;"
            ]
    testParseFile [] [] [] noMacros input
      [ TheoremDef
          "identity_lemma"
          [TermBinding "t"]
          (RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test")))
          (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test")),
        TheoremDef
          "test_ref"
          [TermBinding "s"]
          (RelJudgment (Var "s" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "s" 0 (initialPos "test")))
          (PTheoremApp "identity_lemma" [] (initialPos "test")) -- theorem reference
      ]

  it "distinguishes between theorem names and proof variables" $ do
    -- Test that theorem names are resolved correctly when there's no shadowing
    let input = "⊢ simple (t : Term) : t [(λ x . x)] t ≔ ι⟨t, t⟩; ⊢ test (s : Term) : s [(λ x . x)] s ≔ simple;"
    testParseFile [] [] [] noMacros input
      [ TheoremDef "simple" [TermBinding "t"] (RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test"))) (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test")),
        TheoremDef "test" [TermBinding "s"] (RelJudgment (Var "s" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "s" 0 (initialPos "test"))) (PTheoremApp "simple" [] (initialPos "test"))
      ]

  it "handles theorem name shadowing by proof variables" $ do
    -- Test that proof variables take precedence over theorem names
    let input =
          unlines
            [ "⊢ myTheorem (t : Term) : t [(λ x . x)] t ≔ ι⟨t, t⟩;",
              "⊢ shadowTest (s : Term) (myTheorem : s [(λ x . x)] s) : s [(λ x . x)] s ≔ myTheorem;"
            ]
    testParseFile [] [] [] noMacros input
      [ TheoremDef "myTheorem" [TermBinding "t"] (RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test"))) (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test")),
        TheoremDef
          "shadowTest"
          [TermBinding "s", ProofBinding "myTheorem" (RelJudgment (Var "s" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "s" 0 (initialPos "test")))]
          (RelJudgment (Var "s" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "s" 0 (initialPos "test")))
          (PVar "myTheorem" 0 (initialPos "test")) -- bound proof variable, not theorem reference
      ]

  it "produces error for undeclared theorem references" $ do
    -- Test that referencing a non-existent theorem produces a parse error
    let input = "⊢ test (s : Term) : s [(λ x . x)] s ≔ undeclaredTheorem;"
    case runParser parseFile "test" (input) of
      Left _ -> return () -- Expected failure during raw parsing
      Right rawResults -> 
        case mapM (elaborate (ElaborateContext noMacros noTheorems 0 0 0 Map.empty Map.empty Map.empty)) rawResults of
          Left _ -> return () -- Expected failure during elaboration
          Right _ -> expectationFailure "Expected elaboration error for undeclared theorem reference"
