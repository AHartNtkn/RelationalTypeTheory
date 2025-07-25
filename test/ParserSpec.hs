{-# LANGUAGE OverloadedStrings #-}

module ParserSpec (spec) where

import Context (extendMacroEnvironment, noMacros, noTheorems)
import qualified Data.Map as Map
import Lib
import qualified RawParser as Raw
import Elaborate
import Test.Hspec
import TestHelpers
import Text.Megaparsec (eof, errorBundlePretty, initialPos, runParser)

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

-- Helper functions for two-phase parsing
testParseTerm :: [String] -> [String] -> [String] -> MacroEnvironment -> String -> Term -> Expectation
testParseTerm tVars rVars pVars testMacroEnv input expected =
  let termVarMap = Map.fromList (zip tVars (reverse [0 .. length tVars - 1]))
      relVarMap = Map.fromList (zip rVars (reverse [0 .. length rVars - 1]))
      proofVarMap = Map.fromList (zip pVars (reverse [0 .. length pVars - 1]))
      ctx = (emptyElaborateContext Map.empty testMacroEnv noTheorems) { termVars = termVarMap, relVars = relVarMap, proofVars = proofVarMap }
   in case runParser (Raw.parseTerm <* eof) "test" input of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right rawTerm -> case elaborateTerm ctx rawTerm of
          Left err -> expectationFailure $ "Elaboration failed: " ++ show err
          Right result -> result `shouldBeEqual` expected

testParseRType :: [String] -> [String] -> [String] -> MacroEnvironment -> String -> RType -> Expectation
testParseRType tVars rVars pVars testMacroEnv input expected =
  let termVarMap = Map.fromList (zip tVars (reverse [0 .. length tVars - 1]))
      relVarMap = Map.fromList (zip rVars (reverse [0 .. length rVars - 1]))
      proofVarMap = Map.fromList (zip pVars (reverse [0 .. length pVars - 1]))
      ctx = (emptyElaborateContext Map.empty testMacroEnv noTheorems) { termVars = termVarMap, relVars = relVarMap, proofVars = proofVarMap }
   in case runParser (Raw.parseRType <* eof) "test" input of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right rawRType -> case elaborateRType ctx rawRType of
          Left err -> expectationFailure $ "Elaboration failed: " ++ show err
          Right result -> result `shouldBeEqual` expected

testParseProof :: [String] -> [String] -> [String] -> MacroEnvironment -> String -> Proof -> Expectation
testParseProof tVars rVars pVars testMacroEnv input expected =
  let termVarMap = Map.fromList (zip tVars (reverse [0 .. length tVars - 1]))
      relVarMap = Map.fromList (zip rVars (reverse [0 .. length rVars - 1]))
      proofVarMap = Map.fromList (zip pVars (reverse [0 .. length pVars - 1]))
      ctx = (emptyElaborateContext Map.empty testMacroEnv noTheorems) { termVars = termVarMap, relVars = relVarMap, proofVars = proofVarMap }
   in case runParser (Raw.parseProof <* eof) "test" input of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right rawProof -> case elaborateProof ctx rawProof of
          Left err -> expectationFailure $ "Elaboration failed: " ++ show err
          Right result -> result `shouldBeEqual` expected

testParseDeclaration :: MacroEnvironment -> String -> Declaration -> Expectation
testParseDeclaration testMacroEnv input expected =
  let ctx = emptyElaborateContext Map.empty testMacroEnv noTheorems
   in case runParser (Raw.parseDeclaration <* eof) "test" input of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right rawDecl -> case elaborateDeclaration ctx rawDecl of
          Left err -> expectationFailure $ "Elaboration failed: " ++ show err
          Right result -> result `shouldBeEqual` expected

createTermMacroEnv :: [(String, [String])] -> MacroEnvironment
createTermMacroEnv macros = foldr (\(name, params) env -> 
  extendMacroEnvironment name params (TermMacro (Var "dummy" 0 (initialPos "test"))) defaultFixity env) noMacros macros

-- Helper for testing parse failures
testParseFailure :: String -> Expectation
testParseFailure input =
  case runParser (Raw.parseTerm <* eof) "test" input of
    Left _ -> return () -- Expected failure
    Right result -> expectationFailure $ "Expected parse failure, but got: " ++ show result

-- Test specs (all restored from original with simplified conversions)
termParserSpec :: Spec
termParserSpec = describe "Term parser" $ do
  it "parses variables" $ do
    testParseTerm ["x"] [] [] noMacros "x" (Var "x" 0 (initialPos "test"))
    testParseTerm ["foo"] [] [] noMacros "foo" (Var "foo" 0 (initialPos "test"))
    testParseTerm ["x123"] [] [] noMacros "x123" (Var "x123" 0 (initialPos "test"))
    testParseTerm ["foo_bar"] [] [] noMacros "foo_bar" (Var "foo_bar" 0 (initialPos "test"))
    testParseTerm ["test_123"] [] [] noMacros "test_123" (Var "test_123" 0 (initialPos "test"))
    testParseTerm ["a_b_c"] [] [] noMacros "a_b_c" (Var "a_b_c" 0 (initialPos "test"))
    testParseTerm ["x'"] [] [] noMacros "x'" (Var "x'" 0 (initialPos "test"))
    testParseTerm ["foo'"] [] [] noMacros "foo'" (Var "foo'" 0 (initialPos "test"))
    testParseTerm ["x''"] [] [] noMacros "x''" (Var "x''" 0 (initialPos "test"))

  it "parses lambda abstractions" $ do
    testParseTerm [] [] [] noMacros "λx. x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] noMacros "\\x. x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] noMacros "λx. λy. x" (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] noMacros "λx_1. x_1" (Lam "x_1" (Var "x_1" 0 (initialPos "test")) (initialPos "test"))

  it "parses complex nested lambda abstractions" $ do
    testParseTerm [] [] [] noMacros "λx. λy. λz. x" (Lam "x" (Lam "y" (Lam "z" (Var "x" 2 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] noMacros "λx. λy. λz. y" (Lam "x" (Lam "y" (Lam "z" (Var "y" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] noMacros "λx. λy. λz. z" (Lam "x" (Lam "y" (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses variable shadowing scenarios" $ do
    testParseTerm [] [] [] noMacros "λx. λx. x" (Lam "x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses applications" $ do
    testParseTerm ["f", "x"] [] [] noMacros "f x" (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["f", "x", "y"] [] [] noMacros "f x y" (App (App (Var "f" 2 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))

  it "parses parentheses correctly" $ do
    testParseTerm [] [] [] noMacros "(λx. x)" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["f", "x", "y"] [] [] noMacros "(f x) y" (App (App (Var "f" 2 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["f", "x", "y"] [] [] noMacros "f (x y)" (App (Var "f" 2 (initialPos "test")) (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

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
    testParseTerm ["g", "h", "y"] [] [] env "compose (λx. x) g (h y)" (TMacro "compose" [Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"), Var "g" 2 (initialPos "test"), App (Var "h" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")] (initialPos "test"))

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
  it "distinguishes variables from macros based on context" $ do
    let env = createTermMacroEnv [("f", [])]
    testParseTerm ["f"] [] [] noMacros "f" (Var "f" 0 (initialPos "test"))
    testParseTerm [] [] [] env "f" (TMacro "f" [] (initialPos "test"))

  it "handles context with multiple macros" $ do
    let env = createTermMacroEnv [("add", ["x", "y"]), ("mul", ["x", "y"]), ("id", ["x"])]
    testParseTerm ["x", "y"] [] [] env "add x y" (TMacro "add" [Var "x" 1 (initialPos "test"), Var "y" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["a", "b"] [] [] env "mul a b" (TMacro "mul" [Var "a" 1 (initialPos "test"), Var "b" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["z"] [] [] env "id z" (TMacro "id" [Var "z" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["unknown", "x"] [] [] env "unknown x" (App (Var "unknown" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))

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
    testParseTerm [] [] [] env "λz. f z" (Lam "z" (TMacro "f" [Var "z" 0 (initialPos "test")] (initialPos "test")) (initialPos "test"))

  it "handles partial macro applications" $ do
    let env = createTermMacroEnv [("f", ["x", "y"])]
    -- Partial application should fail with arity mismatch
    testParseTermFailure ["x"] [] [] env "f x" (MacroArityMismatch "f" 2 1)
    -- Full application should succeed
    testParseTerm ["x", "y"] [] [] env "f x y" (TMacro "f" [Var "x" 1 (initialPos "test"), Var "y" 0 (initialPos "test")] (initialPos "test"))

  it "respects macro arity limits" $ do
    let env = createTermMacroEnv [("unary", ["x"]), ("binary", ["x", "y"])]
    testParseTerm ["a"] [] [] env "unary a" (TMacro "unary" [Var "a" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["a", "b"] [] [] env "binary a b" (TMacro "binary" [Var "a" 1 (initialPos "test"), Var "b" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["a", "b"] [] [] env "unary a b" (App (TMacro "unary" [Var "a" 1 (initialPos "test")] (initialPos "test")) (Var "b" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["a", "b", "c"] [] [] env "binary a b c" (App (TMacro "binary" [Var "a" 2 (initialPos "test"), Var "b" 1 (initialPos "test")] (initialPos "test")) (Var "c" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["a", "b"] [] [] env "(unary a) b" (App (TMacro "unary" [Var "a" 1 (initialPos "test")] (initialPos "test")) (Var "b" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm ["a", "b", "c"] [] [] env "(binary a b) c" (App (TMacro "binary" [Var "a" 2 (initialPos "test"), Var "b" 1 (initialPos "test")] (initialPos "test")) (Var "c" 0 (initialPos "test")) (initialPos "test"))

advancedTermMacroScenarioSpec :: Spec
advancedTermMacroScenarioSpec = describe "Advanced term macro scenarios" $ do
  it "handles deeply nested TMacro applications" $ do
    let env = createTermMacroEnv [("f", ["x"]), ("g", ["y"]), ("h", ["z"])]
    testParseTerm ["x"] [] [] env "f (g (h x))" (TMacro "f" [TMacro "g" [TMacro "h" [Var "x" 0 (initialPos "test")] (initialPos "test")] (initialPos "test")] (initialPos "test"))
    testParseTerm ["x", "y"] [] [] env "f (g (x y))" (TMacro "f" [TMacro "g" [App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")] (initialPos "test")] (initialPos "test"))

  it "handles TMacro in lambda abstractions with variable capture" $ do
    let env = createTermMacroEnv [("apply", ["f", "x"])]
    testParseTerm ["x"] [] [] env "λf. apply f x" (Lam "f" (TMacro "apply" [Var "f" 0 (initialPos "test"), Var "x" 1 (initialPos "test")] (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] env "λx. λy. apply x y" (Lam "x" (Lam "y" (TMacro "apply" [Var "x" 1 (initialPos "test"), Var "y" 0 (initialPos "test")] (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles mixed macro patterns with bound variables" $ do
    let env = createTermMacroEnv [("compose", ["f", "g"]), ("id", [])]
    testParseTerm ["f", "g"] [] [] env "compose (compose id f) g" (TMacro "compose" [TMacro "compose" [TMacro "id" [] (initialPos "test"), Var "f" 1 (initialPos "test")] (initialPos "test"), Var "g" 0 (initialPos "test")] (initialPos "test"))

  it "handles TMacro with complex argument patterns" $ do
    let env = createTermMacroEnv [("curry", ["f", "x", "y"]), ("uncurry", ["f"])]
    testParseTerm ["a", "b"] [] [] env "curry (λx. λy. x y) a b" (TMacro "curry" [Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"), Var "a" 1 (initialPos "test"), Var "b" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["f", "x", "y"] [] [] env "uncurry (curry f x y)" (TMacro "uncurry" [TMacro "curry" [Var "f" 2 (initialPos "test"), Var "x" 1 (initialPos "test"), Var "y" 0 (initialPos "test")] (initialPos "test")] (initialPos "test"))

  it "handles variable shadowing with TMacros" $ do
    let env = createTermMacroEnv [("bind", ["x", "f"])]
    testParseTerm [] [] [] env "λx. bind x (λx. x)" (Lam "x" (TMacro "bind" [Var "x" 0 (initialPos "test"), Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")] (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] env "λf. λx. bind (f x) (λf. f)" (Lam "f" (Lam "x" (TMacro "bind" [App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"), Lam "f" (Var "f" 0 (initialPos "test")) (initialPos "test")] (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles TMacro arity edge cases" $ do
    let env = createTermMacroEnv [("binary", ["x", "y"]), ("ternary", ["x", "y", "z"])]
    -- Partial application should fail
    testParseTermFailure ["x", "y", "z"] [] [] env "binary x" (MacroArityMismatch "binary" 2 1)
    -- Full application should succeed
    testParseTerm ["x", "y", "z"] [] [] env "binary x y" (TMacro "binary" [Var "x" 2 (initialPos "test"), Var "y" 1 (initialPos "test")] (initialPos "test"))
    -- Over-application should succeed (macro consumes exact arity, rest becomes application)
    testParseTerm ["x", "y", "z"] [] [] env "binary x y z" (App (TMacro "binary" [Var "x" 2 (initialPos "test"), Var "y" 1 (initialPos "test")] (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test"))

  it "handles TMacro in complex application chains" $ do
    let env = createTermMacroEnv [("map", ["f", "xs"]), ("filter", ["p", "xs"])]
    testParseTerm ["f", "p", "xs"] [] [] env "map f (filter p xs)" (TMacro "map" [Var "f" 2 (initialPos "test"), TMacro "filter" [Var "p" 1 (initialPos "test"), Var "xs" 0 (initialPos "test")] (initialPos "test")] (initialPos "test"))
    testParseTerm ["f", "xs", "ys"] [] [] env "map f xs ys" (App (TMacro "map" [Var "f" 2 (initialPos "test"), Var "xs" 1 (initialPos "test")] (initialPos "test")) (Var "ys" 0 (initialPos "test")) (initialPos "test"))

  it "handles TMacro with parentheses and precedence" $ do
    let env = createTermMacroEnv [("add", ["x", "y"]), ("mul", ["x", "y"])]
    testParseTerm ["x", "y", "z"] [] [] env "add (mul x y) z" (TMacro "add" [TMacro "mul" [Var "x" 2 (initialPos "test"), Var "y" 1 (initialPos "test")] (initialPos "test"), Var "z" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["x", "y", "z"] [] [] env "(add x y) z" (App (TMacro "add" [Var "x" 2 (initialPos "test"), Var "y" 1 (initialPos "test")] (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test"))

  it "handles large argument lists for TMacros" $ do
    let env = createTermMacroEnv [("manyArgs", ["a", "b", "c", "d", "e", "f", "g", "h"])]
    testParseTerm ["a", "b", "c", "d", "e", "f", "g", "h"] [] [] env "manyArgs a b c d e f g h" 
      (TMacro "manyArgs" [Var "a" 7 (initialPos "test"), Var "b" 6 (initialPos "test"), Var "c" 5 (initialPos "test"), Var "d" 4 (initialPos "test"), Var "e" 3 (initialPos "test"), Var "f" 2 (initialPos "test"), Var "g" 1 (initialPos "test"), Var "h" 0 (initialPos "test")] (initialPos "test"))

  it "handles TMacro names that are also variable names" $ do
    let env = createTermMacroEnv [("f", ["x"])]
    testParseTerm ["x"] [] [] env "f x" (TMacro "f" [Var "x" 0 (initialPos "test")] (initialPos "test"))
    testParseTerm ["x"] [] [] env "λf. f x" (Lam "f" (App (Var "f" 0 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseTerm ["y"] [] [] env "λg. g (f y)" (Lam "g" (App (Var "g" 0 (initialPos "test")) (TMacro "f" [Var "y" 1 (initialPos "test")] (initialPos "test")) (initialPos "test")) (initialPos "test"))

macroBodyDisambiguationSpec :: Spec
macroBodyDisambiguationSpec = describe "Macro body disambiguation" $ do
  it "parses macro definitions with term bodies" $ do
    testParseDeclaration noMacros "TermMacro x := x ;" (MacroDef "TermMacro" ["x"] (TermMacro (Var "x" 0 (initialPos "test"))))
    testParseDeclaration noMacros "Lambda := λx. x ;" (MacroDef "Lambda" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "AppMacro f x := f x ;" (MacroDef "AppMacro" ["f", "x"] (TermMacro (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))))

  it "parses macro definitions with relational type bodies" $ do
    testParseDeclaration noMacros "Arrow A B := A -> B ;" (MacroDef "Arrow" ["A", "B"] (RelMacro (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "Composition R S := R ∘ S ;" (MacroDef "Composition" ["R", "S"] (RelMacro (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "Universal X := ∀Y. X -> Y ;" (MacroDef "Universal" ["X"] (RelMacro (All "Y" (Arr (RVar "X" 1 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))))

  it "parses parenthesized terms as term macros" $ do
    testParseDeclaration noMacros "ParenId := (λx. x) ;" (MacroDef "ParenId" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "ParenApp f x := (f x) ;" (MacroDef "ParenApp" ["f", "x"] (TermMacro (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))))

  it "tries term parsing first, then falls back to relational" $ do
    testParseDeclaration noMacros "TermFirst x := λy. x y ;" (MacroDef "TermFirst" ["x"] (TermMacro (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "RelSecond R := R -> R ;" (MacroDef "RelSecond" ["R"] (RelMacro (Arr (RVar "R" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test"))))

  it "handles complex macro body disambiguation" $ do
    testParseDeclaration noMacros "LambdaBody := λx. λy. x y ;" (MacroDef "LambdaBody" [] (TermMacro (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "CompBody R S := R ∘ S ;" (MacroDef "CompBody" ["R", "S"] (RelMacro (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "ArrowBody A B := A -> B ;" (MacroDef "ArrowBody" ["A", "B"] (RelMacro (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))))

  it "handles macro body with quantifiers" $ do
    testParseDeclaration noMacros "ForallBody := ∀X. X ;" (MacroDef "ForallBody" [] (RelMacro (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "ForallComp R := ∀X. R ∘ X ;" (MacroDef "ForallComp" ["R"] (RelMacro (All "X" (Comp (RVar "R" 1 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))))

  it "handles macro body with converse operations" $ do
    testParseDeclaration noMacros "ConvBody R := R˘ ;" (MacroDef "ConvBody" ["R"] (RelMacro (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "ConvComp R S := (R ∘ S)˘ ;" (MacroDef "ConvComp" ["R", "S"] (RelMacro (Conv (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))))

  it "handles nested disambiguation in complex expressions" $ do
    testParseDeclaration noMacros "ComplexTerm f g x := (λh. h (f x)) g ;" (MacroDef "ComplexTerm" ["f", "g", "x"] (TermMacro (App (Lam "h" (App (Var "h" 0 (initialPos "test")) (App (Var "f" 3 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "g" 1 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "ComplexRel R S T := ∀X. (R ∘ X) -> (S˘ ∘ T) ;" (MacroDef "ComplexRel" ["R", "S", "T"] (RelMacro (All "X" (Arr (Comp (RVar "R" 3 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (Comp (Conv (RVar "S" 2 (initialPos "test")) (initialPos "test")) (RVar "T" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))))

rtypeParserSpec :: Spec
rtypeParserSpec = describe "RType parser" $ do
  it "parses Unicode and ASCII alternatives consistently" $ do
    testParseRType [] ["A", "B"] [] noMacros "A -> B" (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A", "B"] [] noMacros "A → B" (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A"] [] noMacros "∀x. A" (All "x" (RVar "A" 1 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A"] [] noMacros "forall x. A" (All "x" (RVar "A" 1 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["R"] [] noMacros "R˘" (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["R", "S"] [] noMacros "R ∘ S" (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))

  it "parses relation variables with bound context" $ do
    testParseRType [] ["A"] [] noMacros "A" (RVar "A" 0 (initialPos "test"))
    testParseRType [] ["R"] [] noMacros "R" (RVar "R" 0 (initialPos "test"))

  it "parses arrow types with bound variables" $ do
    testParseRType [] ["A", "B"] [] noMacros "A -> B" (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A", "B"] [] noMacros "A → B" (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A", "B", "C"] [] noMacros "A -> B -> C" (Arr (RVar "A" 2 (initialPos "test")) (Arr (RVar "B" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses universal quantification with mixed bound variables" $ do
    testParseRType [] ["A"] [] noMacros "∀x. A" (All "x" (RVar "A" 1 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A"] [] noMacros "forall x. A" (All "x" (RVar "A" 1 (initialPos "test")) (initialPos "test"))

  it "parses bound variables correctly in quantifier scope" $ do
    testParseRType [] [] [] noMacros "∀x. x" (All "x" (RVar "x" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["S"] [] noMacros "∀R. R ∘ S" (All "R" (Comp (RVar "R" 0 (initialPos "test")) (RVar "S" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses nested quantification with multiple bound variables" $ do
    testParseRType [] [] [] noMacros "∀x. ∀y. x ∘ y" (All "x" (All "y" (Comp (RVar "x" 1 (initialPos "test")) (RVar "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseRType [] [] [] noMacros "∀R. ∀S. R ∘ S˘" (All "R" (All "S" (Comp (RVar "R" 1 (initialPos "test")) (Conv (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses deeply nested quantification" $ do
    testParseRType [] [] [] noMacros "∀A. ∀B. ∀C. A ∘ B ∘ C" (All "A" (All "B" (All "C" (Comp (Comp (RVar "A" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses relation variable shadowing" $ do
    testParseRType [] [] [] noMacros "∀R. ∀R. R" (All "R" (All "R" (RVar "R" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses mixed bound and unbound variables" $ do
    testParseRType [] ["Unbound"] [] noMacros "∀x. x ∘ Unbound" (All "x" (Comp (RVar "x" 0 (initialPos "test")) (RVar "Unbound" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseRType [] ["Unbound"] [] noMacros "∀R. Unbound ∘ R" (All "R" (Comp (RVar "Unbound" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses composition" $ do
    testParseRType [] ["R", "S"] [] noMacros "R ∘ S" (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["R", "S", "T"] [] noMacros "R ∘ S ∘ T" (Comp (Comp (RVar "R" 2 (initialPos "test")) (RVar "S" 1 (initialPos "test")) (initialPos "test")) (RVar "T" 0 (initialPos "test")) (initialPos "test"))

  it "parses converse" $ do
    testParseRType [] ["R"] [] noMacros "R˘" (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["R", "S"] [] noMacros "(R ∘ S)˘" (Conv (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses promotion" $ do
    testParseRType [] [] [] noMacros "(λx. x)" (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "distinguishes between promotion and macro applications" $ do
    testParseRType ["y"] [] [] noMacros "(λx. x y)" (Prom (Lam "x" (App (Var "x" 0 (initialPos "test")) (Var "y" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseRType [] ["SomeType"] [] noMacros "SomeType" (RVar "SomeType" 0 (initialPos "test"))

  it "parses type application" $ do
    let listEnv = extendMacroEnvironment "List" ["A"] (RelMacro (RVar "A" 0 (initialPos "test"))) defaultFixity noMacros
    testParseRType [] ["A"] [] listEnv "List A" (RMacro "List" [RVar "A" 0 (initialPos "test")] (initialPos "test"))
    let pairEnv = extendMacroEnvironment "Pair" ["A", "B"] (RelMacro (RVar "A" 1 (initialPos "test"))) defaultFixity noMacros
    testParseRType [] ["A", "B"] [] pairEnv "Pair A B" (RMacro "Pair" [RVar "A" 1 (initialPos "test"), RVar "B" 0 (initialPos "test")] (initialPos "test"))

  it "respects operator precedence" $ do
    testParseRType [] ["A", "B", "C"] [] noMacros "A -> B ∘ C" (Arr (RVar "A" 2 (initialPos "test")) (Comp (RVar "B" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseRType [] ["R", "S"] [] noMacros "R ∘ S˘" (Comp (RVar "R" 1 (initialPos "test")) (Conv (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "respects complex operator precedence and associativity" $ do
    testParseRType [] ["A", "B", "C"] [] noMacros "A ∘ B˘ ∘ C" (Comp (Comp (RVar "A" 2 (initialPos "test")) (Conv (RVar "B" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A", "B", "C", "D"] [] noMacros "A ∘ B ∘ C ∘ D" (Comp (Comp (Comp (RVar "A" 3 (initialPos "test")) (RVar "B" 2 (initialPos "test")) (initialPos "test")) (RVar "C" 1 (initialPos "test")) (initialPos "test")) (RVar "D" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A", "B", "C", "D"] [] noMacros "A -> B -> C -> D" (Arr (RVar "A" 3 (initialPos "test")) (Arr (RVar "B" 2 (initialPos "test")) (Arr (RVar "C" 1 (initialPos "test")) (RVar "D" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseRType [] ["A", "B", "C", "D"] [] noMacros "A -> B ∘ C˘ -> D" (Arr (RVar "A" 3 (initialPos "test")) (Arr (Comp (RVar "B" 2 (initialPos "test")) (Conv (RVar "C" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (RVar "D" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

proofParserSpec :: Spec
proofParserSpec = describe "Proof parser" $ do
  it "parses Unicode and ASCII alternatives for proofs" $ do
    testParseProof [] ["A"] ["p"] noMacros "λx: A. p" (LamP "x" (RVar "A" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test"))
    testParseProof [] ["A"] ["p"] noMacros "\\x: A. p" (LamP "x" (RVar "A" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "Λα. p" (TyLam "α" (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "TyLam α. p" (TyLam "α" (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["x", "y"] [] [] noMacros "ι⟨x, y⟩" (Iota (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["x", "y"] [] [] noMacros "ι<x, y>" (Iota (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "∪ᵢ p" (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "convIntro p" (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "∪ₑ p" (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "convElim p" (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p", "q"] noMacros "π p - x.y.z.q" (Pi (PVar "p" 1 (initialPos "test")) "x" "y" "z" (PVar "q" 2 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p", "q"] noMacros "pi p - x.y.z.q" (Pi (PVar "p" 1 (initialPos "test")) "x" "y" "z" (PVar "q" 2 (initialPos "test")) (initialPos "test"))
    testParseProof ["t1", "t2"] [] ["p", "q"] noMacros "ρ{x. t1, t2} p - q" (RhoElim "x" (Var "t1" 2 (initialPos "test")) (Var "t2" 1 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["t1", "t2"] [] ["p", "q"] noMacros "rho{x. t1, t2} p - q" (RhoElim "x" (Var "t1" 2 (initialPos "test")) (Var "t2" 1 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))

  it "parses proof variables and constants" $ do
    testParseProof [] [] ["p"] noMacros "p" (PVar "p" 0 (initialPos "test"))
    testParseProof [] [] ["axiom"] noMacros "axiom" (PVar "axiom" 0 (initialPos "test"))

  it "parses proof lambda abstractions" $ do
    testParseProof [] ["A"] ["p"] noMacros "λx: A. p" (LamP "x" (RVar "A" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test"))
    testParseProof [] ["A", "B"] ["p"] noMacros "\\x: A -> B. p" (LamP "x" (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test"))

  it "parses type lambda abstractions" $ do
    testParseProof [] [] ["p"] noMacros "Λα. p" (TyLam "α" (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "TyLam α. p" (TyLam "α" (PVar "p" 0 (initialPos "test")) (initialPos "test"))

  it "parses type applications" $ do
    testParseProof [] ["A"] ["p"] noMacros "p{A}" (TyApp (PVar "p" 0 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] ["B"] ["q"] noMacros "(Λα. q){B}" (TyApp (TyLam "α" (PVar "q" 0 (initialPos "test")) (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))

  it "parses proof applications" $ do
    testParseProof [] [] ["p", "q"] noMacros "p q" (AppP (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p", "q", "r"] noMacros "p q r" (AppP (AppP (PVar "p" 2 (initialPos "test")) (PVar "q" 1 (initialPos "test")) (initialPos "test")) (PVar "r" 0 (initialPos "test")) (initialPos "test"))

  it "parses iota (term promotion introduction)" $ do
    testParseProof ["x", "y"] [] [] noMacros "ι⟨x, y⟩" (Iota (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["x", "y"] [] [] noMacros "ι<x, y>" (Iota (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test"))

  it "parses conversion proofs" $ do
    testParseProof ["t", "u"] [] ["p"] noMacros "t ⇃ p ⇂ u" (ConvProof (Var "t" 1 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["f", "a"] [] ["p"] noMacros "((λz.z) (f a)) ⇃ p ⇂ (f ((λw.w) a))" (ConvProof (App (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (PVar "p" 0 (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (App (Lam "w" (Var "w" 0 (initialPos "test")) (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseProof ["x", "y"] [] ["q"] noMacros "((λa.a) x) ⇃ q ⇂ ((λb.b) y)" (ConvProof (App (Lam "a" (Var "a" 0 (initialPos "test")) (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (PVar "q" 0 (initialPos "test")) (App (Lam "b" (Var "b" 0 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseProof ["f", "g", "a"] [] ["r"] noMacros "((λx.f (g x)) a) ⇃ r ⇂ (f (g a))" (ConvProof (App (Lam "x" (App (Var "f" 3 (initialPos "test")) (App (Var "g" 2 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")) (PVar "r" 0 (initialPos "test")) (App (Var "f" 2 (initialPos "test")) (App (Var "g" 1 (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses rho elimination" $ do
    testParseProof ["t1", "t2"] [] ["p", "q"] noMacros "ρ{x. t1, t2} p - q" (RhoElim "x" (Var "t1" 2 (initialPos "test")) (Var "t2" 1 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["u", "v"] [] ["r", "s"] noMacros "rho{y. u, v} r - s" (RhoElim "y" (Var "u" 2 (initialPos "test")) (Var "v" 1 (initialPos "test")) (PVar "r" 1 (initialPos "test")) (PVar "s" 0 (initialPos "test")) (initialPos "test"))

  it "parses rho elimination with bound variable usage" $ do
    testParseProof ["a"] [] ["p", "q"] noMacros "ρ{x. x, a} p - q" (RhoElim "x" (Var "x" 0 (initialPos "test")) (Var "a" 1 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["b"] [] ["r", "s"] noMacros "rho{y. y, b} r - s" (RhoElim "y" (Var "y" 0 (initialPos "test")) (Var "b" 1 (initialPos "test")) (PVar "r" 1 (initialPos "test")) (PVar "s" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p", "q"] noMacros "ρ{z. z, z} p - q" (RhoElim "z" (Var "z" 0 (initialPos "test")) (Var "z" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof ["f"] [] ["p", "q"] noMacros "ρ{x. f x, x} p - q" (RhoElim "x" (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))

  it "parses pi elimination" $ do
    testParseProof [] [] ["p", "q"] noMacros "π p - x.y.z.q" (Pi (PVar "p" 1 (initialPos "test")) "x" "y" "z" (PVar "q" 2 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["r", "s"] noMacros "pi r - a.b.c.s" (Pi (PVar "r" 1 (initialPos "test")) "a" "b" "c" (PVar "s" 2 (initialPos "test")) (initialPos "test"))

  it "parses pi elimination with bound variables used in proof" $ do
    testParseProof [] [] ["p"] noMacros "π p - x.u.v.(u,v)" (Pi (PVar "p" 0 (initialPos "test")) "x" "u" "v" (Pair (PVar "u" 1 (initialPos "test")) (PVar "v" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses converse operations" $ do
    testParseProof [] [] ["p"] noMacros "∪ᵢ p" (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "convIntro p" (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "∪ₑ p" (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "convElim p" (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test"))

  it "parses pairs" $ do
    testParseProof [] [] ["p", "q"] noMacros "(p, q)" (Pair (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] [] ["p", "q", "r"] noMacros "(p, (q, r))" (Pair (PVar "p" 2 (initialPos "test")) (Pair (PVar "q" 1 (initialPos "test")) (PVar "r" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses complex proof lambda abstractions with nested types" $ do
    testParseProof [] [] ["p"] noMacros "λx: ∀A. A -> A. p" (LamP "x" (All "A" (Arr (RVar "A" 0 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (PVar "p" 1 (initialPos "test")) (initialPos "test"))
    testParseProof [] ["A", "B"] ["q"] noMacros "λy: A ∘ B˘. q" (LamP "y" (Comp (RVar "A" 1 (initialPos "test")) (Conv (RVar "B" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (PVar "q" 1 (initialPos "test")) (initialPos "test"))

  it "parses nested type and proof lambda abstractions" $ do
    testParseProof [] [] ["q"] noMacros "Λα. λp: α. Λβ. q" (TyLam "α" (LamP "p" (RVar "α" 0 (initialPos "test")) (TyLam "β" (PVar "q" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses complex type applications with nested structures" $ do
    testParseProof [] [] ["p"] noMacros "p{∀A. A -> A}" (TyApp (PVar "p" 0 (initialPos "test")) (All "A" (Arr (RVar "A" 0 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseProof [] ["A", "B", "C"] ["p"] noMacros "(p{A}){B ∘ C}" (TyApp (TyApp (PVar "p" 0 (initialPos "test")) (RVar "A" 2 (initialPos "test")) (initialPos "test")) (Comp (RVar "B" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

declarationParserSpec :: Spec
declarationParserSpec = describe "Declaration parser" $ do
  it "parses Unicode and ASCII alternatives for declarations" $ do
    testParseDeclaration noMacros "Id ≔ (λx. x) ;" (MacroDef "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "Id := (λx. x) ;" (MacroDef "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "⊢ test (t : Term) (u : Term) (A : Rel) (p : t [A] u) : t [A] u ≔ p ;" 
      (TheoremDef "test" [TermBinding "t", TermBinding "u", RelBinding "A", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))] 
        (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test"))) 
        (PVar "p" 0 (initialPos "test")))
    testParseDeclaration noMacros "theorem test (t : Term) (u : Term) (A : Rel) (p : t [A] u) : t [A] u := p ;" 
      (TheoremDef "test" [TermBinding "t", TermBinding "u", RelBinding "A", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))] 
        (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test"))) 
        (PVar "p" 0 (initialPos "test")))

  it "parses macro definitions" $ do
    testParseDeclaration noMacros "Id ≔ (λx. x) ;" (MacroDef "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "Comp R S ≔ R ∘ S ;" (MacroDef "Comp" ["R", "S"] (RelMacro (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "Id := (λx. x) ;" (MacroDef "Id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))))
    testParseDeclaration noMacros "BoolEq := ∀X. X → X → X ;" (MacroDef "BoolEq" [] (RelMacro (All "X" (Arr (RVar "X" 0 (initialPos "test")) (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))))

  it "parses theorem definitions" $ do
    let idMacroEnv = extendMacroEnvironment "Id" [] (RelMacro (RVar "dummy" 0 (initialPos "test"))) defaultFixity noMacros
    testParseDeclaration idMacroEnv "⊢ refl (t : Term) : t [Id] t ≔ ι⟨t, t⟩ ;" 
      (TheoremDef "refl" [TermBinding "t"] 
        (RelJudgment (Var "t" 0 (initialPos "test")) (RMacro "Id" [] (initialPos "test")) (Var "t" 0 (initialPos "test"))) 
        (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test")))
    
    let symMacroEnv = extendMacroEnvironment "Sym" ["R"] (RelMacro (RVar "dummy" 0 (initialPos "test"))) defaultFixity noMacros
    testParseDeclaration symMacroEnv "theorem sym (t : Term) (u : Term) (R : Rel) (p : t [R] u) : u [Sym R] t := ∪ᵢ p ;" 
      (TheoremDef "sym" [TermBinding "t", TermBinding "u", RelBinding "R", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))] 
        (RelJudgment (Var "u" 0 (initialPos "test")) (RMacro "Sym" [RVar "R" 0 (initialPos "test")] (initialPos "test")) (Var "t" 1 (initialPos "test"))) 
        (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")))
    
    testParseDeclaration noMacros "⊢ id_test : (λx. x) [(λx. x)] (λx. x) := ι⟨λx. x, λx. x⟩ ;" 
      (TheoremDef "id_test" [] 
        (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))) 
        (Iota (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")))

  it "parses relational judgments with complex terms" $ do
    let idMacroEnv2 = extendMacroEnvironment "Id" [] (RelMacro (RVar "dummy" 0 (initialPos "test"))) defaultFixity noMacros
    testParseDeclaration idMacroEnv2 "⊢ beta : (λx. x) [Id] (λy. y) ≔ ι⟨λx. x, λy. y⟩ ;" 
      (TheoremDef "beta" [] 
        (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (RMacro "Id" [] (initialPos "test")) (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test"))) 
        (Iota (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")))
    
    testParseDeclaration noMacros "⊢ app (f : Term) (x : Term) (R : Rel) (p : (f x) [R] (f x)) : (f x) [R] (f x) ≔ p ;" 
      (TheoremDef "app" [TermBinding "f", TermBinding "x", RelBinding "R", ProofBinding "p" (RelJudgment (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (RVar "R" 0 (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")))] 
        (RelJudgment (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (RVar "R" 0 (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))) 
        (PVar "p" 0 (initialPos "test")))

  it "parses relation bindings" $ do
    testParseDeclaration noMacros "⊢ test (t : Term) (u : Term) (A : Rel) (p : t [A] u) : t [A] u ≔ p ;" 
      (TheoremDef "test" [TermBinding "t", TermBinding "u", RelBinding "A", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))] 
        (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (Var "u" 0 (initialPos "test"))) 
        (PVar "p" 0 (initialPos "test")))

  it "parses files with multiple declarations" $ do
    let input = unlines ["Id ≔ (λx. x) ;", "Sym R ≔ R˘ ;", "⊢ refl (t : Term) : t [Id] t ≔ ι⟨t, t⟩ ;"]
    case runParser (Raw.parseFile <* eof) "test" input of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawDecls -> do
            -- Elaborate each declaration individually (simplified for tests)
            let expected = 3 :: Int
            length rawDecls `shouldBe` expected

  it "correctly distinguishes macros vs variables based on context" $ do
    let env = createTermMacroEnv [("f", [])]
    testParseTerm ["f"] [] [] noMacros "f" (Var "f" 0 (initialPos "test"))
    testParseTerm [] [] [] env "f" (TMacro "f" [] (initialPos "test"))

  it "parses fixity declarations" $ do
    testParseDeclaration noMacros "infixl 6 _+_ ;" (FixityDecl (Infixl 6) "_+_")
    testParseDeclaration noMacros "infixr 7 _*_ ;" (FixityDecl (Infixr 7) "_*_")
    testParseDeclaration noMacros "prefix 9 not_ ;" (FixityDecl (Prefix 9) "not_")

declarationComplexCasesSpec :: Spec
declarationComplexCasesSpec = describe "Declaration complex cases" $ do
  it "parses theorems with many bindings of different types" $ do
    let input = "⊢ complex (t : Term) (u : Term) (v : Term) (A : Rel) (B : Rel) (x : Term) (y : Term) (p : t [A] u) (q : u [B] v) (transProof : t [A ∘ B] v) : t [A ∘ B] v ≔ transProof ;"
    testParseDeclaration noMacros input
      (TheoremDef "complex" 
        [TermBinding "t", TermBinding "u", TermBinding "v", RelBinding "A", RelBinding "B", TermBinding "x", TermBinding "y",
         ProofBinding "p" (RelJudgment (Var "t" 4 (initialPos "test")) (RVar "A" 1 (initialPos "test")) (Var "u" 3 (initialPos "test"))),
         ProofBinding "q" (RelJudgment (Var "u" 3 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (Var "v" 2 (initialPos "test"))),
         ProofBinding "transProof" (RelJudgment (Var "t" 4 (initialPos "test")) (Comp (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")) (Var "v" 2 (initialPos "test")))]
        (RelJudgment (Var "t" 4 (initialPos "test")) (Comp (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")) (Var "v" 2 (initialPos "test")))
        (PVar "transProof" 0 (initialPos "test")))

  it "parses macro definitions with deeply nested bodies" $ do
    let input = "NestedComp R S T U ≔ ((R ∘ S) ∘ (T˘ ∘ U))˘ ;"
    testParseDeclaration noMacros input
      (MacroDef "NestedComp" ["R", "S", "T", "U"]
        (RelMacro (Conv (Comp (Comp (RVar "R" 3 (initialPos "test")) (RVar "S" 2 (initialPos "test")) (initialPos "test"))
                              (Comp (Conv (RVar "T" 1 (initialPos "test")) (initialPos "test")) (RVar "U" 0 (initialPos "test")) (initialPos "test"))
                              (initialPos "test")) (initialPos "test"))))

  it "parses theorems with complex relational judgments" $ do
    let input = "⊢ complexRel (R : Rel) (S : Rel) (complexProof : (λx. x) [(∀X. R ∘ X ∘ S)] (λy. y)) : (λx. x) [(∀X. R ∘ X ∘ S)] (λy. y) ≔ complexProof ;"
    testParseDeclaration noMacros input
      (TheoremDef "complexRel" 
        [RelBinding "R", RelBinding "S",
         ProofBinding "complexProof" (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
                                                  (All "X" (Comp (Comp (RVar "R" 2 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (RVar "S" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
                                                  (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")))]
        (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
                     (All "X" (Comp (Comp (RVar "R" 2 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (RVar "S" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
                     (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")))
        (PVar "complexProof" 0 (initialPos "test")))

  it "parses macro definitions with promoted lambda terms" $ do
    let input = "LambdaMacro A B ≔ (λx. λy. x y) ;"
    testParseDeclaration noMacros input
      (MacroDef "LambdaMacro" ["A", "B"] (TermMacro (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))))

  it "parses files with multiple complex declarations" $ do
    let input = unlines 
          ["DoubleComp R S ≔ R ∘ R ∘ S ;",
           "TripleRel A B C ≔ A ∘ (B˘ ∘ C) ;",
           "⊢ composition (t : Term) (u : Term) (v : Term) (w : Term) (X : Rel) (Y : Rel) (Z : Rel) (p : t [X] u) (q : u [Y] v) (r : v [Z] w) (tripleComp : t [X ∘ Y ∘ Z] w) : t [X ∘ Y ∘ Z] w ≔ tripleComp ;",
           "Identity ≔ (λx. x) ;",
           "⊢ identity (t : Term) : t [Identity] t ≔ ι⟨t, t⟩ ;"]
    case runParser (Raw.parseFile <* eof) "test" input of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawDecls -> do
            let expected = 5 :: Int
            length rawDecls `shouldBe` expected

  it "parses theorems with nested quantified types in bindings" $ do
    let input = "⊢ nestedQuant (A : Rel) (B : Rel) (p : (λx. x) [∀Y. A ∘ Y ∘ B] (λz. z)) : (λx. x) [∀Y. A ∘ Y ∘ B] (λz. z) ≔ p ;"
    testParseDeclaration noMacros input
      (TheoremDef "nestedQuant" 
        [RelBinding "A", RelBinding "B",
         ProofBinding "p" (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
                                      (All "Y" (Comp (Comp (RVar "A" 2 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
                                      (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")))]
        (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
                     (All "Y" (Comp (Comp (RVar "A" 2 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
                     (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")))
        (PVar "p" 0 (initialPos "test")))

  it "parses macro definitions with variable shadowing" $ do
    let input = "ShadowMacro x y ≔ λx. λy. x y ;"
    testParseDeclaration noMacros input
      (MacroDef "ShadowMacro" ["x", "y"] (TermMacro (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))))

  it "parses theorems with complex proof terms" $ do
    let input = "⊢ complexProof (f : Term) (g : Term) (x : Term) : (λh. h (f x)) [(λh. h (g x))] (λh. h (f x)) ≔ ι⟨λh. h (f x), λh. h (f x)⟩ ;"
    testParseDeclaration noMacros input
      (TheoremDef "complexProof" [TermBinding "f", TermBinding "g", TermBinding "x"]
        (RelJudgment (Lam "h" (App (Var "h" 0 (initialPos "test")) (App (Var "f" 3 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
                     (Prom (Lam "h" (App (Var "h" 0 (initialPos "test")) (App (Var "g" 2 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
                     (Lam "h" (App (Var "h" 0 (initialPos "test")) (App (Var "f" 3 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")))
        (Iota (Lam "h" (App (Var "h" 0 (initialPos "test")) (App (Var "f" 2 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
              (Lam "h" (App (Var "h" 0 (initialPos "test")) (App (Var "f" 2 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")))

  it "parses macro applications within macro definitions" $ do
    let compEnv = extendMacroEnvironment "Comp" ["A", "B"] (RelMacro (Comp (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))) defaultFixity noMacros
    let input = "CompChain R S T ≔ Comp (Comp R S) T ;"
    testParseDeclaration compEnv input
      (MacroDef "CompChain" ["R", "S", "T"] (RelMacro (RMacro "Comp" [RMacro "Comp" [RVar "R" 2 (initialPos "test"), RVar "S" 1 (initialPos "test")] (initialPos "test"), RVar "T" 0 (initialPos "test")] (initialPos "test"))))

  it "parses extremely long macro parameter lists" $ do
    let input = "ManyParams a b c d e f g h i j k l m n o ≔ a ;"
    testParseDeclaration noMacros input
      (MacroDef "ManyParams" ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o"] (TermMacro (Var "a" 14 (initialPos "test"))))

  it "parses theorems with deeply nested binding contexts" $ do
    let input = "⊢ deepNesting (w : Term) (x : Term) (y : Term) (z : Term) (A : Rel) (B : Rel) (C : Rel) (D : Rel) (E : Rel) (p1 : w [A] x) (p2 : x [B] y) (p3 : y [C] z) (p4 : z [D] w) (p5 : w [E] z) (deepProof : w [A ∘ B ∘ C ∘ D ∘ E] z) : w [A ∘ B ∘ C ∘ D ∘ E] z ≔ deepProof ;"
    testParseDeclaration noMacros input
      (TheoremDef "deepNesting" 
        [TermBinding "w", TermBinding "x", TermBinding "y", TermBinding "z", RelBinding "A", RelBinding "B", RelBinding "C", RelBinding "D", RelBinding "E",
         ProofBinding "p1" (RelJudgment (Var "w" 3 (initialPos "test")) (RVar "A" 4 (initialPos "test")) (Var "x" 2 (initialPos "test"))),
         ProofBinding "p2" (RelJudgment (Var "x" 2 (initialPos "test")) (RVar "B" 3 (initialPos "test")) (Var "y" 1 (initialPos "test"))),
         ProofBinding "p3" (RelJudgment (Var "y" 1 (initialPos "test")) (RVar "C" 2 (initialPos "test")) (Var "z" 0 (initialPos "test"))),
         ProofBinding "p4" (RelJudgment (Var "z" 0 (initialPos "test")) (RVar "D" 1 (initialPos "test")) (Var "w" 3 (initialPos "test"))),
         ProofBinding "p5" (RelJudgment (Var "w" 3 (initialPos "test")) (RVar "E" 0 (initialPos "test")) (Var "z" 0 (initialPos "test"))),
         ProofBinding "deepProof" (RelJudgment (Var "w" 3 (initialPos "test")) 
           (Comp (Comp (Comp (Comp (RVar "A" 4 (initialPos "test")) (RVar "B" 3 (initialPos "test")) (initialPos "test")) (RVar "C" 2 (initialPos "test")) (initialPos "test")) (RVar "D" 1 (initialPos "test")) (initialPos "test")) (RVar "E" 0 (initialPos "test")) (initialPos "test"))
           (Var "z" 0 (initialPos "test")))]
        (RelJudgment (Var "w" 3 (initialPos "test")) 
          (Comp (Comp (Comp (Comp (RVar "A" 4 (initialPos "test")) (RVar "B" 3 (initialPos "test")) (initialPos "test")) (RVar "C" 2 (initialPos "test")) (initialPos "test")) (RVar "D" 1 (initialPos "test")) (initialPos "test")) (RVar "E" 0 (initialPos "test")) (initialPos "test"))
          (Var "z" 0 (initialPos "test")))
        (PVar "deepProof" 0 (initialPos "test")))

  it "handles mixed Unicode and ASCII in complex declarations" $ do
    let input = "⊢ mixed (R : Rel) (S : Rel) (p : (λx. x) [R ∘ S˘] (λy. y)) : (λx. x) [R → S] (λy. y) ≔ p ;"
    testParseDeclaration noMacros input
      (TheoremDef "mixed" 
        [RelBinding "R", RelBinding "S",
         ProofBinding "p" (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
                                      (Comp (RVar "R" 1 (initialPos "test")) (Conv (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
                                      (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")))]
        (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
                     (Arr (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))
                     (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")))
        (PVar "p" 0 (initialPos "test")))

theoremReferencingSpec :: Spec
theoremReferencingSpec = describe "Theorem referencing" $ do
  it "parses proof variables as theorem references" $ do
    testParseProof [] [] ["identity", "p"] noMacros "identity p" 
      (AppP (PVar "identity" 1 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (initialPos "test"))

  it "parses complex proof applications" $ do
    testParseProof [] [] ["use_proof", "p", "identity", "q"] noMacros "use_proof p (identity q)" 
      (AppP (AppP (PVar "use_proof" 3 (initialPos "test")) (PVar "p" 2 (initialPos "test")) (initialPos "test")) 
           (AppP (PVar "identity" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "parses theorem applications with type arguments" $ do
    testParseProof [] ["R"] ["thm"] noMacros "thm {R}" 
      (TyApp (PVar "thm" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test"))

deBruijnEdgeCasesSpec :: Spec
deBruijnEdgeCasesSpec = describe "De Bruijn edge cases" $ do
  it "handles deep nesting with correct index calculation" $ do
    testParseTerm [] [] [] noMacros "λx. λy. λz. λw. λv. x" 
      (Lam "x" (Lam "y" (Lam "z" (Lam "w" (Lam "v" (Var "x" 4 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles complex variable shadowing patterns" $ do
    testParseTerm [] [] [] noMacros "λx. λy. λx. λy. x y" 
      (Lam "x" (Lam "y" (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles variable references across multiple shadow levels" $ do
    testParseTerm [] [] [] noMacros "λx. λy. λx. λz. λx. λy. x y z" 
      (Lam "x" (Lam "y" (Lam "x" (Lam "z" (Lam "x" (Lam "y" 
        (App (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (Var "z" 2 (initialPos "test")) (initialPos "test"))
        (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles boundary conditions with index 0" $ do
    testParseTerm [] [] [] noMacros "λx. x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseRType [] [] [] noMacros "∀x. x" (All "x" (RVar "x" 0 (initialPos "test")) (initialPos "test"))
    testParseProof [] ["A"] [] noMacros "λx: A. x" (LamP "x" (RVar "A" 0 (initialPos "test")) (PVar "x" 0 (initialPos "test")) (initialPos "test"))

  it "handles free variables with correct indices" $ do
    testParseTerm ["x"] [] [] noMacros "x" (Var "x" 0 (initialPos "test"))
    testParseRType [] ["R"] [] noMacros "R" (RVar "R" 0 (initialPos "test"))
    testParseProof [] [] ["p"] noMacros "p" (PVar "p" 0 (initialPos "test"))

  it "handles mixed free and bound variables" $ do
    testParseTerm ["free"] [] [] noMacros "λx. x free" 
      (Lam "x" (App (Var "x" 0 (initialPos "test")) (Var "free" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles quantifier nesting with correct indices" $ do
    testParseRType [] [] [] noMacros "∀A. ∀B. ∀C. A ∘ B ∘ C" 
      (All "A" (All "B" (All "C" (Comp (Comp (RVar "A" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles extreme nesting depth" $ do
    let buildNestedLambda 0 = Var "x20" 19 (initialPos "test")
        buildNestedLambda n = Lam ("x" ++ show n) (buildNestedLambda (n - 1)) (initialPos "test")
        expected = buildNestedLambda 20
        buildInput 0 = "x20"
        buildInput n = "λx" ++ show n ++ ". " ++ buildInput (n - 1)
        input = buildInput 20
    testParseTerm [] [] [] noMacros input expected

  it "handles complex proof binding contexts" $ do
    let input = "⊢ multiBinding (x : Term) (y : Term) (z : Term) (R : Rel) (S : Rel) (p1 : x [R] y) (p2 : y [S] z) (p3 : x [R ∘ S] z) : x [R] z ≔ p1 ;"
    testParseDeclaration noMacros input
      (TheoremDef "multiBinding" 
        [TermBinding "x", TermBinding "y", TermBinding "z", RelBinding "R", RelBinding "S",
         ProofBinding "p1" (RelJudgment (Var "x" 2 (initialPos "test")) (RVar "R" 1 (initialPos "test")) (Var "y" 1 (initialPos "test"))),
         ProofBinding "p2" (RelJudgment (Var "y" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (Var "z" 0 (initialPos "test"))),
         ProofBinding "p3" (RelJudgment (Var "x" 2 (initialPos "test")) (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) (Var "z" 0 (initialPos "test")))]
        (RelJudgment (Var "x" 2 (initialPos "test")) (RVar "R" 1 (initialPos "test")) (Var "z" 0 (initialPos "test")))
        (PVar "p1" 2 (initialPos "test")))

  it "handles variable capture avoidance in complex terms" $ do
    testParseTerm [] [] [] noMacros "λx. λy. (λx. x) y" 
      (Lam "x" (Lam "y" (App (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles index shifting in application contexts" $ do
    testParseTerm ["f", "g"] [] [] noMacros "λx. f (λy. g x y)" 
      (Lam "x" (App (Var "f" 2 (initialPos "test")) (Lam "y" (App (App (Var "g" 2 (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles binding in different syntactic contexts" $ do
    testParseProof [] [] [] noMacros "λx: ∀A. A -> A. Λα. λy: α. x{α} y" 
      (LamP "x" (All "A" (Arr (RVar "A" 0 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
        (TyLam "α" (LamP "y" (RVar "α" 0 (initialPos "test")) 
          (AppP (TyApp (PVar "x" 1 (initialPos "test")) (RVar "α" 0 (initialPos "test")) (initialPos "test")) (PVar "y" 0 (initialPos "test")) (initialPos "test"))
          (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles index boundary stress test" $ do
    testParseTerm [] [] [] noMacros "λa. λb. λc. λd. λe. a e (b d (c e))" 
      (Lam "a" (Lam "b" (Lam "c" (Lam "d" (Lam "e" 
        (App (App (Var "a" 4 (initialPos "test")) (Var "e" 0 (initialPos "test")) (initialPos "test"))
             (App (App (Var "b" 3 (initialPos "test")) (Var "d" 1 (initialPos "test")) (initialPos "test"))
                  (App (Var "c" 2 (initialPos "test")) (Var "e" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
        (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))

  it "handles interleaved binding types in complex declarations" $ do
    let input = "⊢ interleaved (t1 : Term) (R1 : Rel) (t2 : Term) (R2 : Rel) (t3 : Term) (p : t1 [R1 ∘ R2] t3) : t2 [R2] t3 ≔ p ;"
    testParseDeclaration noMacros input
      (TheoremDef "interleaved" 
        [TermBinding "t1", RelBinding "R1", TermBinding "t2", RelBinding "R2", TermBinding "t3",
         ProofBinding "p" (RelJudgment (Var "t1" 2 (initialPos "test")) (Comp (RVar "R1" 1 (initialPos "test")) (RVar "R2" 0 (initialPos "test")) (initialPos "test")) (Var "t3" 0 (initialPos "test")))]
        (RelJudgment (Var "t2" 1 (initialPos "test")) (RVar "R2" 0 (initialPos "test")) (Var "t3" 0 (initialPos "test")))
        (PVar "p" 0 (initialPos "test")))

  it "handles edge case of zero bindings" $ do
    testParseDeclaration noMacros "⊢ noBind : (λx. x) [(λx. x)] (λx. x) := ι⟨λx. x, λx. x⟩ ;" 
      (TheoremDef "noBind" [] 
        (RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))) 
        (Iota (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")))

  it "handles maximum complexity binding scenario" $ do
    let input = "⊢ maxComplex (x : Term) (y : Term) (z : Term) (w : Term) (A : Rel) (B : Rel) (C : Rel) (p1 : (λa. x a) [A] (λb. y b)) (p2 : (λc. y c) [B] (λd. z d)) (p3 : (λe. z e) [C] (λf. w f)) (bigProof : (λg. x g) [A ∘ B ∘ C] (λh. w h)) : (λi. x i) [A ∘ B ∘ C] (λj. w j) ≔ bigProof ;"
    testParseDeclaration noMacros input
      (TheoremDef "maxComplex" 
        [TermBinding "x", TermBinding "y", TermBinding "z", TermBinding "w", RelBinding "A", RelBinding "B", RelBinding "C",
         ProofBinding "p1" (RelJudgment (Lam "a" (App (Var "x" 4 (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) 
                                       (RVar "A" 2 (initialPos "test"))
                                       (Lam "b" (App (Var "y" 4 (initialPos "test")) (Var "b" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))),
         ProofBinding "p2" (RelJudgment (Lam "c" (App (Var "y" 4 (initialPos "test")) (Var "c" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
                                       (RVar "B" 1 (initialPos "test"))
                                       (Lam "d" (App (Var "z" 3 (initialPos "test")) (Var "d" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))),
         ProofBinding "p3" (RelJudgment (Lam "e" (App (Var "z" 3 (initialPos "test")) (Var "e" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
                                       (RVar "C" 0 (initialPos "test"))
                                       (Lam "f" (App (Var "w" 3 (initialPos "test")) (Var "f" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))),
         ProofBinding "bigProof" (RelJudgment (Lam "g" (App (Var "x" 4 (initialPos "test")) (Var "g" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
                                             (Comp (Comp (RVar "A" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test"))
                                             (Lam "h" (App (Var "w" 3 (initialPos "test")) (Var "h" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")))]
        (RelJudgment (Lam "i" (App (Var "x" 4 (initialPos "test")) (Var "i" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
                     (Comp (Comp (RVar "A" 2 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test"))
                     (Lam "j" (App (Var "w" 3 (initialPos "test")) (Var "j" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")))
        (PVar "bigProof" 0 (initialPos "test")))

parserErrorSpec :: Spec
parserErrorSpec = describe "Parser error handling" $ do
  it "handles empty input gracefully" $ do
    testParseFailure ""
    case runParser (Raw.parseRType <* eof) "test" "" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for empty RType"
    case runParser (Raw.parseProof <* eof) "test" "" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for empty Proof"
    case runParser (Raw.parseDeclaration <* eof) "test" "" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for empty Declaration"

  it "handles malformed operators" $ do
    case runParser (Raw.parseRType <* eof) "test" "∘" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for lone ∘"
    case runParser (Raw.parseRType <* eof) "test" "->" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for lone ->"
    case runParser (Raw.parseRType <* eof) "test" "˘" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for lone ˘"

  it "handles incomplete constructs" $ do
    case runParser (Raw.parseRType <* eof) "test" "∀" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for incomplete ∀"
    case runParser (Raw.parseTerm <* eof) "test" "λ" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for incomplete λ"
    case runParser (Raw.parseProof <* eof) "test" "p{" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for incomplete type app"

  it "handles mismatched delimiters" $ do
    testParseFailure "("
    testParseFailure ")"
    case runParser (Raw.parseRType <* eof) "test" "⟨" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for unmatched ⟨"
    case runParser (Raw.parseProof <* eof) "test" "⟨x" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for incomplete ⟨x"

  it "handles invalid characters" $ do
    testParseFailure "#@$"
    case runParser (Raw.parseRType <* eof) "test" "#@$" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for invalid RType characters"
    case runParser (Raw.parseProof <* eof) "test" "#@$" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for invalid Proof characters"

  it "handles malformed lambda expressions" $ do
    testParseFailure "λ. x"
    testParseFailure "λx x"
    testParseFailure "λx."
    testParseFailure "λx. λ. y"

  it "handles malformed quantifiers" $ do
    case runParser (Raw.parseRType <* eof) "test" "∀. A" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for ∀. A"
    case runParser (Raw.parseRType <* eof) "test" "∀x A" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for ∀x A"
    case runParser (Raw.parseRType <* eof) "test" "∀x." of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for ∀x."
    case runParser (Raw.parseRType <* eof) "test" "∀∀x. A" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for ∀∀x. A"

  it "handles malformed proof terms" $ do
    case runParser (Raw.parseProof <* eof) "test" "ι{x" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for ι{x"
    case runParser (Raw.parseProof <* eof) "test" "ι{x,y" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for ι{x,y"
    case runParser (Raw.parseProof <* eof) "test" "ι{,y}" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for ι{,y}"
    case runParser (Raw.parseProof <* eof) "test" "x ⇃ p" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for incomplete conversion"
    case runParser (Raw.parseProof <* eof) "test" "ρ{x.t,t} p" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for incomplete rho"

  it "handles malformed type applications" $ do
    case runParser (Raw.parseProof <* eof) "test" "p{" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for p{"
    case runParser (Raw.parseProof <* eof) "test" "p{}" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for p{}"
    case runParser (Raw.parseProof <* eof) "test" "{R}" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for {R}"

  it "handles malformed macro definitions" $ do
    case runParser (Raw.parseDeclaration <* eof) "test" "Id" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for incomplete macro"
    case runParser (Raw.parseDeclaration <* eof) "test" "Id ≔" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for macro without body"
    case runParser (Raw.parseDeclaration <* eof) "test" "Id [] ≔ R" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for invalid parameter syntax"

  it "handles malformed theorem definitions" $ do
    case runParser (Raw.parseDeclaration <* eof) "test" "thm :" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for incomplete theorem"
    case runParser (Raw.parseDeclaration <* eof) "test" "thm : t[R]u :=" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for theorem without proof"
    case runParser (Raw.parseDeclaration <* eof) "test" "thm (x y) : t[R]u := p" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for invalid binding syntax"

  it "handles nested parsing errors in complex expressions" $ do
    testParseFailure "λx. λy. λ. z"
    case runParser (Raw.parseRType <* eof) "test" "∀X. ∀Y. ∀. Z" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for nested ∀ error"
    case runParser (Raw.parseProof <* eof) "test" "λu:R. λv:S. ι{x" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for nested proof error"

  it "handles operator precedence errors" $ do
    case runParser (Raw.parseRType <* eof) "test" "R ∘ ∘ S" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for R ∘ ∘ S"
    case runParser (Raw.parseRType <* eof) "test" "A → → B" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for A → → B"
    case runParser (Raw.parseRType <* eof) "test" "^" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for lone ^"

  it "handles Unicode vs ASCII inconsistencies" $ do
    case runParser (Raw.parseRType <* eof) "test" "∀x -> A" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for mixed Unicode/ASCII"
    case runParser (Raw.parseProof <* eof) "test" "∪i p" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for ∪i p"
    case runParser (Raw.parseRType <* eof) "test" "R ∘˘ S" of
      Left _ -> return ()
      Right _ -> expectationFailure "Expected parse failure for invalid operator combination"

  it "validates successful mixed Unicode/ASCII parsing" $ do
    testParseRType [] ["A", "B", "C"] [] noMacros "A → B -> C" (Arr (RVar "A" 2 (initialPos "test")) (Arr (RVar "B" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] noMacros "λx. x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
    testParseTerm [] [] [] noMacros "\\x. x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))