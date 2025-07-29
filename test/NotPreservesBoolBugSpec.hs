{-# LANGUAGE OverloadedStrings #-}

module NotPreservesBoolBugSpec (spec) where

import Core.Context
import Core.Syntax
import Core.Context (emptyContext, extendMacroContext)
import Operations.Generic.Expansion (expandFully)
import Parser.Mixfix (defaultFixity)
import TypeCheck.Proof
import Test.Hspec
import TestHelpers (buildContextFromDeclarations, buildContextFromBindings, simpleParamInfo, parseFileDeclarations)
import Text.Megaparsec (initialPos)

spec :: Spec
spec = do
  parseAndRunBoolRttContentSpec
  extractAndTestJudgmentComparisonSpec

-- Approach 1: Parse and run the actual bool.rtt content directly
parseAndRunBoolRttContentSpec :: Spec
parseAndRunBoolRttContentSpec = describe "Parse and run bool.rtt content" $ do
  it "verifies that the not_preserves_bool theorem type checks successfully" $ do
    let boolRttContent =
          unlines
            [ "Bool ≔ ∀ X . X → X → X;",
              "Not b ≔ (λ t . λ f . b f t);",
              "⊢ not_preserves_bool (b : Term) (p : b [Bool] b) : (Not b) [Bool] (Not b) ≔",
              "  Λ X . λ x : X . λ y : X . (p { X } y x);"
            ]

    case parseFileDeclarations boolRttContent of
      Left parseErr -> expectationFailure $ "Parse failed: " ++ parseErr
      Right decls -> do
        -- Extract macro definitions and theorem
        let theorems = [d | d@(TheoremDef _ _ _ _) <- decls]
            context = buildContextFromDeclarations decls

        case theorems of
          [TheoremDef _ bindings judgment proof] -> do
            let ctx = buildContextFromBindings bindings
            case checkProof context proof judgment of
              Left err ->
                expectationFailure $ "Proof checking failed: " ++ show err
              Right _ ->
                return () -- Success: The proof type checks correctly
          _ -> expectationFailure "Failed to extract theorem from parsed content"

-- Approach 2: Extract and test just the judgment comparison
extractAndTestJudgmentComparisonSpec :: Spec
extractAndTestJudgmentComparisonSpec = describe "Judgment comparison focus" $ do
  it "verifies that macro and expanded forms are considered equal" $ do
    let pos = initialPos "test"
        macrEnv =
          extendMacroContext
            "Not"
            [simpleParamInfo "b" TermK]
            (TermMacro $ Lam "t" (Lam "f" (App (App (Var "b" 0 pos) (Var "f" 0 pos) pos) (Var "t" 1 pos) pos) pos) pos)
            (defaultFixity "TEST")
            $ extendMacroContext
              "Bool"
              []
              (RelMacro $ All "X" (Arr (RVar "X" 0 pos) (Arr (RVar "X" 0 pos) (RVar "X" 0 pos) pos) pos) pos)
              (defaultFixity "TEST")
              emptyContext

        -- Expected judgment (with macro)
        expectedJudgment =
          RelJudgment
            (TMacro "Not" [MTerm (Var "b" 0 pos)] pos)
            (RMacro "Bool" [] pos)
            (TMacro "Not" [MTerm (Var "b" 0 pos)] pos)

        -- Actual judgment (expanded form with correct indices after macro expansion)
        -- The macro expands to λ t . λ f . b f t where b has index 0 (the substituted argument)
        actualJudgment =
          RelJudgment
            (Lam "t" (Lam "f" (App (App (Var "b" 0 pos) (Var "f" 0 pos) pos) (Var "t" 1 pos) pos) pos) pos)
            (RMacro "Bool" [] pos)
            (Lam "t" (Lam "f" (App (App (Var "b" 0 pos) (Var "f" 0 pos) pos) (Var "t" 1 pos) pos) pos) pos)

    -- First test: can we expand the macro correctly?
    let notMacro = TMacro "Not" [MTerm (Var "b" 0 pos)] pos
    case expandFully macrEnv notMacro of
      Left err -> expectationFailure $ "Macro expansion failed: " ++ show err
      Right expanded -> do
        -- Test the comparison - should now succeed with lazy macro expansion
        case relJudgmentEqual macrEnv expectedJudgment actualJudgment of
          Right True -> return () -- Success: judgments are now considered equal
          Right False -> expectationFailure $ "Bug not fixed: macro form and expanded form are still not considered equal. Expanded form: " ++ show expanded
          Left err -> expectationFailure $ "Comparison error: " ++ show err
