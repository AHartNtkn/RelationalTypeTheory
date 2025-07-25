{-# LANGUAGE OverloadedStrings #-}

module NotPreservesBoolBugSpec (spec) where

import Context
import Lib
import Normalize (expandTermMacrosOneStep)
import qualified RawParser as Raw
import Elaborate
import ProofChecker
import Test.Hspec
import Text.Megaparsec (initialPos, runParser, errorBundlePretty)
import qualified Data.Map as Map

-- Helper functions for two-phase parsing
parseFileWithTwoPhase :: String -> Either String [Declaration]
parseFileWithTwoPhase content = do
  rawDecls <- case runParser Raw.parseFile "test" content of
    Left err -> Left (errorBundlePretty err)
    Right raw -> Right raw
  let ctx = emptyElaborateContext Map.empty noMacros noTheorems
  case elaborateDeclarationsWithAccumulation ctx rawDecls of
    Left err -> Left (show err)
    Right decls -> Right decls

-- Helper function to elaborate declarations while threading the environment
elaborateDeclarationsWithAccumulation :: ElaborateContext -> [Raw.RawDeclaration] -> Either ElaborateError [Declaration]
elaborateDeclarationsWithAccumulation _ [] = Right []
elaborateDeclarationsWithAccumulation ctx (rawDecl:rest) = do
  decl <- elaborateDeclaration ctx rawDecl
  let updatedCtx = updateContextWithDeclaration ctx decl
  restDecls <- elaborateDeclarationsWithAccumulation updatedCtx rest
  return (decl : restDecls)

-- Update context with newly elaborated declaration
updateContextWithDeclaration :: ElaborateContext -> Declaration -> ElaborateContext
updateContextWithDeclaration ctx (MacroDef name params body) =
  let newMacroEnv = extendMacroEnvironment name params body defaultFixity (macroEnv ctx)
  in ctx { macroEnv = newMacroEnv }
updateContextWithDeclaration ctx (FixityDecl fixity name) =
  let currentMacroEnv = macroEnv ctx
      newMacroEnv = currentMacroEnv { macroFixities = Map.insert name fixity (macroFixities currentMacroEnv) }
  in ctx { macroEnv = newMacroEnv }
updateContextWithDeclaration ctx (TheoremDef name bindings judgment proof) =
  let newTheoremEnv = extendTheoremEnvironment name bindings judgment proof (theoremEnv ctx)
  in ctx { theoremEnv = newTheoremEnv }
updateContextWithDeclaration ctx _ = ctx  -- Other declarations don't affect context

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
            [ "Bool := ∀X. X → X → X;",
              "Not b := (λt. λf. b f t);",
              "⊢ not_preserves_bool (b : Term) (p : b [Bool] b) : (Not b) [Bool] (Not b) :=",
              "  ΛX. λx:X. λy:X. (p{X} y x);"
            ]

    case parseFileWithTwoPhase boolRttContent of
      Left parseErr -> expectationFailure $ "Parse failed: " ++ show parseErr
      Right decls -> do
        -- Extract macro definitions and theorem
        let macros = [d | d@(MacroDef _ _ _) <- decls]
            theorems = [d | d@(TheoremDef _ _ _ _) <- decls]

        case (buildMacroEnvironmentFromDecls macros, theorems) of
          (Right macrEnv, [TheoremDef _ bindings judgment proof]) -> do
            let ctx = buildContextFromBindings bindings
            case checkProof ctx macrEnv noTheorems proof judgment of
              Left err ->
                expectationFailure $ "Proof checking failed: " ++ show err
              Right _ ->
                return () -- Success: The proof type checks correctly
          _ -> expectationFailure "Failed to extract theorem from parsed content"
  where
    buildMacroEnvironmentFromDecls [] = Right noMacros
    buildMacroEnvironmentFromDecls ((MacroDef name params body) : rest) = do
      env <- buildMacroEnvironmentFromDecls rest
      return $ extendMacroEnvironment name params body defaultFixity env
    buildMacroEnvironmentFromDecls (_ : rest) = buildMacroEnvironmentFromDecls rest

    buildContextFromBindings = foldl addBinding emptyTypingContext
      where
        addBinding ctx (TermBinding name) = extendTermContext name (RMacro "Type" [] (initialPos "<builtin>")) ctx
        addBinding ctx (RelBinding name) = extendRelContext name ctx
        addBinding ctx (ProofBinding name judgment) = extendProofContext name judgment ctx

-- Approach 2: Extract and test just the judgment comparison
extractAndTestJudgmentComparisonSpec :: Spec
extractAndTestJudgmentComparisonSpec = describe "Judgment comparison focus" $ do
  it "verifies that macro and expanded forms are considered equal" $ do
    let pos = initialPos "test"
        macrEnv =
          extendMacroEnvironment
            "Not"
            ["b"]
            (TermMacro $ Lam "t" (Lam "f" (App (App (Var "b" 0 pos) (Var "f" 0 pos) pos) (Var "t" 1 pos) pos) pos) pos)
            defaultFixity
            $ extendMacroEnvironment
              "Bool"
              []
              (RelMacro $ All "X" (Arr (RVar "X" 0 pos) (Arr (RVar "X" 0 pos) (RVar "X" 0 pos) pos) pos) pos)
              defaultFixity
              noMacros

        -- Expected judgment (with macro)
        expectedJudgment =
          RelJudgment
            (TMacro "Not" [Var "b" 0 pos] pos)
            (RMacro "Bool" [] pos)
            (TMacro "Not" [Var "b" 0 pos] pos)

        -- Actual judgment (expanded form with correct indices after macro expansion)
        -- The macro expands to λt. λf. b f t where b has index 0 (the substituted argument)
        actualJudgment =
          RelJudgment
            (Lam "t" (Lam "f" (App (App (Var "b" 0 pos) (Var "f" 0 pos) pos) (Var "t" 1 pos) pos) pos) pos)
            (RMacro "Bool" [] pos)
            (Lam "t" (Lam "f" (App (App (Var "b" 0 pos) (Var "f" 0 pos) pos) (Var "t" 1 pos) pos) pos) pos)

    -- First test: can we expand the macro correctly?
    let notMacro = TMacro "Not" [Var "b" 0 pos] pos
    case expandTermMacrosOneStep macrEnv notMacro of
      Left err -> expectationFailure $ "Macro expansion failed: " ++ show err
      Right expanded -> do
        -- Test the comparison - should now succeed with lazy macro expansion
        case relJudgmentEqual macrEnv expectedJudgment actualJudgment of
          Right True -> return () -- Success: judgments are now considered equal
          Right False -> expectationFailure $ "Bug not fixed: macro form and expanded form are still not considered equal. Expanded form: " ++ show expanded
          Left err -> expectationFailure $ "Comparison error: " ++ show err
