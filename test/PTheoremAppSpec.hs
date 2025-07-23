module PTheoremAppSpec (spec) where

import qualified Data.Map as Map
import Errors
import Lib
import ProofChecker
import Test.Hspec
import Text.Megaparsec (initialPos)

-- Helper to create dummy source position
dummyPos :: SourcePos
dummyPos = initialPos "test"

-- Helper to create empty contexts
emptyCtx :: TypingContext
emptyCtx = TypingContext Map.empty Map.empty Map.empty 0

emptyMacroEnv :: MacroEnvironment
emptyMacroEnv = MacroEnvironment Map.empty Map.empty

spec :: Spec
spec = describe "PTheoremApp Proof Checking" $ do
  describe "theorem with no arguments" $ do
    it "correctly types theorem with no parameters" $ do
      let theoremName = "identity_thm"
          -- Theorem: ⊢ identity_thm : x [λy.y] x
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (Prom (Lam "y" (Var "y" 0 dummyPos) dummyPos) dummyPos) (Var "x" 0 dummyPos)
          theoremProof = Iota (Var "x" 0 dummyPos) (Lam "y" (Var "y" 0 dummyPos) dummyPos) dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, ([], theoremJudgment, theoremProof))]

          -- Application: identity_thm (no arguments)
          theoremApp = PTheoremApp theoremName [] dummyPos

      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` theoremJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

  describe "theorem with single term argument" $ do
    it "correctly types theorem with one term parameter" $ do
      let theoremName = "simple_thm"
          -- Theorem: ⊢ simple_thm (x : Term) : x [λy.y] x
          theoremBindings = [TermBinding "x"]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (Prom (Lam "y" (Var "y" 0 dummyPos) dummyPos) dummyPos) (Var "x" 0 dummyPos)
          theoremProof = Iota (Var "x" 0 dummyPos) (Lam "y" (Var "y" 0 dummyPos) dummyPos) dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]

          -- Application: simple_thm a
          argTerm = Var "a" 0 dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argTerm] dummyPos

          -- Expected result: a [λy.y] a
          expectedJudgment = RelJudgment argTerm (Prom (Lam "y" (Var "y" 0 dummyPos) dummyPos) dummyPos) argTerm

      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

  describe "theorem with single relation argument" $ do
    it "correctly types theorem with one relation parameter" $ do
      let theoremName = "rel_thm"
          -- Theorem: ⊢ rel_thm (R : Rel) : x [R] y
          theoremBindings = [RelBinding "R"]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "y" 1 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos -- Dummy proof for testing
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]

          -- Application: rel_thm S
          argRel = RVar "S" 0 dummyPos
          theoremApp = PTheoremApp theoremName [RelArg argRel] dummyPos

          -- Expected result: x [S] y
          expectedJudgment = RelJudgment (Var "x" 0 dummyPos) argRel (Var "y" 1 dummyPos)

      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

  describe "theorem with multiple arguments" $ do
    it "correctly types theorem with mixed parameters" $ do
      let theoremName = "mixed_thm"
          -- Theorem: ⊢ mixed_thm (x : Term) (R : Rel) (y : Term) : x [R] y
          theoremBindings = [TermBinding "x", RelBinding "R", TermBinding "y"]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "y" 1 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]

          -- Application: mixed_thm a S b
          argTerm1 = Var "a" 0 dummyPos
          argRel = RVar "S" 0 dummyPos
          argTerm2 = Var "b" 1 dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argTerm1, RelArg argRel, TermArg argTerm2] dummyPos

          -- Expected result: a [S] b
          expectedJudgment = RelJudgment argTerm1 argRel argTerm2

      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

  describe "error cases" $ do
    it "rejects theorem application with too many arguments" $ do
      let theoremName = "simple_thm"
          -- Theorem with one parameter
          theoremBindings = [TermBinding "x"]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "x" 0 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]

          -- Application with too many arguments: simple_thm a b
          argTerm1 = Var "a" 0 dummyPos
          argTerm2 = Var "b" 1 dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argTerm1, TermArg argTerm2] dummyPos

      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Left (InternalError msg _) -> msg `shouldContain` "Too many arguments"
        Left err -> expectationFailure $ "Expected InternalError about too many arguments, got: " ++ show err
        Right _ -> expectationFailure "Expected error, but got success"

    it "rejects undefined theorem reference" $ do
      let theoremApp = PTheoremApp "nonexistent_thm" [] dummyPos
          emptyTheoremEnv = TheoremEnvironment Map.empty

      case inferProofType emptyCtx emptyMacroEnv emptyTheoremEnv theoremApp of
        Left (UnboundVariable "nonexistent_thm" _) -> return () -- Expected
        Left err -> expectationFailure $ "Expected UnboundVariable error, got: " ++ show err
        Right _ -> expectationFailure "Expected error, but got success"

  describe "partial argument application" $ do
    it "correctly types theorem with fewer arguments than parameters" $ do
      let theoremName = "multi_param_thm"
          -- Theorem: ⊢ multi_param_thm (x : Term) (y : Term) : x [R] y
          theoremBindings = [TermBinding "x", TermBinding "y"]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "y" 1 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]

          -- Application with only first argument: multi_param_thm a
          argTerm = Var "a" 0 dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argTerm] dummyPos

          -- Expected result: a [R] y (only x substituted)
          expectedJudgment = RelJudgment argTerm (RVar "R" 0 dummyPos) (Var "y" 1 dummyPos)

      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err
