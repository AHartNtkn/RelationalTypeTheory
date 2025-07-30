module TheoremArgValidationSpec (spec) where

import qualified Data.Map as Map
import Core.Context (emptyContext, Context)
import Core.Errors
import Core.Syntax
import TypeCheck.Proof
import Operations.Generic.Substitution (applyTheoremFreeVarSubsToTerm, applyTheoremFreeVarSubsToRType)
import Test.Hspec
import Text.Megaparsec (initialPos)

-- Helper to create dummy source position
dummyPos :: SourcePos
dummyPos = initialPos "test"

-- Helper to create empty contexts
emptyCtx :: Context
emptyCtx = emptyContext

spec :: Spec
spec = describe "Theorem Argument Validation" $ do
  describe "checkTheoremArgs" $ do
    it "validates empty argument list correctly" $ do
      let bindings = []
          args = []
      result <- return $ checkTheoremArgs bindings args emptyCtx dummyPos
      result `shouldBe` Right []

    it "validates single term argument correctly" $ do
      let bindings = [TermBinding "x"]
          term = Var "a" 0 dummyPos
          args = [TermArg term]
      result <- return $ checkTheoremArgs bindings args emptyCtx dummyPos
      result `shouldBe` Right [TermArg term]

    it "validates single relation argument correctly" $ do
      let bindings = [RelBinding "R"]
          rtype = RVar "S" 0 dummyPos
          args = [RelArg rtype]
      result <- return $ checkTheoremArgs bindings args emptyCtx dummyPos
      result `shouldBe` Right [RelArg rtype]

    it "validates multiple mixed arguments correctly" $ do
      let bindings = [TermBinding "x", RelBinding "R", TermBinding "y"]
          term1 = Var "a" 0 dummyPos
          rtype = RVar "S" 0 dummyPos
          term2 = Var "b" 1 dummyPos
          args = [TermArg term1, RelArg rtype, TermArg term2]
      result <- return $ checkTheoremArgs bindings args emptyCtx dummyPos
      result `shouldBe` Right [TermArg term1, RelArg rtype, TermArg term2]

    it "rejects mismatched argument types" $ do
      let bindings = [TermBinding "x"]
          rtype = RVar "R" 0 dummyPos
          args = [RelArg rtype] -- Wrong type: should be TermArg
      result <- return $ checkTheoremArgs bindings args emptyCtx dummyPos
      result `shouldSatisfy` isLeft

  describe "instantiateTheoremJudgment" $ do
    it "returns original judgment when no arguments" $ do
      let bindings = []
          args = []
          judgment = RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "y" 1 dummyPos)
      result <- return $ instantiateTheoremJudgment bindings args judgment
      result `shouldBe` Right judgment

    it "substitutes single term argument correctly" $ do
      let bindings = [TermBinding "x"]
          replacementTerm = Var "a" 0 dummyPos
          args = [TermArg replacementTerm]
          -- Original judgment: x [R] y
          originalJudgment = RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "y" 1 dummyPos)
          -- Expected result: a [R] y (x substituted with a)
          expectedJudgment = RelJudgment replacementTerm (RVar "R" 0 dummyPos) (Var "y" 1 dummyPos)
      result <- return $ instantiateTheoremJudgment bindings args originalJudgment
      result `shouldBe` Right expectedJudgment

    it "substitutes single relation argument correctly" $ do
      let bindings = [RelBinding "R"]
          replacementRel = RVar "S" 0 dummyPos
          args = [RelArg replacementRel]
          -- Original judgment: x [R] y
          originalJudgment = RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "y" 1 dummyPos)
          -- Expected result: x [S] y (R substituted with S)
          expectedJudgment = RelJudgment (Var "x" 0 dummyPos) replacementRel (Var "y" 1 dummyPos)
      result <- return $ instantiateTheoremJudgment bindings args originalJudgment
      result `shouldBe` Right expectedJudgment

    it "substitutes multiple arguments correctly" $ do
      let bindings = [TermBinding "x", RelBinding "R"]
          termReplacement = Var "a" 0 dummyPos
          relReplacement = RVar "S" 0 dummyPos
          args = [TermArg termReplacement, RelArg relReplacement]
          -- Original judgment: x [R] x
          originalJudgment = RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "x" 0 dummyPos)
          -- Expected result: a [S] a
          expectedJudgment = RelJudgment termReplacement relReplacement termReplacement
      result <- return $ instantiateTheoremJudgment bindings args originalJudgment
      result `shouldBe` Right expectedJudgment

  describe "applyTheoremFreeVarSubsToTerm" $ do
    it "handles empty substitutions" $ do
      let term = FVar "x" dummyPos  -- Use free variable
          substitutions = []
      result <- return $ applyTheoremFreeVarSubsToTerm substitutions term
      result `shouldBe` Right term

    it "substitutes free variable correctly" $ do
      let originalTerm = FVar "x" dummyPos  -- Use free variable
          replacementTerm = Var "a" 0 dummyPos
          substitutions = [("x", TermArg replacementTerm)]  -- Use parameter name mapping
      result <- return $ applyTheoremFreeVarSubsToTerm substitutions originalTerm
      result `shouldBe` Right replacementTerm

    it "preserves non-matching variables" $ do
      let term = FVar "y" dummyPos  -- Use free variable
          replacementTerm = Var "a" 0 dummyPos
          substitutions = [("x", TermArg replacementTerm)]  -- Use parameter name mapping
      result <- return $ applyTheoremFreeVarSubsToTerm substitutions term
      result `shouldBe` Right term

    it "handles complex term substitutions" $ do
      let originalTerm = App (FVar "f" dummyPos) (FVar "x" dummyPos) dummyPos  -- Use free variables
          replacementTerm = Var "a" 0 dummyPos
          substitutions = [("x", TermArg replacementTerm)]  -- Use parameter name mapping
          expectedTerm = App (FVar "f" dummyPos) replacementTerm dummyPos
      result <- return $ applyTheoremFreeVarSubsToTerm substitutions originalTerm
      result `shouldBe` Right expectedTerm

  describe "applyTheoremFreeVarSubsToRType" $ do
    it "handles empty substitutions" $ do
      let rtype = FRVar "R" dummyPos  -- Use free relation variable
          substitutions = []
      result <- return $ applyTheoremFreeVarSubsToRType substitutions rtype
      result `shouldBe` Right rtype

    it "substitutes free relation variable correctly" $ do
      let originalRType = FRVar "R" dummyPos  -- Use free relation variable
          replacementRType = RVar "S" 0 dummyPos
          substitutions = [("R", RelArg replacementRType)]  -- Use parameter name mapping
      result <- return $ applyTheoremFreeVarSubsToRType substitutions originalRType
      result `shouldBe` Right replacementRType

    it "handles complex relation substitutions" $ do
      let originalRType = Comp (FRVar "R" dummyPos) (FRVar "S" dummyPos) dummyPos  -- Use free relation variables
          replacementRType = RVar "T" 0 dummyPos
          substitutions = [("R", RelArg replacementRType)]  -- Use parameter name mapping
          expectedRType = Comp replacementRType (FRVar "S" dummyPos) dummyPos
      result <- return $ applyTheoremFreeVarSubsToRType substitutions originalRType
      result `shouldBe` Right expectedRType

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False
