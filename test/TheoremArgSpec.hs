module TheoremArgSpec (spec) where

import Lib
import PrettyPrint
import Test.Hspec
import Text.Megaparsec (SourcePos, initialPos)

-- Helper to create dummy source position
dummyPos :: SourcePos
dummyPos = initialPos "test"

spec :: Spec
spec = describe "TheoremArg" $ do
  describe "data type construction" $ do
    it "creates TermArg correctly" $ do
      let term = Var "x" 0 dummyPos
          termArg = TermArg term
      termArg `shouldBe` TermArg (Var "x" 0 dummyPos)

    it "creates RelArg correctly" $ do
      let rtype = RVar "R" 0 dummyPos
          relArg = RelArg rtype
      relArg `shouldBe` RelArg (RVar "R" 0 dummyPos)

    it "creates ProofArg correctly" $ do
      let proof = PVar "p" 0 dummyPos
          proofArg = ProofArg proof
      proofArg `shouldBe` ProofArg (PVar "p" 0 dummyPos)

  describe "pretty printing" $ do
    let config = defaultPrettyConfig

    it "pretty prints TermArg with parentheses" $ do
      let term = Var "x" 0 dummyPos
          termArg = TermArg term
      prettyTheoremArgWithConfig config termArg `shouldBe` "(x)"

    it "pretty prints RelArg with parentheses" $ do
      let rtype = RVar "R" 0 dummyPos
          relArg = RelArg rtype
      prettyTheoremArgWithConfig config relArg `shouldBe` "(R)"

    it "pretty prints ProofArg with parentheses" $ do
      let proof = PVar "p" 0 dummyPos
          proofArg = ProofArg proof
      prettyTheoremArgWithConfig config proofArg `shouldBe` "(p)"

    it "pretty prints complex TermArg" $ do
      let term = Lam "x" (Var "x" 0 dummyPos) dummyPos
          termArg = TermArg term
      prettyTheoremArgWithConfig config termArg `shouldBe` "(λx. x)"

    it "pretty prints complex RelArg" $ do
      let rtype = Arr (RVar "R" 0 dummyPos) (RVar "S" 1 dummyPos) dummyPos
          relArg = RelArg rtype
      prettyTheoremArgWithConfig config relArg `shouldBe` "(R → S)"

  describe "PTheoremApp pretty printing" $ do
    let config = defaultPrettyConfig

    it "pretty prints theorem with no arguments" $ do
      let proof = PTheoremApp "my_thm" [] dummyPos
      prettyProofWithConfig config proof `shouldBe` "my_thm"

    it "pretty prints theorem with single term argument" $ do
      let term = Var "x" 0 dummyPos
          termArg = TermArg term
          proof = PTheoremApp "my_thm" [termArg] dummyPos
      prettyProofWithConfig config proof `shouldBe` "my_thm (x)"

    it "pretty prints theorem with multiple arguments" $ do
      let term = Var "x" 0 dummyPos
          rtype = RVar "R" 0 dummyPos
          proofTerm = PVar "p" 0 dummyPos
          args = [TermArg term, RelArg rtype, ProofArg proofTerm]
          proof = PTheoremApp "complex_thm" args dummyPos
      prettyProofWithConfig config proof `shouldBe` "complex_thm (x) (R) (p)"

  describe "TheoremArg equality" $ do
    it "considers equal TermArgs equal" $ do
      let term1 = Var "x" 0 dummyPos
          term2 = Var "x" 0 dummyPos
          arg1 = TermArg term1
          arg2 = TermArg term2
      arg1 `shouldBe` arg2

    it "considers different TermArgs different" $ do
      let term1 = Var "x" 0 dummyPos
          term2 = Var "y" 1 dummyPos
          arg1 = TermArg term1
          arg2 = TermArg term2
      arg1 `shouldNotBe` arg2

    it "considers equal RelArgs equal" $ do
      let rel1 = RVar "R" 0 dummyPos
          rel2 = RVar "R" 0 dummyPos
          arg1 = RelArg rel1
          arg2 = RelArg rel2
      arg1 `shouldBe` arg2

    it "considers different argument types different" $ do
      let term = Var "x" 0 dummyPos
          rel = RVar "R" 0 dummyPos
          termArg = TermArg term
          relArg = RelArg rel
      termArg `shouldNotBe` relArg

  describe "PTheoremApp equality" $ do
    it "considers theorems with same name and args equal" $ do
      let term = Var "x" 0 dummyPos
          args = [TermArg term]
          proof1 = PTheoremApp "thm" args dummyPos
          proof2 = PTheoremApp "thm" args dummyPos
      proof1 `shouldBe` proof2

    it "considers theorems with different names different" $ do
      let args = []
          proof1 = PTheoremApp "thm1" args dummyPos
          proof2 = PTheoremApp "thm2" args dummyPos
      proof1 `shouldNotBe` proof2

    it "considers theorems with different arguments different" $ do
      let term1 = Var "x" 0 dummyPos
          term2 = Var "y" 1 dummyPos
          args1 = [TermArg term1]
          args2 = [TermArg term2]
          proof1 = PTheoremApp "thm" args1 dummyPos
          proof2 = PTheoremApp "thm" args2 dummyPos
      proof1 `shouldNotBe` proof2

  describe "proofPos extraction" $ do
    it "extracts position from PTheoremApp correctly" $ do
      let customPos = initialPos "custom"
          proof = PTheoremApp "thm" [] customPos
      proofPos proof `shouldBe` customPos
