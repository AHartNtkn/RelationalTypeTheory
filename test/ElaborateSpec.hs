{-# LANGUAGE OverloadedStrings #-}

module ElaborateSpec (spec) where

import Elaborate
import RawParser
import Lib
import Context (noMacros, noTheorems, extendTheoremEnvironment)
import Test.Hspec
import Text.Megaparsec (initialPos, SourcePos)
import qualified Data.Map as Map

spec :: Spec
spec = do
  termElaborationSpec
  rtypeElaborationSpec
  proofElaborationSpec

-- Helper to create test position
testPos :: SourcePos
testPos = initialPos "test"

-- Helper contexts
emptyCtx :: ElaborateContext
emptyCtx = (emptyElaborateContext Map.empty noMacros noTheorems) { currentPos = testPos }

-- Context with one term variable 'x' bound
ctxWithTermVar :: ElaborateContext  
ctxWithTermVar = emptyCtx { termVars = Map.fromList [("x", 0)] }

-- Context with one relation variable 'R' bound
ctxWithRelVar :: ElaborateContext
ctxWithRelVar = emptyCtx { relVars = Map.fromList [("R", 0)] }

-- Context with one proof variable 'p' bound
ctxWithProofVar :: ElaborateContext
ctxWithProofVar = emptyCtx { proofVars = Map.fromList [("p", 0)] }

termElaborationSpec :: Spec
termElaborationSpec = describe "Term elaboration" $ do
  it "elaborates bound variables correctly" $ do
    let result = elaborateTerm ctxWithTermVar (RTVar "x")
    result `shouldBe` Right (Var "x" 0 testPos)

  it "fails on unknown variables" $ do
    let result = elaborateTerm emptyCtx (RTVar "unknown")
    result `shouldBe` Left (UnknownTerm "unknown")

  it "elaborates lambda abstractions" $ do
    let result = elaborateTerm emptyCtx (RTLam "x" (RTVar "x"))
    result `shouldBe` Right (Lam "x" (Var "x" 0 testPos) testPos)

  it "elaborates applications" $ do 
    let rawTerm = RTApp (RTVar "f") (RTVar "x")
        ctx = emptyCtx { termVars = Map.fromList [("f", 1), ("x", 0)] }
        result = elaborateTerm ctx rawTerm
    result `shouldBe` Right (App (Var "f" 1 testPos) (Var "x" 0 testPos) testPos)

  it "handles nested lambda abstractions with proper de Bruijn indices" $ do
    let rawTerm = RTLam "x" (RTLam "y" (RTVar "x"))
        result = elaborateTerm emptyCtx rawTerm
        expected = Lam "x" (Lam "y" (Var "x" 1 testPos) testPos) testPos
    result `shouldBe` Right expected

  it "handles variable shadowing correctly" $ do
    let rawTerm = RTLam "x" (RTVar "x")
        ctx = emptyCtx { termVars = Map.fromList [("x", 5)] } -- outer x has index 5
        result = elaborateTerm ctx rawTerm
        expected = Lam "x" (Var "x" 0 testPos) testPos -- inner x has index 0
    result `shouldBe` Right expected

rtypeElaborationSpec :: Spec
rtypeElaborationSpec = describe "Relation type elaboration" $ do
  it "elaborates bound relation variables correctly" $ do
    let result = elaborateRType ctxWithRelVar (RRVar "R")
    result `shouldBe` Right (RVar "R" 0 testPos)

  it "fails on unknown relation variables" $ do
    let result = elaborateRType emptyCtx (RRVar "unknown")
    result `shouldBe` Left (UnknownRelation "unknown")

  it "elaborates arrow types" $ do
    let rawType = RRArr (RRVar "A") (RRVar "B")
        ctx = emptyCtx { relVars = Map.fromList [("A", 1), ("B", 0)] }
        result = elaborateRType ctx rawType
        expected = Arr (RVar "A" 1 testPos) (RVar "B" 0 testPos) testPos
    result `shouldBe` Right expected

  it "elaborates universal quantification" $ do
    let rawType = RRAll "R" (RRVar "R")
        result = elaborateRType emptyCtx rawType
        expected = All "R" (RVar "R" 0 testPos) testPos
    result `shouldBe` Right expected

  it "elaborates promotion" $ do
    let rawType = RRProm (RTVar "x")
        ctx = emptyCtx { termVars = Map.fromList [("x", 0)] }
        result = elaborateRType ctx rawType
        expected = Prom (Var "x" 0 testPos) testPos
    result `shouldBe` Right expected

proofElaborationSpec :: Spec  
proofElaborationSpec = describe "Proof elaboration" $ do
  it "elaborates bound proof variables correctly" $ do
    let result = elaborateProof ctxWithProofVar (RPVar "p")
    result `shouldBe` Right (PVar "p" 0 testPos)

  it "fails on unknown proof variables and theorems" $ do
    let result = elaborateProof emptyCtx (RPVar "unknown")
    result `shouldBe` Left (UnknownProof "unknown")

  it "elaborates proof lambda abstractions" $ do
    let rawProof = RPLam "p" (RRVar "A") (RPVar "p")
        ctx = emptyCtx { relVars = Map.fromList [("A", 0)] }
        result = elaborateProof ctx rawProof
        expected = LamP "p" (RVar "A" 0 testPos) (PVar "p" 0 testPos) testPos
    result `shouldBe` Right expected

  it "elaborates type lambda abstractions" $ do
    let rawProof = RPTyLam "R" (RPVar "p")
        ctx = emptyCtx { proofVars = Map.fromList [("p", 0)] }
        result = elaborateProof ctx rawProof
        expected = TyLam "R" (PVar "p" 0 testPos) testPos
    result `shouldBe` Right expected

  it "elaborates proof applications" $ do
    let rawProof = RPApp (RPVar "f") (RPVar "x")
        ctx = emptyCtx { proofVars = Map.fromList [("f", 1), ("x", 0)] }
        result = elaborateProof ctx rawProof
        expected = AppP (PVar "f" 1 testPos) (PVar "x" 0 testPos) testPos
    result `shouldBe` Right expected

  it "elaborates type applications" $ do
    let rawProof = RPTyApp (RPVar "p") (RRVar "A")
        ctx = emptyCtx { proofVars = Map.fromList [("p", 0)], relVars = Map.fromList [("A", 0)] }
        result = elaborateProof ctx rawProof
        expected = TyApp (PVar "p" 0 testPos) (RVar "A" 0 testPos) testPos
    result `shouldBe` Right expected

  it "elaborates conversion introduction patterns" $ do
    let rawProof = RPApp (RPVar "∪ᵢ") (RPVar "p")
        ctx = emptyCtx { proofVars = Map.fromList [("p", 0)] }
        result = elaborateProof ctx rawProof
        expected = ConvIntro (PVar "p" 0 testPos) testPos
    result `shouldBe` Right expected

  it "elaborates conversion elimination patterns" $ do
    let rawProof = RPApp (RPVar "∪ₑ") (RPVar "p")
        ctx = emptyCtx { proofVars = Map.fromList [("p", 0)] }
        result = elaborateProof ctx rawProof
        expected = ConvElim (PVar "p" 0 testPos) testPos
    result `shouldBe` Right expected

  it "elaborates iota expression patterns" $ do
    let rawProof = RPApp (RPVar "ι⟨") (RPApp (RPVar "x") (RPVar "y"))
        ctx = emptyCtx { termVars = Map.fromList [("x", 1), ("y", 0)] }
        result = elaborateProof ctx rawProof
        expected = Iota (Var "x" 1 testPos) (Var "y" 0 testPos) testPos
    result `shouldBe` Right expected

  it "elaborates conversion proof patterns" $ do
    let rawProof = RPApp (RPApp (RPApp (RPVar "x") (RPVar "⇃")) (RPVar "p")) (RPVar "y")
        ctx = emptyCtx { termVars = Map.fromList [("x", 1), ("y", 0)], proofVars = Map.fromList [("p", 0)] }
        result = elaborateProof ctx rawProof
        expected = ConvProof (Var "x" 1 testPos) (PVar "p" 0 testPos) (Var "y" 0 testPos) testPos
    result `shouldBe` Right expected

  -- This is the key test - it should elaborate theorem references without error during parsing
  it "elaborates theorem references (when they exist in environment)" $ do
    -- Create a theorem environment with an 'identity' theorem
    let judgment = RelJudgment (Var "a" 0 testPos) (RVar "R" 0 testPos) (Var "a" 0 testPos)
        tEnv = extendTheoremEnvironment "identity" [] judgment (PVar "dummy" 0 testPos) noTheorems
        ctx = (emptyElaborateContext Map.empty noMacros tEnv) { currentPos = testPos }
        result = elaborateProof ctx (RPVar "identity")
        expected = PTheoremApp "identity" [] testPos
    result `shouldBe` Right expected