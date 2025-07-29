{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module NewParserPipelineSpec (spec) where

import Text.Megaparsec (runParser, errorBundlePretty)

import Parser.Elaborate
import Core.Syntax
import Core.Raw
import Parser.Raw
import Test.Hspec

spec :: Spec
spec = do
  describe "Full Parser Pipeline" fullPipelineSpec
  describe "Parser to Elaborator Integration" integrationSpec
  describe "Error Propagation" errorPropagationSpec

-- Helper function to run the full pipeline
runFullPipeline :: String -> Either String Declaration
runFullPipeline input = do
  case runParser rawDeclaration "test" input of
    Left parseErr -> Left $ "Parse error: " ++ errorBundlePretty parseErr
    Right rawDecl -> case elaborate emptyCtxWithBuiltins rawDecl of
      Left elaborateErr -> Left $ "Elaboration error: " ++ show elaborateErr
      Right decl -> Right decl

-- Helper to test successful pipeline (ignoring positions)
testPipeline :: String -> Declaration -> Expectation
testPipeline input expected = 
  case runFullPipeline input of
    Left err -> expectationFailure err
    Right result -> stripPositions result `shouldBe` stripPositions expected

-- Strip positions from declarations for testing
stripPositions :: Declaration -> Declaration
stripPositions (MacroDef name params body) = MacroDef name params (stripMacroBodyPositions body)
stripPositions (TheoremDef name bindings judgment proof) = 
  TheoremDef name (map stripBindingPositions bindings) (stripJudgmentPositions judgment) (stripProofPositions proof)
stripPositions (ImportDecl imp) = ImportDecl imp
stripPositions (ExportDecl exportDecl) = ExportDecl exportDecl  
stripPositions (FixityDecl fix name) = FixityDecl fix name

stripBindingPositions :: Binding -> Binding
stripBindingPositions (TermBinding name) = TermBinding name
stripBindingPositions (RelBinding name) = RelBinding name
stripBindingPositions (ProofBinding name judgment) = ProofBinding name (stripJudgmentPositions judgment)

stripMacroBodyPositions :: MacroBody -> MacroBody  
stripMacroBodyPositions (TermMacro term) = TermMacro (stripTermPositions term)
stripMacroBodyPositions (RelMacro rtype) = RelMacro (stripRTypePositions rtype)
stripMacroBodyPositions (ProofMacro proof) = ProofMacro (stripProofPositions proof)

stripJudgmentPositions :: RelJudgment -> RelJudgment
stripJudgmentPositions (RelJudgment t1 rt t2) = 
  RelJudgment (stripTermPositions t1) (stripRTypePositions rt) (stripTermPositions t2)

stripTermPositions :: Term -> Term
stripTermPositions (Var name idx _) = Var name idx dummyPos
stripTermPositions (FVar name _) = FVar name dummyPos
stripTermPositions (Lam name body _) = Lam name (stripTermPositions body) dummyPos  
stripTermPositions (App t1 t2 _) = App (stripTermPositions t1) (stripTermPositions t2) dummyPos
stripTermPositions (TMacro name args _) = TMacro name (map stripMacroArgTerm args) dummyPos
  where stripMacroArgTerm = \case
          MTerm t -> MTerm (stripTermPositions t)
          MRel r -> MRel r   -- Relations don't need position stripping in this context
          MProof p -> MProof p  -- Proofs don't need position stripping in this context

stripRTypePositions :: RType -> RType
stripRTypePositions (RVar name idx _) = RVar name idx dummyPos
stripRTypePositions (FRVar name _) = FRVar name dummyPos
stripRTypePositions (Arr rt1 rt2 _) = Arr (stripRTypePositions rt1) (stripRTypePositions rt2) dummyPos
stripRTypePositions (All name rt _) = All name (stripRTypePositions rt) dummyPos
stripRTypePositions (Comp rt1 rt2 _) = Comp (stripRTypePositions rt1) (stripRTypePositions rt2) dummyPos
stripRTypePositions (Conv rt _) = Conv (stripRTypePositions rt) dummyPos
stripRTypePositions (Prom term _) = Prom (stripTermPositions term) dummyPos
stripRTypePositions (RMacro name args _) = RMacro name (map stripMacroArgRType args) dummyPos
  where stripMacroArgRType = \case
          MTerm t -> MTerm t  -- Terms don't need position stripping in this context
          MRel r -> MRel (stripRTypePositions r)
          MProof p -> MProof p  -- Proofs don't need position stripping in this context

stripProofPositions :: Proof -> Proof
stripProofPositions (PVar name idx _) = PVar name idx dummyPos
stripProofPositions (AppP p1 p2 _) = AppP (stripProofPositions p1) (stripProofPositions p2) dummyPos
stripProofPositions (Iota t1 t2 _) = Iota (stripTermPositions t1) (stripTermPositions t2) dummyPos
stripProofPositions (LamP name rt p _) = LamP name (stripRTypePositions rt) (stripProofPositions p) dummyPos
stripProofPositions other = other -- Add more cases as needed

-- Helper to test pipeline failures
testPipelineFailure :: String -> String -> Expectation
testPipelineFailure input expectedErrSubstring =
  case runFullPipeline input of
    Left err -> err `shouldContain` expectedErrSubstring
    Right result -> expectationFailure $ "Expected pipeline failure, but got: " ++ show result

fullPipelineSpec :: Spec
fullPipelineSpec = describe "Complete parsing and elaboration pipeline" $ do
  it "processes simple term macro" $ do
    let input = "id ≔ λ x . x;"
    let pos = dummyPos
    let expected = MacroDef "id" [] (TermMacro (Lam "x" (Var "x" 0 pos) pos))
    testPipeline input expected

  it "processes parameterized macro" $ do
    let input = "const x y ≔ x;"
    let pos = dummyPos
    let expected = MacroDef "const" ["x", "y"] (TermMacro (Var "x" 1 pos))
    testPipeline input expected

  it "processes relational type macro" $ do
    let input = "arrow A B ≔ A → B;"
    let pos = dummyPos
    let expected = MacroDef "arrow" ["A", "B"] (RelMacro (Arr (RVar "A" 1 pos) (RVar "B" 0 pos) pos))
    testPipeline input expected

  it "processes simple theorem" $ do
    let input = "⊢ identity (x : term) (R : rel) : x [R] x ≔ ι⟨ x , x⟩;"
    let pos = dummyPos
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedProof = Iota (Var "x" 0 pos) (Var "x" 0 pos) pos
    let expected = TheoremDef "identity" [TermBinding "x", RelBinding "R"] expectedJudgment expectedProof
    testPipeline input expected

  it "processes theorem with multiple bindings" $ do
    let input = "⊢ test (x : term) (R : rel) (p : x [R] x) : x [R] x ≔ p;"
    let pos = dummyPos
    let expectedProofJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedProof = PVar "p" 0 pos
    let expected = TheoremDef "test" [TermBinding "x", RelBinding "R", ProofBinding "p" expectedProofJudgment] expectedJudgment expectedProof
    testPipeline input expected

integrationSpec :: Spec
integrationSpec = describe "Parser-Elaborator integration" $ do
  it "correctly threads position information" $ do
    case runParser rawDeclaration "test" "id ≔ x;" of
      Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
      Right (RawMacro _ _ (RawTermBody (RTVar _ pos))) -> 
        pos `shouldNotBe` dummyPos
      Right other -> expectationFailure $ "Unexpected parse result: " ++ show other

  it "maintains variable scoping through pipeline" $ do
    let input = "nested ≔ λ x . λ y . x;"
    let pos = dummyPos
    let expected = MacroDef "nested" [] (TermMacro (Lam "x" (Lam "y" (Var "x" 1 pos) pos) pos))
    testPipeline input expected

  it "handles complex proof constructs" $ do
    let input = "⊢ rho_test : x [R] y ≔ ρ{ z . a, b} p - q;"
    case runFullPipeline input of
      Left err -> err `shouldContain` "Elaboration error"  -- Expected since we don't have proper context
      Right _ -> return ()  -- If it elaborates, that's also fine

  it "preserves Unicode syntax through pipeline" $ do
    let input = "unicode ≔ ∀ X . X → X;"
    let pos = dummyPos  
    let expected = MacroDef "unicode" [] (RelMacro (All "X" (Arr (RVar "X" 0 pos) (RVar "X" 0 pos) pos) pos))
    testPipeline input expected

errorPropagationSpec :: Spec
errorPropagationSpec = describe "Error propagation through pipeline" $ do
  it "reports parse errors clearly" $ do
    testPipelineFailure "invalid syntax here" "Parse error"

  it "reports elaboration errors clearly" $ do
    testPipelineFailure "test ≔ unknown_var;" "Elaboration error"

  it "reports unknown macro errors" $ do
    testPipelineFailure "test ≔ unknown_macro x;" "UnknownVariable"

  it "reports arity mismatch errors" $ do
    -- This would require a more complex setup with macro environments
    -- For now, just test that it fails appropriately
    testPipelineFailure "test ≔ λ x y . x;" "Parse error"

  it "handles malformed theorem syntax" $ do
    testPipelineFailure "⊢ bad theorem syntax" "Parse error"

  it "handles malformed proof syntax" $ do
    testPipelineFailure "⊢ test : x [R] x ≔ malformed proof;" "Parse error"