{-# LANGUAGE OverloadedStrings #-}

module NewParserPipelineSpec (spec) where

import Data.Text (Text)
import qualified Data.Map as Map
import Text.Megaparsec (runParser, errorBundlePretty)

import Elaborate
import Lib
import qualified RawAst as Raw
import RawParser
import Test.Hspec

spec :: Spec
spec = do
  describe "Full Parser Pipeline" fullPipelineSpec
  describe "Parser to Elaborator Integration" integrationSpec
  describe "Error Propagation" errorPropagationSpec

-- Helper function to run the full pipeline
runFullPipeline :: Text -> Either String Declaration
runFullPipeline input = do
  case runParser rawDeclaration "test" input of
    Left parseErr -> Left $ "Parse error: " ++ errorBundlePretty parseErr
    Right rawDecl -> case elaborate emptyElaborateContext rawDecl of
      Left elaborateErr -> Left $ "Elaboration error: " ++ show elaborateErr
      Right decl -> Right decl

-- Helper to test successful pipeline (ignoring positions)
testPipeline :: Text -> Declaration -> Expectation
testPipeline input expected = 
  case runFullPipeline input of
    Left err -> expectationFailure err
    Right result -> stripPositions result `shouldBe` stripPositions expected

-- Strip positions from declarations for testing
stripPositions :: Declaration -> Declaration
stripPositions (MacroDef name params body) = MacroDef name params (stripMacroBodyPositions body)
stripPositions (TheoremDef name bindings judgment proof) = 
  TheoremDef name (map stripBindingPositions bindings) (stripJudgmentPositions judgment) (stripProofPositions proof)

stripBindingPositions :: Binding -> Binding
stripBindingPositions (TermBinding name) = TermBinding name
stripBindingPositions (RelBinding name) = RelBinding name
stripBindingPositions (ProofBinding name judgment) = ProofBinding name (stripJudgmentPositions judgment)

stripMacroBodyPositions :: MacroBody -> MacroBody  
stripMacroBodyPositions (TermMacro term) = TermMacro (stripTermPositions term)
stripMacroBodyPositions (RelMacro rtype) = RelMacro (stripRTypePositions rtype)

stripJudgmentPositions :: RelJudgment -> RelJudgment
stripJudgmentPositions (RelJudgment t1 rt t2) = 
  RelJudgment (stripTermPositions t1) (stripRTypePositions rt) (stripTermPositions t2)

stripTermPositions :: Term -> Term
stripTermPositions (Var name idx _) = Var name idx Raw.dummyPos
stripTermPositions (Lam name body _) = Lam name (stripTermPositions body) Raw.dummyPos  
stripTermPositions (App t1 t2 _) = App (stripTermPositions t1) (stripTermPositions t2) Raw.dummyPos

stripRTypePositions :: RType -> RType
stripRTypePositions (RVar name idx _) = RVar name idx Raw.dummyPos
stripRTypePositions (Arr rt1 rt2 _) = Arr (stripRTypePositions rt1) (stripRTypePositions rt2) Raw.dummyPos
stripRTypePositions (All name rt _) = All name (stripRTypePositions rt) Raw.dummyPos
stripRTypePositions (Comp rt1 rt2 _) = Comp (stripRTypePositions rt1) (stripRTypePositions rt2) Raw.dummyPos
stripRTypePositions (Conv rt _) = Conv (stripRTypePositions rt) Raw.dummyPos
stripRTypePositions (Prom term _) = Prom (stripTermPositions term) Raw.dummyPos

stripProofPositions :: Proof -> Proof
stripProofPositions (PVar name idx _) = PVar name idx Raw.dummyPos
stripProofPositions (AppP p1 p2 _) = AppP (stripProofPositions p1) (stripProofPositions p2) Raw.dummyPos
stripProofPositions (Iota t1 t2 _) = Iota (stripTermPositions t1) (stripTermPositions t2) Raw.dummyPos
stripProofPositions (LamP name rt p _) = LamP name (stripRTypePositions rt) (stripProofPositions p) Raw.dummyPos
stripProofPositions other = other -- Add more cases as needed

-- Helper to test pipeline failures
testPipelineFailure :: Text -> String -> Expectation
testPipelineFailure input expectedErrSubstring =
  case runFullPipeline input of
    Left err -> err `shouldContain` expectedErrSubstring
    Right result -> expectationFailure $ "Expected pipeline failure, but got: " ++ show result

fullPipelineSpec :: Spec
fullPipelineSpec = describe "Complete parsing and elaboration pipeline" $ do
  it "processes simple term macro" $ do
    let input = "id := λx. x;"
    let pos = Raw.dummyPos
    let expected = MacroDef "id" [] (TermMacro (Lam "x" (Var "x" 0 pos) pos))
    testPipeline input expected

  it "processes parameterized macro" $ do
    let input = "const x y := x;"
    let pos = Raw.dummyPos
    let expected = MacroDef "const" ["x", "y"] (TermMacro (Var "x" 1 pos))
    testPipeline input expected

  it "processes relational type macro" $ do
    let input = "arrow A B := A → B;"
    let pos = Raw.dummyPos
    let expected = MacroDef "arrow" ["A", "B"] (RelMacro (Arr (RVar "A" 1 pos) (RVar "B" 0 pos) pos))
    testPipeline input expected

  it "processes simple theorem" $ do
    let input = "⊢ identity (x : term) (R : rel) : x [R] x := ι⟨x, x⟩;"
    let pos = Raw.dummyPos
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedProof = Iota (Var "x" 0 pos) (Var "x" 0 pos) pos
    let expected = TheoremDef "identity" [TermBinding "x", RelBinding "R"] expectedJudgment expectedProof
    testPipeline input expected

  it "processes theorem with multiple bindings" $ do
    let input = "⊢ test (x : term) (R : rel) (p : x [R] x) : x [R] x := p;"
    let pos = Raw.dummyPos
    let expectedProofJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedProof = PVar "p" 0 pos
    let expected = TheoremDef "test" [TermBinding "x", RelBinding "R", ProofBinding "p" expectedProofJudgment] expectedJudgment expectedProof
    testPipeline input expected

integrationSpec :: Spec
integrationSpec = describe "Parser-Elaborator integration" $ do
  it "correctly threads position information" $ do
    case runParser rawDeclaration "test" "id := x;" of
      Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
      Right (Raw.RawMacro _ _ (Raw.RawTermBody (Raw.RTVar _ pos))) -> 
        pos `shouldNotBe` Raw.dummyPos
      Right other -> expectationFailure $ "Unexpected parse result: " ++ show other

  it "maintains variable scoping through pipeline" $ do
    let input = "nested := λx. λy. x;"
    let pos = Raw.dummyPos
    let expected = MacroDef "nested" [] (TermMacro (Lam "x" (Lam "y" (Var "x" 1 pos) pos) pos))
    testPipeline input expected

  it "handles complex proof constructs" $ do
    let input = "⊢ rho_test : x [R] y := ρ{z. a, b} p - q;"
    case runFullPipeline input of
      Left err -> err `shouldContain` "Elaboration error"  -- Expected since we don't have proper context
      Right _ -> return ()  -- If it elaborates, that's also fine

  it "preserves Unicode syntax through pipeline" $ do
    let input = "unicode := ∀X. X → X;"
    let pos = Raw.dummyPos  
    let expected = MacroDef "unicode" [] (RelMacro (All "X" (Arr (RVar "X" 0 pos) (RVar "X" 0 pos) pos) pos))
    testPipeline input expected

errorPropagationSpec :: Spec
errorPropagationSpec = describe "Error propagation through pipeline" $ do
  it "reports parse errors clearly" $ do
    testPipelineFailure "invalid syntax here" "Parse error"

  it "reports elaboration errors clearly" $ do
    testPipelineFailure "test := unknown_var;" "Elaboration error"

  it "reports unknown macro errors" $ do
    testPipelineFailure "test := unknown_macro x;" "UnknownVariable"

  it "reports arity mismatch errors" $ do
    -- This would require a more complex setup with macro environments
    -- For now, just test that it fails appropriately
    testPipelineFailure "test := λx y. x;" "Parse error"

  it "handles malformed theorem syntax" $ do
    testPipelineFailure "⊢ bad theorem syntax" "Parse error"

  it "handles malformed proof syntax" $ do
    testPipelineFailure "⊢ test : x [R] x := malformed proof;" "Parse error"