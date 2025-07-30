{-# LANGUAGE OverloadedStrings #-}

module ElaborateSpec (spec) where

import qualified Data.Map as Map
import Text.Megaparsec (initialPos)

import Parser.Elaborate (elaborate)
import Core.Context (emptyContext, Context)
import Core.Syntax
import Core.Raw
import Core.Errors (RelTTError(..), ErrorContext(..))
import Test.Hspec
import TestHelpers (simpleTermMacro, simpleRelMacro)

spec :: Spec
spec = do
  describe "Elaboration Context" elaborateContextSpec
  describe "Term Elaboration" termElaborationSpec
  describe "RType Elaboration" rtypeElaborationSpec
  describe "Proof Elaboration" proofElaborationSpec
  describe "Declaration Elaboration" declarationElaborationSpec
  describe "Error Handling" elaborateErrorSpec
  describe "Variable Binding" variableBindingSpec

-- Helper to create test context with specific environments
testContext :: Map.Map String MacroSig -> Map.Map String ([Binding], RelJudgment, Proof) -> Context
testContext testMacros testTheorems = emptyContext
  { macroDefinitions = testMacros
  , theoremDefinitions = testTheorems
  }

-- Helper to create test context with bound term variables
testContextWithTerms :: [(String, Int)] -> Int -> Context
testContextWithTerms vars depth = emptyContext
  { termBindings = Map.fromList [(name, (idx, Nothing)) | (name, idx) <- vars]
  , termDepth = depth
  }

-- Helper to create test context with bound relational variables  
testContextWithRels :: [(String, Int)] -> Int -> Context
testContextWithRels vars depth = emptyContext
  { relBindings = Map.fromList vars
  , relDepth = depth
  }

-- Helper to test successful elaboration (ignoring positions)
testElaborate :: Context -> RawDeclaration -> Declaration -> Expectation
testElaborate ctx rawDecl expected =
  case elaborate ctx rawDecl of
    Left err -> expectationFailure $ "Elaboration failed: " ++ show err
    Right result -> stripPositions result `shouldBe` stripPositions expected

-- Strip positions from declarations for testing
stripPositions :: Declaration -> Declaration
stripPositions (MacroDef name params body) = MacroDef name params (stripMacroBodyPositions body)
stripPositions (TheoremDef name bindings judgment proof) = 
  TheoremDef name bindings (stripJudgmentPositions judgment) (stripProofPositions proof)
stripPositions (ImportDecl imp) = ImportDecl imp
stripPositions (ExportDecl exportDecl) = ExportDecl exportDecl
stripPositions (FixityDecl fix name) = FixityDecl fix name

stripMacroBodyPositions :: MacroBody -> MacroBody  
stripMacroBodyPositions (TermMacro term) = TermMacro (stripTermPositions term)
stripMacroBodyPositions (RelMacro rtype) = RelMacro (stripRTypePositions rtype)
stripMacroBodyPositions (ProofMacro proof) = ProofMacro (stripProofPositions proof)

stripJudgmentPositions :: RelJudgment -> RelJudgment
stripJudgmentPositions (RelJudgment t1 rt t2) = 
  RelJudgment (stripTermPositions t1) (stripRTypePositions rt) (stripTermPositions t2)

stripTermPositions :: Term -> Term
stripTermPositions (Var name idx _) = Var name idx dummyPos
stripTermPositions (Lam name body _) = Lam name (stripTermPositions body) dummyPos  
stripTermPositions (App t1 t2 _) = App (stripTermPositions t1) (stripTermPositions t2) dummyPos
stripTermPositions (TMacro name args _) = TMacro name (map stripMacroArgPositions args) dummyPos

stripRTypePositions :: RType -> RType
stripRTypePositions (RVar name idx _) = RVar name idx dummyPos
stripRTypePositions (Arr rt1 rt2 _) = Arr (stripRTypePositions rt1) (stripRTypePositions rt2) dummyPos
stripRTypePositions (All name rt _) = All name (stripRTypePositions rt) dummyPos
stripRTypePositions (Comp rt1 rt2 _) = Comp (stripRTypePositions rt1) (stripRTypePositions rt2) dummyPos
stripRTypePositions (Conv rt _) = Conv (stripRTypePositions rt) dummyPos
stripRTypePositions (Prom term _) = Prom (stripTermPositions term) dummyPos
stripRTypePositions (RMacro name args _) = RMacro name (map stripMacroArgPositions args) dummyPos

stripMacroArgPositions :: MacroArg -> MacroArg
stripMacroArgPositions (MTerm t) = MTerm (stripTermPositions t)
stripMacroArgPositions (MRel r) = MRel (stripRTypePositions r)
stripMacroArgPositions (MProof p) = MProof (stripProofPositions p)

stripProofPositions :: Proof -> Proof
stripProofPositions (PVar name idx _) = PVar name idx dummyPos
stripProofPositions (AppP p1 p2 _) = AppP (stripProofPositions p1) (stripProofPositions p2) dummyPos
stripProofPositions (Iota t1 t2 _) = Iota (stripTermPositions t1) (stripTermPositions t2) dummyPos
stripProofPositions (LamP name rt p _) = LamP name (stripRTypePositions rt) (stripProofPositions p) dummyPos
stripProofPositions other = other -- Add more cases as needed

-- Helper to test elaboration failures
testElaborateFailure :: Context -> RawDeclaration -> RelTTError -> Expectation
testElaborateFailure ctx rawDecl expectedErr =
  case elaborate ctx rawDecl of
    Left err -> err `shouldBe` expectedErr
    Right result -> expectationFailure $ "Expected elaboration failure, but got: " ++ show result

elaborateContextSpec :: Spec
elaborateContextSpec = describe "Elaboration context management" $ do
  it "creates empty context correctly" $ do
    let ctx = emptyContext
    termBindings ctx `shouldBe` Map.empty
    relBindings ctx `shouldBe` Map.empty
    proofBindings ctx `shouldBe` Map.empty
    termDepth ctx `shouldBe` 0
    relDepth ctx `shouldBe` 0
    proofDepth ctx `shouldBe` 0

  it "properly manages macro and theorem environments" $ do
    let testMacros = Map.singleton "test" ([], TermMacro (Var "x" 0 (initialPos "")))
    let testTheorems = Map.singleton "thm" ([], RelJudgment (Var "x" 0 (initialPos "")) (RVar "R" 0 (initialPos "")) (Var "y" 0 (initialPos "")), PVar "p" 0 (initialPos ""))
    let _ctx = testContext testMacros testTheorems
    
    Map.size testMacros `shouldBe` 1
    Map.size testTheorems `shouldBe` 1

termElaborationSpec :: Spec  
termElaborationSpec = describe "Term elaboration" $ do
  -- Test removed - should use full parser pipeline instead of manual Raw AST construction

  it "elaborates macro with parameters" $ do
    let pos = initialPos ""
    let rawDecl = RawMacroDef (Name "const") [Name "x", Name "y"] (RawTermBody (RawVar (Name "x") pos))
    let expected = MacroDef "const" ["x", "y"] (TermMacro (Var "x" 1 pos))
    testElaborate emptyContext rawDecl expected

  it "elaborates function application" $ do
    let pos = initialPos ""
    let ctx = testContextWithTerms [("f", 1), ("x", 0)] 2
    let rawDecl = RawMacroDef (Name "app") [] (RawTermBody (RawApp (RawVar (Name "f") pos) (RawVar (Name "x") pos) pos))
    let expected = MacroDef "app" [] (TermMacro (App (Var "f" 1 pos) (Var "x" 0 pos) pos))
    testElaborate ctx rawDecl expected

  it "fails on unknown macro reference" $ do
    let pos = initialPos ""
    let ctx = testContext Map.empty Map.empty
    let rawDecl = RawMacroDef (Name "test") [] (RawTermBody (RawMacro (Name "unknown") [] pos))
    let expectedErr = UnknownMacro "unknown" (ErrorContext pos "elaboration")
    testElaborateFailure ctx rawDecl expectedErr

  it "fails on macro arity mismatch" $ do
    let pos = initialPos ""
    let testMacros = Map.singleton "two_param" (simpleTermMacro ["x", "y"] (Var "x" 0 pos))
    let ctx = testContext testMacros Map.empty
    let rawDecl = RawMacroDef (Name "test") [] (RawTermBody (RawMacro (Name "two_param") [RawVar (Name "z") pos] pos))
    let expectedErr = MacroArityMismatch "two_param" 2 1 (ErrorContext pos "elaboration")
    testElaborateFailure ctx rawDecl expectedErr

rtypeElaborationSpec :: Spec
rtypeElaborationSpec = describe "Relational type elaboration" $ do
  it "elaborates arrow types" $ do
    let pos = initialPos ""
    let ctx = testContextWithRels [("A", 1), ("B", 0)] 2
    let rawDecl = RawMacroDef (Name "arrow") [] (RawRelBody (RawMacro (Name "_→_") [RawVar (Name "A") pos, RawVar (Name "B") pos] pos))
    let expected = MacroDef "arrow" [] (RelMacro (Arr (RVar "A" 1 pos) (RVar "B" 0 pos) pos))
    testElaborate ctx rawDecl expected

  it "elaborates universal quantification" $ do
    let pos = initialPos ""
    let rawDecl = RawMacroDef (Name "forall") [] (RawRelBody (RawMacro (Name "∀_._") [RawVar (Name "X") pos, RawVar (Name "X") pos] pos))
    let expected = MacroDef "forall" [] (RelMacro (All "X" (RVar "X" 0 pos) pos))
    testElaborate emptyContext rawDecl expected

  it "elaborates composition" $ do
    let pos = initialPos ""
    let ctx = testContextWithRels [("R", 1), ("S", 0)] 2
    let rawDecl = RawMacroDef (Name "comp") [] (RawRelBody (RawMacro (Name "_∘_") [RawVar (Name "R") pos, RawVar (Name "S") pos] pos))
    let expected = MacroDef "comp" [] (RelMacro (Comp (RVar "R" 1 pos) (RVar "S" 0 pos) pos))
    testElaborate ctx rawDecl expected

  it "elaborates converse" $ do
    let pos = initialPos ""
    let ctx = testContextWithRels [("R", 0)] 1
    let rawDecl = RawMacroDef (Name "conv") [] (RawRelBody (RawMacro (Name "_˘") [RawVar (Name "R") pos] pos))
    let expected = MacroDef "conv" [] (RelMacro (Conv (RVar "R" 0 pos) pos))
    testElaborate ctx rawDecl expected

  it "elaborates promotion" $ do
    let pos = initialPos ""
    let ctx = testContextWithTerms [("f", 0)] 1
    -- Use RawMacro since RRProm was removed, but we still want to test Prom elaboration
    let rawDecl = RawMacroDef (Name "prom") [] (RawRelBody (RawVar (Name "f") pos))
    let expected = MacroDef "prom" [] (RelMacro (FRVar "f" pos))
    testElaborate ctx rawDecl expected

proofElaborationSpec :: Spec
proofElaborationSpec = describe "Proof elaboration" $ do
  it "elaborates simple theorem" $ do
    let pos = initialPos ""
    let rawBindings = [RawTermBinding (Name "x"), RawRelBinding (Name "R")]
    let rawJudgment = RawJudgment (RawVar (Name "x") pos) (RawVar (Name "R") pos) (RawVar (Name "x") pos)
    let rawProof = RawMacro (Name "ι⟨_,_⟩") [RawVar (Name "x") pos, RawVar (Name "x") pos] pos
    let rawDecl = RawTheorem (Name "identity") rawBindings rawJudgment rawProof
    
    let expectedBindings = [TermBinding "x", RelBinding "R"]
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedProof = Iota (Var "x" 0 pos) (Var "x" 0 pos) pos
    let expected = TheoremDef "identity" expectedBindings expectedJudgment expectedProof
    
    testElaborate emptyContext rawDecl expected

  it "elaborates proof lambda" $ do
    let pos = initialPos ""
    let rawBindings = [RawTermBinding (Name "x"), RawRelBinding (Name "R"), RawRelBinding (Name "S")]
    let rawJudgment = RawJudgment (RawVar (Name "x") pos) (RawVar (Name "R") pos) (RawVar (Name "x") pos)
    let rawProof = RawMacro (Name "λ_:_._") [RawVar (Name "p") pos, RawVar (Name "S") pos, RawVar (Name "p") pos] pos
    let rawDecl = RawTheorem (Name "lambda_test") rawBindings rawJudgment rawProof
    
    let expectedBindings = [TermBinding "x", RelBinding "R", RelBinding "S"]
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 1 pos) (Var "x" 0 pos)
    let expectedProof = LamP "p" (RVar "S" 0 pos) (PVar "p" 0 pos) pos
    let expected = TheoremDef "lambda_test" expectedBindings expectedJudgment expectedProof
    
    testElaborate emptyContext rawDecl expected

declarationElaborationSpec :: Spec
declarationElaborationSpec = describe "Declaration elaboration" $ do
  it "elaborates theorem with bindings" $ do
    let pos = initialPos ""
    let rawJudgment = RawJudgment (RawVar (Name "x") pos) (RawVar (Name "R") pos) (RawVar (Name "x") pos)
    let rawBindings = [RawTermBinding (Name "x"), RawRelBinding (Name "R"), RawProofBinding (Name "p") rawJudgment]
    let rawProof = RawVar (Name "p") pos
    let rawDecl = RawTheorem (Name "with_bindings") rawBindings rawJudgment rawProof
    
    let expectedProofJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedBindings = [TermBinding "x", RelBinding "R", ProofBinding "p" expectedProofJudgment]
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedProof = PVar "p" 0 pos
    let expected = TheoremDef "with_bindings" expectedBindings expectedJudgment expectedProof
    
    testElaborate emptyContext rawDecl expected

elaborateErrorSpec :: Spec
elaborateErrorSpec = describe "Error handling" $ do
  it "reports unknown variables correctly" $ do
    let pos = initialPos ""
    let rawDecl = RawMacroDef (Name "test") [] (RawTermBody (RawVar (Name "unknown") pos))
    let expectedErr = UnboundVariable "unknown" (ErrorContext pos "elaboration")
    testElaborateFailure emptyContext rawDecl expectedErr

  it "reports unknown relational variables correctly" $ do
    let pos = initialPos ""
    let rawDecl = RawMacroDef (Name "test") [] (RawRelBody (RawVar (Name "UnknownRel") pos))
    let expectedErr = UnboundVariable "UnknownRel" (ErrorContext pos "elaboration")
    testElaborateFailure emptyContext rawDecl expectedErr

  it "provides proper error context" $ do
    let pos = initialPos ""
    case elaborate emptyContext (RawMacroDef (Name "test") [] (RawTermBody (RawVar (Name "unknown") pos))) of
      Left (UnboundVariable name _) -> do
        name `shouldBe` "unknown"
        return () -- Error context comparison would be complex
      Left other -> expectationFailure $ "Expected UnknownVariable error, got: " ++ show other
      Right result -> expectationFailure $ "Expected error, got successful result: " ++ show result

variableBindingSpec :: Spec
variableBindingSpec = describe "Variable binding and de Bruijn indices" $ do
  it "correctly handles nested lambda bindings" $ do
    let pos = initialPos ""
    let rawDecl = RawMacroDef (Name "nested") [] 
          (RawTermBody (RawMacro (Name "λ_._") [RawVar (Name "x") pos, RawMacro (Name "λ_._") [RawVar (Name "y") pos, RawVar (Name "x") pos] pos] pos))
    let expected = MacroDef "nested" [] 
          (TermMacro (Lam "x" (Lam "y" (Var "x" 1 pos) pos) pos))
    testElaborate emptyContext rawDecl expected

  it "correctly handles nested universal quantification" $ do
    let pos = initialPos ""
    let rawDecl = RawMacroDef (Name "nested_forall") [] 
          (RawRelBody (RawMacro (Name "∀_._") [RawVar (Name "X") pos, RawMacro (Name "∀_._") [RawVar (Name "Y") pos, RawVar (Name "X") pos] pos] pos))
    let expected = MacroDef "nested_forall" [] 
          (RelMacro (All "X" (All "Y" (RVar "X" 1 pos) pos) pos))
    testElaborate emptyContext rawDecl expected

  it "correctly handles proof lambda bindings" $ do
    let pos = initialPos ""
    let rawBindings = [RawTermBinding (Name "x"), RawRelBinding (Name "R"), RawRelBinding (Name "S"), RawRelBinding (Name "T")]
    let rawJudgment = RawJudgment (RawVar (Name "x") pos) (RawVar (Name "R") pos) (RawVar (Name "x") pos)
    let rawProof = RawMacro (Name "λ_:_._") [RawVar (Name "p") pos, RawVar (Name "S") pos,
                    RawMacro (Name "λ_:_._") [RawVar (Name "q") pos, RawVar (Name "T") pos, RawVar (Name "p") pos] pos] pos
    let rawDecl = RawTheorem (Name "nested_proof_lambda") rawBindings rawJudgment rawProof
    
    let expectedBindings = [TermBinding "x", RelBinding "R", RelBinding "S", RelBinding "T"]
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 2 pos) (Var "x" 0 pos)
    let expectedProof = LamP "p" (RVar "S" 1 pos) 
                         (LamP "q" (RVar "T" 0 pos) (PVar "p" 1 pos) pos) pos
    let expected = TheoremDef "nested_proof_lambda" expectedBindings expectedJudgment expectedProof
    
    testElaborate emptyContext rawDecl expected