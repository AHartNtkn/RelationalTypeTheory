{-# LANGUAGE OverloadedStrings #-}

module ElaborateSpec (spec) where

import qualified Data.Map as Map
import Text.Megaparsec (initialPos)

import Elaborate (FrontEndError(..), ElaborateError(..), ElaborateContext(..), elaborate, emptyElaborateContext)
import Lib
import qualified RawAst as Raw
import Test.Hspec

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
testContext :: MacroEnvironment -> TheoremEnvironment -> ElaborateContext
testContext testMacroEnv testTheoremEnv = ElaborateContext
  { macroEnv = testMacroEnv
  , theoremEnv = testTheoremEnv
  , termDepth = 0
  , relDepth = 0
  , proofDepth = 0
  , boundVars = Map.empty
  , boundRelVars = Map.empty
  , boundProofVars = Map.empty
  }

-- Helper to create test context with bound term variables
testContextWithTerms :: [(String, Int)] -> Int -> ElaborateContext
testContextWithTerms vars depth = emptyElaborateContext
  { boundVars = Map.fromList vars
  , termDepth = depth
  }

-- Helper to create test context with bound relational variables  
testContextWithRels :: [(String, Int)] -> Int -> ElaborateContext
testContextWithRels vars depth = emptyElaborateContext
  { boundRelVars = Map.fromList vars
  , relDepth = depth
  }

-- Helper to test successful elaboration (ignoring positions)
testElaborate :: ElaborateContext -> Raw.RawDeclaration -> Declaration -> Expectation
testElaborate ctx rawDecl expected =
  case elaborate ctx rawDecl of
    Left err -> expectationFailure $ "Elaboration failed: " ++ show err
    Right result -> stripPositions result `shouldBe` stripPositions expected

-- Strip positions from declarations for testing
stripPositions :: Declaration -> Declaration
stripPositions (MacroDef name params body) = MacroDef name params (stripMacroBodyPositions body)
stripPositions (TheoremDef name bindings judgment proof) = 
  TheoremDef name bindings (stripJudgmentPositions judgment) (stripProofPositions proof)

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

-- Helper to test elaboration failures
testElaborateFailure :: ElaborateContext -> Raw.RawDeclaration -> ElaborateError -> Expectation
testElaborateFailure ctx rawDecl expectedErr =
  case elaborate ctx rawDecl of
    Left (ElabError err) -> err `shouldBe` expectedErr
    Left (ParseError _) -> expectationFailure "Expected elaboration error, but got parse error"
    Right result -> expectationFailure $ "Expected elaboration failure, but got: " ++ show result

elaborateContextSpec :: Spec
elaborateContextSpec = describe "Elaboration context management" $ do
  it "creates empty context correctly" $ do
    let ctx = emptyElaborateContext
    boundVars ctx `shouldBe` Map.empty
    boundRelVars ctx `shouldBe` Map.empty
    boundProofVars ctx `shouldBe` Map.empty
    termDepth ctx `shouldBe` 0
    relDepth ctx `shouldBe` 0
    proofDepth ctx `shouldBe` 0

  it "properly manages macro and theorem environments" $ do
    let testMacroEnv = MacroEnvironment (Map.singleton "test" ([], TermMacro (Var "x" 0 (initialPos "")))) Map.empty
    let testTheoremEnv = TheoremEnvironment (Map.singleton "thm" ([], RelJudgment (Var "x" 0 (initialPos "")) (RVar "R" 0 (initialPos "")) (Var "y" 0 (initialPos "")), PVar "p" 0 (initialPos "")))
    let ctx = testContext testMacroEnv testTheoremEnv
    
    Map.size (macroDefinitions testMacroEnv) `shouldBe` 1
    Map.size (theoremDefinitions testTheoremEnv) `shouldBe` 1

termElaborationSpec :: Spec  
termElaborationSpec = describe "Term elaboration" $ do
  it "elaborates simple macro definition" $ do
    let pos = initialPos ""
    let rawDecl = Raw.RawMacro (Raw.Name "id") [] (Raw.RawTermBody (Raw.RTLam (Raw.Name "x") (Raw.RTVar (Raw.Name "x") pos) pos))
    let expected = MacroDef "id" [] (TermMacro (Lam "x" (Var "x" 0 pos) pos))
    testElaborate emptyElaborateContext rawDecl expected

  it "elaborates macro with parameters" $ do
    let pos = initialPos ""
    let rawDecl = Raw.RawMacro (Raw.Name "const") [Raw.Name "x", Raw.Name "y"] (Raw.RawTermBody (Raw.RTVar (Raw.Name "x") pos))
    let expected = MacroDef "const" ["x", "y"] (TermMacro (Var "x" 1 pos))
    testElaborate emptyElaborateContext rawDecl expected

  it "elaborates function application" $ do
    let pos = initialPos ""
    let ctx = testContextWithTerms [("f", 1), ("x", 0)] 2
    let rawDecl = Raw.RawMacro (Raw.Name "app") [] (Raw.RawTermBody (Raw.RTApp (Raw.RTVar (Raw.Name "f") pos) (Raw.RTVar (Raw.Name "x") pos) pos))
    let expected = MacroDef "app" [] (TermMacro (App (Var "f" 1 pos) (Var "x" 0 pos) pos))
    testElaborate ctx rawDecl expected

  it "fails on unknown macro reference" $ do
    let pos = initialPos ""
    let testMacroEnv = MacroEnvironment Map.empty Map.empty
    let ctx = testContext testMacroEnv (TheoremEnvironment Map.empty)
    let rawDecl = Raw.RawMacro (Raw.Name "test") [] (Raw.RawTermBody (Raw.RTMacro (Raw.Name "unknown") [] pos))
    let expectedErr = UnknownMacro "unknown" pos
    testElaborateFailure ctx rawDecl expectedErr

  it "fails on macro arity mismatch" $ do
    let pos = initialPos ""
    let testMacroEnv = MacroEnvironment (Map.singleton "two_param" (["x", "y"], TermMacro (Var "x" 0 pos))) Map.empty
    let ctx = testContext testMacroEnv (TheoremEnvironment Map.empty)
    let rawDecl = Raw.RawMacro (Raw.Name "test") [] (Raw.RawTermBody (Raw.RTMacro (Raw.Name "two_param") [Raw.RTVar (Raw.Name "z") pos] pos))
    let expectedErr = MacroArityMismatch "two_param" 2 1 pos
    testElaborateFailure ctx rawDecl expectedErr

rtypeElaborationSpec :: Spec
rtypeElaborationSpec = describe "Relational type elaboration" $ do
  it "elaborates arrow types" $ do
    let pos = initialPos ""
    let ctx = testContextWithRels [("A", 1), ("B", 0)] 2
    let rawDecl = Raw.RawMacro (Raw.Name "arrow") [] (Raw.RawRelBody (Raw.RRArr (Raw.RRVar (Raw.Name "A") pos) (Raw.RRVar (Raw.Name "B") pos) pos))
    let expected = MacroDef "arrow" [] (RelMacro (Arr (RVar "A" 1 pos) (RVar "B" 0 pos) pos))
    testElaborate ctx rawDecl expected

  it "elaborates universal quantification" $ do
    let pos = initialPos ""
    let rawDecl = Raw.RawMacro (Raw.Name "forall") [] (Raw.RawRelBody (Raw.RRAll (Raw.Name "X") (Raw.RRVar (Raw.Name "X") pos) pos))
    let expected = MacroDef "forall" [] (RelMacro (All "X" (RVar "X" 0 pos) pos))
    testElaborate emptyElaborateContext rawDecl expected

  it "elaborates composition" $ do
    let pos = initialPos ""
    let ctx = testContextWithRels [("R", 1), ("S", 0)] 2
    let rawDecl = Raw.RawMacro (Raw.Name "comp") [] (Raw.RawRelBody (Raw.RRComp (Raw.RRVar (Raw.Name "R") pos) (Raw.RRVar (Raw.Name "S") pos) pos))
    let expected = MacroDef "comp" [] (RelMacro (Comp (RVar "R" 1 pos) (RVar "S" 0 pos) pos))
    testElaborate ctx rawDecl expected

  it "elaborates converse" $ do
    let pos = initialPos ""
    let ctx = testContextWithRels [("R", 0)] 1
    let rawDecl = Raw.RawMacro (Raw.Name "conv") [] (Raw.RawRelBody (Raw.RRConv (Raw.RRVar (Raw.Name "R") pos) pos))
    let expected = MacroDef "conv" [] (RelMacro (Conv (RVar "R" 0 pos) pos))
    testElaborate ctx rawDecl expected

  it "elaborates promotion" $ do
    let pos = initialPos ""
    let ctx = testContextWithTerms [("f", 0)] 1
    let rawDecl = Raw.RawMacro (Raw.Name "prom") [] (Raw.RawRelBody (Raw.RRProm (Raw.RTVar (Raw.Name "f") pos) pos))
    let expected = MacroDef "prom" [] (RelMacro (Prom (Var "f" 0 pos) pos))
    testElaborate ctx rawDecl expected

proofElaborationSpec :: Spec
proofElaborationSpec = describe "Proof elaboration" $ do
  it "elaborates simple theorem" $ do
    let pos = initialPos ""
    let rawBindings = [Raw.RawTermBinding (Raw.Name "x"), Raw.RawRelBinding (Raw.Name "R")]
    let rawJudgment = Raw.RawJudgment (Raw.RTVar (Raw.Name "x") pos) (Raw.RRVar (Raw.Name "R") pos) (Raw.RTVar (Raw.Name "x") pos)
    let rawProof = Raw.RPIota (Raw.RTVar (Raw.Name "x") pos) (Raw.RTVar (Raw.Name "x") pos) pos
    let rawDecl = Raw.RawTheorem (Raw.Name "identity") rawBindings rawJudgment rawProof
    
    let expectedBindings = [TermBinding "x", RelBinding "R"]
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedProof = Iota (Var "x" 0 pos) (Var "x" 0 pos) pos
    let expected = TheoremDef "identity" expectedBindings expectedJudgment expectedProof
    
    testElaborate emptyElaborateContext rawDecl expected

  it "elaborates proof lambda" $ do
    let pos = initialPos ""
    let rawBindings = [Raw.RawTermBinding (Raw.Name "x"), Raw.RawRelBinding (Raw.Name "R"), Raw.RawRelBinding (Raw.Name "S")]
    let rawJudgment = Raw.RawJudgment (Raw.RTVar (Raw.Name "x") pos) (Raw.RRVar (Raw.Name "R") pos) (Raw.RTVar (Raw.Name "x") pos)
    let rawProof = Raw.RPLamP (Raw.Name "p") (Raw.RRVar (Raw.Name "S") pos) (Raw.RPVar (Raw.Name "p") pos) pos
    let rawDecl = Raw.RawTheorem (Raw.Name "lambda_test") rawBindings rawJudgment rawProof
    
    let expectedBindings = [TermBinding "x", RelBinding "R", RelBinding "S"]
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 1 pos) (Var "x" 0 pos)
    let expectedProof = LamP "p" (RVar "S" 0 pos) (PVar "p" 0 pos) pos
    let expected = TheoremDef "lambda_test" expectedBindings expectedJudgment expectedProof
    
    testElaborate emptyElaborateContext rawDecl expected

declarationElaborationSpec :: Spec
declarationElaborationSpec = describe "Declaration elaboration" $ do
  it "elaborates theorem with bindings" $ do
    let pos = initialPos ""
    let rawJudgment = Raw.RawJudgment (Raw.RTVar (Raw.Name "x") pos) (Raw.RRVar (Raw.Name "R") pos) (Raw.RTVar (Raw.Name "x") pos)
    let rawBindings = [Raw.RawTermBinding (Raw.Name "x"), Raw.RawRelBinding (Raw.Name "R"), Raw.RawProofBinding (Raw.Name "p") rawJudgment]
    let rawProof = Raw.RPVar (Raw.Name "p") pos
    let rawDecl = Raw.RawTheorem (Raw.Name "with_bindings") rawBindings rawJudgment rawProof
    
    let expectedProofJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedBindings = [TermBinding "x", RelBinding "R", ProofBinding "p" expectedProofJudgment]
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos)
    let expectedProof = PVar "p" 0 pos
    let expected = TheoremDef "with_bindings" expectedBindings expectedJudgment expectedProof
    
    testElaborate emptyElaborateContext rawDecl expected

elaborateErrorSpec :: Spec
elaborateErrorSpec = describe "Error handling" $ do
  it "reports unknown variables correctly" $ do
    let pos = initialPos ""
    let rawDecl = Raw.RawMacro (Raw.Name "test") [] (Raw.RawTermBody (Raw.RTVar (Raw.Name "unknown") pos))
    let expectedErr = UnknownVariable "unknown" pos
    testElaborateFailure emptyElaborateContext rawDecl expectedErr

  it "reports unknown relational variables correctly" $ do
    let pos = initialPos ""
    let rawDecl = Raw.RawMacro (Raw.Name "test") [] (Raw.RawRelBody (Raw.RRVar (Raw.Name "UnknownRel") pos))
    let expectedErr = UnknownVariable "UnknownRel" pos
    testElaborateFailure emptyElaborateContext rawDecl expectedErr

  it "provides proper error context" $ do
    let pos = initialPos ""
    case elaborate emptyElaborateContext (Raw.RawMacro (Raw.Name "test") [] (Raw.RawTermBody (Raw.RTVar (Raw.Name "unknown") pos))) of
      Left (ElabError (UnknownVariable name errPos)) -> do
        name `shouldBe` "unknown"
        errPos `shouldBe` pos
      Left other -> expectationFailure $ "Expected UnknownVariable error, got: " ++ show other
      Right result -> expectationFailure $ "Expected error, got successful result: " ++ show result

variableBindingSpec :: Spec
variableBindingSpec = describe "Variable binding and de Bruijn indices" $ do
  it "correctly handles nested lambda bindings" $ do
    let pos = initialPos ""
    let rawDecl = Raw.RawMacro (Raw.Name "nested") [] 
          (Raw.RawTermBody (Raw.RTLam (Raw.Name "x") (Raw.RTLam (Raw.Name "y") (Raw.RTVar (Raw.Name "x") pos) pos) pos))
    let expected = MacroDef "nested" [] 
          (TermMacro (Lam "x" (Lam "y" (Var "x" 1 pos) pos) pos))
    testElaborate emptyElaborateContext rawDecl expected

  it "correctly handles nested universal quantification" $ do
    let pos = initialPos ""
    let rawDecl = Raw.RawMacro (Raw.Name "nested_forall") [] 
          (Raw.RawRelBody (Raw.RRAll (Raw.Name "X") (Raw.RRAll (Raw.Name "Y") (Raw.RRVar (Raw.Name "X") pos) pos) pos))
    let expected = MacroDef "nested_forall" [] 
          (RelMacro (All "X" (All "Y" (RVar "X" 1 pos) pos) pos))
    testElaborate emptyElaborateContext rawDecl expected

  it "correctly handles proof lambda bindings" $ do
    let pos = initialPos ""
    let rawBindings = [Raw.RawTermBinding (Raw.Name "x"), Raw.RawRelBinding (Raw.Name "R"), Raw.RawRelBinding (Raw.Name "S"), Raw.RawRelBinding (Raw.Name "T")]
    let rawJudgment = Raw.RawJudgment (Raw.RTVar (Raw.Name "x") pos) (Raw.RRVar (Raw.Name "R") pos) (Raw.RTVar (Raw.Name "x") pos)
    let rawProof = Raw.RPLamP (Raw.Name "p") (Raw.RRVar (Raw.Name "S") pos) 
                    (Raw.RPLamP (Raw.Name "q") (Raw.RRVar (Raw.Name "T") pos) (Raw.RPVar (Raw.Name "p") pos) pos) pos
    let rawDecl = Raw.RawTheorem (Raw.Name "nested_proof_lambda") rawBindings rawJudgment rawProof
    
    let expectedBindings = [TermBinding "x", RelBinding "R", RelBinding "S", RelBinding "T"]
    let expectedJudgment = RelJudgment (Var "x" 0 pos) (RVar "R" 2 pos) (Var "x" 0 pos)
    let expectedProof = LamP "p" (RVar "S" 1 pos) 
                         (LamP "q" (RVar "T" 0 pos) (PVar "p" 1 pos) pos) pos
    let expected = TheoremDef "nested_proof_lambda" expectedBindings expectedJudgment expectedProof
    
    testElaborate emptyElaborateContext rawDecl expected