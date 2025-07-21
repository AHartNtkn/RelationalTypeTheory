module ComprehensiveTheoremAppSpec where

import Test.Hspec
import Lib
import ProofChecker
import Context
import Errors
import Text.Megaparsec (SourcePos, initialPos)
import qualified Data.Map as Map

-- Helper to create dummy source position
dummyPos :: SourcePos
dummyPos = initialPos "test"

-- Helper to create empty contexts
emptyCtx :: TypingContext
emptyCtx = TypingContext Map.empty Map.empty Map.empty

emptyMacroEnv :: MacroEnvironment
emptyMacroEnv = MacroEnvironment Map.empty

spec :: Spec
spec = describe "Comprehensive Theorem Application Tests" $ do
  
  describe "Mixed argument type theorem applications" $ do
    it "handles theorem with term, relation, and proof arguments in order (SUCCESS)" $ do
      let theoremName = "mixed_args_thm"
          -- Theorem: ⊢ mixed_args_thm (x : Term) (R : Rel) (p : x [R] x) : x [R ∘ R] x
          theoremBindings = [TermBinding "x", RelBinding "R", ProofBinding "p" (RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "x" 0 dummyPos))]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (Comp (RVar "R" 0 dummyPos) (RVar "R" 0 dummyPos) dummyPos) (Var "x" 0 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Add an axiom theorem that provides the needed proof: ⊢ axiom_proof (x : Term) (R : Rel) : x [R] x
          axiomTheoremEnv = extendTheoremEnvironment "axiom_proof" 
            [TermBinding "x", RelBinding "R"]
            (RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "x" 0 dummyPos))
            (PVar "axiom" 0 dummyPos) theoremEnv
          
          -- Application: mixed_args_thm a S (axiom_proof a S)
          argTerm = Var "a" 0 dummyPos
          argRel = RVar "S" 0 dummyPos
          -- Use the axiom proof as the proof argument - this will correctly provide (a [S] a)
          proofArg = PTheoremApp "axiom_proof" [TermArg argTerm, RelArg argRel] dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argTerm, RelArg argRel, ProofArg proofArg] dummyPos
          
          -- Expected result: a [S ∘ S] a
          expectedJudgment = RelJudgment argTerm (Comp argRel argRel dummyPos) argTerm
      
      case inferProofType emptyCtx emptyMacroEnv axiomTheoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

    it "fails when proof argument type doesn't match after substitution (DESIGNED FAILURE)" $ do
      let theoremName = "mixed_args_thm"
          -- Same theorem: ⊢ mixed_args_thm (x : Term) (R : Rel) (p : x [R] x) : x [R ∘ R] x
          theoremBindings = [TermBinding "x", RelBinding "R", ProofBinding "p" (RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "x" 0 dummyPos))]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (Comp (RVar "R" 0 dummyPos) (RVar "R" 0 dummyPos) dummyPos) (Var "x" 0 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Add an axiom theorem with WRONG type: ⊢ wrong_axiom (x : Term) (R : Rel) : x [R ∘ R] x
          wrongAxiomEnv = extendTheoremEnvironment "wrong_axiom" 
            [TermBinding "x", RelBinding "R"]
            (RelJudgment (Var "x" 0 dummyPos) (Comp (RVar "R" 0 dummyPos) (RVar "R" 0 dummyPos) dummyPos) (Var "x" 0 dummyPos))
            (PVar "wrong_axiom" 0 dummyPos) theoremEnv
          
          -- Application: mixed_args_thm a S (wrong_axiom a S)
          argTerm = Var "a" 0 dummyPos
          argRel = RVar "S" 0 dummyPos
          -- This will provide (a [S ∘ S] a) but theorem expects (a [S] a) after substitution
          wrongProofArg = PTheoremApp "wrong_axiom" [TermArg argTerm, RelArg argRel] dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argTerm, RelArg argRel, ProofArg wrongProofArg] dummyPos
      
      case inferProofType emptyCtx emptyMacroEnv wrongAxiomEnv theoremApp of
        Left (ProofTypingError _ _ _ _) -> return () -- Expected failure due to substitution type mismatch
        Left err -> expectationFailure $ "Expected ProofTypingError, got: " ++ show err
        Right _ -> expectationFailure "Expected type checking failure due to proof argument type mismatch after substitution"

    it "handles theorem with interleaved argument types" $ do
      let theoremName = "interleaved_thm"
          -- Theorem: ⊢ interleaved_thm (R : Rel) (x : Term) (S : Rel) (y : Term) : x [R ∘ S] y
          theoremBindings = [RelBinding "R", TermBinding "x", RelBinding "S", TermBinding "y"]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (Comp (RVar "R" 0 dummyPos) (RVar "S" 0 dummyPos) dummyPos) (Var "y" 1 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Application: interleaved_thm T a U b
          argRel1 = RVar "T" 0 dummyPos
          argTerm1 = Var "a" 0 dummyPos
          argRel2 = RVar "U" 1 dummyPos
          argTerm2 = Var "b" 1 dummyPos
          theoremApp = PTheoremApp theoremName [RelArg argRel1, TermArg argTerm1, RelArg argRel2, TermArg argTerm2] dummyPos
          
          -- Expected result: a [T ∘ U] b
          expectedJudgment = RelJudgment argTerm1 (Comp argRel1 argRel2 dummyPos) argTerm2
      
      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

    it "handles theorem with multiple proof arguments (SUCCESS)" $ do
      let theoremName = "multi_proof_thm"
          -- Theorem: ⊢ multi_proof_thm (x : Term) (p1 : x [λy.y] x) (p2 : x [λy.y] x) : x [λy.y ∘ λy.y] x
          idRel = Prom (Lam "y" (Var "y" 0 dummyPos) dummyPos) dummyPos
          theoremBindings = [TermBinding "x", 
                           ProofBinding "p1" (RelJudgment (Var "x" 0 dummyPos) idRel (Var "x" 0 dummyPos)),
                           ProofBinding "p2" (RelJudgment (Var "x" 0 dummyPos) idRel (Var "x" 0 dummyPos))]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (Comp idRel idRel dummyPos) (Var "x" 0 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Add axiom theorem for identity proofs: ⊢ id_proof (x : Term) : x [λy.y] x
          idTheoremEnv = extendTheoremEnvironment "id_proof"
            [TermBinding "x"]
            (RelJudgment (Var "x" 0 dummyPos) idRel (Var "x" 0 dummyPos))
            (PVar "id_axiom" 0 dummyPos) theoremEnv
          
          -- Application: multi_proof_thm a (id_proof a) (id_proof a)
          argTerm = Var "a" 0 dummyPos
          proofArg1 = PTheoremApp "id_proof" [TermArg argTerm] dummyPos
          proofArg2 = PTheoremApp "id_proof" [TermArg argTerm] dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argTerm, ProofArg proofArg1, ProofArg proofArg2] dummyPos
          
          -- Expected result: a [λy.y ∘ λy.y] a
          expectedJudgment = RelJudgment argTerm (Comp idRel idRel dummyPos) argTerm
      
      case inferProofType emptyCtx emptyMacroEnv idTheoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

    it "fails when multiple proof arguments have wrong types after substitution (DESIGNED FAILURE)" $ do
      let theoremName = "multi_proof_thm"
          -- Same theorem: ⊢ multi_proof_thm (x : Term) (p1 : x [λy.y] x) (p2 : x [λy.y] x) : x [λy.y ∘ λy.y] x
          idRel = Prom (Lam "y" (Var "y" 0 dummyPos) dummyPos) dummyPos
          theoremBindings = [TermBinding "x", 
                           ProofBinding "p1" (RelJudgment (Var "x" 0 dummyPos) idRel (Var "x" 0 dummyPos)),
                           ProofBinding "p2" (RelJudgment (Var "x" 0 dummyPos) idRel (Var "x" 0 dummyPos))]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (Comp idRel idRel dummyPos) (Var "x" 0 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Add axiom theorem with WRONG type: ⊢ wrong_id_proof (x : Term) : x [λy.y ∘ λy.y] x
          wrongIdTheoremEnv = extendTheoremEnvironment "wrong_id_proof"
            [TermBinding "x"]
            (RelJudgment (Var "x" 0 dummyPos) (Comp idRel idRel dummyPos) (Var "x" 0 dummyPos))
            (PVar "wrong_id_axiom" 0 dummyPos) theoremEnv
          
          -- Application: multi_proof_thm a (wrong_id_proof a) (wrong_id_proof a)
          argTerm = Var "a" 0 dummyPos
          -- These provide (a [λy.y ∘ λy.y] a) but theorem expects (a [λy.y] a) for each proof argument
          wrongProofArg1 = PTheoremApp "wrong_id_proof" [TermArg argTerm] dummyPos
          wrongProofArg2 = PTheoremApp "wrong_id_proof" [TermArg argTerm] dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argTerm, ProofArg wrongProofArg1, ProofArg wrongProofArg2] dummyPos
      
      case inferProofType emptyCtx emptyMacroEnv wrongIdTheoremEnv theoremApp of
        Left (ProofTypingError _ _ _ _) -> return () -- Expected failure - first proof argument type mismatch
        Left err -> expectationFailure $ "Expected ProofTypingError for first proof argument, got: " ++ show err
        Right _ -> expectationFailure "Expected type checking failure due to proof argument type mismatch"

  describe "Substitution validation tests" $ do
    it "correctly substitutes term arguments in return judgment" $ do
      let theoremName = "subst_test_thm"
          -- Theorem: ⊢ subst_test_thm (f : Term) (x : Term) : (f x) [λy.y] (f x)
          theoremBindings = [TermBinding "f", TermBinding "x"]
          theoremJudgment = RelJudgment 
            (App (Var "f" 0 dummyPos) (Var "x" 1 dummyPos) dummyPos) 
            (Prom (Lam "y" (Var "y" 0 dummyPos) dummyPos) dummyPos) 
            (App (Var "f" 0 dummyPos) (Var "x" 1 dummyPos) dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Application: subst_test_thm g a
          argF = Var "g" 0 dummyPos
          argX = Var "a" 0 dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argF, TermArg argX] dummyPos
          
          -- Expected result: (g a) [λy.y] (g a)
          expectedJudgment = RelJudgment 
            (App argF argX dummyPos) 
            (Prom (Lam "y" (Var "y" 0 dummyPos) dummyPos) dummyPos) 
            (App argF argX dummyPos)
      
      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

    it "correctly substitutes relation arguments in return judgment" $ do
      let theoremName = "rel_subst_thm"
          -- Theorem: ⊢ rel_subst_thm (R : Rel) (S : Rel) (x : Term) : x [R ∘ S ∘ R˘] x
          theoremBindings = [RelBinding "R", RelBinding "S", TermBinding "x"]
          theoremJudgment = RelJudgment 
            (Var "x" 0 dummyPos)
            (Comp (Comp (RVar "R" 0 dummyPos) (RVar "S" 0 dummyPos) dummyPos) (Conv (RVar "R" 0 dummyPos) dummyPos) dummyPos)
            (Var "x" 0 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Application: rel_subst_thm T U a
          argR = RVar "T" 0 dummyPos
          argS = RVar "U" 1 dummyPos
          argX = Var "a" 0 dummyPos
          theoremApp = PTheoremApp theoremName [RelArg argR, RelArg argS, TermArg argX] dummyPos
          
          -- Expected result: a [T ∘ U ∘ T˘] a
          expectedJudgment = RelJudgment 
            argX
            (Comp (Comp argR argS dummyPos) (Conv argR dummyPos) dummyPos)
            argX
      
      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

    it "validates proof argument type matches substituted expectation (SUCCESS)" $ do
      let theoremName = "proof_validation_thm"
          -- Theorem: ⊢ proof_validation_thm (f : Term) (R : Rel) (p : (f a) [R] (f a)) : (f a) [R ∘ R] (f a)
          termA = Var "a" 0 dummyPos
          appFA = App (Var "f" 0 dummyPos) termA dummyPos
          theoremBindings = [TermBinding "f", RelBinding "R", ProofBinding "p" (RelJudgment appFA (RVar "R" 0 dummyPos) appFA)]
          theoremJudgment = RelJudgment appFA (Comp (RVar "R" 0 dummyPos) (RVar "R" 0 dummyPos) dummyPos) appFA
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Add axiom theorem: ⊢ axiom_rel_proof (x : Term) (R : Rel) : x [R] x
          axiomRelTheoremEnv = extendTheoremEnvironment "axiom_rel_proof"
            [TermBinding "x", RelBinding "R"]
            (RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "x" 0 dummyPos))
            (PVar "axiom_rel" 0 dummyPos) theoremEnv
          
          -- Application: proof_validation_thm g S (axiom_rel_proof (g a) S)
          argF = Var "g" 0 dummyPos
          argR = RVar "S" 0 dummyPos
          -- Create proof with correct type: (g a) [S] (g a)
          correctProof = PTheoremApp "axiom_rel_proof" [TermArg (App argF termA dummyPos), RelArg argR] dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argF, RelArg argR, ProofArg correctProof] dummyPos
          
          -- Expected result: (g a) [S ∘ S] (g a)
          expectedJudgment = RelJudgment (App argF termA dummyPos) (Comp argR argR dummyPos) (App argF termA dummyPos)
      
      case inferProofType emptyCtx emptyMacroEnv axiomRelTheoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

    it "fails when proof argument uses wrong term in substitution (DESIGNED FAILURE)" $ do
      let theoremName = "proof_validation_thm"
          -- Same theorem: ⊢ proof_validation_thm (f : Term) (R : Rel) (p : (f a) [R] (f a)) : (f a) [R ∘ R] (f a)
          termA = Var "a" 0 dummyPos
          appFA = App (Var "f" 0 dummyPos) termA dummyPos
          theoremBindings = [TermBinding "f", RelBinding "R", ProofBinding "p" (RelJudgment appFA (RVar "R" 0 dummyPos) appFA)]
          theoremJudgment = RelJudgment appFA (Comp (RVar "R" 0 dummyPos) (RVar "R" 0 dummyPos) dummyPos) appFA
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Add axiom theorem: ⊢ axiom_rel_proof (x : Term) (R : Rel) : x [R] x
          axiomRelTheoremEnv = extendTheoremEnvironment "axiom_rel_proof"
            [TermBinding "x", RelBinding "R"]
            (RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "x" 0 dummyPos))
            (PVar "axiom_rel" 0 dummyPos) theoremEnv
          
          -- Application: proof_validation_thm g S (axiom_rel_proof (g b) S)  -- Note: using 'b' instead of 'a'
          argF = Var "g" 0 dummyPos
          argR = RVar "S" 0 dummyPos
          termB = Var "b" 1 dummyPos  -- Different term!
          -- This proof provides (g b) [S] (g b) but theorem expects (g a) [S] (g a) after substitution
          wrongProof = PTheoremApp "axiom_rel_proof" [TermArg (App argF termB dummyPos), RelArg argR] dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argF, RelArg argR, ProofArg wrongProof] dummyPos
      
      case inferProofType emptyCtx emptyMacroEnv axiomRelTheoremEnv theoremApp of
        Left (ProofTypingError _ _ _ _) -> return () -- Expected failure - proof uses wrong term
        Left err -> expectationFailure $ "Expected ProofTypingError for wrong term in proof, got: " ++ show err
        Right _ -> expectationFailure "Expected type checking failure due to proof using wrong term"

  describe "Type checking failure tests" $ do
    it "rejects proof argument with wrong substituted type" $ do
      let theoremName = "strict_validation_thm"
          -- Theorem: ⊢ strict_validation_thm (f : Term) (R : Rel) (p : (f x) [R] (f x)) : (f x) [R] (f x)
          termX = Var "x" 0 dummyPos
          appFX = App (Var "f" 0 dummyPos) termX dummyPos
          theoremBindings = [TermBinding "f", RelBinding "R", ProofBinding "p" (RelJudgment appFX (RVar "R" 0 dummyPos) appFX)]
          theoremJudgment = RelJudgment appFX (RVar "R" 0 dummyPos) appFX
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Application: strict_validation_thm g S wrong_proof
          argF = Var "g" 0 dummyPos
          argR = RVar "S" 0 dummyPos
          -- Create proof with WRONG type: uses 'y' instead of 'x', so we get (g y) [S] (g y) instead of (g x) [S] (g x)
          termY = Var "y" 0 dummyPos
          wrongProof = Iota (App argF termY dummyPos) (App argF termY dummyPos) dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argF, RelArg argR, ProofArg wrongProof] dummyPos
      
      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Left (ProofTypingError _ _ _ _) -> return () -- Expected failure
        Left err -> expectationFailure $ "Expected ProofTypingError, got: " ++ show err
        Right _ -> expectationFailure "Expected type checking failure, but got success"

    it "rejects proof argument with wrong relation in substituted type" $ do
      let theoremName = "relation_validation_thm"
          -- Theorem: ⊢ relation_validation_thm (f : Term) (R : Rel) (p : (f t) [R ∘ R] (f t)) : (f t) [R ∘ R ∘ R] (f t)
          termT = Var "t" 0 dummyPos
          appFT = App (Var "f" 0 dummyPos) termT dummyPos
          compRR = Comp (RVar "R" 0 dummyPos) (RVar "R" 0 dummyPos) dummyPos
          theoremBindings = [TermBinding "f", RelBinding "R", ProofBinding "p" (RelJudgment appFT compRR appFT)]
          theoremJudgment = RelJudgment appFT (Comp compRR (RVar "R" 0 dummyPos) dummyPos) appFT
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Application: relation_validation_thm h T wrong_proof
          argF = Var "h" 0 dummyPos
          argR = RVar "T" 0 dummyPos
          -- Create proof with WRONG relation: uses T instead of T ∘ T, so we get (h t) [T] (h t) instead of (h t) [T ∘ T] (h t)
          wrongProof = Iota (App argF termT dummyPos) (App argF termT dummyPos) dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argF, RelArg argR, ProofArg wrongProof] dummyPos
      
      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Left (ProofTypingError _ _ _ _) -> return () -- Expected failure
        Left err -> expectationFailure $ "Expected ProofTypingError, got: " ++ show err
        Right _ -> expectationFailure "Expected type checking failure, but got success"

    it "rejects theorem application with too many arguments" $ do
      let theoremName = "limited_args_thm"
          -- Theorem with only 2 parameters: ⊢ limited_args_thm (x : Term) (R : Rel) : x [R] x
          theoremBindings = [TermBinding "x", RelBinding "R"]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (RVar "R" 0 dummyPos) (Var "x" 0 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Application with too many arguments: limited_args_thm a S extra_proof
          argTerm = Var "a" 0 dummyPos
          argRel = RVar "S" 0 dummyPos
          extraProof = PVar "extra" 0 dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argTerm, RelArg argRel, ProofArg extraProof] dummyPos
      
      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Left (InternalError msg _) -> msg `shouldContain` "Too many arguments"
        Left err -> expectationFailure $ "Expected InternalError about too many arguments, got: " ++ show err
        Right _ -> expectationFailure "Expected error for too many arguments, but got success"

  describe "Complex multi-argument applications" $ do
    it "handles theorem with 6 mixed arguments" $ do
      let theoremName = "complex_six_arg_thm"
          -- ⊢ complex_six_arg_thm (x : Term) (R : Rel) (y : Term) (S : Rel) (z : Term) (T : Rel) : x [(R ∘ S) ∘ T] z
          theoremBindings = [TermBinding "x", RelBinding "R", TermBinding "y", RelBinding "S", TermBinding "z", RelBinding "T"]
          theoremJudgment = RelJudgment 
            (Var "x" 0 dummyPos) 
            (Comp (Comp (RVar "R" 0 dummyPos) (RVar "S" 0 dummyPos) dummyPos) (RVar "T" 0 dummyPos) dummyPos)
            (Var "z" 2 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Application: complex_six_arg_thm a1 R1 a2 R2 a3 R3
          args = [TermArg (Var "a1" 0 dummyPos), 
                  RelArg (RVar "R1" 0 dummyPos),
                  TermArg (Var "a2" 1 dummyPos),
                  RelArg (RVar "R2" 1 dummyPos),
                  TermArg (Var "a3" 2 dummyPos),
                  RelArg (RVar "R3" 2 dummyPos)]
          theoremApp = PTheoremApp theoremName args dummyPos
          
          -- Expected result: a1 [(R1 ∘ R2) ∘ R3] a3
          expectedJudgment = RelJudgment 
            (Var "a1" 0 dummyPos)
            (Comp (Comp (RVar "R1" 0 dummyPos) (RVar "R2" 1 dummyPos) dummyPos) (RVar "R3" 2 dummyPos) dummyPos)
            (Var "a3" 2 dummyPos)
      
      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

    it "handles partial application (fewer arguments than parameters)" $ do
      let theoremName = "partial_app_thm"
          -- Theorem with 4 parameters: ⊢ partial_app_thm (x : Term) (R : Rel) (y : Term) (S : Rel) : x [R ∘ S] y
          theoremBindings = [TermBinding "x", RelBinding "R", TermBinding "y", RelBinding "S"]
          theoremJudgment = RelJudgment (Var "x" 0 dummyPos) (Comp (RVar "R" 0 dummyPos) (RVar "S" 0 dummyPos) dummyPos) (Var "y" 1 dummyPos)
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Partial application with only 2 arguments: partial_app_thm a T
          args = [TermArg (Var "a" 0 dummyPos), RelArg (RVar "T" 0 dummyPos)]
          theoremApp = PTheoremApp theoremName args dummyPos
          
          -- Expected result: a [T ∘ S] y (only x and R substituted)
          expectedJudgment = RelJudgment (Var "a" 0 dummyPos) (Comp (RVar "T" 0 dummyPos) (RVar "S" 0 dummyPos) dummyPos) (Var "y" 1 dummyPos)
      
      case inferProofType emptyCtx emptyMacroEnv theoremEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

    it "validates complex nested substitutions (SUCCESS)" $ do
      let theoremName = "nested_subst_thm"
          -- ⊢ nested_subst_thm (f : Term) (g : Term) (R : Rel) (p : (f (g x)) [R ∘ R˘] (f (g x))) : (f (g x)) [R ∘ R˘ ∘ R] (f (g x))
          termX = Var "x" 0 dummyPos
          appGX = App (Var "g" 0 dummyPos) termX dummyPos  
          appFGX = App (Var "f" 0 dummyPos) appGX dummyPos
          relRRConv = Comp (RVar "R" 0 dummyPos) (Conv (RVar "R" 0 dummyPos) dummyPos) dummyPos
          theoremBindings = [TermBinding "f", TermBinding "g", RelBinding "R", ProofBinding "p" (RelJudgment appFGX relRRConv appFGX)]
          theoremJudgment = RelJudgment appFGX (Comp relRRConv (RVar "R" 0 dummyPos) dummyPos) appFGX
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Add axiom theorem: ⊢ complex_axiom (f : Term) (g : Term) (R : Rel) : (f (g x)) [R ∘ R˘] (f (g x))
          complexAxiomEnv = extendTheoremEnvironment "complex_axiom"
            [TermBinding "f", TermBinding "g", RelBinding "R"]
            (RelJudgment appFGX relRRConv appFGX)
            (PVar "complex_ax" 0 dummyPos) theoremEnv
          
          -- Application: nested_subst_thm h k S (complex_axiom h k S)
          argF = Var "h" 0 dummyPos
          argG = Var "k" 0 dummyPos
          argR = RVar "S" 0 dummyPos
          -- Create proof with correct nested structure
          substAppGX = App argG termX dummyPos
          substAppFGX = App argF substAppGX dummyPos
          substRelRRConv = Comp argR (Conv argR dummyPos) dummyPos
          validProof = PTheoremApp "complex_axiom" [TermArg argF, TermArg argG, RelArg argR] dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argF, TermArg argG, RelArg argR, ProofArg validProof] dummyPos
          
          -- Expected result: (h (k x)) [S ∘ S˘ ∘ S] (h (k x))
          expectedJudgment = RelJudgment substAppFGX (Comp substRelRRConv argR dummyPos) substAppFGX
      
      case inferProofType emptyCtx emptyMacroEnv complexAxiomEnv theoremApp of
        Right result -> resultJudgment result `shouldBe` expectedJudgment
        Left err -> expectationFailure $ "Expected success, got error: " ++ show err

    it "fails when nested substitutions don't match exactly (DESIGNED FAILURE)" $ do
      let theoremName = "nested_subst_thm"
          -- Same theorem: ⊢ nested_subst_thm (f : Term) (g : Term) (R : Rel) (p : (f (g x)) [R ∘ R˘] (f (g x))) : (f (g x)) [R ∘ R˘ ∘ R] (f (g x))
          termX = Var "x" 0 dummyPos
          appGX = App (Var "g" 0 dummyPos) termX dummyPos  
          appFGX = App (Var "f" 0 dummyPos) appGX dummyPos
          relRRConv = Comp (RVar "R" 0 dummyPos) (Conv (RVar "R" 0 dummyPos) dummyPos) dummyPos
          theoremBindings = [TermBinding "f", TermBinding "g", RelBinding "R", ProofBinding "p" (RelJudgment appFGX relRRConv appFGX)]
          theoremJudgment = RelJudgment appFGX (Comp relRRConv (RVar "R" 0 dummyPos) dummyPos) appFGX
          theoremProof = PVar "dummy_proof" 0 dummyPos
          theoremEnv = TheoremEnvironment $ Map.fromList [(theoremName, (theoremBindings, theoremJudgment, theoremProof))]
          
          -- Add axiom theorem with DIFFERENT nested structure: ⊢ wrong_complex_axiom (f : Term) (g : Term) (R : Rel) : (g (f x)) [R ∘ R˘] (g (f x))
          termY = Var "y" 0 dummyPos  -- Different base variable
          appFY = App (Var "f" 0 dummyPos) termY dummyPos  
          appGFY = App (Var "g" 0 dummyPos) appFY dummyPos  -- Different nesting: g(f(y)) instead of f(g(x))
          wrongComplexAxiomEnv = extendTheoremEnvironment "wrong_complex_axiom"
            [TermBinding "f", TermBinding "g", RelBinding "R"]
            (RelJudgment appGFY relRRConv appGFY)  -- Wrong nesting structure
            (PVar "wrong_complex_ax" 0 dummyPos) theoremEnv
          
          -- Application: nested_subst_thm h k S (wrong_complex_axiom h k S)
          argF = Var "h" 0 dummyPos
          argG = Var "k" 0 dummyPos
          argR = RVar "S" 0 dummyPos
          -- This proof will provide (k (h y)) [S ∘ S˘] (k (h y)) but theorem expects (h (k x)) [S ∘ S˘] (h (k x))
          wrongProof = PTheoremApp "wrong_complex_axiom" [TermArg argF, TermArg argG, RelArg argR] dummyPos
          theoremApp = PTheoremApp theoremName [TermArg argF, TermArg argG, RelArg argR, ProofArg wrongProof] dummyPos
      
      case inferProofType emptyCtx emptyMacroEnv wrongComplexAxiomEnv theoremApp of
        Left (ProofTypingError _ _ _ _) -> return () -- Expected failure - nested structure doesn't match
        Left err -> expectationFailure $ "Expected ProofTypingError for mismatched nested structure, got: " ++ show err
        Right _ -> expectationFailure "Expected type checking failure due to mismatched nested term structure"