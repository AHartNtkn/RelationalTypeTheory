{-# LANGUAGE OverloadedStrings #-}

module SubstitutionBugSpec (spec) where

import Context
import Errors  
import Lib
import ProofChecker (checkTheoremArgs, instantiateTheoremJudgment)
import Substitution (applySubstitutionsToTerm)
import Test.Hspec
import TestHelpers
import Text.Megaparsec (initialPos)

spec :: Spec
spec = do
  substitutionOrderBugSpec
  theoremJudgmentInstantiationBugSpec
  theoremArgumentCheckingBugSpec

-- | Test Method 1: Direct unit test of applySubstitutionsToTerm with cyclic substitutions
-- This test directly exposes the substitution order bug
substitutionOrderBugSpec :: Spec
substitutionOrderBugSpec = describe "substitution order bug in applySubstitutionsToTerm" $ do
  it "should correctly apply cyclic variable substitutions a↔b" $ do
    let pos = initialPos "test"
        -- Create the problematic substitutions from pi_left: a→b, b→a
        substitutions = [
          (TermBinding "a", TermArg (Var "b" 0 pos)),
          (TermBinding "b", TermArg (Var "a" 0 pos))
          ]
        
        termA = Var "a" 0 pos
        termB = Var "b" 0 pos
    
    -- Test substitution of 'a' - should become 'b'
    case applySubstitutionsToTerm substitutions termA of
      Right result -> 
        result `shouldBeEqualTerm` Var "b" 0 pos
      Left err -> 
        expectationFailure $ "applySubstitutionsToTerm failed on term 'a': " ++ show err
    
    -- Test substitution of 'b' - should become 'a' (BUT CURRENTLY BECOMES 'b' DUE TO BUG)
    case applySubstitutionsToTerm substitutions termB of
      Right result -> do
        -- This test expects the CORRECT behavior (b should become a)
        -- When the bug is present, this test will FAIL because result will be 'b'
        -- When the bug is fixed, this test will PASS because result will be 'a'
        result `shouldBeEqualTerm` Var "a" 0 pos
      Left err -> 
        expectationFailure $ "applySubstitutionsToTerm failed on term 'b': " ++ show err

  it "should correctly apply triple cyclic substitutions a→b→c→a" $ do
    let pos = initialPos "test"
        -- Test a more complex cycle: a→b, b→c, c→a
        substitutions = [
          (TermBinding "a", TermArg (Var "b" 0 pos)),
          (TermBinding "b", TermArg (Var "c" 0 pos)),
          (TermBinding "c", TermArg (Var "a" 0 pos))
          ]
        
        termA = Var "a" 0 pos
        termB = Var "b" 0 pos  
        termC = Var "c" 0 pos
    
    -- a should become b
    case applySubstitutionsToTerm substitutions termA of
      Right result -> result `shouldBeEqualTerm` Var "b" 0 pos
      Left err -> expectationFailure $ "Failed on 'a': " ++ show err
    
    -- b should become c  
    case applySubstitutionsToTerm substitutions termB of
      Right result -> result `shouldBeEqualTerm` Var "c" 0 pos
      Left err -> expectationFailure $ "Failed on 'b': " ++ show err
    
    -- c should become a (WILL FAIL if bug is present)
    case applySubstitutionsToTerm substitutions termC of
      Right result -> result `shouldBeEqualTerm` Var "a" 0 pos
      Left err -> expectationFailure $ "Failed on 'c': " ++ show err

-- | Test Method 2: Unit test of instantiateTheoremJudgment with variable swapping
-- This tests the bug at the RelJudgment level
theoremJudgmentInstantiationBugSpec :: Spec
theoremJudgmentInstantiationBugSpec = describe "theorem judgment instantiation with variable swapping" $ do
  it "should correctly instantiate pi_left-style judgment with swapped arguments" $ do
    let pos = initialPos "test"
        -- Simulate pi_left signature: (S : Rel) (a : Term) (b : Term) (f : Term) (p : a [f ∘ S] b)
        bindings = [
          RelBinding "S",
          TermBinding "a", 
          TermBinding "b",
          TermBinding "f"
          ]
        
        -- Simulate pi_left call: pi_left (S˘) b a f 
        args = [
          RelArg (Conv (RVar "S" 0 pos) pos),  -- S˘ 
          TermArg (Var "b" 0 pos),             -- b (for parameter a)
          TermArg (Var "a" 0 pos),             -- a (for parameter b)  
          TermArg (Var "f" 0 pos)              -- f
          ]
        
        -- Template judgment: a [f ∘ S] b (the 5th parameter type of pi_left)
        templateJudgment = RelJudgment 
          (Var "a" 0 pos)                                                     -- left: a
          (Comp (Prom (Var "f" 0 pos) pos) (RVar "S" 0 pos) pos)            -- relation: f ∘ S
          (Var "b" 0 pos)                                                     -- right: b
        
        -- Expected result after substitution: b [f ∘ S˘] a
        expectedJudgment = RelJudgment
          (Var "b" 0 pos)                                                     -- left: b (was a)
          (Comp (Prom (Var "f" 0 pos) pos) (Conv (RVar "S" 0 pos) pos) pos) -- relation: f ∘ S˘ 
          (Var "a" 0 pos)                                                     -- right: a (was b)
    
    case instantiateTheoremJudgment bindings args templateJudgment of
      Right result -> do
        -- This test expects the CORRECT result
        -- If the bug is present, the right term will be 'b' instead of 'a'
        result `shouldBeEqualJudgment` expectedJudgment
      Left err -> 
        expectationFailure $ "instantiateTheoremJudgment failed: " ++ show err

-- | Test Method 3: Integration test of checkTheoremArgs with pi_left pattern
-- This tests the bug in the context where it actually occurs
theoremArgumentCheckingBugSpec :: Spec  
theoremArgumentCheckingBugSpec = describe "theorem argument checking with variable swapping" $ do
  it "should correctly validate pi_left-style theorem arguments" $ do
    let pos = initialPos "test"
        ctx = emptyTypingContext
        macroEnv = Context.noMacros
        theoremEnv = Context.noTheorems
        
        -- Create bindings that match pi_left signature
        bindings = [
          RelBinding "S",
          TermBinding "a",
          TermBinding "b", 
          TermBinding "f",
          ProofBinding "p" (RelJudgment 
            (Var "a" 0 pos) 
            (Comp (Prom (Var "f" 0 pos) pos) (RVar "S" 0 pos) pos) 
            (Var "b" 0 pos))
          ]
        
        -- Create a dummy proof that would match the expected type after substitution
        -- The expected type should be: b [f ∘ S˘] a (correct)
        -- But due to the bug, it's computed as: b [f ∘ S˘] b (incorrect) 
        dummyProof = PVar "dummy" 0 pos
        
        -- Arguments for pi_left call: pi_left (S˘) b a f (...)
        args = [
          RelArg (Conv (RVar "S" 0 pos) pos),   -- S˘
          TermArg (Var "b" 0 pos),              -- b (for a)
          TermArg (Var "a" 0 pos),              -- a (for b)
          TermArg (Var "f" 0 pos),              -- f
          ProofArg dummyProof                   -- proof with type b [f ∘ S˘] a
          ]
        
        -- We need to set up the context so that the dummy proof has the correct type
        correctJudgment = RelJudgment 
          (Var "b" 0 pos) 
          (Comp (Prom (Var "f" 0 pos) pos) (Conv (RVar "S" 0 pos) pos) pos)
          (Var "a" 0 pos)
        ctxWithProof = extendProofContext "dummy" correctJudgment ctx
    
    -- This test should pass when the bug is fixed, but currently fails
    -- because checkTheoremArgs computes the wrong expected type due to substitution bug
    case checkTheoremArgs bindings args ctxWithProof macroEnv theoremEnv pos of
      Right validatedArgs -> do
        -- If we get here, the argument checking succeeded
        length validatedArgs `shouldBe` length args
      Left (ProofTypingError _ expectedJudg actualJudg _ _ _) -> do
        -- This is where the bug manifests - in the error message
        -- The expectedJudg will be wrong due to the substitution bug
        let RelJudgment _ _ expectedRightTerm = expectedJudg
            RelJudgment _ _ actualRightTerm = actualJudg
        
        -- The bug causes both terms to become 'b', so expectedRightTerm should be 'a' but isn't
        -- We expect this test to fail until the bug is fixed
        expectationFailure $ 
          "Substitution bug detected in error reporting:\n" ++
          "Expected judgment right term: " ++ show expectedRightTerm ++ " (should be 'a' but is probably 'b')\n" ++  
          "Actual judgment right term: " ++ show actualRightTerm ++ " (correctly 'a')\n" ++
          "Full expected judgment: " ++ show expectedJudg ++ "\n" ++
          "Full actual judgment: " ++ show actualJudg
      Left err -> 
        expectationFailure $ "Unexpected error type: " ++ show err


-- Custom shouldBe for RelJudgment that provides better error messages
shouldBeEqualJudgment :: RelJudgment -> RelJudgment -> Expectation
shouldBeEqualJudgment actual expected = 
  let RelJudgment actualLeft actualRel actualRight = actual
      RelJudgment expectedLeft expectedRel expectedRight = expected
  in do
    actualLeft `shouldBeEqualTerm` expectedLeft
    actualRel `shouldBeEqualRType` expectedRel  
    actualRight `shouldBeEqualTerm` expectedRight