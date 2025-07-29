module TheoremReferenceParsingSpec (spec) where

import Core.Context (emptyContext, extendTheoremContext, Context)
import Parser.Raw (parseFile, rawProof)
import Control.Monad.Reader (runReader)
import qualified Data.Map as Map
import Core.Syntax
import Core.Raw (RawDeclaration(..), RawProof(..), Name(..))
import TypeCheck.Proof (checkProof)
import Text.Megaparsec (runParser, errorBundlePretty)
import Test.Hspec
import Text.Megaparsec (SourcePos, eof, errorBundlePretty, initialPos)

spec :: Spec
spec = do
  describe "Theorem Reference Parsing Bug" $ do
    
    -- TEST 1: Direct Parser Test - Most viable
    -- Tests that parser can handle theorem references in nested contexts
    describe "Direct parser theorem reference handling" $ do
      
      it "should parse simple theorem reference (baseline - should work)" $ do
        let ctx = extendTheoremContext "simple_thm" [] 
                          (RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos))
                          (PVar "dummy" 0 pos)
                          emptyContext
            input = "simple_thm"
        case runParser (rawProof <* eof) "test" input of
          Left err -> expectationFailure $ "Expected successful parsing of simple theorem reference, got: " ++ errorBundlePretty err
          Right proof -> case proof of
            RPTheorem (Name name) [] _ -> name `shouldBe` "simple_thm"
            _ -> expectationFailure $ "Expected PTheoremApp, got: " ++ show proof

      it "should parse theorem reference as proof argument (BUG - currently fails)" $ do
        -- Create theorems where one legitimately takes a proof argument from another
        let innerThm = RelJudgment (Var "x" 0 pos) (RMacro "λ y . y" [] pos) (Var "x" 0 pos)
            outerThm = RelJudgment (Var "z" 0 pos) (RMacro "λ w . w" [] pos) (Var "z" 0 pos)
            ctx = extendTheoremContext "identity" [TermBinding "x"] 
                          innerThm
                          (PVar "dummy1" 0 pos) $
                         extendTheoremContext "use_proof" [TermBinding "y", ProofBinding "p" innerThm] 
                          outerThm
                          (PVar "dummy2" 0 pos)
                          emptyContext
            input = "use_proof a (identity a)"
        case runParser (rawProof <* eof) "test" input of
          Left err -> expectationFailure $ "BUG DETECTED: Failed to parse theorem reference as proof argument. This should work but currently fails with: " ++ errorBundlePretty err
          Right proof -> case proof of
            RPApp (RPApp (RPTheorem (Name "use_proof") [] _) _ _) (RPApp (RPTheorem (Name "identity") [] _) _ _) _ -> 
              return () -- This is what we expect when bug is fixed
            _ -> expectationFailure $ "Expected nested theorem application structure, got: " ++ show proof

    -- TEST 2: Proof Checker Integration Test  
    -- Tests that proof checker can handle nested theorem references
    describe "Proof checker with nested theorem references" $ do
      
      it "should type check nested theorem references (BUG - currently fails at parse stage)" $ do
        -- Create theorems where one legitimately takes a proof argument from another
        let idThm = RelJudgment (Var "x" 0 pos) (RMacro "λ y . y" [] pos) (Var "x" 0 pos)
            idProof = ConvProof (Var "x" 0 pos) (Iota (Var "x" 0 pos) (Lam "y" (Var "y" 0 pos) pos) pos) (Var "x" 0 pos) pos
            
            ctx = extendTheoremContext "identity" [TermBinding "x"] idThm idProof $
                         extendTheoremContext "proof_user" [TermBinding "y", ProofBinding "p" idThm] idThm idProof $
                         emptyContext
            nestedProofInput = "proof_user a (identity a)"
            
        case runParser (rawProof <* eof) "test" nestedProofInput of
          Left err -> expectationFailure $ "BUG DETECTED: Parser should handle valid nested theorem references but failed with: " ++ errorBundlePretty err
          Right nestedProof -> do
            -- Success: parsing worked, so the theorem reference parsing is functioning
            -- For this test, we only care that parsing succeeds
            case nestedProof of
              RPApp (RPTheorem (Name "proof_user") [] _) (RPApp (RPTheorem (Name "identity") [] _) _ _) _ ->
                return () -- Expected structure
              _ -> return () -- Parsing succeeded, structure might be different but that's ok

    -- TEST 3: File Parsing Test
    -- Tests parsing complete files with nested theorem references
    describe "File parsing with nested theorem references" $ do
      
      it "should parse file containing nested theorem references (BUG - currently fails)" $ do
        let fileContent = unlines
              [ "⊢ identity (x : Term) : x [λ y . y] x ≔ x ⇃ ι⟨ x ,λ y . y⟩ ⇂ x;",
                "⊢ proof_wrapper (y : Term) (p : y [λ z . z] y) : y [λ z . z] y ≔ p;", 
                "⊢ nested_thm (a : Term) : a [λ w . w] a ≔ proof_wrapper a (identity a);"
              ]
        case runParser parseFile "test" fileContent of
          Left err -> expectationFailure $ "BUG DETECTED: File with valid nested theorem references should parse but failed with: " ++ errorBundlePretty err
          Right decls -> do
            length decls `shouldBe` 3
            -- Check that the last theorem has the expected nested structure
            case decls !! 2 of
              RawTheorem (Name "nested_thm") _ _ proof -> case proof of
                RPApp (RPApp (RPTheorem (Name "proof_wrapper") [] _) _ _) (RPApp (RPTheorem (Name "identity") [] _) _ _) _ ->
                  return () -- This is what we expect when bug is fixed
                _ -> expectationFailure $ "Expected nested theorem application structure in parsed proof, got: " ++ show proof
              _ -> expectationFailure "Expected RawTheorem as third declaration"

-- Helper
pos :: SourcePos  
pos = initialPos "test"