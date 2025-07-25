module TheoremReferenceParsingSpec (spec) where

import Context (emptyTypingContext, extendTheoremEnvironment, noMacros, noTheorems)
import qualified Data.Map as Map
import Lib
import qualified RawParser as Raw
import Elaborate
import ProofChecker (checkProof)
import Test.Hspec
import TestHelpers ()
import Text.Megaparsec (SourcePos, eof, errorBundlePretty, initialPos, runParser)

spec :: Spec
spec = do
  describe "Theorem Reference Parsing Bug" $ do
    
    -- TEST 1: Direct Parser Test - Most viable
    -- Tests that parser can handle theorem references in nested contexts
    describe "Direct parser theorem reference handling" $ do
      
      it "should parse simple theorem reference (baseline - should work)" $ do
        let testTheoremEnv = extendTheoremEnvironment "simple_thm" [] 
                          (RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos))
                          (PVar "dummy" 0 pos)
                          noTheorems
            ctx = emptyElaborateContext Map.empty noMacros testTheoremEnv
            input = "simple_thm"
        case runParser (Raw.parseProof <* eof) "test" input of
          Left err -> expectationFailure $ "Expected successful parsing of simple theorem reference, got: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Expected successful elaboration, got: " ++ show err
            Right proof -> case proof of
              PTheoremApp name [] _ -> name `shouldBe` "simple_thm"
              _ -> expectationFailure $ "Expected PTheoremApp, got: " ++ show proof

      it "should parse theorem reference as proof argument (BUG FIXED - now works)" $ do
        -- Create theorems where one legitimately takes a proof argument from another
        let innerThm = RelJudgment (Var "x" 0 pos) (RMacro "λy.y" [] pos) (Var "x" 0 pos)
            outerThm = RelJudgment (Var "z" 0 pos) (RMacro "λw.w" [] pos) (Var "z" 0 pos)
            testTheoremEnv = extendTheoremEnvironment "identity" [TermBinding "x"] 
                          innerThm
                          (PVar "dummy1" 0 pos) $
                         extendTheoremEnvironment "use_proof" [TermBinding "y", ProofBinding "p" innerThm] 
                          outerThm
                          (PVar "dummy2" 0 pos)
                          noTheorems
            -- Add "a" to the term context so it can be parsed as a term argument
            termContext = Map.fromList [("a", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros testTheoremEnv) { termVars = termContext }
            input = "use_proof a (identity a)"
        case runParser (Raw.parseProof <* eof) "test" input of
          Left err -> expectationFailure $ "Parse error: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration error: " ++ show err
            Right proof -> case proof of
              AppP (AppP (PTheoremApp "use_proof" [] _) _ _) (AppP (PTheoremApp "identity" [] _) _ _) _ -> 
                return () -- This is what we expect when bug is fixed
              _ -> expectationFailure $ "Expected nested theorem application structure, got: " ++ show proof

    -- TEST 2: Proof Checker Integration Test  
    -- Tests that proof checker can handle nested theorem references
    describe "Proof checker with nested theorem references" $ do
      
      it "should type check nested theorem references (BUG FIXED - now works)" $ do
        -- Create theorems where one legitimately takes a proof argument from another
        let idThm = RelJudgment (Var "x" 0 pos) (RMacro "λy.y" [] pos) (Var "x" 0 pos)
            idProof = ConvProof (Var "x" 0 pos) (Iota (Var "x" 0 pos) (Lam "y" (Var "y" 0 pos) pos) pos) (Var "x" 0 pos) pos
            
            testTheoremEnv = extendTheoremEnvironment "identity" [TermBinding "x"] idThm idProof $
                         extendTheoremEnvironment "proof_user" [TermBinding "y", ProofBinding "p" idThm] idThm idProof $
                         noTheorems
            
        -- Try to create a theorem that uses valid nested references: proof_user a (identity a)
        let termContext = Map.fromList [("a", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros testTheoremEnv) { termVars = termContext }
            nestedProofInput = "proof_user a (identity a)"
            
        case runParser (Raw.parseProof <* eof) "test" nestedProofInput of
          Left err -> expectationFailure $ "Parse error: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration error: " ++ show err
            Right nestedProof -> do
              -- If parsing succeeds, try type checking
              let typingCtx = emptyTypingContext
              case checkProof typingCtx noMacros testTheoremEnv nestedProof idThm of
                Left err -> expectationFailure $ "Type checking failed (this might be expected): " ++ show err  
                Right _ -> return () -- Success case when bug is fixed

    -- TEST 3: File Parsing Test
    -- Tests parsing complete files with nested theorem references
    describe "File parsing with nested theorem references" $ do
      
      it "should parse file containing nested theorem references (BUG FIXED - now works)" $ do
        let fileContent = unlines
              [ "⊢ identity (x : Term) : x [λy.y] x := x ⇃ ι⟨x,λy.y⟩ ⇂ x;",
                "⊢ proof_wrapper (y : Term) (p : y [λz.z] y) : y [λz.z] y := p;", 
                "⊢ nested_thm (a : Term) : a [λw.w] a := proof_wrapper a (identity a);"
              ]
        case runParser Raw.parseFile "test" fileContent of
          Left err -> expectationFailure $ "Parse error: " ++ errorBundlePretty err
          Right rawDecls -> do
            let ctx = emptyElaborateContext Map.empty noMacros noTheorems
            case mapM (elaborateDeclaration ctx) rawDecls of
              Left err -> expectationFailure $ "Elaboration error: " ++ show err
              Right decls -> do
                length decls `shouldBe` 3
                -- Check that the last theorem has the expected nested structure
                case decls !! 2 of
                  TheoremDef "nested_thm" _ _ proof -> case proof of
                    AppP (AppP (PTheoremApp "proof_wrapper" [] _) _ _) (AppP (PTheoremApp "identity" [] _) _ _) _ ->
                      return () -- This is what we expect when bug is fixed
                    _ -> expectationFailure $ "Expected nested theorem application structure in parsed proof, got: " ++ show proof
                  _ -> expectationFailure "Expected TheoremDef as third declaration"

-- Helper
pos :: SourcePos  
pos = initialPos "test"