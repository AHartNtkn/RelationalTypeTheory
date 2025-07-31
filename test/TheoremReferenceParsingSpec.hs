module TheoremReferenceParsingSpec where

import Context (emptyTypingContext, extendTheoremEnvironment, noMacros, noTheorems)
import Control.Monad.Reader (runReader)
import qualified Data.Map as Map
import Lib
import Parser (ParseContext (..), emptyParseContext, parseFile, parseProof, runParserEmpty, runParserT)
import ProofChecker (checkProof)
import Test.Hspec
import TestHelpers
import Text.Megaparsec (SourcePos, eof, errorBundlePretty, initialPos)

spec :: Spec
spec = do
  describe "Theorem Reference Parsing Bug" $ do
    
    -- TEST 1: Direct Parser Test - Most viable
    -- Tests that parser can handle theorem references in nested contexts
    describe "Direct parser theorem reference handling" $ do
      
      it "should parse simple theorem reference (baseline - should work)" $ do
        let theoremEnv = extendTheoremEnvironment "simple_thm" [] 
                          (RelJudgment (Var "x" 0 pos) (RVar "R" 0 pos) (Var "x" 0 pos))
                          (PVar "dummy" 0 pos)
                          noTheorems
            ctx = emptyParseContext { theoremEnv = theoremEnv }
            input = "simple_thm"
        case runReader (runParserT (parseProof <* eof) "test" input) ctx of
          Left err -> expectationFailure $ "Expected successful parsing of simple theorem reference, got: " ++ errorBundlePretty err
          Right proof -> case proof of
            PTheoremApp name [] _ -> name `shouldBe` "simple_thm"
            _ -> expectationFailure $ "Expected PTheoremApp, got: " ++ show proof

      it "should parse theorem reference as proof argument" $ do
        -- Create theorems where one legitimately takes a proof argument from another
        let innerThm = RelJudgment (Var "x" 0 pos) (RMacro "λy.y" [] pos) (Var "x" 0 pos)
            outerThm = RelJudgment (Var "z" 0 pos) (RMacro "λw.w" [] pos) (Var "z" 0 pos)
            theoremEnv = extendTheoremEnvironment "identity" [TermBinding "x"] 
                          innerThm
                          (PVar "dummy1" 0 pos) $
                         extendTheoremEnvironment "use_proof" [TermBinding "y", ProofBinding "p" innerThm] 
                          outerThm
                          (PVar "dummy2" 0 pos)
                          noTheorems
            -- Add "a" to the term context so it can be parsed as a term argument
            termContext = Map.fromList [("a", 0)]
            ctx = emptyParseContext { theoremEnv = theoremEnv, termVars = termContext }
            input = "use_proof a (identity a)"
        case runReader (runParserT (parseProof <* eof) "test" input) ctx of
          Left err -> expectationFailure $ "Failed to parse theorem reference as proof argument: " ++ errorBundlePretty err
          Right proof -> case proof of
            PTheoremApp "use_proof" [ TermArg (Var "a" _ _)
                                      , ProofArg (PTheoremApp "identity" [TermArg (Var "a" _ _)] _) ] _ ->
              return ()
            _ -> expectationFailure $ "Expected nested theorem application structure, got: " ++ show proof

    -- TEST 2: Proof Checker Integration Test  
    -- Tests that proof checker can handle nested theorem references
    describe "Proof checker with nested theorem references" $ do
      
      it "should type check nested theorem references" $ do
        -- Create theorems where one legitimately takes a proof argument from another
        let idThm = RelJudgment (Var "x" 0 pos) (RMacro "λy.y" [] pos) (Var "x" 0 pos)
            idProof = ConvProof (Var "x" 0 pos) (Iota (Var "x" 0 pos) (Lam "y" (Var "y" 0 pos) pos) pos) (Var "x" 0 pos) pos
            
            theoremEnv = extendTheoremEnvironment "identity" [TermBinding "x"] idThm idProof $
                         extendTheoremEnvironment "proof_user" [TermBinding "x", ProofBinding "p" idThm] idThm idProof $
                         noTheorems
            
        -- Try to create a theorem that uses valid nested references: proof_user a (identity a)
        let termContext = Map.fromList [("a", 0)]
            ctx = emptyParseContext { theoremEnv = theoremEnv, termVars = termContext }
            nestedProofInput = "proof_user a (identity a)"
            
        case runReader (runParserT (parseProof <* eof) "test" nestedProofInput) ctx of
          Left err -> expectationFailure $ "Parser failed: " ++ errorBundlePretty err
          Right nestedProof -> do
            let typingCtx = emptyTypingContext
                expectedJudgment = RelJudgment (Var "a" 0 pos) (RMacro "λy.y" [] pos) (Var "a" 0 pos)
            case checkProof typingCtx noMacros theoremEnv nestedProof expectedJudgment of
              Left err -> expectationFailure $ "Type checking failed: " ++ show err
              Right _ -> return ()

    -- TEST 3: File Parsing Test
    -- Tests parsing complete files with nested theorem references
    describe "File parsing with nested theorem references" $ do
      
      it "should parse file containing nested theorem references" $ do
        let fileContent = unlines
              [ "⊢ identity (x : Term) : x [λy.y] x := x ⇃ ι⟨x,λy.y⟩ ⇂ x;",
                "⊢ proof_wrapper (y : Term) (p : y [λz.z] y) : y [λz.z] y := p;", 
                "⊢ nested_thm (a : Term) : a [λw.w] a := proof_wrapper a (identity a);"
              ]
        case runParserEmpty parseFile fileContent of
          Left err -> expectationFailure $ "File with valid nested theorem references should parse but failed with: " ++ errorBundlePretty err
          Right decls -> do
            length decls `shouldBe` 3
            -- Check that the last theorem has the expected nested structure
            case decls !! 2 of
              TheoremDef "nested_thm" _ _ proof -> case proof of
                PTheoremApp "proof_wrapper" [ TermArg (Var "a" _ _)
                                             , ProofArg (PTheoremApp "identity" [TermArg (Var "a" _ _)] _) ] _ ->
                  return ()
                _ -> expectationFailure $ "Expected nested theorem application structure in parsed proof, got: " ++ show proof
              _ -> expectationFailure "Expected TheoremDef as third declaration"

-- Helper
pos :: SourcePos  
pos = initialPos "test"