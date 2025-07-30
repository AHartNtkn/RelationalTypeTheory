module TheoremReferenceParsingSpec (spec) where

import Core.Context (emptyContext, extendTheoremContext, Context)
import Parser.Raw (parseFile, raw)
import Control.Monad.Reader (runReader)
import qualified Data.Map as Map
import Core.Syntax
import Core.Raw (RawDeclaration(..), Raw(..), Name(..))
import TypeCheck.Proof (checkProof)
import Text.Megaparsec (runParser, errorBundlePretty)
import Test.Hspec
import Text.Megaparsec (SourcePos, eof, errorBundlePretty, initialPos)

spec :: Spec
spec = do
  describe "Theorem Reference Parsing with Unified Raw" $ do
    
    -- TEST 1: Basic parsing with unified Raw
    describe "Unified raw parser theorem reference handling" $ do
      
      it "should parse simple variable reference" $ do
        let input = "simple_thm"
        case runParser (raw <* eof) "test" input of
          Left err -> expectationFailure $ "Expected successful parsing of variable reference, got: " ++ errorBundlePretty err
          Right proof -> case proof of
            RawVar (Name name) _ -> name `shouldBe` "simple_thm"
            _ -> expectationFailure $ "Expected RawVar, got: " ++ show proof

      it "should parse nested application structure" $ do
        let input = "use_proof a (identity a)"
        case runParser (raw <* eof) "test" input of
          Left err -> expectationFailure $ "Failed to parse nested application: " ++ errorBundlePretty err
          Right proof -> case proof of
            RawApp (RawApp (RawVar (Name "use_proof") _) (RawVar (Name "a") _) _) 
                   (RawApp (RawVar (Name "identity") _) (RawVar (Name "a") _) _) _ -> 
              return () -- Expected nested application structure
            _ -> expectationFailure $ "Expected nested application structure, got: " ++ show proof

    -- TEST 2: File Parsing Test
    describe "File parsing with nested references" $ do
      
      it "should parse file containing nested references" $ do
        let fileContent = unlines
              [ "⊢ identity (x : Term) : x [λ y . y] x ≔ x ⇃ ι⟨ x ,λ y . y⟩ ⇂ x;",
                "⊢ proof_wrapper (y : Term) (p : y [λ z . z] y) : y [λ z . z] y ≔ p;", 
                "⊢ nested_thm (a : Term) : a [λ w . w] a ≔ proof_wrapper a (identity a);"
              ]
        case runParser parseFile "test" fileContent of
          Left err -> expectationFailure $ "File parsing failed: " ++ errorBundlePretty err
          Right decls -> do
            length decls `shouldBe` 3
            -- Check that the last theorem has the expected nested structure
            case decls !! 2 of
              RawTheorem (Name "nested_thm") _ _ proof -> case proof of
                RawApp (RawApp (RawVar (Name "proof_wrapper") _) (RawVar (Name "a") _) _) 
                       (RawApp (RawVar (Name "identity") _) (RawVar (Name "a") _) _) _ ->
                  return () -- Expected nested application structure
                _ -> expectationFailure $ "Expected nested application structure in parsed proof, got: " ++ show proof
              _ -> expectationFailure "Expected RawTheorem as third declaration"

-- Helper
pos :: SourcePos  
pos = initialPos "test"