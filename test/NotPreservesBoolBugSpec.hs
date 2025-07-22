{-# LANGUAGE OverloadedStrings #-}

module NotPreservesBoolBugSpec (spec) where

import Context
import Control.Monad.Reader
import qualified Data.Map as Map
import Errors
import Lib
import Normalize (expandTermMacrosOneStep)
import Parser
import ProofChecker
import Test.Hspec
import Text.Megaparsec (initialPos, runParser)

spec :: Spec
spec = do
  parseAndRunBoolRttContentSpec
  extractAndTestJudgmentComparisonSpec

-- Approach 1: Parse and run the actual bool.rtt content directly
parseAndRunBoolRttContentSpec :: Spec
parseAndRunBoolRttContentSpec = describe "Parse and run bool.rtt content" $ do
  it "verifies that the not_preserves_bool theorem type checks successfully" $ do
    let boolRttContent = unlines
          [ "Bool := ∀X. X → X → X;"
          , "Not b := (λt. λf. b f t);"
          , "⊢ not_preserves_bool (b : Term) (p : b [Bool] b) : (Not b) [Bool] (Not b) :="
          , "  ΛX. λx:X. λy:X. (p{X} y x);"
          ]
    
    case runParserWithFilename "test.rtt" parseFile boolRttContent of
      Left parseErr -> expectationFailure $ "Parse failed: " ++ show parseErr
      Right decls -> do
        -- Extract macro definitions and theorem
        let macros = [d | d@(MacroDef _ _ _) <- decls]
            theorems = [d | d@(TheoremDef _ _ _ _) <- decls]
        
        case (buildMacroEnvironmentFromDecls macros, theorems) of
          (Right macroEnv, [TheoremDef _ bindings judgment proof]) -> do
            let ctx = buildContextFromBindings bindings
            case checkProof ctx macroEnv noTheorems proof judgment of
              Left err -> 
                expectationFailure $ "Proof checking failed: " ++ show err
              Right _ -> 
                return () -- Success: The proof type checks correctly
          _ -> expectationFailure "Failed to extract theorem from parsed content"
    where
      buildMacroEnvironmentFromDecls [] = Right noMacros
      buildMacroEnvironmentFromDecls ((MacroDef name params body):rest) = do
        env <- buildMacroEnvironmentFromDecls rest
        return $ extendMacroEnvironment name params body env
      buildMacroEnvironmentFromDecls (_:rest) = buildMacroEnvironmentFromDecls rest
      
      buildContextFromBindings = foldl addBinding emptyTypingContext
        where
          addBinding ctx (TermBinding name) = extendTermContext name (RMacro "Type" [] (initialPos "<builtin>")) ctx
          addBinding ctx (RelBinding name) = extendRelContext name ctx
          addBinding ctx (ProofBinding name judgment) = extendProofContext name judgment ctx

-- Approach 2: Extract and test just the judgment comparison
extractAndTestJudgmentComparisonSpec :: Spec
extractAndTestJudgmentComparisonSpec = describe "Judgment comparison focus" $ do
  it "verifies that macro and expanded forms are considered equal" $ do
    let pos = initialPos "test"
        macroEnv = extendMacroEnvironment "Not" ["b"] 
                    (TermMacro $ Lam "t" (Lam "f" (App (App (Var "b" 0 pos) (Var "f" 0 pos) pos) (Var "t" 1 pos) pos) pos) pos) $
                  extendMacroEnvironment "Bool" [] 
                    (RelMacro $ All "X" (Arr (RVar "X" 0 pos) (Arr (RVar "X" 0 pos) (RVar "X" 0 pos) pos) pos) pos) noMacros
        
        -- Expected judgment (with macro)
        expectedJudgment = RelJudgment 
          (TMacro "Not" [Var "b" 0 pos] pos) 
          (RMacro "Bool" [] pos) 
          (TMacro "Not" [Var "b" 0 pos] pos)
        
        -- Actual judgment (expanded form with correct indices after macro expansion)
        -- The macro expands to λt. λf. b f t where b has index 0 (the substituted argument)
        actualJudgment = RelJudgment
          (Lam "t" (Lam "f" (App (App (Var "b" 0 pos) (Var "f" 0 pos) pos) (Var "t" 1 pos) pos) pos) pos)
          (RMacro "Bool" [] pos)
          (Lam "t" (Lam "f" (App (App (Var "b" 0 pos) (Var "f" 0 pos) pos) (Var "t" 1 pos) pos) pos) pos)
    
    -- First test: can we expand the macro correctly?
    let notMacro = TMacro "Not" [Var "b" 0 pos] pos
    case expandTermMacrosOneStep macroEnv notMacro of
      Left err -> expectationFailure $ "Macro expansion failed: " ++ show err
      Right expanded -> do
        -- Test the comparison - should now succeed with lazy macro expansion
        case relJudgmentEqual macroEnv expectedJudgment actualJudgment of
          Right True -> return () -- Success: judgments are now considered equal
          Right False -> expectationFailure $ "Bug not fixed: macro form and expanded form are still not considered equal. Expanded form: " ++ show expanded
          Left err -> expectationFailure $ "Comparison error: " ++ show err