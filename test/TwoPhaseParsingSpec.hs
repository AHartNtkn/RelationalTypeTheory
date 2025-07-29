module TwoPhaseParsingSpec (spec) where

import qualified Data.Map as Map
import Core.Syntax
import Module.System
import Core.Errors (RelTTError(..))
import Test.Hspec

spec :: Spec
spec = do
  describe "Two-Phase Parsing System" $ do
    describe "Graph Construction" $ do
      it "builds dependency graph for real files" $ do
        result <- buildCompleteImportGraph ["examples/test"] "test_main.rtt"
        case result of
          Left err -> expectationFailure $ "Expected success but got: " ++ show err
          Right graph -> do
            graph `shouldSatisfy` (\g -> "examples/test/test_main.rtt" `elem` map fst (Map.toList g))
            graph `shouldSatisfy` (\g -> "examples/test/test_lib.rtt" `elem` map fst (Map.toList g))

      it "handles missing files correctly" $ do
        result <- buildCompleteImportGraph ["."] "nonexistent.rtt"
        case result of
          Left (FileNotFound path _) -> path `shouldBe` "nonexistent.rtt"
          Left other -> expectationFailure $ "Expected FileNotFound but got: " ++ show other
          Right _ -> expectationFailure "Expected failure but got success"

    describe "Dependency Resolution" $ do
      it "loads files in correct dependency order" $ do
        result <- parseModuleWithDependencies ["examples/test"] "test_main.rtt"
        case result of
          Left err -> expectationFailure $ "Expected success but got: " ++ show err
          Right decls -> do
            -- Find the Bool macro from library and And macro from main
            let boolMacroIndex = findDeclarationIndex "Bool" decls
                andMacroIndex = findDeclarationIndex "And" decls
            case (boolMacroIndex, andMacroIndex) of
              (Just bIdx, Just aIdx) -> bIdx `shouldSatisfy` (< aIdx)
              (Nothing, _) -> expectationFailure "Bool macro not found in declarations"
              (_, Nothing) -> expectationFailure "And macro not found in declarations"

      it "parses concatenated content successfully" $ do
        result <- parseModuleWithDependencies ["examples/test"] "test_main.rtt"
        case result of
          Left err -> expectationFailure $ "Expected successful parsing but got: " ++ show err
          Right declarations -> do
            declarations `shouldSatisfy` (not . null)
            -- Should contain declarations from both files
            length declarations `shouldSatisfy` (> 2)

    describe "REPL Integration" $ do
      it "loads modules with dependencies in REPL" $ do
        let registry = emptyModuleRegistry
        result <- loadModuleWithDependenciesIntegrated registry "examples/test/test_main.rtt"
        case result of
          Left err -> expectationFailure $ "Expected successful REPL loading but got: " ++ show err
          Right (_, moduleInfo) -> do
            -- Should have successfully loaded the module
            modulePath moduleInfo `shouldBe` "examples/test/test_main.rtt"

    describe "Error Handling" $ do
      it "provides clear error for missing imported file" $ do
        result <- parseModuleWithDependencies ["examples/test"] "test_missing.rtt"
        case result of
          Left (FileNotFound path _) -> path `shouldBe` "nonexistent.rtt"
          Left other -> expectationFailure $ "Expected FileNotFound but got: " ++ show other
          Right _ -> expectationFailure "Expected error but got success"

-- Helper function to find declaration index by name
findDeclarationIndex :: String -> [Declaration] -> Maybe Int
findDeclarationIndex name decls = findIndex (matchesName name) decls
  where
    matchesName target (MacroDef n _ _) = n == target
    matchesName target (TheoremDef n _ _ _) = n == target
    matchesName _ _ = False
    
    findIndex _ [] = Nothing
    findIndex pred (x:xs) = if pred x then Just 0 else fmap (+1) (findIndex pred xs)
