module TwoPhaseParsingSpec (spec) where

import qualified Data.Map as Map
import Lib
import ModuleSystem
import Errors (RelTTError(..))
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
          Left (FileNotFound path) -> path `shouldBe` "nonexistent.rtt"
          Left other -> expectationFailure $ "Expected FileNotFound but got: " ++ show other
          Right _ -> expectationFailure "Expected failure but got success"

    describe "Dependency Resolution" $ do
      it "loads files in correct dependency order" $ do
        result <- loadModuleWithDependencies ["examples/test"] "test_main.rtt"
        case result of
          Left err -> expectationFailure $ "Expected success but got: " ++ show err
          Right content -> do
            -- Library should come before main in concatenated content
            let libIndex = indexOf "Bool ≔ ∀X" content
                mainIndex = indexOf "And b1 b2" content
            libIndex `shouldSatisfy` (< mainIndex)

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
          Left (FileNotFound path) -> path `shouldBe` "nonexistent.rtt"
          Left other -> expectationFailure $ "Expected FileNotFound but got: " ++ show other
          Right _ -> expectationFailure "Expected error but got success"

-- Helper function
indexOf :: String -> String -> Int
indexOf needle haystack = go 0 haystack
  where
    go idx str
      | take (length needle) str == needle = idx
      | null str = -1
      | otherwise = go (idx + 1) (tail str)
