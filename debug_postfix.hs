import qualified Data.Map as Map
import qualified Data.Set as Set
import Lib
import Context
import Text.Megaparsec (initialPos)

-- Test postfix detection
testIsPostfix :: IO ()
testIsPostfix = do
  putStrLn "=== Testing isPostfix function ==="
  let isPostfix name =
        case parseMixfixPattern name of
          [Hole, Literal _] -> True
          _                 -> False
  
  putStrLn $ "isPostfix \"_converse\": " ++ show (isPostfix "_converse")
  putStrLn $ "parseMixfixPattern \"_converse\": " ++ show (parseMixfixPattern "_converse")
  putStrLn $ "isPostfix \"_!\": " ++ show (isPostfix "_!")
  putStrLn $ "parseMixfixPattern \"_!\": " ++ show (parseMixfixPattern "_!")
  putStrLn $ "isPostfix \"not_\": " ++ show (isPostfix "not_")
  putStrLn $ "parseMixfixPattern \"not_\": " ++ show (parseMixfixPattern "not_")

-- Test keyword extraction
testMixfixKeywords :: IO ()
testMixfixKeywords = do
  putStrLn "\n=== Testing mixfixKeywords function ==="
  let env = MacroEnvironment 
        { macroDefinitions = Map.fromList [("_converse", (["A"], RelMacro (Conv (RVar "A" 0 (initialPos "test")) (initialPos "test"))))]
        , macroFixities = Map.fromList [("_converse", Postfix 8)]
        }
  putStrLn $ "mixfixKeywords env: " ++ show (mixfixKeywords env)
  putStrLn $ "splitMixfix \"_converse\": " ++ show (splitMixfix "_converse")

main :: IO ()
main = do
  testIsPostfix
  testMixfixKeywords