import qualified Data.Map as Map
import qualified Data.Set as Set
import Lib
import Context
import Parser
import Text.Megaparsec (parse, initialPos)

testParseRType :: IO ()
testParseRType = do
  putStrLn "=== Testing parseRType with 'X converse' ==="
  let env = MacroEnvironment 
            { macroDefinitions = Map.fromList 
                [ ("_converse", MacroDefinition ["X"] (MacroRType (RConverse (RVar "X" (initialPos "test")))))
                ]
            , macroFixities = Map.fromList [("_converse", Postfix 8)]
            }
  
  putStrLn "Environment set up..."
  putStrLn $ "Macros: " ++ show (Map.keys (macroDefinitions env))
  putStrLn $ "Fixities: " ++ show (Map.keys (macroFixities env))
  
  let result = parse (parseRType env Set.empty) "test" "X converse"
  putStrLn $ "Parse result: " ++ show result

main :: IO ()
main = testParseRType