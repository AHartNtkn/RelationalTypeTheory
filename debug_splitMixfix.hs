import Lib

main :: IO ()
main = do
  putStrLn "=== Testing splitMixfix vs relMixfixPostfix expectations ==="
  putStrLn $ "splitMixfix \"_converse\": " ++ show (splitMixfix "_converse")
  putStrLn $ "splitMixfix \"_!\": " ++ show (splitMixfix "_!")
  putStrLn $ "splitMixfix \"not_\": " ++ show (splitMixfix "not_")
  putStrLn $ "splitMixfix \"_+_\": " ++ show (splitMixfix "_+_")
  
  putStrLn "\n=== What relMixfixPostfix expects ==="
  putStrLn "relMixfixPostfix expects pattern [\"<empty>\", \"<literal>\"] for postfix macros"
  putStrLn "But splitMixfix \"_converse\" actually returns [\"converse\"]"
  putStrLn "This is a FORMAT MISMATCH!"