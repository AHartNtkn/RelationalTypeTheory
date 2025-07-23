module Main (main) where

import Context (emptyTypingContext, extendMacroEnvironment, extendProofContext, extendRelContext, extendTermContext, extendTheoremEnvironment, noMacros, noTheorems)
import Control.Monad (when)
import Errors
import Lib
import Parser
import PrettyPrint
import ProofChecker
import qualified REPL
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import Text.Megaparsec (errorBundlePretty, initialPos)

data Mode = ParseOnly | ProofCheck | Verbose | Interactive
  deriving (Eq, Show)

data Options = Options
  { optMode :: Mode,
    optFile :: Maybe String
  }
  deriving (Show)

-- Parse command line arguments
parseArgs :: [String] -> Either String Options
parseArgs args = case args of
  [] -> Right $ Options Interactive Nothing
  ["--repl"] -> Right $ Options Interactive Nothing
  ["--interactive"] -> Right $ Options Interactive Nothing
  [file] -> Right $ Options ParseOnly (Just file)
  ["--parse-only", file] -> Right $ Options ParseOnly (Just file)
  ["--check", file] -> Right $ Options ProofCheck (Just file)
  ["--verbose", file] -> Right $ Options Verbose (Just file)
  [file, "--check"] -> Right $ Options ProofCheck (Just file)
  [file, "--verbose"] -> Right $ Options Verbose (Just file)
  [file, "--parse-only"] -> Right $ Options ParseOnly (Just file)
  _ -> Left "Usage: reltt-haskell [--check|--parse-only|--verbose|--repl] [<file>]"

-- Build context from bindings
buildContextFromBindings :: [Binding] -> TypingContext
buildContextFromBindings bindings = foldl addBinding emptyTypingContext bindings
  where
    addBinding ctx (TermBinding name) = extendTermContext name (RMacro "Type" [] (initialPos "<builtin>")) ctx
    addBinding ctx (RelBinding name) = extendRelContext name ctx
    addBinding ctx (ProofBinding name judgment) = extendProofContext name judgment ctx

-- Extract macro and theorem declarations
extractDeclarations :: [Declaration] -> ([Declaration], [Declaration])
extractDeclarations decls =
  let macroDefs = [d | d@(MacroDef _ _ _) <- decls]
      theoremDefs = [d | d@(TheoremDef _ _ _ _) <- decls]
   in (macroDefs, theoremDefs)

-- Build macro environment from declarations
buildMacroEnvironmentFromDeclarations :: [Declaration] -> Either RelTTError MacroEnvironment
buildMacroEnvironmentFromDeclarations decls = do
  let env = foldr addMacro noMacros decls
  return env
  where
    addMacro (MacroDef name params body) env =
      extendMacroEnvironment name params body defaultFixity env
    addMacro _ env = env

-- Build theorem environment from declarations
buildTheoremEnvironmentFromDeclarations :: [Declaration] -> TheoremEnvironment
buildTheoremEnvironmentFromDeclarations decls = foldr addTheorem noTheorems decls
  where
    addTheorem (TheoremDef name bindings judgment proof) env =
      extendTheoremEnvironment name bindings judgment proof env
    addTheorem _ env = env

-- Check a theorem in an environment
checkTheoremInEnvironment :: MacroEnvironment -> TheoremEnvironment -> Declaration -> Either RelTTError ()
checkTheoremInEnvironment macroDefs theoremDefs (TheoremDef _ bindings judgment proof) = do
  let ctx = buildContextFromBindings bindings
  _ <- checkProof ctx macroDefs theoremDefs proof judgment
  return ()
checkTheoremInEnvironment _ _ _ = Left $ InternalError "Expected theorem declaration" (ErrorContext (initialPos "<check>") "check")

-- Parse-only mode (original behavior)
parseOnlyMode :: String -> String -> IO ()
parseOnlyMode filename content = do
  case runParserWithFilename filename parseFile content of
    Left err -> putStr (errorBundlePretty err)
    Right decls -> mapM_ (putStrLn . prettyDeclaration) decls

-- Proof checking mode
proofCheckMode :: String -> String -> Bool -> IO ()
proofCheckMode filename content verbose = do
  case runParserWithFilename filename parseFile content of
    Left err -> do
      putStrLn "Parse error:"
      putStr (errorBundlePretty err)
      exitFailure
    Right decls -> do
      let (macroDefs, theoremDefs) = extractDeclarations decls
      when verbose $ putStrLn $ "Found " ++ show (length macroDefs) ++ " macros and " ++ show (length theoremDefs) ++ " theorems"

      case buildMacroEnvironmentFromDeclarations macroDefs of
        Left err -> do
          putStrLn $ "Macro environment error: " ++ prettyError err
          exitFailure
        Right macroEnvironment -> do
          when verbose $ putStrLn "Macro environment built successfully"

          -- Build theorem environment
          let theoremDefs' = buildTheoremEnvironmentFromDeclarations theoremDefs
          when verbose $ putStrLn $ "Built theorem environment with " ++ show (length theoremDefs) ++ " theorems"

          -- Check all theorems
          let results = map (checkTheoremInEnvironment macroEnvironment theoremDefs') theoremDefs
          let errors = [err | Left err <- results]

          if null errors
            then do
              putStrLn $ "All " ++ show (length theoremDefs) ++ " theorems type check successfully!"
              exitSuccess
            else do
              putStrLn $ "Found " ++ show (length errors) ++ " errors:"
              mapM_ (\err -> putStrLn (prettyError err) >> putStrLn "") errors
              exitFailure

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Left usage -> putStrLn usage
    Right options -> case optMode options of
      Interactive -> REPL.runREPL
      _ -> case optFile options of
        Nothing -> putStrLn "Error: File required for non-interactive mode"
        Just filename -> do
          content <- readFile filename
          case optMode options of
            ParseOnly -> parseOnlyMode filename content
            ProofCheck -> proofCheckMode filename content False
            Verbose -> proofCheckMode filename content True
