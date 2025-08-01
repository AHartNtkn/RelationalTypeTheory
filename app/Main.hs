module Main (main) where

import Context (emptyTypingContext, extendMacroEnvironment, extendProofContext, extendRelContext, extendTermContext, extendTheoremEnvironment, noMacros, noTheorems)
import Control.Monad (when)
import Errors (RelTTError(..), ErrorContext(..), formatError)
import Lib
import ModuleSystem (parseModuleWithDependencies, ModuleLoadError(..))
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

-- Parse-only mode (using import-aware parsing)
parseOnlyMode :: String -> IO ()
parseOnlyMode filename = do
  result <- parseModuleWithDependencies ["."] filename
  case result of
    Left (FileNotFound path) -> putStrLn $ "File not found: " ++ path
    Left (ParseError path err) -> putStrLn $ "Parse error in " ++ path ++ ": " ++ err
    Left (CircularDependency cycle) -> putStrLn $ "Circular dependency detected: " ++ show cycle
    Left (ImportResolutionError path err) -> putStrLn $ "Import resolution error in " ++ path ++ ": " ++ err
    Right decls -> mapM_ (putStrLn . prettyDeclaration) decls

-- Proof checking mode (using import-aware parsing)
proofCheckMode :: String -> Bool -> IO ()
proofCheckMode filename verbose = do
  result <- parseModuleWithDependencies ["."] filename
  case result of
    Left (FileNotFound path) -> do
      putStrLn $ "File not found: " ++ path
      exitFailure
    Left (ParseError path err) -> do
      putStrLn $ "Parse error in " ++ path ++ ": " ++ err
      exitFailure
    Left (CircularDependency cycle) -> do
      putStrLn $ "Circular dependency detected: " ++ show cycle
      exitFailure
    Left (ImportResolutionError path err) -> do
      putStrLn $ "Import resolution error in " ++ path ++ ": " ++ err
      exitFailure
    Right decls -> do
      let (macroDefs, theoremDefs) = extractDeclarations decls
      when verbose $ putStrLn $ "Found " ++ show (length macroDefs) ++ " macros and " ++ show (length theoremDefs) ++ " theorems"

      case buildMacroEnvironmentFromDeclarations macroDefs of
        Left err -> do
          putStrLn $ "Macro environment error: " ++ formatError err
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
              mapM_ (\err -> putStrLn (formatError err) >> putStrLn "") errors
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
          case optMode options of
            ParseOnly -> parseOnlyMode filename
            ProofCheck -> proofCheckMode filename False
            Verbose -> proofCheckMode filename True
