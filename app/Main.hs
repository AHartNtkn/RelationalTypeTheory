module Main (main) where

import Core.Context (emptyContext, extendProofContext, extendRelContext, extendTermContext, extendTheoremContext, extendMacroContext)
import Control.Monad (when)
import Core.Errors (formatError, RelTTError(..), ErrorContext(..))
import Core.Syntax
import Parser.Mixfix (defaultFixity)
import Module.System (parseModuleWithDependencies)
import Parser.Elaborate (elaborate)
import qualified Core.Raw as Raw
import Parser.Raw
import Text.Megaparsec (runParser, errorBundlePretty)
import Interface.PrettyPrint
import TypeCheck.Proof
import qualified Interface.REPL as REPL
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import Text.Megaparsec (initialPos)

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
buildContextFromBindings :: [Binding] -> Context
buildContextFromBindings bindings = foldl addBinding emptyContext bindings
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

-- Build unified context from declarations
buildContextFromDeclarations :: [Declaration] -> Context
buildContextFromDeclarations decls = foldr addDeclaration emptyContext decls
  where
    addDeclaration (MacroDef name params body) ctx =
      -- Convert string params to ParamInfo
      let paramInfos = map (\paramName -> ParamInfo paramName (inferParamKind body) False []) params
      in extendMacroContext name paramInfos body (defaultFixity name) ctx
    addDeclaration (TheoremDef name bindings judgment proof) ctx =
      extendTheoremContext name bindings judgment proof ctx
    addDeclaration _ ctx = ctx

-- Helper function to infer parameter kind from macro body
inferParamKind :: MacroBody -> VarKind
inferParamKind (TermMacro _) = TermK
inferParamKind (RelMacro _) = RelK  
inferParamKind (ProofMacro _) = ProofK

-- Check a theorem in a context
checkTheoremInContext :: Context -> Declaration -> Either RelTTError ()
checkTheoremInContext _ (TheoremDef _ bindings judgment proof) = do
  let bindingCtx = buildContextFromBindings bindings
  _ <- checkProof bindingCtx proof judgment
  return ()
checkTheoremInContext _ _ = Left $ InternalError "Expected theorem declaration" (ErrorContext (initialPos "<check>") "check")

-- Parse-only mode (using new parser pipeline)
parseOnlyMode :: String -> IO ()
parseOnlyMode filename = do
  content <- readFile filename
  case runParser parseFile filename content of
    Left parseErr -> putStrLn $ "Parse error: " ++ errorBundlePretty parseErr
    Right rawDecls -> case elaborateDeclarationsSequentially emptyContext rawDecls [] of
      Left elaborateErr -> putStrLn $ "Elaboration error: " ++ elaborateErr
      Right decls -> mapM_ (putStrLn . prettyDeclaration) decls
  where
    elaborateDeclarationsSequentially :: Context -> [Raw.RawDeclaration] -> [Declaration] -> Either String [Declaration]
    elaborateDeclarationsSequentially _ [] acc = Right (reverse acc)
    elaborateDeclarationsSequentially ctx (rawDecl:rest) acc = do
      case elaborate ctx rawDecl of
        Left err -> Left $ formatError err
        Right decl -> do
          let newCtx = updateContextWithDeclaration decl ctx
          elaborateDeclarationsSequentially newCtx rest (decl:acc)
    
    updateContextWithDeclaration :: Declaration -> Context -> Context
    updateContextWithDeclaration (MacroDef name params body) ctx =
      let paramInfos = map (\paramName -> ParamInfo paramName (inferParamKind body) False []) params
      in extendMacroContext name paramInfos body (defaultFixity name) ctx
    updateContextWithDeclaration (TheoremDef name bindings judgment proof) ctx =
      extendTheoremContext name bindings judgment proof ctx
    updateContextWithDeclaration _ ctx = ctx

-- Proof checking mode (using import-aware parsing)
proofCheckMode :: String -> Bool -> IO ()
proofCheckMode filename verbose = do
  result <- parseModuleWithDependencies ["."] filename
  case result of
    Left (FileNotFound path _) -> do
      putStrLn $ "File not found: " ++ path
      exitFailure
    Left (ModuleParseError path err _) -> do
      putStrLn $ "Parse error in " ++ path ++ ": " ++ err
      exitFailure
    Left (CircularDependency depCycle _) -> do
      putStrLn $ "Circular dependency detected: " ++ show depCycle
      exitFailure
    Left (ImportResolutionError path err _) -> do
      putStrLn $ "Import resolution error in " ++ path ++ ": " ++ err
      exitFailure
    Left (DuplicateExport path name _) -> do
      putStrLn $ "Duplicate export in " ++ path ++ ": " ++ name
      exitFailure
    Left otherError -> do
      putStrLn $ "Module error: " ++ formatError otherError
      exitFailure
    Right decls -> do
      let (macroDefs, theoremDefs) = extractDeclarations decls
      when verbose $ putStrLn $ "Found " ++ show (length macroDefs) ++ " macros and " ++ show (length theoremDefs) ++ " theorems"

      -- Build unified context
      let context = buildContextFromDeclarations decls
      when verbose $ putStrLn "Context built successfully"

      -- Check all theorems
      let results = map (checkTheoremInContext context) theoremDefs
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
