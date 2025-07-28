module REPL
  ( runREPL,
    REPLState (..),
    REPLCommand (..),
    parseREPLCommand,
    executeREPLCommand,
    initialREPLState,
  )
where

import Context (emptyTypingContext, extendProofContext, extendRelContext, extendTermContext, lookupMacro, lookupTerm)
import Control.Monad.State
import qualified Data.Map as Map
import Errors
import Lib
import Environment (noMacros, noTheorems, extendMacroEnvironment)
import AST.Mixfix (defaultFixity)
import ModuleSystem (ModuleRegistry, emptyModuleRegistry, loadModuleWithDependenciesIntegrated)
import Parser.Legacy
import PrettyPrint (prettyDeclaration, prettyError, prettyExportDeclaration, prettyImportDeclaration, prettyProof, prettyRType, prettyRelJudgment, prettyTerm)
import ProofChecker
import System.IO (hFlush, hSetEncoding, stdin, stdout, utf8)
import Text.Megaparsec (initialPos)
import TypeOps
import Generic.Expansion (ExpansionResult(..))

-- REPL State holds the current session state
data REPLState = REPLState
  { replMacroEnv :: MacroEnvironment,
    replTheoremEnv :: TheoremEnvironment,
    replContext :: TypingContext,
    replDeclarations :: [Declaration],
    replHistory :: [String],
    replModuleRegistry :: ModuleRegistry
  }
  deriving (Show, Eq)

-- REPL Commands
data REPLCommand
  = QuitREPL
  | HelpREPL
  | LoadFile String
  | CheckProof String String -- proof judgment
  | InferProof String -- proof
  | ExpandMacro String
  | ShowInfo String
  | ListDeclarations
  | ClearSession
  | ShowHistory
  | ParseDeclaration String
  deriving (Show, Eq)

-- Initial empty REPL state
initialREPLState :: REPLState
initialREPLState =
  REPLState
    { replMacroEnv = noMacros,
      replTheoremEnv = noTheorems,
      replContext = emptyTypingContext,
      replDeclarations = [],
      replHistory = [],
      replModuleRegistry = emptyModuleRegistry
    }

-- Parse REPL commands
parseREPLCommand :: String -> Either String REPLCommand
parseREPLCommand input = case words (trim input) of
  [] -> Left "Empty command"
  (":quit" : _) -> Right QuitREPL
  (":q" : _) -> Right QuitREPL
  (":help" : _) -> Right HelpREPL
  (":h" : _) -> Right HelpREPL
  (":load" : filename : _) -> Right (LoadFile filename)
  (":l" : filename : _) -> Right (LoadFile filename)
  (":load" : _) -> Left "Missing filename for :load command"
  (":l" : _) -> Left "Missing filename for :load command"
  (":check" : proof : judgment) -> Right (CheckProof proof (unwords judgment))
  (":c" : proof : judgment) -> Right (CheckProof proof (unwords judgment))
  (":check" : _) -> Left "Usage: :check <proof> <judgment>"
  (":c" : _) -> Left "Usage: :check <proof> <judgment>"
  (":infer" : rest) -> Right (InferProof (unwords rest))
  (":expand" : rest) -> Right (ExpandMacro (unwords rest))
  (":e" : rest) -> Right (ExpandMacro (unwords rest))
  (":info" : rest) -> Right (ShowInfo (unwords rest))
  (":i" : rest) -> Right (ShowInfo (unwords rest))
  (":list" : _) -> Right ListDeclarations
  (":clear" : _) -> Right ClearSession
  (":history" : _) -> Right ShowHistory
  (cmd : _) | take 1 cmd == ":" -> Left $ "Unknown command: " ++ cmd
  (_ : _) -> Right (ParseDeclaration input)
  where
    trim = dropWhile (== ' ')

-- Execute REPL commands
executeREPLCommand :: REPLCommand -> StateT REPLState IO String
executeREPLCommand cmd = case cmd of
  QuitREPL -> return "Goodbye!"
  HelpREPL ->
    return $
      unlines
        [ "RelTT Interactive Proof Assistant",
          "Commands:",
          "  :help, :h                        Show this help",
          "  :quit, :q                        Exit the REPL",
          "  :load <file>, :l                 Load declarations from file",
          "  :check <proof> <judgment>, :c    Check proof against judgment",
          "  :infer <proof>                   Infer judgment from proof",
          "  :expand <macro>, :e              Expand macro",
          "  :info <name>, :i                 Show information about definition",
          "  :list                            List all declarations",
          "  :clear                           Clear session",
          "  :history                         Show command history",
          "",
          "You can also enter macro definitions and theorems directly:",
          "  Macro ≔ Definition;",
          "  ⊢ theorem : judgment ≔ proof;"
        ]
  LoadFile filename -> do
    currentState <- get
    -- Use graph-based loading that handles all dependencies automatically
    result <- liftIO $ loadModuleWithDependenciesIntegrated (replModuleRegistry currentState) filename
    case result of
      Left (FileNotFound path _) -> return $ "File not found: " ++ path
      Left (ModuleParseError path err _) -> return $ "Parse error in " ++ path ++ ": " ++ err
      Left (CircularDependency cyclePath _) -> return $ "Circular dependency detected: " ++ show cyclePath
      Left (ImportResolutionError path err _) -> return $ "Import resolution error in " ++ path ++ ": " ++ err
      Left (DuplicateExport path sym _) -> return $ "Duplicate export in " ++ path ++ ": " ++ sym
      Left otherError -> return $ "Module loading error: " ++ formatError otherError
      Right (newRegistry, moduleInfo) -> do
        -- The new system already loaded all dependencies and built complete environments
        put $
          currentState
            { replModuleRegistry = newRegistry,
              replMacroEnv = loadedMacros moduleInfo,
              replTheoremEnv = loadedTheorems moduleInfo
            }
        return $ "Successfully loaded " ++ filename ++ " with all dependencies using graph-based loading"
  CheckProof proofStr judgmentStr -> do
    currentState <- get
    case runParserWithMacroEnv (replMacroEnv currentState) parseProof proofStr of
      Left err -> return $ "Parse error in proof: " ++ show err
      Right proof -> do
        case runParserWithMacroEnv (replMacroEnv currentState) parseRelJudgment judgmentStr of
          Left err -> return $ "Parse error in judgment: " ++ show err
          Right judgment -> do
            case checkProof (replContext currentState) (replMacroEnv currentState) (replTheoremEnv currentState) proof judgment of
              Left err -> return $ "Proof checking failed: " ++ prettyError err
              Right _ -> return $ "Proof is valid for judgment: " ++ prettyRelJudgment judgment
  InferProof proofStr -> do
    currentState <- get
    case runParserWithMacroEnv (replMacroEnv currentState) parseProof proofStr of
      Left err -> return $ "Parse error: " ++ show err
      Right proof -> do
        case inferProofType (replContext currentState) (replMacroEnv currentState) (replTheoremEnv currentState) proof of
          Left err -> return $ "Type inference failed: " ++ prettyError err
          Right result -> return $ "Inferred judgment: " ++ prettyRelJudgment (resultJudgment result)
  ExpandMacro macroStr -> do
    currentState <- get
    case runParserWithMacroEnv (replMacroEnv currentState) parseRType macroStr of
      Left err -> return $ "Parse error: " ++ show err
      Right rtype -> do
        case expandMacros (replMacroEnv currentState) rtype of
          Left err -> return $ "Expansion error: " ++ prettyError err
          Right result -> return $ "Original: " ++ prettyRType rtype ++ "\nExpanded: " ++ prettyRType (expandedValue result)
  ShowInfo name -> do
    currentState <- get
    let macroInfo = case lookupMacro name (replMacroEnv currentState) of
          Right (params, body) ->
            let paramStr = if null params then "" else " " ++ unwords params
                bodyStr = case body of
                  TermMacro term -> prettyTerm term
                  RelMacro rtype -> prettyRType rtype
                  ProofMacro proof -> prettyProof proof
                fixityStr = case Map.lookup name (macroFixities (replMacroEnv currentState)) of
                  Nothing -> ""
                  Just fixity -> "\nFixity: " ++ show fixity
             in "Macro " ++ name ++ paramStr ++ " ≔ " ++ bodyStr ++ fixityStr
          Left _ -> "No macro named " ++ name
    let contextInfo = case lookupTerm name (replContext currentState) of
          Right (_, rtype) -> "Term " ++ name ++ " : " ++ prettyRType rtype
          Left _ -> "No term named " ++ name
    return $ macroInfo ++ "\n" ++ contextInfo
  ListDeclarations -> do
    currentState <- get
    let decls = replDeclarations currentState
    if null decls
      then return "No declarations"
      else return $ unlines $ map prettyDeclaration decls
  ClearSession -> do
    put initialREPLState
    return "Session cleared"
  ShowHistory -> do
    currentState <- get
    let history = replHistory currentState
    if null history
      then return "No command history"
      else return $ unlines $ zipWith (\i command -> show (i :: Integer) ++ ": " ++ command) [1 ..] (reverse history)
  ParseDeclaration declStr -> do
    currentState <- get
    case runParserWithMacroEnv (replMacroEnv currentState) parseDeclaration declStr of
      Left err -> return $ "Parse error: " ++ show err
      Right decl -> do
        let newDecls = replDeclarations currentState ++ [decl]
        case buildMacroEnvironmentFromDeclarations newDecls of
          Left err -> return $ "Macro environment error: " ++ show err
          Right newMacroEnv -> do
            case decl of
              TheoremDef name bindings judgment proof -> do
                let ctx = buildContextFromBindings bindings
                case checkProof ctx newMacroEnv noTheorems proof judgment of
                  Left err -> return $ "Proof checking error: " ++ show err
                  Right _ -> do
                    put $ currentState {replMacroEnv = newMacroEnv, replDeclarations = newDecls}
                    return $ "Added theorem: " ++ name
              MacroDef name _ _ -> do
                put $ currentState {replMacroEnv = newMacroEnv, replDeclarations = newDecls}
                return $ "Added macro: " ++ name
              ImportDecl importDecl -> do
                put $ currentState {replDeclarations = newDecls}
                return $ "Import declaration processed: " ++ prettyImportDeclaration importDecl
              ExportDecl exportDecl -> do
                put $ currentState {replDeclarations = newDecls}
                return $ "Export declaration processed: " ++ prettyExportDeclaration exportDecl
              FixityDecl fixity name -> do
                put $ currentState {replMacroEnv = newMacroEnv, replDeclarations = newDecls}
                return $ "Added fixity declaration: " ++ show fixity ++ " " ++ name

-- Build macro environment from declarations (helper function)
buildMacroEnvironmentFromDeclarations :: [Declaration] -> Either RelTTError MacroEnvironment
buildMacroEnvironmentFromDeclarations decls = do
  let env = foldr addMacro noMacros decls
  return env
  where
    addMacro (MacroDef name params body) env =
      extendMacroEnvironment name params body (defaultFixity name) env
    addMacro _ env = env

-- Build context from bindings (helper function)
buildContextFromBindings :: [Binding] -> TypingContext
buildContextFromBindings bindings = foldl addBinding emptyTypingContext bindings
  where
    addBinding ctx (TermBinding name) = extendTermContext name (RMacro "Type" [] (initialPos "<repl>")) ctx
    addBinding ctx (RelBinding name) = extendRelContext name ctx
    addBinding ctx (ProofBinding name judgment) = extendProofContext name judgment ctx

-- Main REPL loop
runREPL :: IO ()
runREPL = do
  -- Set UTF-8 encoding for stdin and stdout to handle Unicode characters properly
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  putStrLn "RelTT Interactive Proof Assistant"
  putStrLn "Type :help for available commands"
  evalStateT replLoop initialREPLState

replLoop :: StateT REPLState IO ()
replLoop = do
  liftIO $ putStr "RelTT> "
  liftIO $ hFlush stdout
  input <- liftIO getLine

  -- Add to history
  modify $ \s -> s {replHistory = input : replHistory s}

  case parseREPLCommand input of
    Left err -> do
      liftIO $ putStrLn $ "Error: " ++ err
      replLoop
    Right QuitREPL -> do
      result <- executeREPLCommand QuitREPL
      liftIO $ putStrLn result
      return ()
    Right cmd -> do
      result <- executeREPLCommand cmd
      liftIO $ putStrLn result
      replLoop
