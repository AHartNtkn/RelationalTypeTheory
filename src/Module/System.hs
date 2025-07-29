module Module.System
  ( loadModule,
    resolveImports,
    ModuleRegistry,
    emptyModuleRegistry,
    loadedModules,
    DependencyGraph,
    buildDependencyGraph,
    buildCompleteImportGraph,
    validateDependencyGraph,
    buildAndValidateImportGraph,
    loadFilesInOrder,
    loadModuleWithDependencies,
    parseModuleWithDependencies,
    loadModuleWithDependenciesIntegrated,
    topologicalSort,
    detectCircularDependencies,
  )
where

import Control.Exception (IOException, catch)
import Control.Monad.State
import Data.Either (partitionEithers)
import Data.List (intercalate, find)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Core.Syntax
import Core.Raw
import Parser.Raw (parseFile)
import Text.Megaparsec (runParser)
import Parser.Elaborate (elaborate)
import System.Directory (doesFileExist)
import System.FilePath (normalise, (</>))
import Text.Megaparsec (errorBundlePretty, initialPos)
import Core.Context (extendMacroContext, extendTheoremContext, emptyContext)
import Parser.Mixfix (defaultFixity)
import Core.Errors (RelTTError(..), ErrorContext(..))

-- | Module system error types (now using unified RelTTError)
type ModuleLoadError = RelTTError

-- | Cached processing results for a module
data ProcessedModule = ProcessedModule
  { procModulePath :: FilePath,
    procRawContent :: String,
    procRawDeclarations :: [RawDeclaration],
    procElaboratedDeclarations :: [Declaration],
    procImports :: [ImportDeclaration],
    procExports :: [ExportDeclaration],
    procMacros :: [Declaration],
    procTheorems :: [Declaration],
    procContext :: Context,
    procExportList :: [String]
  }
  deriving (Show, Eq)

-- | Enhanced registry with processing cache
data ModuleRegistry = ModuleRegistry
  { loadedModules :: Map.Map ModulePath ModuleInfo,
    processedModules :: Map.Map FilePath ProcessedModule,
    searchPaths :: [FilePath]
  }
  deriving (Show, Eq)

-- | State monad for module processing operations
type ProcessingState = StateT ModuleRegistry (IO)

-- | Dependency graph representation
type DependencyGraph = Map.Map ModulePath [ModulePath]

-- | Create empty module registry with default search paths
emptyModuleRegistry :: ModuleRegistry
emptyModuleRegistry = ModuleRegistry Map.empty Map.empty [".", "stdlib"]

--------------------------------------------------------------------------------
-- | Unified Module Processing Pipeline
--------------------------------------------------------------------------------

-- | Process a single module with caching
processModule :: FilePath -> Context -> ProcessingState (Either ModuleLoadError ProcessedModule)
processModule filePath baseContext = do
  registry <- get
  case Map.lookup filePath (processedModules registry) of
    Just cached -> return $ Right cached
    Nothing -> do
      result <- liftIO $ processModuleIO filePath baseContext
      case result of
        Left err -> return $ Left err
        Right processed -> do
          modify $ \reg -> reg { processedModules = Map.insert filePath processed (processedModules reg) }
          return $ Right processed

-- | Process a module without caching (IO operation)
processModuleIO :: FilePath -> Context -> IO (Either ModuleLoadError ProcessedModule)
processModuleIO filePath baseContext = do
  -- Read file
  contentResult <- catch (Right <$> readFile filePath) (\e -> return $ Left $ show (e :: IOException))
  case contentResult of
    Left _ -> return $ Left (FileNotFound filePath (ErrorContext (initialPos filePath) "module loading"))
    Right content -> do
      -- Parse
      case runParser parseFile filePath content of
        Left parseErr -> return $ Left (ModuleParseError filePath (errorBundlePretty parseErr) (ErrorContext (initialPos filePath) "module parsing"))
        Right rawDeclarations -> do
          -- Elaborate with context accumulation
          case elaborateDeclarationsWithContext baseContext rawDeclarations of
            Left elaborateErr -> return $ Left (ModuleElaborationError filePath (show elaborateErr) (ErrorContext (initialPos filePath) "module elaboration"))
            Right (elaboratedDeclarations, finalContext) -> do
              -- Partition declarations
              let (imports, exports, macros, theorems) = partitionDeclarations elaboratedDeclarations
                  exportList = extractExportList exports elaboratedDeclarations
              
              -- Create processed module
              let processed = ProcessedModule
                    { procModulePath = filePath,
                      procRawContent = content,
                      procRawDeclarations = rawDeclarations,
                      procElaboratedDeclarations = elaboratedDeclarations,
                      procImports = imports,
                      procExports = exports,
                      procMacros = macros,
                      procTheorems = theorems,
                      procContext = finalContext,
                      procExportList = exportList
                    }
              
              return $ Right processed

-- | Process multiple modules with dependency resolution

-- | Build dependency graph from processed modules
buildDependencyGraphFromProcessed :: Map.Map FilePath ProcessedModule -> DependencyGraph
buildDependencyGraphFromProcessed processedMap = 
  Map.fromList [(procModulePath proc, extractDependencyPaths (procImports proc)) | proc <- Map.elems processedMap]
  where
    extractDependencyPaths :: [ImportDeclaration] -> [FilePath]
    extractDependencyPaths imports = map extractPath imports
    
    extractPath :: ImportDeclaration -> FilePath
    extractPath (ImportModule path) = path
    extractPath (ImportModuleAs path _) = path
    extractPath (ImportOnly path _) = path

-- | Load a module and all its dependencies
loadModule :: ModuleRegistry -> ModulePath -> IO (Either ModuleLoadError (ModuleRegistry, ModuleInfo))
loadModule registry modulePathArg = do
  -- First resolve the file path
  resolvedPath <- resolveModulePath (searchPaths registry) modulePathArg
  case resolvedPath of
    Nothing -> return $ Left (FileNotFound modulePathArg (ErrorContext (initialPos "<resolve>") "module path resolution"))
    Just filePath -> do
      -- Check if already loaded
      case Map.lookup filePath (loadedModules registry) of
        Just moduleInfo -> return $ Right (registry, moduleInfo)
        Nothing -> do
          -- Use unified processing pipeline
          (result, newRegistry) <- runStateT (processModule filePath emptyContext) registry
          case result of
            Left err -> return $ Left err  
            Right processed -> do
              -- Create ModuleInfo from ProcessedModule
              let moduleInfo = ModuleInfo
                    { modulePath = filePath,
                      moduleAlias = Nothing,
                      loadedMacros = macroDefinitions (procContext processed),
                      loadedTheorems = theoremDefinitions (procContext processed),
                      exportedSymbols = procExportList processed,
                      importDeclarations = procImports processed
                    }
              
              -- Update registry with ModuleInfo
              let finalRegistry = newRegistry { loadedModules = Map.insert filePath moduleInfo (loadedModules newRegistry) }
              return $ Right (finalRegistry, moduleInfo)

-- | Resolve module path using search paths
resolveModulePath :: [FilePath] -> ModulePath -> IO (Maybe FilePath)
resolveModulePath searchPathsArg modulePathArg = do
  let candidates = map (</> modulePathArg) searchPathsArg ++ [modulePathArg] -- Also try as absolute path
  findFirst candidates
  where
    findFirst [] = return Nothing
    findFirst (path : paths) = do
      exists <- doesFileExist (normalise path)
      if exists
        then return $ Just (normalise path)
        else findFirst paths

-- | Partition declarations into imports, exports, macros, and theorems
partitionDeclarations :: [Declaration] -> ([ImportDeclaration], [ExportDeclaration], [Declaration], [Declaration])
partitionDeclarations = foldr classify ([], [], [], [])
  where
    classify (ImportDecl imp) (imps, exps, macros, theorems) = (imp : imps, exps, macros, theorems)
    classify (ExportDecl exportDecl) (imps, exps, macros, theorems) = (imps, exportDecl : exps, macros, theorems)
    classify decl@(MacroDef _ _ _) (imps, exps, macros, theorems) = (imps, exps, decl : macros, theorems)
    classify decl@(TheoremDef _ _ _ _) (imps, exps, macros, theorems) = (imps, exps, macros, decl : theorems)
    classify (FixityDecl _ _) (imps, exps, macros, theorems) = (imps, exps, macros, theorems) -- Fixity declarations don't go into any specific category

-- | Elaborate declarations sequentially, accumulating context changes
elaborateDeclarationsWithContext :: Context -> [RawDeclaration] -> Either RelTTError ([Declaration], Context)
elaborateDeclarationsWithContext ctx rawDecls = 
  elaborateSequentially ctx rawDecls []
  where
    elaborateSequentially :: Context -> [RawDeclaration] -> [Declaration] -> Either RelTTError ([Declaration], Context)
    elaborateSequentially finalCtx [] acc = Right (reverse acc, finalCtx)
    elaborateSequentially currentCtx (rawDecl:remaining) acc = do
      elaboratedDecl <- elaborate currentCtx rawDecl
      case elaboratedDecl of
        MacroDef name params body -> do
          -- For macros, we need to convert string params to ParamInfo and extend context
          let paramInfos = map (\paramName -> ParamInfo paramName (inferParamKind body) False []) params
              newCtx = extendMacroContext name paramInfos body (defaultFixity name) currentCtx
          elaborateSequentially newCtx remaining (elaboratedDecl:acc)
        TheoremDef name bindings judgment proof -> do
          -- For theorems, extend the context with the theorem
          let newCtx = extendTheoremContext name bindings judgment proof currentCtx
          elaborateSequentially newCtx remaining (elaboratedDecl:acc)
        _ -> 
          -- Other declarations don't change the context
          elaborateSequentially currentCtx remaining (elaboratedDecl:acc)

-- | Infer parameter kind from macro body (simplified)
inferParamKind :: MacroBody -> VarKind
inferParamKind (TermMacro _) = TermK
inferParamKind (RelMacro _) = RelK  
inferParamKind (ProofMacro _) = ProofK

-- | Extract list of exported symbols
extractExportList :: [ExportDeclaration] -> [Declaration] -> [String]
extractExportList exports allDecls =
  case exports of
    [] -> extractAllSymbols allDecls -- If no explicit exports, export all
    _ -> concatMap extractFromExport exports
  where
    extractFromExport (ExportSymbols names) = names
    extractAllSymbols decls = [name | MacroDef name _ _ <- decls] ++ [name | TheoremDef name _ _ _ <- decls]

-- | Resolve imports for a module (placeholder for Phase 2)
resolveImports :: ModuleRegistry -> [ImportDeclaration] -> IO (Either ModuleLoadError ModuleRegistry)
resolveImports registry [] = return $ Right registry
resolveImports registry (imp : imps) = do
  result <- resolveImport registry imp
  case result of
    Left err -> return $ Left err
    Right newRegistry -> resolveImports newRegistry imps

-- | Resolve a single import (placeholder for Phase 2)
resolveImport :: ModuleRegistry -> ImportDeclaration -> IO (Either ModuleLoadError ModuleRegistry)
resolveImport registry (ImportModule path) = do
  result <- loadModule registry path
  case result of
    Left err -> return $ Left err
    Right (newRegistry, _) -> return $ Right newRegistry
resolveImport registry (ImportModuleAs path alias) = do
  result <- loadModule registry path
  case result of
    Left err -> return $ Left err
    Right (newRegistry, moduleInfo) -> do
      let updatedInfo = moduleInfo {moduleAlias = Just alias}
          updatedRegistry = newRegistry {loadedModules = Map.insert path updatedInfo (loadedModules newRegistry)}
      return $ Right updatedRegistry
resolveImport registry (ImportOnly path _) = do
  result <- loadModule registry path
  case result of
    Left err -> return $ Left err
    Right (newRegistry, _) -> do
      -- For selective imports, we could filter the exported symbols here
      -- For now, just load the module
      return $ Right newRegistry

-- | Build dependency graph from imports
buildDependencyGraph :: ModuleRegistry -> DependencyGraph
buildDependencyGraph registry = 
  case Map.null (processedModules registry) of
    True -> -- Fall back to old method if no processed modules
      Map.fromList $ map extractDeps (Map.toList (loadedModules registry))
      where
        extractDeps (path, _) = (path, extractDependencies path registry)
    False -> -- Use processed modules cache
      buildDependencyGraphFromProcessed (processedModules registry)

-- | Topological sort of dependency graph using Kahn's algorithm
topologicalSort :: DependencyGraph -> Either [ModulePath] [ModulePath]
topologicalSort deps =
  case detectCircularDependencies deps of
    Just cyclePath -> Left cyclePath
    Nothing -> Right $ kahnSort deps
  where
    kahnSort graph =
      let inDegree = computeInDegree graph
          noIncoming = filter (\node -> Map.findWithDefault 0 node inDegree == 0) (Map.keys graph)
       in kahnLoop graph inDegree noIncoming []

    kahnLoop _ _ [] result = result
    kahnLoop graph inDegree (node : queue) result =
      let neighbors = Map.findWithDefault [] node graph
          updatedInDegree = foldr (\neighbor acc -> Map.adjust (subtract 1) neighbor acc) inDegree neighbors
          newNoIncoming = filter (\n -> Map.findWithDefault 0 n updatedInDegree == 0 && n `notElem` (node : result)) neighbors
       in kahnLoop graph updatedInDegree (queue ++ newNoIncoming) (result ++ [node])

    computeInDegree :: DependencyGraph -> Map.Map ModulePath Int
    computeInDegree graph =
      let allNodes = Map.keys graph
          initialCounts = Map.fromList [(node, 0) | node <- allNodes]
       in foldr
            ( \(_, neighbors) acc ->
                foldr (\neighbor acc' -> Map.adjust (+ 1) neighbor acc') acc neighbors
            )
            initialCounts
            (Map.toList graph)

-- | Extract dependencies for a specific module
extractDependencies :: ModulePath -> ModuleRegistry -> [ModulePath]
extractDependencies modulePathArg registry =
  case Map.lookup modulePathArg (loadedModules registry) of
    Nothing -> []
    Just moduleInfo -> map extractPath (importDeclarations moduleInfo)
  where
    extractPath (ImportModule path) = path
    extractPath (ImportModuleAs path _) = path
    extractPath (ImportOnly path _) = path

-- | Detect circular dependencies
detectCircularDependencies :: DependencyGraph -> Maybe [ModulePath]
detectCircularDependencies deps = findCycle (Map.keys deps) deps
  where
    findCycle [] _ = Nothing
    findCycle (node : nodes) graph =
      case dfs node [] graph of
        Just cyclePath -> Just cyclePath
        Nothing -> findCycle nodes graph

    dfs node visited graph
      | node `elem` visited = Just (reverse (node : visited)) -- Found cycle
      | otherwise =
          case Map.lookup node graph of
            Nothing -> Nothing
            Just neighbors ->
              let newVisited = node : visited
               in foldr
                    ( \neighbor acc ->
                        case acc of
                          Just cyclePath -> Just cyclePath
                          Nothing -> dfs neighbor newVisited graph
                    )
                    Nothing
                    neighbors

-- | Build complete import dependency graph starting from entry file (simplified)
buildCompleteImportGraph :: [FilePath] -> ModulePath -> IO (Either ModuleLoadError DependencyGraph)
buildCompleteImportGraph searchPathList entryFile = do
  resolvedEntry <- resolveModulePath searchPathList entryFile
  case resolvedEntry of
    Nothing -> return $ Left (FileNotFound entryFile (ErrorContext (initialPos entryFile) "dependency graph building"))
    Just entryPath -> do
      -- Use unified processing to get all dependencies
      let registry = emptyModuleRegistry { searchPaths = searchPathList }
      (depResult, finalRegistry) <- runStateT (buildDependencyGraphFromEntry entryPath) registry
      case depResult of
        Left err -> return $ Left err
        Right graph -> return $ Right graph
  where
    buildDependencyGraphFromEntry :: FilePath -> ProcessingState (Either ModuleLoadError DependencyGraph)
    buildDependencyGraphFromEntry entryPath = do
      -- Recursively process all dependencies
      allPaths <- gatherAllDependencies [entryPath] Set.empty
      case allPaths of
        Left err -> return $ Left err
        Right paths -> do
          -- Process all modules
          results <- mapM (\path -> processModule path emptyContext) paths
          case partitionEithers results of
            (err:_, _) -> return $ Left err
            ([], _) -> do
              registry <- get
              return $ Right $ buildDependencyGraphFromProcessed (processedModules registry)
    
    gatherAllDependencies :: [FilePath] -> Set.Set FilePath -> ProcessingState (Either ModuleLoadError [FilePath])
    gatherAllDependencies [] visited = return $ Right $ Set.toList visited
    gatherAllDependencies (path:rest) visited
      | Set.member path visited = gatherAllDependencies rest visited
      | otherwise = do
          result <- processModule path emptyContext
          case result of
            Left err -> return $ Left err
            Right processed -> do
              let imports = procImports processed
                  depPaths = map extractPathFromImport imports
              -- Resolve dependency paths
              registry <- get
              let paths = searchPaths registry
              resolvedDeps <- liftIO $ mapM (\depPath -> resolveModulePath paths depPath) depPaths
              let validDeps = [depPath | Just depPath <- resolvedDeps]
                  newVisited = Set.insert path visited
                  newToProcess = rest ++ filter (`Set.notMember` newVisited) validDeps
              gatherAllDependencies newToProcess newVisited
    
    extractPathFromImport :: ImportDeclaration -> FilePath
    extractPathFromImport (ImportModule path) = path
    extractPathFromImport (ImportModuleAs path _) = path
    extractPathFromImport (ImportOnly path _) = path

-- | Validate a dependency graph for cycles and other issues
validateDependencyGraph :: DependencyGraph -> Either ModuleLoadError [ModulePath]
validateDependencyGraph graph = do
  -- Check for circular dependencies
  case detectCircularDependencies graph of
    Just cyclePath -> Left (CircularDependency cyclePath (ErrorContext (initialPos "<dependency>") "circular dependency check"))
    Nothing -> do
      -- Validate that all referenced modules exist in the graph
      let allNodes = Map.keys graph
          allReferencedNodes = concatMap snd (Map.toList graph)
          missingNodes = filter (`notElem` allNodes) allReferencedNodes
      case missingNodes of
        (missing : _) -> Left (FileNotFound missing (ErrorContext (initialPos "<validation>") "dependency validation"))
        [] -> do
          -- Return topological sort order
          case topologicalSort graph of
            Left cyclePath -> Left (CircularDependency cyclePath (ErrorContext (initialPos "<sort>") "topological sort"))
            Right sortedOrder -> Right sortedOrder

-- | Build, validate, and sort complete dependency graph
buildAndValidateImportGraph :: [FilePath] -> ModulePath -> IO (Either ModuleLoadError [ModulePath])
buildAndValidateImportGraph searchPathsArg entryFile = do
  graphResult <- buildCompleteImportGraph searchPathsArg entryFile
  case graphResult of
    Left err -> return $ Left err
    Right graph -> return $ validateDependencyGraph graph

-- | Load and concatenate file contents in dependency order
-- Dependencies should come before dependents, so reverse the topological order
loadFilesInOrder :: [FilePath] -> IO (Either ModuleLoadError String)
loadFilesInOrder [] = return $ Right ""
loadFilesInOrder files = do
  results <- mapM loadSingleFile (reverse files) -- Reverse for proper dependency order
  let (errors, contents) = partitionEithers results
  case errors of
    (err : _) -> return $ Left err
    [] -> return $ Right (intercalate "\n" contents)
  where
    loadSingleFile :: FilePath -> IO (Either ModuleLoadError String)
    loadSingleFile filePath = do
      result <- catch (Right <$> readFile filePath) (\e -> return $ Left $ show (e :: IOException))
      case result of
        Left _ -> return $ Left (FileNotFound filePath (ErrorContext (initialPos filePath) "module loading"))
        Right content -> return $ Right content

-- | Complete graph-based module loading: build graph, validate, and concatenate files
loadModuleWithDependencies :: [FilePath] -> ModulePath -> IO (Either ModuleLoadError String)
loadModuleWithDependencies searchPathsArg entryFile = do
  graphResult <- buildAndValidateImportGraph searchPathsArg entryFile
  case graphResult of
    Left err -> return $ Left err
    Right sortedFiles -> loadFilesInOrder sortedFiles

-- | Parse concatenated content from multiple files as a single unit
parseModuleWithDependencies :: [FilePath] -> ModulePath -> IO (Either ModuleLoadError [Declaration])
parseModuleWithDependencies searchPathList entryFile = do
  -- Use the unified processing system
  graphResult <- buildCompleteImportGraph searchPathList entryFile
  case graphResult of
    Left err -> return $ Left err
    Right graph -> do
      case validateDependencyGraph graph of
        Left err -> return $ Left err
        Right sortedFiles -> do
          -- Process all files in dependency order
          let registry = emptyModuleRegistry { searchPaths = searchPathList }
          (result, _) <- runStateT (processAllInOrder sortedFiles) registry
          case result of
            Left err -> return $ Left err
            Right allDeclarations -> return $ Right allDeclarations
  where
    processAllInOrder :: [FilePath] -> ProcessingState (Either ModuleLoadError [Declaration])
    processAllInOrder paths = do
      results <- mapM (\path -> processModule path emptyContext) paths
      case partitionEithers results of
        (err:_, _) -> return $ Left err
        ([], processed) -> return $ Right $ concatMap procElaboratedDeclarations processed

-- | Graph-based module loading that integrates with ModuleRegistry
loadModuleWithDependenciesIntegrated :: ModuleRegistry -> ModulePath -> IO (Either ModuleLoadError (ModuleRegistry, ModuleInfo))
loadModuleWithDependenciesIntegrated registry entryFile = do
  -- Use the unified processing system with dependency resolution
  (result, newRegistry) <- runStateT (loadWithDependencies entryFile) registry
  case result of
    Left err -> return $ Left err
    Right moduleInfo -> return $ Right (newRegistry, moduleInfo)
  where
    loadWithDependencies :: ModulePath -> ProcessingState (Either ModuleLoadError ModuleInfo)
    loadWithDependencies inputPath = do
      currentRegistry <- get
      -- Resolve the module path
      resolvedPath <- liftIO $ resolveModulePath (searchPaths currentRegistry) inputPath
      case resolvedPath of
        Nothing -> return $ Left (FileNotFound inputPath (ErrorContext (initialPos "<resolve>") "module path resolution"))
        Just filePath -> do
          -- Check if already loaded
          case Map.lookup filePath (loadedModules currentRegistry) of
            Just moduleInfo -> return $ Right moduleInfo
            Nothing -> do
              -- Get all dependencies and process in order
              graphResult <- liftIO $ buildCompleteImportGraph (searchPaths currentRegistry) inputPath
              case graphResult of
                Left err -> return $ Left err
                Right graph -> do
                  case validateDependencyGraph graph of
                    Left err -> return $ Left err
                    Right sortedFiles -> do
                      -- Process all dependencies first
                      results <- mapM (\path -> processModule path emptyContext) sortedFiles
                      case partitionEithers results of
                        (err:_, _) -> return $ Left err
                        ([], processed) -> do
                          -- Find the entry file's processed module
                          case find (\p -> procModulePath p == filePath) processed of
                            Nothing -> return $ Left (FileNotFound filePath (ErrorContext (initialPos filePath) "processed module lookup"))
                            Just entryProcessed -> do
                              -- Create ModuleInfo from the processed entry module
                              let moduleInfo = ModuleInfo
                                    { modulePath = filePath,
                                      moduleAlias = Nothing,
                                      loadedMacros = macroDefinitions (procContext entryProcessed),
                                      loadedTheorems = theoremDefinitions (procContext entryProcessed),
                                      exportedSymbols = procExportList entryProcessed,
                                      importDeclarations = procImports entryProcessed
                                    }
                              
                              -- Update registry
                              modify $ \reg -> reg { loadedModules = Map.insert filePath moduleInfo (loadedModules reg) }
                              return $ Right moduleInfo
