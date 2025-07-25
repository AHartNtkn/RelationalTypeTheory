module ModuleSystem
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
    ModuleLoadError (..),
  )
where

import Context (extendMacroEnvironment, extendTheoremEnvironment, noMacros, noTheorems)
import Control.Exception (IOException, catch)
import Data.Either (partitionEithers)
import Data.List (intercalate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lib
import qualified RawParser as Raw
import Elaborate
import Text.Megaparsec (runParser)
import System.Directory (doesFileExist)
import System.FilePath (normalise, takeDirectory, (</>))
import Text.Megaparsec (errorBundlePretty)

-- | Module system error types
data ModuleLoadError
  = FileNotFound ModulePath
  | ParseError ModulePath String
  | CircularDependency [ModulePath]
  | ImportResolutionError ModulePath String
  | DuplicateExport ModulePath String
  deriving (Show, Eq)

-- | Registry of loaded modules
data ModuleRegistry = ModuleRegistry
  { loadedModules :: Map.Map ModulePath ModuleInfo,
    searchPaths :: [FilePath]
  }
  deriving (Show, Eq)

-- | Dependency graph representation
type DependencyGraph = Map.Map ModulePath [ModulePath]

-- Helper functions for two-phase parsing
parseFileWithElaboration :: String -> Either String [Declaration]
parseFileWithElaboration content = do
  rawDecls <- case runParser Raw.parseFile "" content of
    Left err -> Left (errorBundlePretty err)
    Right raw -> Right raw
  let ctx = emptyElaborateContext Map.empty noMacros noTheorems
  case elaborateDeclarationsWithAccumulation ctx rawDecls of
    Left err -> Left (show err)
    Right decls -> Right decls

-- Helper function to elaborate declarations while threading the environment  
elaborateDeclarationsWithAccumulation :: ElaborateContext -> [Raw.RawDeclaration] -> Either ElaborateError [Declaration]
elaborateDeclarationsWithAccumulation _ [] = Right []
elaborateDeclarationsWithAccumulation ctx (rawDecl:rest) = do
  decl <- elaborateDeclaration ctx rawDecl
  let updatedCtx = updateContextWithDeclaration ctx decl
  restDecls <- elaborateDeclarationsWithAccumulation updatedCtx rest
  return (decl : restDecls)

-- Update context with newly elaborated declaration
updateContextWithDeclaration :: ElaborateContext -> Declaration -> ElaborateContext
updateContextWithDeclaration ctx (MacroDef name params body) =
  let newMacroEnv = extendMacroEnvironment name params body defaultFixity (macroEnv ctx)
  in ctx { macroEnv = newMacroEnv }
updateContextWithDeclaration ctx (FixityDecl fixity name) =
  let currentMacroEnv = macroEnv ctx
      newMacroEnv = currentMacroEnv { macroFixities = Map.insert name fixity (macroFixities currentMacroEnv) }
  in ctx { macroEnv = newMacroEnv }
updateContextWithDeclaration ctx (TheoremDef name bindings judgment proof) =
  let newTheoremEnv = extendTheoremEnvironment name bindings judgment proof (theoremEnv ctx)
  in ctx { theoremEnv = newTheoremEnv }
updateContextWithDeclaration ctx _ = ctx  -- Other declarations don't affect context

parseImportsOnlyWithElaboration :: String -> Either String [ImportDeclaration]
parseImportsOnlyWithElaboration content = do
  -- First parse the full file to get raw declarations
  rawDecls <- case runParser Raw.parseFile "" content of
    Left err -> Left (errorBundlePretty err)
    Right raw -> Right raw
  -- Filter and elaborate import declarations
  let rawImports = [imp | Raw.RawImportDecl imp <- rawDecls]
  Right $ map elaborateRawImport rawImports
  where
    elaborateRawImport (Raw.RawImportModule path) = ImportModule path
    elaborateRawImport (Raw.RawImportModuleAs path alias) = ImportModuleAs path alias
    elaborateRawImport (Raw.RawImportOnly path names) = ImportOnly path names

-- | Create empty module registry with default search paths
emptyModuleRegistry :: ModuleRegistry
emptyModuleRegistry = ModuleRegistry Map.empty [".", "stdlib"]

-- | Load a module and all its dependencies
loadModule :: ModuleRegistry -> ModulePath -> IO (Either ModuleLoadError (ModuleRegistry, ModuleInfo))
loadModule registry modulePathArg = do
  -- First resolve the file path
  resolvedPath <- resolveModulePath (searchPaths registry) modulePathArg
  case resolvedPath of
    Nothing -> return $ Left (FileNotFound modulePathArg)
    Just filePath -> do
      -- Check if already loaded
      case Map.lookup filePath (loadedModules registry) of
        Just moduleInfo -> return $ Right (registry, moduleInfo)
        Nothing -> loadModuleFromFile registry filePath

-- | Load a module from a specific file path
loadModuleFromFile :: ModuleRegistry -> FilePath -> IO (Either ModuleLoadError (ModuleRegistry, ModuleInfo))
loadModuleFromFile registry filePath = do
  result <- catch (Right <$> readFile filePath) (\e -> return $ Left $ show (e :: IOException))
  case result of
    Left _ -> return $ Left (FileNotFound filePath)
    Right content -> do
      case parseFileWithElaboration content of
        Left parseErr -> return $ Left (ParseError filePath parseErr)
        Right declarations -> do
          -- Extract imports, exports, macros, and theorems
          let (imports, exports, macros, theorems) = partitionDeclarations declarations

          -- Build environments
          let macroEnvironment = buildMacroEnvironment macros
              theoremEnvironment = buildTheoremEnvironment theorems
              exportList = extractExportList exports declarations

          let moduleInfo =
                ModuleInfo
                  { modulePath = filePath,
                    moduleAlias = Nothing,
                    loadedMacros = macroEnvironment,
                    loadedTheorems = theoremEnvironment,
                    exportedSymbols = exportList,
                    importDeclarations = imports
                  }

          let newRegistry = registry {loadedModules = Map.insert filePath moduleInfo (loadedModules registry)}
          return $ Right (newRegistry, moduleInfo)

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

-- | Build macro environment from macro declarations
buildMacroEnvironment :: [Declaration] -> MacroEnvironment
buildMacroEnvironment decls = foldr addToEnv noMacros decls
  where
    addToEnv (MacroDef name params body) env = extendMacroEnvironment name params body defaultFixity env
    addToEnv (FixityDecl fixity name) env = env { macroFixities = Map.insert name fixity (macroFixities env) }
    addToEnv _ env = env

-- | Build theorem environment from theorem declarations
buildTheoremEnvironment :: [Declaration] -> TheoremEnvironment
buildTheoremEnvironment decls = foldr addTheorem noTheorems decls
  where
    addTheorem (TheoremDef name bindings judgment proof) env = extendTheoremEnvironment name bindings judgment proof env
    addTheorem _ env = env

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
buildDependencyGraph registry = Map.fromList $ map extractDeps (Map.toList (loadedModules registry))
  where
    extractDeps (path, _) = (path, extractDependencies path registry)

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

-- | Build complete import dependency graph starting from entry file
buildCompleteImportGraph :: [FilePath] -> ModulePath -> IO (Either ModuleLoadError DependencyGraph)
buildCompleteImportGraph searchPathsArg entryFile = do
  resolvedEntry <- resolveModulePath searchPathsArg entryFile
  case resolvedEntry of
    Nothing -> return $ Left (FileNotFound entryFile)
    Just entryPath -> buildGraphRecursive searchPathsArg Set.empty Map.empty [entryPath]
  where
    buildGraphRecursive :: [FilePath] -> Set.Set FilePath -> DependencyGraph -> [FilePath] -> IO (Either ModuleLoadError DependencyGraph)
    buildGraphRecursive _ _ graph [] = return $ Right graph
    buildGraphRecursive searchPathsLocal visited graph (currentFile : remaining) = do
      if Set.member currentFile visited
        then buildGraphRecursive searchPathsLocal visited graph remaining
        else do
          -- Parse imports from current file
          result <- parseFileImports currentFile
          case result of
            Left err -> return $ Left err
            Right imports -> do
              -- Resolve import paths (relative to current file's directory)
              resolvedImports <- resolveImportPaths searchPathsLocal currentFile imports
              case resolvedImports of
                Left err -> return $ Left err
                Right importPaths -> do
                  let newGraph = Map.insert currentFile importPaths graph
                      newVisited = Set.insert currentFile visited
                      newRemaining = remaining ++ (filter (`Set.notMember` newVisited) importPaths)
                  buildGraphRecursive searchPathsLocal newVisited newGraph newRemaining

    parseFileImports :: FilePath -> IO (Either ModuleLoadError [ImportDeclaration])
    parseFileImports filePath = do
      result <- catch (Right <$> readFile filePath) (\e -> return $ Left $ show (e :: IOException))
      case result of
        Left _ -> return $ Left (FileNotFound filePath)
        Right content -> do
          case parseImportsOnlyWithElaboration content of
            Left parseErr -> return $ Left (ParseError filePath parseErr)
            Right imports -> return $ Right imports

    resolveImportPaths :: [FilePath] -> FilePath -> [ImportDeclaration] -> IO (Either ModuleLoadError [FilePath])
    resolveImportPaths searchPathsLocal currentFile imports = do
      let currentDir = takeDirectory currentFile
          -- Add current file's directory as first search path for relative imports
          searchPathsWithCurrent = currentDir : searchPathsLocal
      resolvedPaths <- mapM (resolveImportPath searchPathsWithCurrent) imports
      let (errors, paths) = partitionEithers resolvedPaths
      case errors of
        (err : _) -> return $ Left err
        [] -> return $ Right paths

    resolveImportPath :: [FilePath] -> ImportDeclaration -> IO (Either ModuleLoadError FilePath)
    resolveImportPath searchPathsNested (ImportModule path) = resolveModulePathWithError searchPathsNested path
    resolveImportPath searchPathsNested (ImportModuleAs path _) = resolveModulePathWithError searchPathsNested path
    resolveImportPath searchPathsNested (ImportOnly path _) = resolveModulePathWithError searchPathsNested path

    resolveModulePathWithError :: [FilePath] -> ModulePath -> IO (Either ModuleLoadError FilePath)
    resolveModulePathWithError searchPathsNested modulePathNested = do
      resolved <- resolveModulePath searchPathsNested modulePathNested
      case resolved of
        Just path -> return $ Right path
        Nothing -> return $ Left (FileNotFound modulePathNested)

-- | Validate a dependency graph for cycles and other issues
validateDependencyGraph :: DependencyGraph -> Either ModuleLoadError [ModulePath]
validateDependencyGraph graph = do
  -- Check for circular dependencies
  case detectCircularDependencies graph of
    Just cyclePath -> Left (CircularDependency cyclePath)
    Nothing -> do
      -- Validate that all referenced modules exist in the graph
      let allNodes = Map.keys graph
          allReferencedNodes = concatMap snd (Map.toList graph)
          missingNodes = filter (`notElem` allNodes) allReferencedNodes
      case missingNodes of
        (missing : _) -> Left (FileNotFound missing)
        [] -> do
          -- Return topological sort order
          case topologicalSort graph of
            Left cyclePath -> Left (CircularDependency cyclePath)
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
        Left _ -> return $ Left (FileNotFound filePath)
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
parseModuleWithDependencies searchPathsArg entryFile = do
  contentResult <- loadModuleWithDependencies searchPathsArg entryFile
  case contentResult of
    Left err -> return $ Left err
    Right concatenatedContent -> do
      case parseFileWithElaboration concatenatedContent of
        Left parseErr -> return $ Left (ParseError entryFile parseErr)
        Right declarations -> return $ Right declarations

-- | Graph-based module loading that integrates with ModuleRegistry
loadModuleWithDependenciesIntegrated :: ModuleRegistry -> ModulePath -> IO (Either ModuleLoadError (ModuleRegistry, ModuleInfo))
loadModuleWithDependenciesIntegrated registry entryFile = do
  -- Use graph-based parsing to get all declarations
  result <- parseModuleWithDependencies (searchPaths registry) entryFile
  case result of
    Left err -> return $ Left err
    Right allDeclarations -> do
      -- Extract imports, exports, macros, and theorems from all declarations
      let (imports, exports, macros, theorems) = partitionDeclarations allDeclarations

      -- Build environments from all loaded content
      let macroEnvironment = buildMacroEnvironment macros
          theoremEnvironment = buildTheoremEnvironment theorems
          exportList = extractExportList exports allDeclarations

      -- Create ModuleInfo for the entry file
      let moduleInfo =
            ModuleInfo
              { modulePath = entryFile,
                moduleAlias = Nothing,
                loadedMacros = macroEnvironment,
                loadedTheorems = theoremEnvironment,
                exportedSymbols = exportList,
                importDeclarations = imports
              }

      -- Update registry with the loaded module
      let newRegistry = registry {loadedModules = Map.insert entryFile moduleInfo (loadedModules registry)}
      return $ Right (newRegistry, moduleInfo)
