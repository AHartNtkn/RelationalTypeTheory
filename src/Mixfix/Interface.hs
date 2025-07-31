{-# LANGUAGE OverloadedStrings #-}
-- | Module interface serialization for mixfix macros
--
-- This module handles the serialization and deserialization of macro
-- definitions for cross-module compilation, maintaining stable interfaces
-- across compilation units.
module Mixfix.Interface
  ( -- * Interface types
    InterfaceVersion(..)
  , MacroInterface(..)
  , ModuleInterface(..)
  , -- * Serialization operations
    writeInterface
  , readInterface
  , -- * Interface validation
    validateInterface
  , interfaceCompatible
  , -- * Version management
    currentVersion
  , supportedVersions
  , upgradeInterface
  ) where

import           Control.Exception (try, IOException)
import           Control.Monad (when, unless)
import           Crypto.Hash (SHA256, hash)
import           Data.Aeson
import           Data.Aeson.Encode.Pretty (encodePretty)
import qualified Data.Aeson.KeyMap as KM
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import           Data.Time (UTCTime, getCurrentTime)
import           System.FilePath ((<.>), takeBaseName)

import           Mixfix.Core
import           Mixfix.Util

-- | Interface format version for backwards compatibility
data InterfaceVersion = InterfaceVersion
  { versionMajor :: !Int
  , versionMinor :: !Int  
  , versionPatch :: !Int
  } deriving (Show, Eq, Ord)

-- | Serializable representation of a macro for interface files
data MacroInterface = MacroInterface
  { ifaceMacroName     :: !Text             -- ^ Macro name
  , ifaceLitSeq        :: ![LitOrHole]      -- ^ Literal sequence
  , ifacePrec          :: !Int              -- ^ Precedence
  , ifaceAssocInfo     :: !(Maybe (Assoc, HoleIx))  -- ^ Associativity
  , ifaceHoleTypes     :: ![Text]           -- ^ Hole type names (serialized)
  , ifaceSourceHash    :: !ByteString       -- ^ Hash of source definition
  , ifaceCreatedAt     :: !UTCTime          -- ^ Creation timestamp
  } deriving (Show, Eq)

-- | Complete module interface containing all exported macros
data ModuleInterface = ModuleInterface
  { ifaceVersion       :: !InterfaceVersion
  , ifaceModuleName    :: !Text
  , ifaceExportedMacros :: ![MacroInterface]
  , ifaceImportedMacros :: ![Text]          -- ^ Names of imported modules
  , ifaceInterfaceHash  :: !ByteString      -- ^ Hash of entire interface
  , ifaceGeneratedAt    :: !UTCTime         -- ^ Generation timestamp
  } deriving (Show, Eq)

------------------------------------------------------------
-- JSON serialization instances
------------------------------------------------------------

instance ToJSON InterfaceVersion where
  toJSON (InterfaceVersion maj min pat) = object
    [ "major" .= maj
    , "minor" .= min  
    , "patch" .= pat
    ]

instance FromJSON InterfaceVersion where
  parseJSON = withObject "InterfaceVersion" $ \o -> InterfaceVersion
    <$> o .: "major"
    <*> o .: "minor"
    <*> o .: "patch"

instance ToJSON Assoc where
  toJSON LeftA  = String "left"
  toJSON RightA = String "right"
  toJSON NonA   = String "none"

instance FromJSON Assoc where
  parseJSON = withText "Assoc" $ \t -> case t of
    "left"  -> pure LeftA
    "right" -> pure RightA  
    "none"  -> pure NonA
    _       -> fail ("Unknown associativity: " ++ T.unpack t)

instance ToJSON LitOrHole where
  toJSON (L text) = object ["literal" .= text]
  toJSON (H idx)  = object ["hole" .= idx]

instance FromJSON LitOrHole where
  parseJSON = withObject "LitOrHole" $ \o -> 
    case KM.toList o of
      [("literal", String text)] -> pure (L text)
      [("hole", Number n)] -> case toBoundedInteger n of
        Just idx -> pure (H idx)
        Nothing -> fail "Invalid hole index"
      _ -> fail "Invalid LitOrHole format"

instance ToJSON MacroInterface where
  toJSON (MacroInterface name litSeq prec assocInfo holeTypes srcHash createdAt) = object
    [ "name" .= name
    , "literalSequence" .= litSeq
    , "precedence" .= prec
    , "associativity" .= assocInfo  
    , "holeTypes" .= holeTypes
    , "sourceHash" .= TE.encodeUtf8 (T.pack (show srcHash))
    , "createdAt" .= createdAt
    ]

instance FromJSON MacroInterface where
  parseJSON = withObject "MacroInterface" $ \o -> MacroInterface
    <$> o .: "name"
    <*> o .: "literalSequence"
    <*> o .: "precedence"
    <*> o .: "associativity"
    <*> o .: "holeTypes"
    <*> (parseHash =<< o .: "sourceHash")
    <*> o .: "createdAt"
    where
      parseHash hashText = case reads (T.unpack hashText) of
        [(h, "")] -> pure h
        _ -> fail "Invalid hash format"

instance ToJSON ModuleInterface where
  toJSON (ModuleInterface version modName macros imports ifaceHash genAt) = object
    [ "version" .= version
    , "moduleName" .= modName
    , "exportedMacros" .= macros
    , "importedModules" .= imports
    , "interfaceHash" .= TE.encodeUtf8 (T.pack (show ifaceHash))
    , "generatedAt" .= genAt
    ]

instance FromJSON ModuleInterface where
  parseJSON = withObject "ModuleInterface" $ \o -> ModuleInterface
    <$> o .: "version"
    <*> o .: "moduleName"
    <*> o .: "exportedMacros"
    <*> o .: "importedModules"
    <*> (parseHash =<< o .: "interfaceHash")
    <*> o .: "generatedAt"
    where
      parseHash hashText = case reads (T.unpack hashText) of
        [(h, "")] -> pure h
        _ -> fail "Invalid hash format"

------------------------------------------------------------
-- Version management
------------------------------------------------------------

-- | Current interface version
currentVersion :: InterfaceVersion
currentVersion = InterfaceVersion 1 0 0

-- | List of supported interface versions (for backwards compatibility)
supportedVersions :: [InterfaceVersion]
supportedVersions = [InterfaceVersion 1 0 0]

-- | Check if an interface version is supported
isVersionSupported :: InterfaceVersion -> Bool
isVersionSupported v = v `elem` supportedVersions

------------------------------------------------------------
-- Interface operations
------------------------------------------------------------

-- | Write a module interface to a file
writeInterface :: FilePath -> ModuleInterface -> IO (Either Text ())
writeInterface filePath iface = do
  result <- try $ do
    let jsonData = encodePretty iface
        content = LBS.toStrict jsonData
        footer = "\n-- RelTT-mixfix-interface-v" <> 
                T.pack (show (versionMajor (ifaceVersion iface))) <> "\n" <>
                computeIntegrityHash content
    BS.writeFile (filePath <.> "rtti") (content <> TE.encodeUtf8 footer)
  case result of
    Left (e :: IOException) -> return $ Left $ T.pack $ show e
    Right () -> return $ Right ()

-- | Read a module interface from a file
readInterface :: FilePath -> IO (Either Text ModuleInterface)
readInterface filePath = do
  result <- try $ BS.readFile (filePath <.> "rtti")
  case result of
    Left (e :: IOException) -> return $ Left $ T.pack $ show e
    Right content -> do
      case parseInterfaceFile content of
        Left err -> return $ Left err
        Right iface -> do
          validation <- validateInterface iface
          case validation of
            Left err -> return $ Left err
            Right () -> return $ Right iface

-- | Parse interface file content
parseInterfaceFile :: ByteString -> Either Text ModuleInterface
parseInterfaceFile content = do
  -- Split content and footer
  let contentText = TE.decodeUtf8 content  
  case T.breakOnEnd "\n-- RelTT-mixfix-interface-v" contentText of
    (jsonPart, footer) | not (T.null footer) -> do
      -- Verify version in footer
      unless (isValidFooter footer) $
        Left "Invalid or unsupported interface version"
      
      -- Parse JSON content
      let jsonBytes = TE.encodeUtf8 (T.dropEnd 1 jsonPart)  -- Remove trailing newline
      case eitherDecodeStrict jsonBytes of
        Left parseErr -> Left $ T.pack parseErr
        Right iface -> do
          -- Verify integrity hash
          let expectedHash = computeIntegrityHash jsonBytes
              actualHash = extractHashFromFooter footer
          if expectedHash == actualHash
            then Right iface
            else Left "Interface integrity check failed"
    _ -> Left "Invalid interface file format"

-- | Validate interface for consistency and compatibility
validateInterface :: ModuleInterface -> IO (Either Text ())
validateInterface iface = do
  -- Check version compatibility
  unless (isVersionSupported (ifaceVersion iface)) $
    return $ Left $ "Unsupported interface version: " <> 
                   T.pack (show (ifaceVersion iface))
  
  -- Validate macro definitions
  mapM_ validateMacroInterface (ifaceExportedMacros iface)
  
  -- Check for duplicate macro names
  let macroNames = map ifaceMacroName (ifaceExportedMacros iface)
      duplicates = findDuplicates macroNames
  unless (null duplicates) $
    return $ Left $ "Duplicate macro names: " <> T.intercalate ", " duplicates
  
  return $ Right ()

-- | Check if two interfaces are compatible
interfaceCompatible :: ModuleInterface -> ModuleInterface -> Bool
interfaceCompatible iface1 iface2 = 
  ifaceVersion iface1 == ifaceVersion iface2 &&
  ifaceModuleName iface1 == ifaceModuleName iface2 &&
  compatibleMacros (ifaceExportedMacros iface1) (ifaceExportedMacros iface2)

-- | Upgrade an interface to a newer version
upgradeInterface :: InterfaceVersion -> ModuleInterface -> Either Text ModuleInterface
upgradeInterface targetVersion iface
  | ifaceVersion iface == targetVersion = Right iface
  | ifaceVersion iface > targetVersion = Left "Cannot downgrade interface"
  | otherwise = Left "Interface upgrade not implemented"

------------------------------------------------------------
-- Macro serialization helpers
------------------------------------------------------------

-- | Convert a mixfix macro to interface representation
macroToInterface :: MixfixCat cat => Macro cat -> IO MacroInterface
macroToInterface macro = do
  now <- getCurrentTime
  let sourceText = serializeMacroSource macro
      sourceHash = hash (TE.encodeUtf8 sourceText)
  return $ MacroInterface
    { ifaceMacroName = mName macro
    , ifaceLitSeq = mLitSeq macro  
    , ifacePrec = mPrec macro
    , ifaceAssocInfo = mAssocInfo macro
    , ifaceHoleTypes = serializeHoleTypes (mHoleTy macro)
    , ifaceSourceHash = sourceHash
    , ifaceCreatedAt = now
    }

-- | Convert interface representation back to macro (category-specific)
interfaceToMacro :: MixfixCat cat => MacroInterface -> Either Text (Macro cat)
interfaceToMacro iface = do
  holeTypes <- deserializeHoleTypes (ifaceHoleTypes iface)
  return $ Macro
    { mLitSeq = ifaceLitSeq iface
    , mPrec = ifacePrec iface
    , mAssocInfo = ifaceAssocInfo iface
    , mHoleTy = holeTypes
    , mName = ifaceMacroName iface
    }

------------------------------------------------------------
-- Helper functions (category-specific implementations needed)
------------------------------------------------------------

-- | Serialize macro source for hashing
serializeMacroSource :: MixfixCat cat => Macro cat -> Text
serializeMacroSource = undefined  -- Implementation depends on category

-- | Serialize hole type information  
serializeHoleTypes :: MixfixCat cat => HoleMap cat -> [Text]
serializeHoleTypes = undefined  -- Implementation depends on category

-- | Deserialize hole type information
deserializeHoleTypes :: MixfixCat cat => [Text] -> Either Text (HoleMap cat)
deserializeHoleTypes = undefined  -- Implementation depends on category

-- | Validate a single macro interface
validateMacroInterface :: MacroInterface -> IO ()
validateMacroInterface macro = do
  -- Check precedence bounds
  when (ifacePrec macro < 1 || ifacePrec macro > 100) $
    fail $ "Invalid precedence: " ++ show (ifacePrec macro)
  
  -- Validate literal sequence
  when (null (ifaceLitSeq macro)) $
    fail $ "Empty literal sequence for macro: " ++ T.unpack (ifaceMacroName macro)
  
  -- Check hole indices are valid
  let holes = [i | H i <- ifaceLitSeq macro]
      maxHole = if null holes then -1 else maximum holes
      expectedHoles = [0..maxHole]
  unless (all (`elem` holes) expectedHoles) $
    fail $ "Invalid hole sequence for macro: " ++ T.unpack (ifaceMacroName macro)

------------------------------------------------------------
-- Utility functions
------------------------------------------------------------

-- | Compute integrity hash for interface content
computeIntegrityHash :: ByteString -> Text
computeIntegrityHash content = 
  T.pack $ show (hash content :: SHA256)

-- | Extract hash from interface footer
extractHashFromFooter :: Text -> Text  
extractHashFromFooter footer = 
  case T.lines footer of
    (_:hashLine:_) -> T.strip hashLine
    _ -> ""

-- | Check if footer format is valid
isValidFooter :: Text -> Bool
isValidFooter footer = 
  case T.lines footer of
    (versionLine:_:_) -> "RelTT-mixfix-interface-v" `T.isInfixOf` versionLine
    _ -> False

-- | Find duplicate elements in a list
findDuplicates :: Eq a => [a] -> [a]
findDuplicates = findDupsHelper []
  where
    findDupsHelper seen [] = []
    findDupsHelper seen (x:xs)
      | x `elem` seen = x : findDupsHelper seen xs
      | otherwise = findDupsHelper (x:seen) xs

-- | Check if two macro lists are compatible
compatibleMacros :: [MacroInterface] -> [MacroInterface] -> Bool
compatibleMacros macros1 macros2 = 
  length macros1 == length macros2 &&
  all (\(m1, m2) -> compatibleMacro m1 m2) (zip macros1 macros2)

-- | Check if two macro interfaces are compatible
compatibleMacro :: MacroInterface -> MacroInterface -> Bool
compatibleMacro m1 m2 = 
  ifaceMacroName m1 == ifaceMacroName m2 &&
  ifaceLitSeq m1 == ifaceLitSeq m2 &&
  ifacePrec m1 == ifacePrec m2 &&
  ifaceAssocInfo m1 == ifaceAssocInfo m2