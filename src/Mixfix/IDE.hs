-- | Incremental parsing support for IDE integration
--
-- This module provides APIs for IDE services including incremental parsing,
-- error reporting, code completion, and syntax highlighting support.
module Mixfix.IDE
  ( -- * Snapshot types
    Snapshot(..)
  , SnapshotId(..)
  , DirtyRegion(..)
  , -- * Incremental parsing
    reparseChunk
  , reparseIncremental
  , invalidateRegion
  , -- * IDE services
    completionsAt
  , hoverInfoAt
  , syntaxHighlighting
  , errorDiagnostics
  , -- * Snapshot management
    emptySnapshot
  , updateSnapshot
  , snapshotAt
  , -- * Change tracking
    ChangeSet(..)
  , Change(..)
  , applyChanges
  ) where

import           Control.Concurrent.STM
import           Control.Monad (when)
import           Control.Monad.IO.Class
import           Data.IORef
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Time (UTCTime, getCurrentTime)
import qualified Data.Map.Strict as Map
import           Data.Hashable
import           Text.Megaparsec (SourcePos)

import           Mixfix.Core
import           Mixfix.Env
import           Mixfix.Parse
import           Mixfix.Util
import           Mixfix.Pretty

-- | Unique identifier for a parsing snapshot
newtype SnapshotId = SnapshotId Int
  deriving (Show, Eq, Ord, Hashable)

-- | A dirty region that needs reparsing
data DirtyRegion = DirtyRegion
  { dirtyStart  :: !Int      -- ^ Byte offset start
  , dirtyEnd    :: !Int      -- ^ Byte offset end  
  , dirtyReason :: !Text     -- ^ Reason for invalidation
  } deriving (Show, Eq)

-- | Complete parsing snapshot for a file
data Snapshot cat = Snapshot
  { snapId       :: !SnapshotId     -- ^ Unique snapshot identifier
  , snapEnv      :: !Env            -- ^ Macro environment at snapshot time
  , snapContent  :: !Text           -- ^ File content
  , snapAST      :: !(Node cat)     -- ^ Parsed AST (hash-consed)
  , snapTrie     :: !Trie           -- ^ Cached grammar trie
  , snapErrors   :: ![ParseError]   -- ^ Parse errors found
  , snapDirty    :: ![DirtyRegion]  -- ^ Regions needing reparse
  , snapCreated  :: !UTCTime        -- ^ Snapshot creation time
  } deriving (Show, Eq)

-- | Set of changes to apply to a file
data ChangeSet = ChangeSet
  { changeFile    :: !Text          -- ^ File path
  , changeVersion :: !Int           -- ^ Document version
  , changes       :: ![Change]      -- ^ Individual changes
  } deriving (Show, Eq)

-- | Individual text change
data Change = Change
  { changeRange :: !(Int, Int)      -- ^ Byte range (start, end)
  , changeText  :: !Text            -- ^ Replacement text
  } deriving (Show, Eq)

------------------------------------------------------------
-- Snapshot management
------------------------------------------------------------

-- | Create an empty snapshot
emptySnapshot :: MixfixCat cat => Env -> SnapshotId -> IO (Snapshot cat)
emptySnapshot env sid = do
  now <- getCurrentTime
  let trie = buildTrie (envFingerprint env)
  return $ Snapshot
    { snapId = sid
    , snapEnv = env
    , snapContent = ""
    , snapAST = undefined  -- Would need category-specific empty AST
    , snapTrie = trie
    , snapErrors = []
    , snapDirty = []
    , snapCreated = now
    }

-- | Update a snapshot with new content
updateSnapshot :: MixfixCat cat 
               => Snapshot cat 
               -> Text 
               -> IO (Snapshot cat)
updateSnapshot snap newContent = do
  now <- getCurrentTime
  -- Parse the new content
  case runParser termParser (snapEnv snap) "" newContent of
    Left err -> return $ snap 
      { snapContent = newContent
      , snapErrors = [err]
      , snapCreated = now
      }
    Right ast -> return $ snap
      { snapContent = newContent  
      , snapAST = ast
      , snapErrors = []
      , snapCreated = now
      }

-- | Get snapshot at a specific position
snapshotAt :: MixfixCat cat => Snapshot cat -> Int -> Maybe (Node cat)
snapshotAt snap offset = 
  -- Find the AST node at the given offset
  findNodeAtOffset (snapAST snap) offset

------------------------------------------------------------
-- Incremental parsing
------------------------------------------------------------

-- | Reparse a specific chunk of the file
reparseChunk :: MixfixCat cat
             => Snapshot cat
             -> Text              -- ^ Full updated content
             -> (Int, Int)        -- ^ Dirty byte range
             -> IO (Either ParseError (Snapshot cat))
reparseChunk snap newContent (startOffset, endOffset) = do
  -- Extract the dirty region and surrounding context
  let contextBefore = T.take startOffset newContent
      dirtyRegion = T.take (endOffset - startOffset) 
                   $ T.drop startOffset newContent
      contextAfter = T.drop endOffset newContent
  
  -- Try to parse just the dirty region with context
  case parseRegionIncremental (snapEnv snap) contextBefore dirtyRegion contextAfter of
    Left err -> return $ Left err
    Right newSubAST -> do
      -- Splice the new sub-AST into the full AST
      newAST <- spliceAST (snapAST snap) startOffset endOffset newSubAST
      now <- getCurrentTime
      
      return $ Right $ snap
        { snapContent = newContent
        , snapAST = newAST
        , snapDirty = filter (not . overlapsRegion (startOffset, endOffset)) (snapDirty snap)
        , snapCreated = now
        }

-- | Full incremental reparse with change tracking
reparseIncremental :: MixfixCat cat
                   => Snapshot cat
                   -> ChangeSet
                   -> IO (Either [ParseError] (Snapshot cat))
reparseIncremental snap changeSet = do
  -- Apply all changes to get new content
  let newContent = applyChanges (snapContent snap) (changes changeSet)
  
  -- Determine affected regions
  let affectedRegions = map changeRange (changes changeSet)
      mergedRegions = mergeOverlappingRanges affectedRegions
  
  -- Try incremental reparse for each region
  results <- mapM (\region -> reparseChunk snap newContent region) mergedRegions
  
  case sequence results of
    Left errs -> return $ Left [errs]  -- Return first error for now
    Right snaps -> return $ Right $ last snaps  -- Return final snapshot

-- | Invalidate a region for later reparsing
invalidateRegion :: MixfixCat cat
                 => Snapshot cat  
                 -> DirtyRegion
                 -> Snapshot cat
invalidateRegion snap region = 
  snap { snapDirty = region : snapDirty snap }

------------------------------------------------------------
-- IDE services
------------------------------------------------------------

-- | Get code completions at a specific position
completionsAt :: MixfixCat cat
              => Snapshot cat
              -> Int                    -- ^ Byte offset
              -> IO [CompletionItem]
completionsAt snap offset = do
  -- Find the context at the cursor position
  let context = getParseContext snap offset
      availableMacros = lookupMacros "" (snapEnv snap)  -- Get all macros
  
  -- Generate completions based on context
  return $ map macroToCompletion availableMacros

-- | Get hover information at a position
hoverInfoAt :: MixfixCat cat
            => Snapshot cat
            -> Int                    -- ^ Byte offset  
            -> IO (Maybe HoverInfo)
hoverInfoAt snap offset = do
  case findNodeAtOffset (snapAST snap) offset of
    Nothing -> return Nothing
    Just node -> do
      let info = generateHoverInfo node
      return $ Just info

-- | Generate syntax highlighting for the entire file
syntaxHighlighting :: MixfixCat cat
                   => Snapshot cat
                   -> [HighlightRange]
syntaxHighlighting snap = 
  generateHighlighting (snapAST snap)

-- | Get all error diagnostics for the file
errorDiagnostics :: MixfixCat cat => Snapshot cat -> [Diagnostic]
errorDiagnostics snap = 
  map errorToDiagnostic (snapErrors snap)

------------------------------------------------------------
-- IDE protocol types
------------------------------------------------------------

-- | Code completion item
data CompletionItem = CompletionItem
  { completionLabel  :: !Text
  , completionDetail :: !Text
  , completionKind   :: !CompletionKind
  } deriving (Show, Eq)

data CompletionKind = MacroCompletion | VariableCompletion | KeywordCompletion
  deriving (Show, Eq)

-- | Hover information
data HoverInfo = HoverInfo
  { hoverContents :: !Text
  , hoverRange    :: !(Int, Int)
  } deriving (Show, Eq)

-- | Syntax highlighting range
data HighlightRange = HighlightRange
  { highlightStart :: !Int
  , highlightEnd   :: !Int  
  , highlightKind  :: !HighlightKind
  } deriving (Show, Eq)

data HighlightKind 
  = KeywordHighlight
  | OperatorHighlight  
  | VariableHighlight
  | LiteralHighlight
  | ErrorHighlight
  deriving (Show, Eq)

-- | Diagnostic message
data Diagnostic = Diagnostic
  { diagnosticRange    :: !(Int, Int)
  , diagnosticSeverity :: !DiagnosticSeverity
  , diagnosticMessage  :: !Text
  } deriving (Show, Eq)

data DiagnosticSeverity = Error | Warning | Information | Hint
  deriving (Show, Eq)

------------------------------------------------------------
-- Helper functions (category-specific implementations needed)
------------------------------------------------------------

-- | Find AST node at a given byte offset
findNodeAtOffset :: MixfixCat cat => Node cat -> Int -> Maybe (Node cat)
findNodeAtOffset = undefined  -- Implementation depends on Node structure

-- | Parse a region incrementally with context
parseRegionIncremental :: MixfixCat cat 
                       => Env 
                       -> Text       -- ^ Context before
                       -> Text       -- ^ Dirty region  
                       -> Text       -- ^ Context after
                       -> Either ParseError (Node cat)
parseRegionIncremental = undefined  -- Complex incremental parsing logic

-- | Splice a new AST into an existing one
spliceAST :: MixfixCat cat 
          => Node cat     -- ^ Original AST
          -> Int          -- ^ Start offset
          -> Int          -- ^ End offset  
          -> Node cat     -- ^ New sub-AST
          -> IO (Node cat)
spliceAST = undefined  -- Implementation depends on Node structure

-- | Get parse context at a position (for completions)
getParseContext :: MixfixCat cat => Snapshot cat -> Int -> ParseContext
getParseContext = undefined

data ParseContext = ParseContext
  { contextExpectedTokens :: ![Text]
  , contextParentNode     :: !(Maybe (Node cat))
  } deriving (Show, Eq)

-- | Convert macro to completion item
macroToCompletion :: AnyMacro -> CompletionItem
macroToCompletion (Any macro) = CompletionItem
  { completionLabel = mName macro
  , completionDetail = T.intercalate " " $ map renderLitOrHole (mLitSeq macro)
  , completionKind = MacroCompletion
  }
  where
    renderLitOrHole (L text) = text
    renderLitOrHole (H i) = "_" <> T.pack (show i)

-- | Generate hover information for a node
generateHoverInfo :: MixfixCat cat => Node cat -> HoverInfo
generateHoverInfo = undefined  -- Implementation depends on Node structure

-- | Generate syntax highlighting from AST
generateHighlighting :: MixfixCat cat => Node cat -> [HighlightRange]
generateHighlighting = undefined  -- Implementation depends on Node structure

-- | Convert parse error to diagnostic
errorToDiagnostic :: ParseError -> Diagnostic
errorToDiagnostic (ParseError span msg _) = Diagnostic
  { diagnosticRange = spanToByteRange span
  , diagnosticSeverity = Error
  , diagnosticMessage = msg
  }

-- | Convert span to byte range
spanToByteRange :: Span -> (Int, Int)
spanToByteRange = undefined  -- Needs position to byte offset conversion

------------------------------------------------------------
-- Change application
------------------------------------------------------------

-- | Apply a set of changes to text content
applyChanges :: Text -> [Change] -> Text
applyChanges content changes = 
  foldl applyChange content (reverse (sortChangesByOffset changes))

-- | Apply a single change to text content
applyChange :: Text -> Change -> Text
applyChange content (Change (start, end) newText) =
  let before = T.take start content
      after = T.drop end content
  in before <> newText <> after

-- | Sort changes by offset (highest first for reverse application)
sortChangesByOffset :: [Change] -> [Change]
sortChangesByOffset = undefined  -- Standard sorting implementation

-- | Merge overlapping ranges
mergeOverlappingRanges :: [(Int, Int)] -> [(Int, Int)]
mergeOverlappingRanges = undefined  -- Range merging algorithm

-- | Check if a region overlaps with a range
overlapsRegion :: (Int, Int) -> DirtyRegion -> Bool
overlapsRegion (start, end) region = 
  not (end <= dirtyStart region || start >= dirtyEnd region)

------------------------------------------------------------
-- Performance optimization
------------------------------------------------------------

-- | Cache for parsed subtrees (keyed by content hash)
type ASTCache cat = Map.Map Int (Node cat)

-- | Global AST cache with LRU eviction
{-# NOINLINE globalASTCache #-}
globalASTCache :: IORef (ASTCache cat)
globalASTCache = undefined  -- Would need proper initialization

-- | Look up cached AST by content hash
lookupCachedAST :: Int -> IO (Maybe (Node cat))
lookupCachedAST = undefined

-- | Insert AST into cache
insertCachedAST :: Int -> Node cat -> IO ()
insertCachedAST = undefined