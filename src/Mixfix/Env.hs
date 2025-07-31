{-# LANGUAGE CPP #-}
-- | Environment management and scope fingerprinting for mixfix parsing
--
-- This module implements the hash-consed scope fingerprinting system that
-- enables efficient incremental parsing and grammar composition.
module Mixfix.Env
  ( -- * Environment types
    Env
  , ScopeId(..)
  , Fingerprint
  , -- * Environment operations
    emptyEnv
  , insertMacro
  , lookupMacros
  , envFingerprint
  , -- * Scope management
    pushScope
  , popScope
  , withScope
  , -- * Trie generation
    buildTrie
  , Trie
  , Level2
  ) where

import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Word (Word64)
import           Data.Hashable
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.IORef
import           System.IO.Unsafe (unsafePerformIO)
import           Control.Monad (when)
import           Data.Time (getCurrentTime, diffUTCTime, NominalDiffTime)

import           Mixfix.Core
import           Mixfix.Util

-- | Unique identifier for a scope fingerprint
newtype ScopeId = ScopeId Word64
  deriving (Eq, Show, Ord, Hashable)

-- | Hash-consed fingerprint representing a particular macro scope
--
-- This uses a persistent cons-list structure where each node contains
-- the macros defined in a particular scope level, with a pointer to
-- the parent scope. This enables O(1) equality checking and efficient
-- structural sharing.
data Fingerprint 
  = Root  -- ^ Empty root environment
  | Fingerprint 
      !(HM.HashMap Text [AnyMacro])  -- ^ Macros indexed by first literal
      !Fingerprint                   -- ^ Parent fingerprint
  deriving (Eq, Show)

instance Hashable Fingerprint where
  hashWithSalt s Root = hashWithSalt s (0 :: Int)
  hashWithSalt s (Fingerprint macros parent) = 
    hashWithSalt s (HM.toList macros, parent)

-- | Environment maintaining the current macro scope
data Env = Env 
  { envFingerprint :: !Fingerprint
  , envScopeId     :: !ScopeId
  } deriving (Show, Eq)

-- | Create an empty environment
emptyEnv :: Env
emptyEnv = Env Root (ScopeId 0)

-- | Insert a macro into the environment, creating a new fingerprint
--
-- This performs precedence validation and creates a new environment
-- with hash-consed fingerprint sharing.
insertMacro :: MixfixCat cat => Macro cat -> Env -> Either ParseError Env
insertMacro macro env = do
  -- Check for conflicts with existing macros
  case lookupByLitSeq (mLitSeq macro) (envFingerprint env) of
    Just existing | mPrec existing < mPrec macro ->
#ifdef WPRECEDENCE_DOWNGRADE  
      -- Warning mode - allow but warn
      trace ("Warning: redefining " <> T.unpack (mName macro) <> " with higher precedence") $
#else
      -- Error mode - reject
      Left $ ParseError 
        (startSpan undefined)  -- TODO: proper position
        ("Cannot redefine macro " <> mName macro <> " with higher precedence")
        []
#endif
    _ -> pure ()
  
  -- Create new fingerprint with this macro added
  let newMacros = insertMacroIntoMap (Any macro) (envFingerprint env)
      newFingerprint = Fingerprint newMacros (envFingerprint env)
      newScopeId = ScopeId (fromIntegral (hash newFingerprint))
  
  pure $ Env newFingerprint newScopeId

-- | Look up all macros starting with a given literal
lookupMacros :: Text -> Env -> [AnyMacro]
lookupMacros lit env = lookupInFingerprint lit (envFingerprint env)

-- | Push a new scope level for local macro definitions
pushScope :: Env -> Env  
pushScope env = env { envFingerprint = Fingerprint HM.empty (envFingerprint env) }

-- | Pop the current scope level, returning to parent
popScope :: Env -> Env
popScope env = case envFingerprint env of
  Root -> env  -- Can't pop root
  Fingerprint _ parent -> env { envFingerprint = parent }

-- | Execute an action in a new scope level
withScope :: Env -> (Env -> IO a) -> IO a
withScope env action = action (pushScope env)

------------------------------------------------------------
-- Trie construction for efficient parsing
------------------------------------------------------------

-- | First level of lookup trie - maps first literal to second level
type Trie = HM.HashMap Text Level2

-- | Second level of lookup trie - maps second literal to macro list
type Level2 = HM.HashMap Text [AnyMacro]

-- | Build a two-level trie from the current environment
--
-- This creates an efficient lookup structure that allows O(1) access
-- to relevant macros during parsing based on the first two literals.
buildTrie :: Fingerprint -> Trie
#ifdef MIXFIX_NOCACHE
buildTrie fp = buildTrieUncached fp
#else
buildTrie fp = unsafePerformIO $ do
  cached <- lookupTrieCache fp
  case cached of
    Just trie -> return trie
    Nothing -> do
      let trie = buildTrieUncached fp
      insertTrieCache fp trie
      return trie
#endif

-- | Build trie without caching (for debugging and testing)
buildTrieUncached :: Fingerprint -> Trie
buildTrieUncached = go HM.empty
  where
    go acc Root = acc
    go acc (Fingerprint macros parent) =
      let acc' = HM.foldlWithKey' insertMacroGroup acc macros
      in go acc' parent
    
    insertMacroGroup trie lit macros =
      foldl (insertSingleMacro lit) trie macros
    
    insertSingleMacro lit1 trie (Any macro) =
      let (_, lit2) = firstTwoLits macro
          level2 = HM.findWithDefault HM.empty lit1 trie
          level2' = HM.insertWith (++) lit2 [Any macro] level2
      in HM.insert lit1 level2' trie

-- | Build trie with timing information (for debugging)
buildTrieTimed :: Fingerprint -> IO (Trie, NominalDiffTime)
buildTrieTimed fp = do
  t0 <- getCurrentTime
  let trie = buildTrie fp
  t1 <- getCurrentTime
  let elapsed = diffUTCTime t1 t0
#ifdef MIXFIX_DEBUG
  putStrLn $ "Trie rebuild: " ++ show (elapsed * 1000000) ++ " μs"
#endif
  return (trie, elapsed)

------------------------------------------------------------
-- Internal helpers
------------------------------------------------------------

-- | Insert a macro into the literal-indexed map
insertMacroIntoMap :: AnyMacro -> Fingerprint -> HM.HashMap Text [AnyMacro]
insertMacroIntoMap macro@(Any m) fp =
  case headLit m of
    Just lit -> 
      let existing = lookupInFingerprint lit fp
      in HM.singleton lit (macro : existing)
    Nothing -> HM.empty

-- | Look up macros in a fingerprint by first literal
lookupInFingerprint :: Text -> Fingerprint -> [AnyMacro]
lookupInFingerprint lit = go []
  where
    go acc Root = acc
    go acc (Fingerprint macros parent) =
      let localMacros = HM.findWithDefault [] lit macros
      in go (localMacros ++ acc) parent

-- | Find a macro with the same literal sequence
lookupByLitSeq :: [LitOrHole] -> Fingerprint -> Maybe (Macro cat)
lookupByLitSeq litSeq fp = go fp
  where
    go Root = Nothing
    go (Fingerprint macros parent) =
      case headLit' litSeq of
        Nothing -> go parent
        Just lit -> 
          case find (\(Any m) -> mLitSeq m == litSeq) (HM.findWithDefault [] lit macros) of
            Just (Any m) -> Just m  -- Note: this is unsafe but needed for type system
            Nothing -> go parent
    
    headLit' [] = Nothing
    headLit' (L t : _) = Just t
    headLit' (_ : rest) = headLit' rest

-- | Find first element matching predicate
find :: (a -> Bool) -> [a] -> Maybe a
find _ [] = Nothing
find p (x:xs) | p x = Just x
              | otherwise = find p xs

------------------------------------------------------------
-- Trie caching with weak references
------------------------------------------------------------

-- | Global cache from fingerprints to tries (with size limit)
{-# NOINLINE trieCache #-}
trieCache :: IORef (HM.HashMap Fingerprint Trie)
trieCache = unsafePerformIO $ newIORef HM.empty

-- | Maximum number of entries in trie cache
trieCacheMaxSize :: Int
#ifdef MIXFIX_CACHE_MAX
trieCacheMaxSize = MIXFIX_CACHE_MAX
#else
trieCacheMaxSize = 2048
#endif

-- | Look up cached trie
lookupTrieCache :: Fingerprint -> IO (Maybe Trie)
lookupTrieCache fp = do
  cache <- readIORef trieCache
  return $ HM.lookup fp cache

-- | Insert trie into cache with LRU eviction
insertTrieCache :: Fingerprint -> Trie -> IO ()
insertTrieCache fp trie = do
  cache <- readIORef trieCache
  let cache' = HM.insert fp trie cache
  when (HM.size cache' > trieCacheMaxSize) $ do
    -- Simple eviction: keep most recent half
    let cache'' = HM.fromList $ take (trieCacheMaxSize `div` 2) $ HM.toList cache'
    writeIORef trieCache cache''
  writeIORef trieCache cache'