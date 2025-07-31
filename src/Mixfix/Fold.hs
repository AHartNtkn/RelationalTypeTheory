-- | Generalized associativity (fold axis) chain generation
--
-- This module implements the generalized associativity system that allows
-- operators to chain along any argument position, not just binary infix.
-- For example, if_then_else_ can chain on the "then" branch.
module Mixfix.Fold
  ( -- * Chain generation
    genChain
  , genChainParser
  , -- * Associativity helpers
    isChainable
  , getChainAxis
  , -- * Chain structure analysis
    ChainInfo(..)
  , analyzeChain
  , flattenChain
  ) where

import           Control.Monad (when)
import           Control.Monad.Fix (fix)
import           Data.Text (Text)
import qualified Data.Text as T

import           Mixfix.Core
import           Mixfix.Util

-- | Information about a chain structure
data ChainInfo cat = ChainInfo
  { chainMacro    :: !(Macro cat)       -- ^ The chaining macro
  , chainAxis     :: !HoleIx            -- ^ Which argument position chains
  , chainDirection :: !Assoc            -- ^ Left or right associativity  
  , chainDepth    :: !Int               -- ^ How deep the chain goes
  , chainElements :: ![Node cat]        -- ^ The individual chain elements
  } deriving (Show, Eq)

------------------------------------------------------------
-- Core chain generation
------------------------------------------------------------

-- | Generate a chain parser for an associative macro
--
-- This creates an auxiliary non-terminal that can chain on the specified
-- argument position, implementing the fold axis semantics.
genChain :: MixfixCat cat 
         => Macro cat 
         -> (Int -> Parser (Node cat))  -- ^ Parser for hole at given index
         -> Parser (Node cat)
genChain macro@(Macro _ _ (Just (dir, n)) _ _) holeParser =
  case dir of
    LeftA  -> genLeftChain macro n holeParser
    RightA -> genRightChain macro n holeParser  
    NonA   -> fail $ "Cannot chain non-associative macro: " ++ T.unpack (mName macro)
genChain macro _ = 
  fail $ "Cannot chain macro without associativity info: " ++ T.unpack (mName macro)

-- | Generate a chain parser that can be used in expression parsing
genChainParser :: MixfixCat cat 
               => Macro cat 
               -> Parser (Node cat)
genChainParser macro@(Macro _ _ (Just (dir, n)) _ _) =
  fix $ \chainParser ->
    let holeParser i = if i == n then chainParser else atomParser
    in parseMacroWithHoles macro holeParser
genChainParser macro = 
  fail $ "Cannot create chain parser for non-associative macro: " ++ T.unpack (mName macro)

------------------------------------------------------------
-- Left-associative chains
------------------------------------------------------------

-- | Generate left-associative chain: ((a op b) op c) op d
genLeftChain :: MixfixCat cat
             => Macro cat
             -> HoleIx
             -> (Int -> Parser (Node cat))
             -> Parser (Node cat)
genLeftChain macro chainHole holeParser = do
  -- Parse the base case first
  baseArgs <- parseNonChainHoles macro chainHole holeParser
  firstChainArg <- holeParser chainHole
  
  let initialNode = assembleMacro macro (insertAt chainHole firstChainArg baseArgs)
  
  -- Parse additional chain elements
  fix $ \continue -> do
    moreChain <- optional $ try $ do
      -- Look for the same macro pattern
      nextChainArg <- holeParser chainHole
      return nextChainArg
    
    case moreChain of
      Nothing -> return initialNode
      Just nextArg -> do
        let newArgs = insertAt chainHole nextArg [initialNode]
        let newNode = assembleMacro macro newArgs
        continue  -- Continue chaining

------------------------------------------------------------
-- Right-associative chains  
------------------------------------------------------------

-- | Generate right-associative chain: a op (b op (c op d))
genRightChain :: MixfixCat cat
              => Macro cat
              -> HoleIx  
              -> (Int -> Parser (Node cat))
              -> Parser (Node cat)
genRightChain macro chainHole holeParser = do
  -- Parse non-chain holes first
  baseArgs <- parseNonChainHoles macro chainHole holeParser
  
  -- Parse the chain recursively
  chainArg <- parseChainArg
  
  return $ assembleMacro macro (insertAt chainHole chainArg baseArgs)
  
  where
    parseChainArg = do
      -- Try to parse another instance of the same macro
      chainedMacro <- optional $ try $ genRightChain macro chainHole holeParser
      case chainedMacro of
        Just chained -> return chained
        Nothing -> holeParser chainHole  -- Base case

------------------------------------------------------------
-- Chain analysis and manipulation
------------------------------------------------------------

-- | Check if a macro can be chained
isChainable :: Macro cat -> Bool
isChainable (Macro _ _ (Just (_, _)) _ _) = True
isChainable _ = False

-- | Get the chain axis for a macro
getChainAxis :: Macro cat -> Maybe (Assoc, HoleIx)
getChainAxis (Macro _ _ assocInfo _ _) = assocInfo

-- | Analyze the structure of a chain
analyzeChain :: MixfixCat cat => Node cat -> Maybe (ChainInfo cat)
analyzeChain node = do
  macro <- extractMacroFromNode node
  (dir, axis) <- getChainAxis macro
  let elements = extractChainElements node axis
      depth = length elements
  return $ ChainInfo macro axis dir depth elements

-- | Flatten a chain into a list of elements
flattenChain :: MixfixCat cat => Node cat -> [Node cat]
flattenChain node = 
  case analyzeChain node of
    Just info -> chainElements info
    Nothing -> [node]  -- Not a chain, return singleton

-- | Extract chain elements by following the chain axis
extractChainElements :: MixfixCat cat => Node cat -> HoleIx -> [Node cat]
extractChainElements node axis = go node []
  where
    go currentNode acc =
      case extractMacroFromNode currentNode of
        Just macro | isChainAtAxis macro axis ->
          case getChildAt currentNode axis of
            Just childAtAxis -> go childAtAxis (currentNode : acc)
            Nothing -> currentNode : acc
        _ -> currentNode : acc
    
    isChainAtAxis macro ax = 
      case getChainAxis macro of
        Just (_, axis') -> axis' == ax
        Nothing -> False

------------------------------------------------------------
-- Helper functions
------------------------------------------------------------

-- | Parse all holes except the chain hole
parseNonChainHoles :: MixfixCat cat
                   => Macro cat
                   -> HoleIx
                   -> (Int -> Parser (Node cat))
                   -> Parser [Node cat]
parseNonChainHoles macro chainHole holeParser = 
  sequence $ map parseHole [0 .. arity macro - 1]
  where
    parseHole i | i == chainHole = return Nothing  -- Skip chain hole
                | otherwise = Just <$> holeParser i

-- | Parse a macro with explicit hole parsers
parseMacroWithHoles :: MixfixCat cat
                    => Macro cat
                    -> (Int -> Parser (Node cat))
                    -> Parser (Node cat)
parseMacroWithHoles macro holeParser = do
  args <- sequence $ map holeParser [0 .. arity macro - 1]
  return $ assembleMacro macro args

-- | Assemble a macro application from arguments
assembleMacro :: MixfixCat cat => Macro cat -> [Node cat] -> Node cat
assembleMacro macro args = 
  let span = computeSpanFromArgs args
  in mkMacro span macro args

-- | Compute span from argument list
computeSpanFromArgs :: MixfixCat cat => [Node cat] -> Span
computeSpanFromArgs [] = startSpan (error "no arguments")
computeSpanFromArgs args = 
  let spans = map nodeSpan args
  in foldl1 mergeSpan spans

-- | Insert element at specific position in list
insertAt :: Int -> a -> [a] -> [a]
insertAt 0 x xs = x : xs
insertAt n x (y:ys) = y : insertAt (n-1) x ys
insertAt _ x [] = [x]

-- | Extract macro from node (placeholder - implemented per category)
extractMacroFromNode :: MixfixCat cat => Node cat -> Maybe (Macro cat)
extractMacroFromNode = undefined  -- Implementation depends on Node structure

-- | Get child node at specific argument position
getChildAt :: MixfixCat cat => Node cat -> Int -> Maybe (Node cat)
getChildAt = undefined  -- Implementation depends on Node structure

-- | Basic atom parser (placeholder)
atomParser :: MixfixCat cat => Parser (Node cat)
atomParser = undefined  -- Implementation depends on category

------------------------------------------------------------
-- Chain validation and properties
------------------------------------------------------------

-- | Validate that a chain is well-formed
validateChain :: MixfixCat cat => ChainInfo cat -> Bool
validateChain info = 
  chainDepth info > 0 && 
  length (chainElements info) == chainDepth info &&
  all (isCompatibleWithChain (chainMacro info)) (chainElements info)

-- | Check if a node is compatible with a chain
isCompatibleWithChain :: MixfixCat cat => Macro cat -> Node cat -> Bool
isCompatibleWithChain chainMacro node =
  case extractMacroFromNode node of
    Just nodeMacro -> sameMacro (Any chainMacro) (Any nodeMacro)
    Nothing -> False  -- Leaf nodes can be in chains
  where
    sameMacro (Any m1) (Any m2) = mName m1 == mName m2

-- | Count the depth of a chain
chainLength :: MixfixCat cat => Node cat -> Int
chainLength node = 
  case analyzeChain node of
    Just info -> chainDepth info
    Nothing -> 1

-- | Check if two chains can be merged
canMergeChains :: MixfixCat cat => ChainInfo cat -> ChainInfo cat -> Bool
canMergeChains info1 info2 = 
  sameMacro (Any (chainMacro info1)) (Any (chainMacro info2)) &&
  chainAxis info1 == chainAxis info2 &&
  chainDirection info1 == chainDirection info2
  where
    sameMacro (Any m1) (Any m2) = mName m1 == mName m2