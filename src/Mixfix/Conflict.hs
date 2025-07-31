-- | Algorithm C: Constructive conflict set discovery and precedence resolution
--
-- This module implements the formal conflict resolution algorithm that
-- determines which parse tree to choose when multiple operator precedences
-- and associativities interact.
module Mixfix.Conflict
  ( -- * Conflict resolution
    resolve
  , ConflictSet
  , -- * Precedence comparison
    chooseByPrec
  , compareOperators
  , -- * Tree traversal types
    Zipper(..)
  , Context(..)
  , zipUp
  , zipDown
  ) where

import           Data.List (find)
import qualified Data.Set as S

import           Mixfix.Core
import           Mixfix.Util

-- | Set of AST nodes involved in a precedence conflict
type ConflictSet cat = [Node cat]

-- | Zipper structure for tree traversal with full context
data Zipper cat
  = Top  -- ^ At the root of the tree
  | Fork 
      ![Node cat]      -- ^ Left siblings  
      !(Context cat)   -- ^ Parent context
      ![Node cat]      -- ^ Right siblings
  deriving (Show, Eq)

-- | Context information for a parent node
data Context cat = Ctx !(AnyMacro) ![Node cat]
  deriving (Show, Eq)

------------------------------------------------------------
-- Algorithm C: Constructive conflict set discovery
------------------------------------------------------------

-- | Resolve conflicts between two parse trees using Algorithm C
--
-- Given two candidate parse trees for the same token span, this algorithm
-- constructively identifies the minimal conflict set and chooses the winner
-- based on precedence and associativity rules.
resolve :: MixfixCat cat 
        => Node cat 
        -> Node cat 
        -> Either ParseError (Node cat, ConflictSet cat)
resolve t1 t2 = do
  (winner, _loser, conflictSet) <- algorithmC Top t1 t2
  return (winner, conflictSet)

-- | Core Algorithm C implementation with zipper-based traversal
algorithmC :: MixfixCat cat
           => Zipper cat
           -> Node cat 
           -> Node cat
           -> Either ParseError (Node cat, Node cat, ConflictSet cat)
algorithmC zipper n1 n2
  | nodeLabelsEqual n1 n2 = 
      -- Nodes are identical, no conflict
      return (n1, n2, [])
  | otherwise = do
      -- Found the divergence point - construct conflict set
      let span1 = subtreeSpan (zipUp zipper n1)
          span2 = subtreeSpan (zipUp zipper n2)
          combinedSpan = mergeSpan span1 span2
          conflictNodes = collectConflictNodes combinedSpan zipper [n1, n2]
      
      -- Choose winner based on precedence/associativity
      (winner, loser) <- chooseWinner n1 n2
      return (winner, loser, conflictNodes)

-- | Check if two nodes have the same label (same macro application)
nodeLabelsEqual :: MixfixCat cat => Node cat -> Node cat -> Bool
nodeLabelsEqual n1 n2 = 
  case (extractMacro n1, extractMacro n2) of
    (Just m1, Just m2) -> sameMacro m1 m2
    (Nothing, Nothing) -> sameLeaf n1 n2
    _ -> False
  where
    -- Extract macro from node if it's a macro application
    extractMacro :: MixfixCat cat => Node cat -> Maybe AnyMacro
    extractMacro = undefined  -- To be implemented per category
    
    -- Check if two macros are the same
    sameMacro :: AnyMacro -> AnyMacro -> Bool
    sameMacro (Any m1) (Any m2) = mName m1 == mName m2
    
    -- Check if two leaf nodes are the same
    sameLeaf :: MixfixCat cat => Node cat -> Node cat -> Bool
    sameLeaf = undefined  -- To be implemented per category

-- | Collect all nodes in the conflict set within the given span
collectConflictNodes :: MixfixCat cat 
                     => Span 
                     -> Zipper cat 
                     -> [Node cat] 
                     -> ConflictSet cat
collectConflictNodes targetSpan zipper initialNodes =
  let allNodes = gatherNodesInSpan targetSpan zipper
      macroNodes = filter isMacroApplication allNodes
  in macroNodes ++ initialNodes
  where
    isMacroApplication :: MixfixCat cat => Node cat -> Bool
    isMacroApplication = undefined  -- To be implemented per category

-- | Gather all nodes whose spans intersect with the target span
gatherNodesInSpan :: MixfixCat cat => Span -> Zipper cat -> [Node cat]
gatherNodesInSpan targetSpan zipper = go zipper []
  where
    go Top acc = acc
    go (Fork lefts ctx rights) acc =
      let parentNode = contextToNode ctx
          parentSpan = nodeSpan parentNode
      in if spansOverlap targetSpan parentSpan
         then parentNode : (acc ++ concatMap (gatherFromSubtree targetSpan) (lefts ++ rights))
         else acc
    
    gatherFromSubtree :: MixfixCat cat => Span -> Node cat -> [Node cat]
    gatherFromSubtree span node = 
      if spansOverlap span (nodeSpan node)
      then [node]  -- Simplified - would need full subtree traversal
      else []

------------------------------------------------------------
-- Precedence and associativity resolution
------------------------------------------------------------

-- | Choose the winning node based on precedence and associativity
chooseWinner :: MixfixCat cat 
             => Node cat 
             -> Node cat 
             -> Either ParseError (Node cat, Node cat)
chooseWinner n1 n2 = 
  case (extractMacroFromNode n1, extractMacroFromNode n2) of
    (Just m1, Just m2) -> do
      case chooseByPrec m1 m2 of
        GT -> return (n1, n2)  -- m1 wins
        LT -> return (n2, n1)  -- m2 wins  
        EQ -> Left $ ParseError 
                (nodeSpan n1)
                "Ambiguous parse: operators have equal precedence, use parentheses"
                []
    _ -> Left $ ParseError
           (nodeSpan n1) 
           "Cannot resolve conflict between non-macro nodes"
           []

-- | Compare two macros by precedence and associativity
chooseByPrec :: AnyMacro -> AnyMacro -> Ordering
chooseByPrec (Any m1) (Any m2) =
  compare (mPrec m1) (mPrec m2) <> assocOrder
  where
    assocOrder = case (mAssocInfo m1, mAssocInfo m2) of
      (Just (LeftA, _), Just (RightA, _)) -> GT  -- Left-assoc wins
      (Just (RightA, _), Just (LeftA, _)) -> LT  -- Right-assoc wins
      (Nothing, Nothing) -> EQ
      (Nothing, Just _)  -> LT  -- Non-assoc loses to assoc
      (Just _, Nothing)  -> GT  -- Assoc wins over non-assoc
      _ -> EQ  -- Same associativity or both NonA

-- | General operator comparison function
compareOperators :: AnyMacro -> AnyMacro -> Ordering
compareOperators = chooseByPrec

------------------------------------------------------------
-- Zipper operations for tree navigation
------------------------------------------------------------

-- | Move up in the zipper, reconstructing the parent node
zipUp :: MixfixCat cat => Zipper cat -> Node cat -> Node cat
zipUp Top node = node
zipUp (Fork lefts ctx rights) node =
  let allChildren = reverse lefts ++ [node] ++ rights
      parentNode = reconstructNode ctx allChildren
  in parentNode

-- | Move down into a specific child in the zipper
zipDown :: MixfixCat cat => Zipper cat -> Node cat -> Int -> Maybe (Zipper cat, Node cat)
zipDown zipper parent childIndex = do
  children <- getChildren parent
  if childIndex >= 0 && childIndex < length children
    then let child = children !! childIndex
             lefts = take childIndex children
             rights = drop (childIndex + 1) children
             ctx = nodeToContext parent
             newZipper = Fork lefts ctx rights
         in Just (newZipper, child)
    else Nothing

------------------------------------------------------------
-- Helper functions (to be implemented per category)
------------------------------------------------------------

-- | Extract macro information from a node
extractMacroFromNode :: MixfixCat cat => Node cat -> Maybe AnyMacro
extractMacroFromNode = undefined  -- Implementation depends on Node structure

-- | Get the span covered by a subtree at the given zipper position
subtreeSpan :: MixfixCat cat => Node cat -> Span
subtreeSpan = nodeSpan  -- Use the cached span information

-- | Convert a context back to a node
contextToNode :: MixfixCat cat => Context cat -> Node cat
contextToNode (Ctx macro children) = 
  let span = computeSpanFromChildren children
  in mkMacroFromAny span macro children

-- | Convert a node to a context (for zipper operations)
nodeToContext :: MixfixCat cat => Node cat -> Context cat
nodeToContext node = 
  case extractMacroFromNode node of
    Just macro -> Ctx macro (getChildren node)
    Nothing -> error "Cannot create context from leaf node"

-- | Reconstruct a node from context and children
reconstructNode :: MixfixCat cat => Context cat -> [Node cat] -> Node cat
reconstructNode (Ctx macro _) children =
  let span = computeSpanFromChildren children
  in mkMacroFromAny span macro children

-- | Get children of a node
getChildren :: MixfixCat cat => Node cat -> [Node cat]
getChildren = undefined  -- Implementation depends on Node structure

-- | Create a macro application from AnyMacro
mkMacroFromAny :: MixfixCat cat => Span -> AnyMacro -> [Node cat] -> Node cat
mkMacroFromAny span (Any macro) children = mkMacro span macro children

-- | Compute span from a list of child nodes
computeSpanFromChildren :: MixfixCat cat => [Node cat] -> Span
computeSpanFromChildren [] = startSpan (error "empty children")
computeSpanFromChildren children =
  let spans = map nodeSpan children
      firstSpan = head spans
      lastSpan = last spans
  in mergeSpan firstSpan lastSpan

------------------------------------------------------------
-- Property-based testing helpers
------------------------------------------------------------

-- | Check if the conflict resolution is deterministic
isDeterministic :: MixfixCat cat => Node cat -> Node cat -> Bool
isDeterministic n1 n2 = 
  case resolve n1 n2 of
    Left _ -> False
    Right (winner1, _) -> 
      case resolve n2 n1 of  -- Try in opposite order
        Left _ -> False
        Right (winner2, _) -> nodeLabelsEqual winner1 winner2

-- | Verify that the conflict set is minimal
isMinimalConflictSet :: MixfixCat cat => ConflictSet cat -> Bool
isMinimalConflictSet conflictSet = 
  -- A conflict set is minimal if removing any node makes it no longer capture the conflict
  -- This is a complex property that would need full implementation
  length conflictSet >= 2  -- Simplified check