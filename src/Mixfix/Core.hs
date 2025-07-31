{-# LANGUAGE GADTs, KindSignatures, DataKinds, TypeFamilies #-}
-- | Core types and typeclasses for the grammar-based mixfix system
--
-- This module provides the foundational abstractions that allow the mixfix
-- parsing system to work uniformly across different syntactic categories
-- (terms, types, proofs) while maintaining complete type safety.
module Mixfix.Core 
  ( -- * Core typeclass
    MixfixCat(..)
  , -- * Macro specification  
    Macro(..)
  , Assoc(..)
  , LitOrHole(..)
  , HoleIx
  , -- * Existential wrapper
    AnyMacro(..)
  ) where

import           Data.Text (Text)
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import qualified Data.HashMap.Strict as HM
import           Data.Hashable
import           Text.Megaparsec (SourcePos)

-- | Type-level index for holes in macro patterns
type HoleIx = Int

-- | Associativity specification for operators
data Assoc = LeftA | RightA | NonA
  deriving (Show, Eq, Ord)

-- | Elements in a macro's literal sequence - either fixed text or parameter holes
data LitOrHole 
  = L !Text    -- ^ Literal text that must appear exactly
  | H !HoleIx  -- ^ Hole for argument at given index
  deriving (Eq, Show, Ord)

-- | Core typeclass that every syntactic category must implement to use mixfix parsing
--
-- This abstracts over the specific AST node types while providing the operations
-- needed for generic parsing, conflict resolution, and pretty-printing.
class MixfixCat cat where
  -- | The AST node type for this category
  data Node cat :: *
  
  -- | Leaf values (identifiers, literals, etc.) for this category
  data Leaf cat :: *
  
  -- | Type-level map from hole indices to syntactic categories
  -- This allows macros to have holes of different types (e.g., term, type, proof)
  type family HoleMap cat :: *
  
  -- | Extract source position span from a leaf
  leafPos :: Leaf cat -> (SourcePos, SourcePos)
  
  -- | Extract cached source position span from a node
  nodeSpan :: Node cat -> (SourcePos, SourcePos)
  
  -- | Build a leaf node
  mkLeaf :: Leaf cat -> Node cat
  
  -- | Build a macro application node with computed span
  mkMacro :: (SourcePos, SourcePos) -> Macro cat -> [Node cat] -> Node cat

-- | A complete mixfix macro specification
--
-- This contains all information needed to parse and resolve conflicts for
-- a single macro pattern, regardless of syntactic category.
data Macro cat = Macro
  { mLitSeq    :: ![LitOrHole]           -- ^ Literal sequence pattern
  , mPrec      :: !Int                   -- ^ Precedence (1 = lowest)
  , mAssocInfo :: !(Maybe (Assoc, HoleIx)) -- ^ Associativity and fold axis
  , mHoleTy    :: !(HoleMap cat)         -- ^ Type information for holes
  , mName      :: !Text                  -- ^ Macro name for diagnostics
  } deriving (Show, Eq)

-- | Existential wrapper that erases the category type
--
-- This allows storing macros of different categories in the same data structure
-- while maintaining type safety through the existential quantification.
data AnyMacro where
  Any :: MixfixCat cat => Macro cat -> AnyMacro

instance Show AnyMacro where
  show (Any m) = "Any(" ++ show (mName m) ++ ")"

instance Eq AnyMacro where
  (Any m1) == (Any m2) = mName m1 == mName m2 && mLitSeq m1 == mLitSeq m2

instance Hashable AnyMacro where
  hashWithSalt s (Any m) = hashWithSalt s (mName m, mLitSeq m)

-- Helper functions for working with macros

-- | Extract the first literal from a macro pattern, if any
headLit :: Macro cat -> Maybe Text
headLit m = case mLitSeq m of
  (L t : _) -> Just t
  _         -> Nothing

-- | Extract the first two literals for two-level trie indexing
firstTwoLits :: Macro cat -> (Text, Text)
firstTwoLits m = 
  let lits = [t | L t <- mLitSeq m]
  in case lits of
    []       -> ("", "")
    [t]      -> (t, "")
    (t1:t2:_) -> (t1, t2)

-- | Check if two macros have the same literal sequence
sameLitSeq :: Macro cat1 -> Macro cat2 -> Bool
sameLitSeq m1 m2 = mLitSeq m1 == mLitSeq m2

-- | Count the number of holes in a macro
arity :: Macro cat -> Int
arity = length . filter isHole . mLitSeq
  where
    isHole (H _) = True
    isHole _     = False

-- | Check if a macro pattern is prefix (starts with literal)
isPrefix :: Macro cat -> Bool
isPrefix m = case mLitSeq m of
  (L _ : _) -> True
  _        -> False

-- | Check if a macro pattern is infix (has holes before and after)
isInfix :: Macro cat -> Bool
isInfix m = 
  let hasHoleBefore = any isHole (take 1 (mLitSeq m))
      hasHoleAfter = any isHole (drop 1 (mLitSeq m))
  in hasHoleBefore && hasHoleAfter
  where
    isHole (H _) = True
    isHole _     = False

-- | Check if a macro pattern is postfix (ends with literal)
isPostfix :: Macro cat -> Bool
isPostfix m = case reverse (mLitSeq m) of
  (L _ : _) -> True
  _        -> False