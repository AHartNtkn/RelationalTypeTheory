{-# LANGUAGE OverloadedStrings, LambdaCase, TypeFamilies #-}
-- | Unified raw (unelaborated) AST type with mixfix support
-- This module contains the unified raw AST type as parsed from source,
-- before elaboration into the typed AST. It implements MixfixCat to support
-- the new grammar-based mixfix parsing system.
module Core.Raw 
  ( Name(..)
  , Raw(..)
  , RawArg(..)
  , RawDeclaration(..)
  , RawMacroBody(..)
  , RawBinding(..)
  , RawJudgment(..)
  , RawImportDeclaration(..)
  , Positioned(..)
  , nameText
  , nameString
  , getPos
  , getValue
  , dummyPos
  , StripPos(..)
  -- Mixfix integration
  , RawHoleMap
  ) where

import Text.Megaparsec (SourcePos, initialPos)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM

import Mixfix.Core
import Mixfix.Util

-- Raw (unresolved) identifiers - just strings, no de Bruijn indices
newtype Name = Name String deriving (Show, Eq, Ord)

-- Unified raw AST - supports mixfix parsing with proper spans
-- This replaces RawTerm, RawRType, and RawProof with a single type
data Raw
  = RawVar Name Span                         -- x, X, p
  | RawApp Raw Raw Span                      -- t u, R S, p q (application)
  | RawParens Raw Span                       -- (t), (R), (p) - explicit parentheses
  | RawMixfix T.Text [Raw] Span              -- mixfix macro application
  deriving (Show, Eq)

-- Leaf values for the Raw category
data RawLeaf
  = RawVarLeaf Name                          -- Variable/identifier leaf
  | RawLitLeaf T.Text                        -- Literal value leaf
  deriving (Show, Eq)

-- Hole type mapping for Raw category (unified - everything is Raw)
type RawHoleMap = IM.IntMap ()  -- All holes have the same type in Raw

-- Raw theorem/macro arguments - now just Raw
data RawArg = RawArg Raw
  deriving (Show, Eq)

-- Raw import declarations  
data RawImportDeclaration
  = RawImportModule String                    -- import "path";
  deriving (Show, Eq)

-- Raw declarations (no more fixity declarations)
data RawDeclaration
  = RawMacroDef Name [Name] RawMacroBody      -- macro name params ≔ body
  | RawTheorem Name [RawBinding] RawJudgment Raw  -- ⊢ name bindings : judgment ≔ proof
  | RawImportDecl RawImportDeclaration        -- import declarations
  deriving (Show, Eq)

-- Raw macro bodies (can be terms, relational types, or proofs)
data RawMacroBody
  = RawTermBody Raw
  | RawRelBody Raw
  | RawProofBody Raw
  deriving (Show, Eq)

-- Raw bindings for theorem parameters
data RawBinding
  = RawTermBinding Name             -- (x : Term)
  | RawRelBinding Name              -- (R : Rel) 
  | RawProofBinding Name RawJudgment -- (p : judgment)
  deriving (Show, Eq)

-- Raw relational judgments t [R] u
data RawJudgment = RawJudgment Raw Raw Raw
  deriving (Show, Eq)

-- Position information (carried through from parser)
data Positioned a = Positioned a SourcePos
  deriving (Show, Eq)

-- Helper functions for working with names
nameText :: Name -> String  
nameText (Name s) = s

nameString :: Name -> String
nameString (Name s) = s

-- Helper functions for extracting position info
getPos :: Positioned a -> SourcePos
getPos (Positioned _ pos) = pos

getValue :: Positioned a -> a  
getValue (Positioned val _) = val

dummyPos :: SourcePos
dummyPos = initialPos ""

dummySpan :: Span
dummySpan = (dummyPos, dummyPos)

------------------------------------------------------------
-- MixfixCat instance for Raw
------------------------------------------------------------

instance MixfixCat Raw where
  data Node Raw = RawNode Raw deriving (Show, Eq)
  data Leaf Raw = RawLeafNode RawLeaf deriving (Show, Eq)
  type HoleMap Raw = RawHoleMap
  
  leafPos (RawLeafNode (RawVarLeaf (Name n))) = 
    let pos = initialPos n in (pos, pos)  -- Approximate span
  leafPos (RawLeafNode (RawLitLeaf t)) = 
    let pos = initialPos (T.unpack t) in (pos, pos)
    
  nodeSpan (RawNode raw) = rawSpan raw
    where
      rawSpan (RawVar _ span) = span
      rawSpan (RawApp _ _ span) = span  
      rawSpan (RawParens _ span) = span
      rawSpan (RawMixfix _ _ span) = span
      
  mkLeaf leaf = RawNode $ case leaf of
    RawLeafNode (RawVarLeaf name) -> RawVar name (leafPos leaf)
    RawLeafNode (RawLitLeaf text) -> RawVar (Name (T.unpack text)) (leafPos leaf)
    
  mkMacro span macro args =
    let rawArgs = [raw | RawNode raw <- args]
        macroName = mName macro
    in RawNode $ RawMixfix macroName rawArgs span

class StripPos a where
  stripPos :: a -> a

instance StripPos Raw where
  stripPos = \case
    RawVar n _              -> RawVar n dummySpan
    RawApp f x _            -> RawApp (stripPos f) (stripPos x) dummySpan
    RawParens t _           -> RawParens (stripPos t) dummySpan
    RawMixfix name args _   -> RawMixfix name (map stripPos args) dummySpan

instance StripPos RawArg where
  stripPos (RawArg r) = RawArg (stripPos r)

instance StripPos RawJudgment where
  stripPos (RawJudgment t r u) =
    RawJudgment (stripPos t) (stripPos r) (stripPos u)

instance StripPos RawMacroBody where
  stripPos (RawTermBody t) = RawTermBody (stripPos t)
  stripPos (RawRelBody r)  = RawRelBody  (stripPos r)
  stripPos (RawProofBody p) = RawProofBody (stripPos p)

instance StripPos RawBinding where
  stripPos = \case
    RawTermBinding  n      -> RawTermBinding  n
    RawRelBinding   n      -> RawRelBinding   n
    RawProofBinding n j    -> RawProofBinding n (stripPos j)

instance StripPos RawDeclaration where
  stripPos = \case
    RawMacroDef n ps b     -> RawMacroDef n ps (stripPos b)
    RawTheorem n bs j p      -> RawTheorem n (map stripPos bs)
                                             (stripPos j) (stripPos p)
    RawImportDecl i          -> RawImportDecl (stripPos i)

instance StripPos RawImportDeclaration where
  stripPos = \case
    RawImportModule path -> RawImportModule path