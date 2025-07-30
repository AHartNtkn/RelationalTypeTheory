{-# LANGUAGE OverloadedStrings, LambdaCase #-}
-- | Unified raw (unelaborated) AST type
-- This module contains the unified raw AST type as parsed from source,
-- before elaboration into the typed AST.
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
  ) where

import Text.Megaparsec (SourcePos, initialPos)
import Core.Syntax (Fixity(..))

-- Raw (unresolved) identifiers - just strings, no de Bruijn indices
newtype Name = Name String deriving (Show, Eq, Ord)

-- Unified raw AST - parser + mixfix generated constructors
-- This replaces RawTerm, RawRType, and RawProof with a single type
data Raw
  = RawVar Name SourcePos                    -- x, X, p
  | RawApp Raw Raw SourcePos                 -- t u, R S, p q
  | RawMacro Name [Raw] SourcePos            -- user mixfix/macros _+_ etc.
  | RawParens Raw SourcePos                  -- (t), (R), (p) - explicit parentheses
  deriving (Show, Eq)

-- Raw theorem/macro arguments - now just Raw
data RawArg = RawArg Raw
  deriving (Show, Eq)

-- Raw import declarations  
data RawImportDeclaration
  = RawImportModule String                    -- import "path";
  deriving (Show, Eq)

-- Raw declarations
data RawDeclaration
  = RawMacroDef Name [Name] RawMacroBody      -- macro name params ≔ body
  | RawTheorem Name [RawBinding] RawJudgment Raw  -- ⊢ name bindings : judgment ≔ proof
  | RawFixityDecl Fixity Name                 -- fixity declarations
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

class StripPos a where
  stripPos :: a -> a

instance StripPos Raw where
  stripPos = \case
    RawVar n _          -> RawVar n dummyPos
    RawApp f x _        -> RawApp (stripPos f) (stripPos x) dummyPos
    RawMacro n ts _     -> RawMacro n (map stripPos ts) dummyPos
    RawParens t _       -> RawParens (stripPos t) dummyPos

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
    RawFixityDecl f n        -> RawFixityDecl f n
    RawImportDecl i          -> RawImportDecl (stripPos i)

instance StripPos RawImportDeclaration where
  stripPos = \case
    RawImportModule path -> RawImportModule path