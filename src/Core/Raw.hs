{-# LANGUAGE OverloadedStrings, LambdaCase #-}
-- | Raw (unelaborated) AST types
-- This module contains the raw AST types as parsed from source,
-- before elaboration into the typed AST.
module Core.Raw 
  ( Name(..)
  , RawTerm(..)
  , RawRType(..)
  , RawProof(..)
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

-- Raw terms - parser + mixfix generated constructors
data RawTerm
  = RTVar Name SourcePos                    -- x
  | RTApp RawTerm RawTerm SourcePos        -- t u
  | RTMacro Name [RawTerm] SourcePos       -- user mixfix/macros _+_ etc.
  | RTParens RawTerm SourcePos             -- (t) - explicit parentheses
  deriving (Show, Eq)

-- Raw relational types - parser + mixfix generated constructors  
data RawRType
  = RRVar Name SourcePos                   -- X
  | RRApp  RawRType RawRType SourcePos     -- *juxtaposition*  R S
  | RRMacro Name [RawRType] SourcePos      -- mixfix on rel-types
  | RRParens RawRType SourcePos            -- (R) - explicit parentheses
  deriving (Show, Eq)

-- Raw proofs - parser + mixfix generated constructors
data RawProof  
  = RPVar Name SourcePos                                -- p
  | RPApp RawProof RawProof SourcePos                   -- p q
  | RPMixfix Name [RawProof] SourcePos                  -- mixfix on proofs
  | RPParens RawProof SourcePos                         -- (p) - explicit parentheses
  deriving (Show, Eq)

-- Raw theorem/macro arguments - can be terms, types, or proofs
data RawArg 
  = RawTermArg RawTerm 
  | RawRelArg RawRType 
  | RawProofArg RawProof
  deriving (Show, Eq)

-- Raw import declarations  
data RawImportDeclaration
  = RawImportModule String                    -- import "path";
  deriving (Show, Eq)

-- Raw declarations
data RawDeclaration
  = RawMacro Name [Name] RawMacroBody         -- macro name params ≔ body
  | RawTheorem Name [RawBinding] RawJudgment RawProof  -- ⊢ name bindings : judgment ≔ proof
  | RawFixityDecl Fixity Name                 -- fixity declarations
  | RawImportDecl RawImportDeclaration        -- import declarations
  deriving (Show, Eq)

-- Raw macro bodies (can be terms or relational types)
data RawMacroBody
  = RawTermBody RawTerm
  | RawRelBody RawRType
  | RawProofBody RawProof
  deriving (Show, Eq)

-- Raw bindings for theorem parameters
data RawBinding
  = RawTermBinding Name             -- (x : Term)
  | RawRelBinding Name              -- (R : Rel) 
  | RawProofBinding Name RawJudgment -- (p : judgment)
  deriving (Show, Eq)

-- Raw relational judgments t [R] u
data RawJudgment = RawJudgment RawTerm RawRType RawTerm
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

instance StripPos RawTerm where
  stripPos = \case
    RTVar n _          -> RTVar n dummyPos
    RTApp f x _        -> RTApp (stripPos f) (stripPos x) dummyPos
    RTMacro n ts _     -> RTMacro n (map stripPos ts) dummyPos
    RTParens t _       -> RTParens (stripPos t) dummyPos

instance StripPos RawRType where
  stripPos = \case
    RRVar n _          -> RRVar n dummyPos
    RRApp  a b _       -> RRApp  (stripPos a) (stripPos b) dummyPos
    RRMacro n rs _     -> RRMacro n (map stripPos rs) dummyPos
    RRParens r _       -> RRParens (stripPos r) dummyPos

instance StripPos RawProof where
  stripPos = \case
    RPVar n _                    -> RPVar n dummyPos
    RPApp p q _                  -> RPApp (stripPos p) (stripPos q) dummyPos
    RPMixfix n ps _              -> RPMixfix n (map stripPos ps) dummyPos
    RPParens p _                 -> RPParens (stripPos p) dummyPos

instance StripPos RawArg where
  stripPos (RawTermArg t)  = RawTermArg  (stripPos t)
  stripPos (RawRelArg r)   = RawRelArg   (stripPos r)
  stripPos (RawProofArg p) = RawProofArg (stripPos p)

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
    RawMacro n ps b          -> RawMacro n ps (stripPos b)
    RawTheorem n bs j p      -> RawTheorem n (map stripPos bs)
                                             (stripPos j) (stripPos p)
    RawFixityDecl f n        -> RawFixityDecl f n
    RawImportDecl i          -> RawImportDecl (stripPos i)

instance StripPos RawImportDeclaration where
  stripPos = \case
    RawImportModule path -> RawImportModule path