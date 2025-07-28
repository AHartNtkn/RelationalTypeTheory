{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module RawAst 
  ( Name(..)
  , Fixity(..)
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
import Lib (Fixity(..))

-- Raw (unresolved) identifiers - just strings, no de Bruijn indices
newtype Name = Name String deriving (Show, Eq, Ord)

-- Raw terms - no context, no validation
data RawTerm
  = RTVar Name SourcePos                    -- x
  | RTLam Name RawTerm SourcePos           -- λ x . t  
  | RTApp RawTerm RawTerm SourcePos        -- t u
  | RTMacro Name [RawTerm] SourcePos       -- user mixfix/macros _+_ etc.
  deriving (Show, Eq)

-- Raw relational types - no context, no validation  
data RawRType
  = RRVar Name SourcePos                   -- X
  | RRArr RawRType RawRType SourcePos      -- T → U
  | RRAll Name RawRType SourcePos          -- ∀ X . T
  | RRComp RawRType RawRType SourcePos     -- R ∘ S
  | RRConv RawRType SourcePos              -- R ˘
  | RRMacro Name [RawRType] SourcePos      -- mixfix on rel-types
  | RRApp  RawRType RawRType SourcePos     -- *juxtaposition*  R S
  | RRProm RawTerm SourcePos               -- promotion ⌈t⌉
  deriving (Show, Eq)

-- Raw proofs - no context, no validation
data RawProof  
  = RPVar Name SourcePos                                -- p
  | RPApp RawProof RawProof SourcePos                   -- p q
  | RPTheorem Name [RawArg] SourcePos                   -- theorem applications (NO arity check here)
  | RPLamP Name RawRType RawProof SourcePos            -- λ p : R . q (proof lambda)  
  | RPLamT Name RawProof SourcePos                      -- Λ X . p (type lambda)
  | RPAppT RawProof RawRType SourcePos                  -- p T (type application)
  | RPConv RawTerm RawProof RawTerm SourcePos          -- t ⇃ p ⇂ u (conversion)
  | RPIota RawTerm RawTerm SourcePos                    -- ι⟨t,u⟩ (term promotion)
  | RPRho Name RawTerm RawTerm RawProof RawProof SourcePos  -- ρ{ x . t1, t2} p1 - p2 (rho elimination)
  | RPPi RawProof Name Name Name RawProof SourcePos          -- π(p,x .u.v,q) - x:term, u,v:proofs
  | RPConvIntro RawProof SourcePos                      -- ∪ᵢ p (converse intro)
  | RPConvElim RawProof SourcePos                       -- ∪ₑ p (converse elim)
  | RPPair RawProof RawProof SourcePos                  -- ⟨p,q⟩ (pair)
  | RPMixfix Name [RawProof] SourcePos                  -- mixfix on proofs
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
    RTLam n t _        -> RTLam n (stripPos t) dummyPos
    RTApp f x _        -> RTApp (stripPos f) (stripPos x) dummyPos
    RTMacro n ts _     -> RTMacro n (map stripPos ts) dummyPos

instance StripPos RawRType where
  stripPos = \case
    RRVar n _          -> RRVar n dummyPos
    RRArr a b _        -> RRArr (stripPos a) (stripPos b) dummyPos
    RRAll n t _        -> RRAll n (stripPos t) dummyPos
    RRComp a b _       -> RRComp (stripPos a) (stripPos b) dummyPos
    RRConv r _         -> RRConv (stripPos r) dummyPos
    RRMacro n rs _     -> RRMacro n (map stripPos rs) dummyPos
    RRApp  a b _       -> RRApp  (stripPos a) (stripPos b) dummyPos
    RRProm t _         -> RRProm (stripPos t) dummyPos

instance StripPos RawProof where
  stripPos = \case
    RPVar n _                    -> RPVar n dummyPos
    RPApp p q _                  -> RPApp (stripPos p) (stripPos q) dummyPos
    RPTheorem n as _             -> RPTheorem n (map stripPos as) dummyPos
    RPLamP n rt p _              -> RPLamP n (stripPos rt) (stripPos p) dummyPos
    RPLamT n p _                 -> RPLamT n (stripPos p) dummyPos
    RPAppT p rt _                -> RPAppT (stripPos p) (stripPos rt) dummyPos
    RPConv t1 p t2 _             -> RPConv (stripPos t1) (stripPos p) (stripPos t2) dummyPos
    RPIota t u _                 -> RPIota (stripPos t) (stripPos u) dummyPos
    RPRho n t1 t2 p1 p2 _        -> RPRho n (stripPos t1) (stripPos t2)
                                         (stripPos p1) (stripPos p2) dummyPos
    RPPi p x r y q _             -> RPPi (stripPos p) x r y (stripPos q) dummyPos
    RPConvIntro p _              -> RPConvIntro (stripPos p) dummyPos
    RPConvElim  p _              -> RPConvElim  (stripPos p) dummyPos
    RPPair p q _                 -> RPPair (stripPos p) (stripPos q) dummyPos
    RPMixfix n ps _              -> RPMixfix n (map stripPos ps) dummyPos

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
