{-# LANGUAGE LambdaCase #-}
-- | Core syntax definitions for RelTT
-- This module contains all the core data types for the RelTT language.
module Core.Syntax
  ( -- * Terms
    Term (..),
    termPos,
    -- * Relational Types
    RType (..),
    rtypePos,
    -- * Proofs
    Proof (..),
    proofPos,
    -- * Theorem Arguments
    TheoremArg (..),
    -- * Declarations
    Declaration (..),
    MacroBody (..),
    Binding (..),
    RelJudgment (..),
    -- * Contexts and Environments
    TypingContext (..),
    TypeEnvironment (..),
    MacroEnvironment (..),
    TheoremEnvironment (..),
    -- * Module System
    ImportDeclaration (..),
    ExportDeclaration (..),
    Visibility (..),
    ModuleInfo (..),
    ModulePath,
    -- * Fixity and Parameters
    Fixity (..),
    VarKind (..),
    ParamInfo (..),
    MacroSig,
  )
where

import qualified Data.Map as Map
import Text.Megaparsec (SourcePos)

-- | Lambda calculus terms
data Term
  = Var String Int SourcePos         -- ^ Bound variable with name, de Bruijn index, position
  | FVar String SourcePos            -- ^ Free variable (unresolved)
  | Lam String Term SourcePos        -- ^ Lambda abstraction
  | App Term Term SourcePos          -- ^ Application
  | TMacro String [Term] SourcePos   -- ^ Term macro application
  deriving (Show, Eq)

-- | Relational types
data RType
  = RVar String Int SourcePos           -- ^ Bound relational variable
  | FRVar String SourcePos              -- ^ Free relational variable (unresolved)
  | RMacro String [RType] SourcePos     -- ^ Type macro application
  | Arr RType RType SourcePos           -- ^ Arrow type (→)
  | All String RType SourcePos          -- ^ Universal quantification (∀)
  | Conv RType SourcePos                -- ^ Converse (˘)
  | Comp RType RType SourcePos          -- ^ Composition (∘)
  | Prom Term SourcePos                 -- ^ Promotion (⌈t⌉)
  deriving (Show, Eq)

-- | Proof terms
data Proof
  = PVar String Int SourcePos                              -- ^ Bound proof variable
  | FPVar String SourcePos                                 -- ^ Free proof variable (unresolved)
  | PTheoremApp String [TheoremArg] SourcePos              -- ^ Theorem application
  | LamP String RType Proof SourcePos                      -- ^ Proof lambda
  | AppP Proof Proof SourcePos                             -- ^ Proof application
  | TyApp Proof RType SourcePos                            -- ^ Type application
  | TyLam String Proof SourcePos                           -- ^ Type lambda
  | ConvProof Term Proof Term SourcePos                    -- ^ Conversion
  | ConvIntro Proof SourcePos                              -- ^ Converse introduction (∪ᵢ)
  | ConvElim Proof SourcePos                               -- ^ Converse elimination (∪ₑ)
  | Iota Term Term SourcePos                               -- ^ Term promotion (ι⟨t,u⟩)
  | RhoElim String Term Term Proof Proof SourcePos         -- ^ Rho elimination
  | Pair Proof Proof SourcePos                             -- ^ Pair (⟨p,q⟩)
  | Pi Proof String String String Proof SourcePos          -- ^ Pi (π p - x . u . v .q)
  | PMacro String [Proof] SourcePos                        -- ^ Proof macro
  deriving (Show, Eq)

-- | Relational judgment: t [R] t'
data RelJudgment = RelJudgment Term RType Term
  deriving (Show, Eq)

-- | Macro body variants
data MacroBody
  = TermMacro Term
  | RelMacro RType
  | ProofMacro Proof
  deriving (Show, Eq)

-- | Top-level declarations
data Declaration
  = MacroDef String [String] MacroBody
  | TheoremDef String [Binding] RelJudgment Proof
  | ImportDecl ImportDeclaration
  | ExportDecl ExportDeclaration
  | FixityDecl Fixity String
  deriving (Show, Eq)

-- | Theorem parameter bindings
data Binding
  = TermBinding String              -- ^ (t : Term)
  | RelBinding String               -- ^ (R : Rel)
  | ProofBinding String RelJudgment -- ^ (p : t[R]u)
  deriving (Show, Eq)

-- | Arguments to theorem applications
data TheoremArg
  = TermArg Term
  | RelArg RType
  | ProofArg Proof
  deriving (Show, Eq)

-- | Context for type checking, tracking bound variables and their types
data TypingContext = TypingContext
  { termBindings :: Map.Map String (Int, RType), -- ^ var name -> (de Bruijn index, type)
    relBindings :: Map.Map String Int,            -- ^ rel var name -> de Bruijn index
    proofBindings :: Map.Map String (Int, Int, RelJudgment), -- ^ proof var -> (index, termDepthWhenStored, judgment)
    gensymCounter :: Int -- ^ counter for generating fresh variable names
  }
  deriving (Show, Eq)

-- | Environment mapping type variables to relational types
data TypeEnvironment = TypeEnvironment
  { typeVarBindings :: Map.Map String RType
  }
  deriving (Show, Eq)

-- | Fixity declarations for mixfix operators
data Fixity
  = Infixl Int  -- ^ left associative, level 0-9
  | Infixr Int  -- ^ right associative, level 0-9
  | InfixN Int  -- ^ non-associative, level 0-9
  | Prefix Int  -- ^ prefix operator, level 0-9
  | Postfix Int -- ^ postfix operator, level 0-9
  | Closed Int  -- ^ closed/delimited operator, level 0-9
  deriving (Show, Eq)

-- | Kind of variable for macro parameters
data VarKind = TermK | RelK | ProofK deriving (Show, Eq)

-- | Information about a macro parameter
data ParamInfo = ParamInfo
  { pName :: String
  , pKind :: VarKind
  , pBinds :: Bool   -- ^ True if this parameter introduces a binder
  , pDeps :: [Int]   -- ^ indices of binder-params this argument lives under
  } deriving (Show, Eq)

-- | Macro signature with parameter information
type MacroSig = ([ParamInfo], MacroBody)

-- | Environment for macro definitions
data MacroEnvironment = MacroEnvironment
  { macroDefinitions :: Map.Map String MacroSig, -- ^ macro name -> (param info, body)
    macroFixities :: Map.Map String Fixity       -- ^ macro name -> fixity declaration
  }
  deriving (Show, Eq)

-- | Environment for theorem definitions
data TheoremEnvironment = TheoremEnvironment
  { theoremDefinitions :: Map.Map String ([Binding], RelJudgment, Proof) -- ^ theorem name -> (bindings, judgment, proof)
  }
  deriving (Show, Eq)

-- | Module system types

-- | Type alias for module file paths
type ModulePath = String

-- | Visibility of declarations
data Visibility = Public | Private
  deriving (Show, Eq)

-- | Import declaration types
data ImportDeclaration
  = ImportModule ModulePath              -- ^ import "path/file.rtt"
  | ImportModuleAs ModulePath String     -- ^ import "path/file.rtt" as ModName
  | ImportOnly ModulePath [String]       -- ^ import "path/file.rtt" (name1, name2)
  deriving (Show, Eq)

-- | Export declaration
data ExportDeclaration = ExportSymbols [String] -- ^ export Symbol1, Symbol2
  deriving (Show, Eq)

-- | Information about a loaded module
data ModuleInfo = ModuleInfo
  { modulePath :: ModulePath,
    moduleAlias :: Maybe String,
    loadedMacros :: MacroEnvironment,
    loadedTheorems :: TheoremEnvironment,
    exportedSymbols :: [String], -- ^ empty list means export all
    importDeclarations :: [ImportDeclaration] -- ^ track imports for dependency graph
  }
  deriving (Show, Eq)

-- | Extract source position from Term
termPos :: Term -> SourcePos
termPos (Var _ _ pos) = pos
termPos (FVar _ pos) = pos
termPos (Lam _ _ pos) = pos
termPos (App _ _ pos) = pos
termPos (TMacro _ _ pos) = pos

-- | Extract source position from RType
rtypePos :: RType -> SourcePos
rtypePos (RVar _ _ pos) = pos
rtypePos (FRVar _ pos) = pos
rtypePos (RMacro _ _ pos) = pos
rtypePos (Arr _ _ pos) = pos
rtypePos (All _ _ pos) = pos
rtypePos (Conv _ pos) = pos
rtypePos (Comp _ _ pos) = pos
rtypePos (Prom _ pos) = pos

-- | Extract source position from Proof
proofPos :: Proof -> SourcePos
proofPos (PVar _ _ pos) = pos
proofPos (FPVar _ pos) = pos
proofPos (PTheoremApp _ _ pos) = pos
proofPos (LamP _ _ _ pos) = pos
proofPos (AppP _ _ pos) = pos
proofPos (TyApp _ _ pos) = pos
proofPos (TyLam _ _ pos) = pos
proofPos (ConvProof _ _ _ pos) = pos
proofPos (ConvIntro _ pos) = pos
proofPos (ConvElim _ pos) = pos
proofPos (Iota _ _ pos) = pos
proofPos (RhoElim _ _ _ _ _ pos) = pos
proofPos (Pair _ _ pos) = pos
proofPos (Pi _ _ _ _ _ pos) = pos
proofPos (PMacro _ _ pos) = pos