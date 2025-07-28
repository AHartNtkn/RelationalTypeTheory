{-# LANGUAGE LambdaCase #-}
module Lib
  ( Term (..),
    RType (..),
    Proof (..),
    TheoremArg (..),
    Declaration (..),
    MacroBody (..),
    Binding (..),
    RelJudgment (..),
    TypingContext (..),
    TypeEnvironment (..),
    MacroEnvironment (..),
    TheoremEnvironment (..),
    ImportDeclaration (..),
    ExportDeclaration (..),
    Visibility (..),
    ModuleInfo (..),
    ModulePath,
    Fixity (..),
    VarKind (..),
    ParamInfo (..),
    MacroSig,
    termPos,
    rtypePos,
    proofPos,
  )
where

import qualified Data.Map as Map
import Text.Megaparsec (SourcePos)

data Term
  = Var String Int SourcePos
  | Lam String Term SourcePos
  | App Term Term SourcePos
  | TMacro String [Term] SourcePos
  deriving (Show, Eq)

data RType
  = RVar String Int SourcePos
  | RMacro String [RType] SourcePos
  | Arr RType RType SourcePos
  | All String RType SourcePos
  | Conv RType SourcePos
  | Comp RType RType SourcePos
  | Prom Term SourcePos
  deriving (Show, Eq)

data Proof
  = PVar String Int SourcePos
  | PTheoremApp String [TheoremArg] SourcePos -- theorem application (empty list = no args)
  | LamP String RType Proof SourcePos
  | AppP Proof Proof SourcePos
  | TyApp Proof RType SourcePos
  | TyLam String Proof SourcePos
  | ConvProof Term Proof Term SourcePos
  | ConvIntro Proof SourcePos
  | ConvElim Proof SourcePos
  | Iota Term Term SourcePos
  | RhoElim String Term Term Proof Proof SourcePos
  | Pair Proof Proof SourcePos
  | Pi Proof String String String Proof SourcePos  -- π p - x . u . v .q (x:term, u,v:proofs)
  | PMacro String [Proof] SourcePos             -- NEW
  deriving (Show, Eq)

data RelJudgment = RelJudgment Term RType Term -- t [R] t'
  deriving (Show, Eq)

data MacroBody
  = TermMacro Term
  | RelMacro RType
  | ProofMacro Proof
  deriving (Show, Eq)

data Declaration
  = MacroDef String [String] MacroBody
  | TheoremDef String [Binding] RelJudgment Proof
  | ImportDecl ImportDeclaration
  | ExportDecl ExportDeclaration
  | FixityDecl Fixity String -- NEW: fixity declaration for a macro
  deriving (Show, Eq)

data Binding
  = TermBinding String -- (t : Term)
  | RelBinding String -- (R : Rel)
  | ProofBinding String RelJudgment -- (p : t[R]u)
  deriving (Show, Eq)

-- | Arguments to theorem applications
data TheoremArg
  = TermArg Term
  | RelArg RType
  | ProofArg Proof
  deriving (Show, Eq)

-- | Context for type checking, tracking bound variables and their types
data TypingContext = TypingContext
  { termBindings :: Map.Map String (Int, RType), -- var name -> (de Bruijn index, type)
    relBindings :: Map.Map String Int, -- rel var name -> de Bruijn index
    proofBindings :: Map.Map String (Int, Int, RelJudgment), -- proof var -> (index, termDepthWhenStored, judgment)
    gensymCounter :: Int -- counter for generating fresh variable names
  }
  deriving (Show, Eq)

-- | Environment mapping type variables to relational types
data TypeEnvironment = TypeEnvironment
  { typeVarBindings :: Map.Map String RType
  }
  deriving (Show, Eq)

-- | Fixity declarations for mixfix operators
data Fixity
  = Infixl Int -- left associative, level 0-9
  | Infixr Int -- right associative, level 0-9
  | InfixN Int -- non-associative, level 0-9
  | Prefix Int -- prefix operator, level 0-9
  | Postfix Int -- postfix operator, level 0-9
  | Closed Int -- closed/delimited operator, level 0-9
  deriving (Show, Eq)

-- | Kind of variable for macro parameters
data VarKind = TermK | RelK | ProofK deriving (Show, Eq)

-- | Information about a macro parameter
data ParamInfo = ParamInfo
  { pName :: String
  , pKind :: VarKind
  , pBinds :: Bool          -- ^ True if this parameter introduces a binder
  , pDeps :: [Int]         -- ^ indices of binder-params this argument lives under
  } deriving (Show, Eq)

-- | Macro signature with parameter information
type MacroSig = ([ParamInfo], MacroBody)

-- | Environment for macro definitions
data MacroEnvironment = MacroEnvironment
  { macroDefinitions :: Map.Map String MacroSig, -- macro name -> (param info, body)
    macroFixities :: Map.Map String Fixity -- macro name -> fixity declaration
  }
  deriving (Show, Eq)

-- | Environment for theorem definitions
data TheoremEnvironment = TheoremEnvironment
  { theoremDefinitions :: Map.Map String ([Binding], RelJudgment, Proof) -- theorem name -> (bindings, judgment, proof)
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
  = ImportModule ModulePath -- import "path/file.rtt"
  | ImportModuleAs ModulePath String -- import "path/file.rtt" as ModName
  | ImportOnly ModulePath [String] -- import "path/file.rtt" (name1, name2)
  deriving (Show, Eq)

-- | Export declaration
data ExportDeclaration = ExportSymbols [String] -- export Symbol1, Symbol2
  deriving (Show, Eq)

-- | Information about a loaded module
data ModuleInfo = ModuleInfo
  { modulePath :: ModulePath,
    moduleAlias :: Maybe String,
    loadedMacros :: MacroEnvironment,
    loadedTheorems :: TheoremEnvironment,
    exportedSymbols :: [String], -- empty list means export all
    importDeclarations :: [ImportDeclaration] -- track imports for dependency graph
  }
  deriving (Show, Eq)

-- | Extract source position from Term
termPos :: Term -> SourcePos
termPos (Var _ _ pos) = pos
termPos (Lam _ _ pos) = pos
termPos (App _ _ pos) = pos
termPos (TMacro _ _ pos) = pos

-- | Extract source position from RType
rtypePos :: RType -> SourcePos
rtypePos (RVar _ _ pos) = pos
rtypePos (RMacro _ _ pos) = pos
rtypePos (Arr _ _ pos) = pos
rtypePos (All _ _ pos) = pos
rtypePos (Conv _ pos) = pos
rtypePos (Comp _ _ pos) = pos
rtypePos (Prom _ pos) = pos

-- | Extract source position from Proof
proofPos :: Proof -> SourcePos
proofPos (PVar _ _ pos) = pos
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



