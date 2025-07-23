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
    MixfixPart (..),
    parseMixfixPattern,
    splitMixfix,
    holes,
    defaultFixity,
    mixfixKeywords,
    termPos,
    rtypePos,
    proofPos,
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
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
  | Pi Proof String String String Proof SourcePos
  deriving (Show, Eq)

data RelJudgment = RelJudgment Term RType Term -- t [R] t'
  deriving (Show, Eq)

data MacroBody
  = TermMacro Term
  | RelMacro RType
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
  deriving (Show, Eq)

-- | Environment for macro definitions
data MacroEnvironment = MacroEnvironment
  { macroDefinitions :: Map.Map String ([String], MacroBody), -- macro name -> (params, body)
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

-- | Principled representation of mixfix pattern parts
data MixfixPart = Hole | Literal String
  deriving (Show, Eq)

-- | Parse a mixfix identifier into its constituent parts
-- "_+_" -> [Hole, Literal "+", Hole]
-- "if_then_else_" -> [Literal "if", Hole, Literal "then", Hole, Literal "else", Hole]
-- "not_" -> [Literal "not", Hole]
-- "_!" -> [Hole, Literal "!"]
-- "regular" -> [Literal "regular"]
parseMixfixPattern :: String -> [MixfixPart]
parseMixfixPattern = go
  where
    go [] = []
    go ('_' : rest) = Hole : go rest
    go str =
      let (literal, rest) = span (/= '_') str
       in if null literal
            then go rest
            else Literal literal : go rest

-- | Count the number of holes in a mixfix pattern
holes :: String -> Int
holes = length . filter isHole . parseMixfixPattern
  where
    isHole Hole = True
    isHole _ = False

-- | Extract just the literal parts from a mixfix pattern (for backward compatibility)
splitMixfix :: String -> [String]
splitMixfix = map extractLiteral . filter isLiteral . parseMixfixPattern
  where
    isLiteral (Literal _) = True
    isLiteral _ = False
    extractLiteral (Literal s) = s
    extractLiteral _ = error "extractLiteral called on non-literal"

-- | Default fixity for macros (preserves old behavior)
defaultFixity :: Fixity
defaultFixity = Prefix 9

-- | Extract all mixfix keywords (literal segments) from macro definitions
mixfixKeywords :: MacroEnvironment -> Set.Set String
mixfixKeywords env =
  Set.fromList
    . filter (not . null)
    . concatMap splitMixfix
    . filter ('_' `elem`) -- Only process mixfix patterns (containing underscores)
    . Map.keys
    $ macroDefinitions env
