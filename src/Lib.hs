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
    MixfixPart (..),
    parseMixfixPattern,
    splitMixfix,
    holes,
    defaultFixity,
    mixfixKeywords,
    extendMacroEnvironment,
    updateAt,
    noMacros,
    noTheorems,
    termPos,
    rtypePos,
    proofPos,
    inferParamInfosTerm,
    inferParamInfosRel,
    inferParamInfosProof,
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State.Strict
import Data.List (foldl')
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

-- | Default fixity for macros based on hole count and position
defaultFixity :: String -> Fixity
defaultFixity name = case holes name of
  2 -> Infixl 6   -- Haskell's default for binary infix
  1 | head name == '_' -> Postfix 8
    | last name == '_' -> Prefix  9
  _ -> Prefix 9

-- | Extract all mixfix keywords (literal segments) from macro definitions
mixfixKeywords :: MacroEnvironment -> Set.Set String
mixfixKeywords env =
  Set.fromList
    . filter (not . null)
    . concatMap splitMixfix
    . filter ('_' `elem`) -- Only process mixfix patterns (containing underscores)
    . Map.keys
    $ macroDefinitions env

------------------------------------------------------------------
-- | Insert / overwrite a macro together with its (possibly default)
--   fixity.  Used by the elaborator **and** by the test helper in
--   MixfixSpec.
extendMacroEnvironment
  :: String              -- ^ name  (mix‑fix or ordinary)
  -> [String]            -- ^ parameters
  -> MacroBody
  -> Fixity              -- ^ chosen fixity
  -> MacroEnvironment -> MacroEnvironment
extendMacroEnvironment n ps body fix env =
  let pInfo = case body of
                TermMacro tm  -> inferParamInfosTerm ps tm
                RelMacro  rt  -> inferParamInfosRel  ps rt
                ProofMacro pr -> inferParamInfosProof ps pr
  in env { macroDefinitions = Map.insert n (pInfo, body) (macroDefinitions env)
         , macroFixities    = Map.insert n fix            (macroFixities    env)
         }

------------------------------------------------------------------
-- | Empty environments used by tests.
noMacros :: MacroEnvironment
noMacros = MacroEnvironment Map.empty Map.empty

noTheorems :: TheoremEnvironment
noTheorems = TheoremEnvironment Map.empty

-- | Safe list update at a given index
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt i f xs = zipWith (\j x -> if j == i then f x else x) [0..] xs

------------------------------------------------------------
--  Macro parameter inference
------------------------------------------------------------

-- | Infer parameter information for term macros
inferParamInfosTerm :: [String] -> Term -> [ParamInfo]
inferParamInfosTerm ps body =
  let initPI = [ ParamInfo nm TermK False [] | nm <- ps ]
      idxOf  = Map.fromList (zip ps [0..])
      walk :: [Int] -> Term -> State [ParamInfo] ()
      walk stk term = case term of
        Lam v t _ -> do
          case Map.lookup v idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pBinds=True}))
            _      -> pure ()
          walk (maybe stk (:stk) (Map.lookup v idxOf)) t
        Var v _ _ -> case Map.lookup v idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pDeps = Set.toAscList
                                                        (Set.fromList (pDeps pi) `Set.union` Set.fromList stk)}))
            _      -> pure ()
        App f x _     -> walk stk f >> walk stk x
        TMacro _ as _ -> mapM_ (walk stk) as
  in execState (walk [] body) initPI

-- | Infer parameter information for relational type macros
inferParamInfosRel :: [String] -> RType -> [ParamInfo]
inferParamInfosRel ps body =
  let initPI = [ ParamInfo nm RelK False [] | nm <- ps ]
      idxOf  = Map.fromList (zip ps [0..])
      go :: [Int] -> RType -> State [ParamInfo] ()
      go stk rtype = case rtype of
        All v t _ -> do
          case Map.lookup v idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pBinds=True, pKind=RelK}))
            _      -> pure ()
          go (maybe stk (:stk) (Map.lookup v idxOf)) t
        RVar v _ _ -> case Map.lookup v idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pDeps = Set.toAscList
                                                        (Set.fromList (pDeps pi) `Set.union` Set.fromList stk)}))
            _      -> pure ()
        Arr a b _   -> go stk a >> go stk b
        Comp a b _  -> go stk a >> go stk b
        Conv r _    -> go stk r
        RMacro _ as _ -> mapM_ (go stk) as
        Prom _ _    -> pure ()
  in execState (go [] body) initPI

-- | Infer parameter information for proof macros
inferParamInfosProof :: [String] -> Proof -> [ParamInfo]
inferParamInfosProof ps body =
  let initPI = [ ParamInfo nm ProofK False [] | nm <- ps ]
      idxOf  = Map.fromList (zip ps [0..])
      walk :: [Int] -> Proof -> State [ParamInfo] ()
      walk stk proof = case proof of
        -- LamP binds a proof variable
        LamP v _ p _ -> do
          case Map.lookup v idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pBinds=True, pKind=ProofK}))
            _      -> pure ()
          walk (maybe stk (:stk) (Map.lookup v idxOf)) p
        
        -- TyLam binds a type variable (relation)
        TyLam v p _ -> do
          case Map.lookup v idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pBinds=True, pKind=RelK}))
            _      -> pure ()
          walk (maybe stk (:stk) (Map.lookup v idxOf)) p
        
        -- RhoElim binds a term variable
        RhoElim x _ _ p1 p2 _ -> do
          case Map.lookup x idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pBinds=True, pKind=TermK}))
            _      -> pure ()
          let xStk = maybe stk (:stk) (Map.lookup x idxOf)
          walk stk p1
          walk xStk p2
        
        -- Pi binds 1 term variable (x) and 2 proof variables (u, v)
        Pi p1 x u v p2 _ -> do
          -- Mark x as a term binder
          case Map.lookup x idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pBinds=True, pKind=TermK}))
            _      -> pure ()
          -- Mark u as a proof binder
          case Map.lookup u idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pBinds=True, pKind=ProofK}))
            _      -> pure ()
          -- Mark v as a proof binder
          case Map.lookup v idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pBinds=True, pKind=ProofK}))
            _      -> pure ()
          
          walk stk p1
          -- Build the stack for p2 (which can see x, u, v)
          let xIdx = Map.lookup x idxOf
              uIdx = Map.lookup u idxOf
              vIdx = Map.lookup v idxOf
              newStk = foldl' (\s mi -> maybe s (:s) mi) stk [xIdx, uIdx, vIdx]
          walk newStk p2
        
        -- Variable references
        PVar v _ _ -> case Map.lookup v idxOf of
            Just i -> modify (updateAt i (\pi -> pi{pDeps = Set.toAscList
                                                        (Set.fromList (pDeps pi) `Set.union` Set.fromList stk)}))
            _      -> pure ()
        
        -- Recursive cases
        AppP p1 p2 _       -> walk stk p1 >> walk stk p2
        TyApp p _ _        -> walk stk p
        ConvProof _ p _ _  -> walk stk p
        ConvIntro p _      -> walk stk p
        ConvElim p _       -> walk stk p
        Pair p1 p2 _       -> walk stk p1 >> walk stk p2
        PMacro _ as _      -> mapM_ (walk stk) as
        
        -- Non-recursive cases
        PTheoremApp _ _ _  -> pure ()
        Iota _ _ _         -> pure ()
  in execState (walk [] body) initPI
