{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

-- | Unified, binder-aware macro application for Term, RType and Proof.
-- This module provides a generic infrastructure that eliminates code duplication
-- across the three AST categories while maintaining identical public APIs.

module Operations.Generic.Macro
  ( -- | Typeclass for generic macro operations
    MacroAst(..)
    -- | Generic helper algorithms
  , renameBinderVarsG
  , substituteArgsG
    -- | Top-level elaborator for all AST categories
  , elabMacroAppG
    -- | Generic parameter inference  
  , ParamInferAst(..)
  , inferParamInfosG
  ) where

import           Text.Megaparsec                (initialPos)
import           Core.Errors
import           Core.Syntax
import           Operations.Generic.Shift (ShiftAst(..), shift, shiftAbove)
import           Operations.Generic.Substitution (SubstAst(..))
import qualified Operations.Resolve as Operations.Resolve
import           Operations.Resolve (ResolveAst(..), ResolveEnv)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Control.Monad.State.Strict
import           Data.List (foldl')
import           Core.Utils (updateAt)

--------------------------------------------------------------------------------
-- | Minimal operations that any AST category must provide for macro processing
--------------------------------------------------------------------------------

class SubstAst a => MacroAst a where
  -- | de Bruijn shift free variables by given amount
  shiftN      :: Int -> a -> a
  -- | Extract variable name if this node is a variable, Nothing otherwise
  varNameOf   :: a -> Maybe String
  -- | Rename binder variable names (α-conversion only, indices untouched)
  mapBinders  :: (String -> String) -> a -> a
  -- | Convert to a MacroArg for heterogeneous collections
  toArg       :: a -> MacroArg
  -- | Try to extract from a MacroArg (fails if wrong constructor)
  fromArg     :: MacroArg -> Maybe a

--------------------------------------------------------------------------------
-- | Term instance
--------------------------------------------------------------------------------

instance MacroAst Term where
  shiftN           = shift
  varNameOf (Var v _ _) = Just v
  varNameOf (FVar v _)  = Just v
  varNameOf _           = Nothing
  mapBinders f = go
    where
      go tm = case tm of
        Lam n b p      -> Lam (f n) (go b) p
        App l r p      -> App (go l) (go r) p
        TMacro n as p  -> TMacro n as p  -- MacroArgs are already heterogeneous, no mapping needed
        other          -> other
  toArg = MTerm
  fromArg (MTerm t) = Just t
  fromArg _ = Nothing

--------------------------------------------------------------------------------
-- | Relational type instance  
--------------------------------------------------------------------------------

instance MacroAst RType where
  shiftN           = shiftAbove 0
  varNameOf (RVar v _ _) = Just v
  varNameOf (FRVar v _)  = Just v
  varNameOf _            = Nothing
  mapBinders f = go
    where
      go rt = case rt of
        All n b p      -> All (f n) (go b) p
        Arr a b p      -> Arr (go a) (go b) p
        Comp a b p     -> Comp (go a) (go b) p
        Conv r p       -> Conv (go r) p
        RMacro n as p  -> RMacro n as p  -- MacroArgs are already heterogeneous
        other          -> other
  toArg = MRel
  fromArg (MRel r) = Just r
  fromArg _ = Nothing

--------------------------------------------------------------------------------
-- | Proof instance
--------------------------------------------------------------------------------

instance MacroAst Proof where
  shiftN      = shift
  varNameOf (PVar v _ _) = Just v
  varNameOf (FPVar v _)  = Just v
  varNameOf _            = Nothing
  mapBinders f = go
    where
      go pr = case pr of
        LamP n t b p          -> LamP (f n) t (go b) p
        TyLam n b p           -> TyLam (f n) (go b) p
        RhoElim x t u p1 p2 p -> RhoElim (f x) t u (go p1) (go p2) p
        Pi p1 x u v p2 p      -> Pi (go p1) (f x) (f u) (f v) (go p2) p
        AppP l r p            -> AppP (go l) (go r) p
        TyApp q t p           -> TyApp (go q) t p
        ConvProof t q u p     -> ConvProof t (go q) u p
        ConvIntro q p         -> ConvIntro (go q) p
        ConvElim  q p         -> ConvElim  (go q) p
        Pair l r p            -> Pair (go l) (go r) p
        PMacro n as p         -> PMacro n as p  -- MacroArgs are already heterogeneous
        other                 -> other
  toArg = MProof
  fromArg (MProof p) = Just p
  fromArg _ = Nothing

--------------------------------------------------------------------------------
-- | Typeclass for generic parameter inference
--------------------------------------------------------------------------------

class ParamInferAst a where
  -- | Get the VarKind for this AST type
  getVarKind :: a -> VarKind
  -- | Walk the AST to infer parameter information
  walkForParams :: Map.Map String Int -> [Int] -> a -> State [ParamInfo] ()

--------------------------------------------------------------------------------
-- | Generic parameter inference
--------------------------------------------------------------------------------

-- | Generic parameter information inference
inferParamInfosG :: ParamInferAst a => [String] -> a -> [ParamInfo]
inferParamInfosG ps body =
  let initPI = [ ParamInfo nm (getVarKind body) False [] | nm <- ps ]
      idxOf  = Map.fromList (zip ps [0..])
  in execState (walkForParams idxOf [] body) initPI

--------------------------------------------------------------------------------
-- | Instances for ParamInferAst
--------------------------------------------------------------------------------

instance ParamInferAst Term where
  getVarKind _ = TermK
  walkForParams idxOf stk term = case term of
    Lam v t _ -> do
      case Map.lookup v idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pBinds=True}))
        _      -> pure ()
      walkForParams idxOf (maybe stk (:stk) (Map.lookup v idxOf)) t
    Var v _ _ -> case Map.lookup v idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pDeps = Set.toAscList
                                                    (Set.fromList (pDeps paramInfo) `Set.union` Set.fromList stk)}))
        _      -> pure ()
    App f x _     -> walkForParams idxOf stk f >> walkForParams idxOf stk x
    TMacro _ as _ -> mapM_ (walkForParams idxOf stk) as

instance ParamInferAst RType where
  getVarKind _ = RelK
  walkForParams idxOf stk rtype = case rtype of
    All v t _ -> do
      case Map.lookup v idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pBinds=True, pKind=RelK}))
        _      -> pure ()
      walkForParams idxOf (maybe stk (:stk) (Map.lookup v idxOf)) t
    RVar v _ _ -> case Map.lookup v idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pDeps = Set.toAscList
                                                    (Set.fromList (pDeps paramInfo) `Set.union` Set.fromList stk)
                                                   , pKind = RelK}))
        _      -> pure ()
    Arr a b _   -> walkForParams idxOf stk a >> walkForParams idxOf stk b
    Comp a b _  -> walkForParams idxOf stk a >> walkForParams idxOf stk b
    Conv r _    -> walkForParams idxOf stk r
    RMacro _ as _ -> mapM_ (walkForParams idxOf stk) as
    Prom _ _    -> pure ()

instance ParamInferAst Proof where
  getVarKind _ = ProofK
  walkForParams idxOf stk proof = case proof of
    -- LamP binds a proof variable
    LamP v ty p _ -> do
      case Map.lookup v idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pBinds=True, pKind=ProofK}))
        _      -> pure ()
      walkForParams idxOf stk ty
      walkForParams idxOf (maybe stk (:stk) (Map.lookup v idxOf)) p
    
    -- TyLam binds a type variable (relation)
    TyLam v p _ -> do
      case Map.lookup v idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pBinds=True, pKind=RelK}))
        _      -> pure ()
      walkForParams idxOf (maybe stk (:stk) (Map.lookup v idxOf)) p
    
    -- RhoElim binds a term variable
    RhoElim x _ _ p1 p2 _ -> do
      case Map.lookup x idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pBinds=True, pKind=TermK}))
        _      -> pure ()
      let xStk = maybe stk (:stk) (Map.lookup x idxOf)
      walkForParams idxOf stk p1
      walkForParams idxOf xStk p2
    
    -- Pi binds 1 term variable (x) and 2 proof variables (u, v)
    Pi p1 x u v p2 _ -> do
      -- Mark x as a term binder
      case Map.lookup x idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pBinds=True, pKind=TermK}))
        _      -> pure ()
      -- Mark u as a proof binder
      case Map.lookup u idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pBinds=True, pKind=ProofK}))
        _      -> pure ()
      -- Mark v as a proof binder
      case Map.lookup v idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pBinds=True, pKind=ProofK}))
        _      -> pure ()
      
      walkForParams idxOf stk p1
      -- Build the stack for p2 (which can see x, u, v)
      let xIdx = Map.lookup x idxOf
          uIdx = Map.lookup u idxOf
          vIdx = Map.lookup v idxOf
          newStk = foldl' (\s mi -> maybe s (:s) mi) stk [xIdx, uIdx, vIdx]
      walkForParams idxOf newStk p2
    
    -- Variable references
    PVar v _ _ -> case Map.lookup v idxOf of
        Just i -> modify (updateAt i (\paramInfo -> paramInfo{pDeps = Set.toAscList
                                                    (Set.fromList (pDeps paramInfo) `Set.union` Set.fromList stk)}))
        _      -> pure ()
    
    -- Recursive cases
    AppP p1 p2 _       -> walkForParams idxOf stk p1 >> walkForParams idxOf stk p2
    TyApp p ty _       -> walkForParams idxOf stk p >> walkForParams idxOf stk ty
    ConvProof t1 p t2 _ -> do
      walkForParams @Term idxOf stk t1
      walkForParams idxOf stk p
      walkForParams @Term idxOf stk t2
    ConvIntro p _      -> walkForParams idxOf stk p
    ConvElim p _       -> walkForParams idxOf stk p
    Iota t1 t2 _ -> do
      walkForParams @Term idxOf stk t1
      walkForParams @Term idxOf stk t2
    Pair p1 p2 _       -> walkForParams idxOf stk p1 >> walkForParams idxOf stk p2
    PMacro _ as _      -> mapM_ (walkForParams idxOf stk) as
    
    -- Non-recursive cases
    PTheoremApp _ _ _  -> pure ()

instance ParamInferAst MacroArg where
  getVarKind = \case
    MTerm _ -> TermK
    MRel _ -> RelK
    MProof _ -> ProofK
  
  walkForParams idxOf stk = \case
    MTerm t -> walkForParams idxOf stk t
    MRel r -> walkForParams idxOf stk r
    MProof p -> walkForParams idxOf stk p

-- | MacroAst instance for MacroArg
instance MacroAst MacroArg where
  shiftN amount = \case
    MTerm t -> MTerm (shiftN amount t)
    MRel r -> MRel (shiftN amount r) 
    MProof p -> MProof (shiftN amount p)
  
  varNameOf = \case
    MTerm t -> varNameOf t
    MRel r -> varNameOf r
    MProof p -> varNameOf p
  
  mapBinders rename = \case
    MTerm t -> MTerm (mapBinders rename t)
    MRel r -> MRel (mapBinders rename r)
    MProof p -> MProof (mapBinders rename p)
  
  toArg = id  -- MacroArg is already the target type
  
  fromArg = Just  -- Any MacroArg can be converted to MacroArg

--------------------------------------------------------------------------------
-- | Generic helper functions
--------------------------------------------------------------------------------

-- | Count how many parameter binders occur to the left of index j
binderPrefixCount :: [ParamInfo] -> Int -> Int
binderPrefixCount sig j =
  length [ () | (k,ParamInfo{pBinds=True}) <- zip [0..] sig, k < j ]

-- | α-rename each binder parameter to the printed name of its actual argument
renameBinderVarsG :: MacroAst a => [ParamInfo] -> [a] -> a -> a
renameBinderVarsG sig actuals =
  let renameOne acc (j,ParamInfo{pBinds=True}) =
        case varNameOf (actuals !! j) of
          Just new -> mapBinders (\n -> if n == pName (sig!!j) then new else n) acc
          Nothing  -> error "binder argument must be a variable"
      renameOne acc _ = acc
  in  \body -> foldl renameOne body (zip [0..] sig)

-- | Positional substitution for value parameters (capture-avoiding, index-based)
substituteArgsG :: MacroAst a => [ParamInfo] -> [a] -> a -> a
substituteArgsG sig actuals =
  let doOne acc (j,paramInfo,arg)
        | pBinds paramInfo = acc
        | otherwise =
            let k     = binderPrefixCount sig j
                arg'  = shiftN k arg
                idx   = length sig - 1 - j
            in  substIndex idx arg' acc
  in  \body -> foldl doOne body (zip3 [0..] sig actuals)

--------------------------------------------------------------------------------
-- | Top-level macro elaborator (used by Elaborate.hs)
--------------------------------------------------------------------------------

elabMacroAppG
  :: (MacroAst a, ResolveAst a)
  => MacroEnvironment
  -> ResolveEnv          -- ^ resolve environment for free variables
  -> String              -- ^ macro name
  -> [ParamInfo]         -- ^ signature from environment
  -> a                   -- ^ stored macro body
  -> [a]                 -- ^ elaborated actual arguments
  -> Either RelTTError a
elabMacroAppG macroEnv resolveEnv name sig body actuals
  | length sig /= length actuals =
      Left $ MacroArityMismatch name (length sig) (length actuals)
             (ErrorContext (initialPos "<elab>") "macro application")
  | otherwise =
      let body1 = renameBinderVarsG sig actuals body
          body2 = substituteArgsG   sig actuals body1
          body3 = Operations.Resolve.resolveWithEnv resolveEnv body2
      in  Right body3