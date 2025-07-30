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
import           Core.Context (buildDependentContexts)
import           Operations.Generic.Shift (ShiftAst(..), shift, shiftAbove)
import           Operations.Generic.Substitution (SubstInto(..), AstCore(..))
import           Operations.Resolve (ResolveAst(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Control.Monad.State.Strict
import           Data.List (foldl')
import           Core.Utils (updateAt)

--------------------------------------------------------------------------------
-- | Minimal operations that any AST category must provide for macro processing
--------------------------------------------------------------------------------

class (ShiftAst a, SubstInto a a, AstCore a) => MacroAst a where
  -- | Convert to a MacroArg for heterogeneous collections
  toArg       :: a -> MacroArg
  -- | Try to extract from a MacroArg (fails if wrong constructor)
  fromArg     :: MacroArg -> Maybe a
  -- | Extract variable name from simple variable references (for bound parameters)
  extractBoundVarName :: a -> Maybe String
  -- | Rename bound variable names in AST (for bound parameter substitution)
  renameBoundVar :: String -> String -> a -> a

--------------------------------------------------------------------------------
-- | Term instance
--------------------------------------------------------------------------------

instance MacroAst Term where
  toArg = MTerm
  fromArg (MTerm t) = Just t
  fromArg _ = Nothing
  
  extractBoundVarName (Var name _ _) = Just name
  extractBoundVarName (FVar name _) = Just name
  extractBoundVarName _ = Nothing
  
  renameBoundVar oldName newName = go
    where
      go (Var name idx pos) = Var name idx pos
      go (FVar name pos) = FVar name pos
      go (Lam name body pos) 
        | name == oldName = Lam newName (go body) pos
        | otherwise = Lam name (go body) pos
      go (App t1 t2 pos) = App (go t1) (go t2) pos
      go (TMacro name args pos) = TMacro name args pos

--------------------------------------------------------------------------------
-- | Relational type instance  
--------------------------------------------------------------------------------

instance MacroAst RType where
  toArg = MRel
  fromArg (MRel r) = Just r
  fromArg _ = Nothing
  
  extractBoundVarName (RVar name _ _) = Just name
  extractBoundVarName (FRVar name _) = Just name
  extractBoundVarName _ = Nothing
  
  renameBoundVar oldName newName = go
    where
      go (RVar name idx pos) = RVar name idx pos
      go (FRVar name pos) = FRVar name pos
      go (RMacro name args pos) = RMacro name args pos
      go (Arr r1 r2 pos) = Arr (go r1) (go r2) pos
      go (All name body pos)
        | name == oldName = All newName (go body) pos
        | otherwise = All name (go body) pos
      go (Conv r pos) = Conv (go r) pos
      go (Comp r1 r2 pos) = Comp (go r1) (go r2) pos
      go (Prom t pos) = Prom t pos

--------------------------------------------------------------------------------
-- | Proof instance
--------------------------------------------------------------------------------

instance MacroAst Proof where
  toArg = MProof
  fromArg (MProof p) = Just p
  fromArg _ = Nothing
  
  extractBoundVarName (PVar name _ _) = Just name
  extractBoundVarName (FPVar name _) = Just name
  extractBoundVarName _ = Nothing
  
  renameBoundVar oldName newName = go
    where
      go (PVar name idx pos) = PVar name idx pos
      go (FPVar name pos) = FPVar name pos
      go (PTheoremApp name args pos) = PTheoremApp name args pos
      go (LamP name rtype body pos)
        | name == oldName = LamP newName rtype (go body) pos
        | otherwise = LamP name rtype (go body) pos
      go (AppP p1 p2 pos) = AppP (go p1) (go p2) pos
      go (TyApp proof rtype pos) = TyApp (go proof) rtype pos
      go (TyLam name body pos)
        | name == oldName = TyLam newName (go body) pos
        | otherwise = TyLam name (go body) pos
      go (ConvProof t1 proof t2 pos) = ConvProof t1 (go proof) t2 pos
      go (ConvIntro proof pos) = ConvIntro (go proof) pos
      go (ConvElim proof pos) = ConvElim (go proof) pos
      go (Iota t1 t2 pos) = Iota t1 t2 pos
      go (RhoElim name t1 t2 p1 p2 pos)
        | name == oldName = RhoElim newName t1 t2 (go p1) (go p2) pos
        | otherwise = RhoElim name t1 t2 (go p1) (go p2) pos
      go (Pi p1 n1 n2 n3 p2 pos)
        | n1 == oldName = Pi (go p1) newName n2 n3 (go p2) pos
        | n2 == oldName = Pi (go p1) n1 newName n3 (go p2) pos
        | n3 == oldName = Pi (go p1) n1 n2 newName (go p2) pos
        | otherwise = Pi (go p1) n1 n2 n3 (go p2) pos
      go (Pair p1 p2 pos) = Pair (go p1) (go p2) pos
      go (PMacro name args pos) = PMacro name args pos

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
    FVar _ _ -> pure ()                  -- Free variables don't affect parameters
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
    FRVar _ _ -> pure ()                 -- Free relation variables don't affect parameters
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
    FPVar _ _ -> pure ()                 -- Free proof variables don't affect parameters
    
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
  toArg = id  -- MacroArg is already the target type
  fromArg = Just  -- Any MacroArg can be converted to MacroArg
  
  extractBoundVarName (MTerm t) = extractBoundVarName t
  extractBoundVarName (MRel r) = extractBoundVarName r
  extractBoundVarName (MProof p) = extractBoundVarName p
  
  renameBoundVar oldName newName (MTerm t) = MTerm (renameBoundVar oldName newName t)
  renameBoundVar oldName newName (MRel r) = MRel (renameBoundVar oldName newName r)
  renameBoundVar oldName newName (MProof p) = MProof (renameBoundVar oldName newName p)

--------------------------------------------------------------------------------
-- | Generic helper functions
--------------------------------------------------------------------------------

-- | Count how many parameter binders occur to the left of index j
binderPrefixCount :: [ParamInfo] -> Int -> Int
binderPrefixCount sig j =
  length [ () | (k,ParamInfo{pBinds=True}) <- zip [0..] sig, k < j ]


-- | Free variable substitution for macro parameters
substituteArgsG :: MacroAst a => [ParamInfo] -> [a] -> a -> a
substituteArgsG sig actuals body = 
  foldl doSubst body (zip sig actuals)
  where
    doSubst acc (paramInfo, arg)
      | pBinds paramInfo = 
          case extractBoundVarName arg of
            Just newName -> renameBoundVar (pName paramInfo) newName acc
            Nothing -> acc  -- malformed bound parameter, skip
      | otherwise = substFreeVar (pName paramInfo) arg acc

--------------------------------------------------------------------------------
-- | Top-level macro elaborator (used by Elaborate.hs)
--------------------------------------------------------------------------------

elabMacroAppG
  :: (MacroAst a, ResolveAst a)
  => Context             -- ^ unified context
  -> String              -- ^ macro name
  -> [ParamInfo]         -- ^ signature from environment
  -> a                   -- ^ stored macro body
  -> [a]                 -- ^ elaborated actual arguments
  -> Either RelTTError a
elabMacroAppG ctx name sig body actuals
  | length sig /= length actuals =
      Left $ MacroArityMismatch name (length sig) (length actuals)
             (ErrorContext (initialPos "<elab>") "macro application")
  | otherwise = do
      let body2 = substituteArgsG   sig actuals body
          -- Convert arguments to MacroArgs for context extension
          macroArgs = map toArg actuals
          -- Build dependency-aware contexts
          (_, finalCtx) = buildDependentContexts sig macroArgs ctx
      Operations.Resolve.resolveWithContext finalCtx body2