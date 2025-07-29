{-# LANGUAGE LambdaCase #-}

-- | Generic resolution of free variables to de Bruijn indices
-- This module provides a generic resolution system that converts free variables
-- in macro bodies to proper de Bruijn indices based on the binder context.

module Operations.Resolve
  ( ResolveAst(..)
  , resolve
  ) where

import qualified Data.Map as Map
import Core.Syntax

-- | Type for tracking binder depth and variable mappings
type ResolveContext = Map.Map String Int  -- variable name -> index (relative to binder)

-- | Context for tracking all three kinds of binders
data ResolveEnv = ResolveEnv
  { termDepth :: Int
  , relDepth :: Int
  , proofDepth :: Int
  , termCtx :: ResolveContext
  , relCtx :: ResolveContext
  , proofCtx :: ResolveContext
  }

-- | Empty resolve environment
emptyResolveEnv :: ResolveEnv
emptyResolveEnv = ResolveEnv 0 0 0 Map.empty Map.empty Map.empty

-- | Generic typeclass for resolving free variables to de Bruijn indices
class ResolveAst a where
  -- | Resolve free variables in the AST using the current environment
  resolveWithEnv :: ResolveEnv -> a -> a

-- | Main entry point: resolve all free variables in an AST
resolve :: ResolveAst a => a -> a
resolve = resolveWithEnv emptyResolveEnv

--------------------------------------------------------------------------------
-- | Instance for Term
--------------------------------------------------------------------------------

instance ResolveAst Term where
  resolveWithEnv env = \case
    Var n i p   -> Var n i p                      -- Already resolved
    FVar n p    -> case Map.lookup n (termCtx env) of  -- Free variable to resolve
      Just k  -> Var n (termDepth env - 1 - k) p
      Nothing -> error ("unbound term variable \"" ++ n ++ "\" after macro resolution")
    Lam n b p   -> 
      let env' = env { termDepth = termDepth env + 1
                     , termCtx = Map.insert n (termDepth env) (termCtx env) }
      in Lam n (resolveWithEnv env' b) p
    App f x p   -> App (resolveWithEnv env f) (resolveWithEnv env x) p
    TMacro n as p -> TMacro n (map (resolveWithEnv env) as) p

--------------------------------------------------------------------------------
-- | Instance for RType
--------------------------------------------------------------------------------

instance ResolveAst RType where
  resolveWithEnv env = \case
    RVar n i p   -> RVar n i p                     -- Already resolved
    FRVar n p    -> case Map.lookup n (relCtx env) of   -- Free relational variable to resolve
      Just k  -> RVar n (relDepth env - 1 - k) p
      Nothing -> error ("unbound relational variable \"" ++ n ++ "\"")
    RMacro n as p -> RMacro n (map (resolveWithEnv env) as) p
    Arr a b p    -> Arr (resolveWithEnv env a) (resolveWithEnv env b) p
    All n r p    -> 
      let env' = env { relDepth = relDepth env + 1
                     , relCtx = Map.insert n (relDepth env) (relCtx env) }
      in All n (resolveWithEnv env' r) p
    Conv r p     -> Conv (resolveWithEnv env r) p
    Comp a b p   -> Comp (resolveWithEnv env a) (resolveWithEnv env b) p
    Prom t p     -> Prom (resolve t) p             -- Terms use their own resolution

--------------------------------------------------------------------------------
-- | Instance for Proof
--------------------------------------------------------------------------------

instance ResolveAst Proof where
  resolveWithEnv env = \case
    PVar n i p -> PVar n i p                      -- Already resolved
    FPVar n p  -> case Map.lookup n (proofCtx env) of   -- Free proof variable to resolve
      Just k  -> PVar n (proofDepth env - 1 - k) p
      Nothing -> error ("unbound proof variable \"" ++ n ++ "\"")
    PTheoremApp n args p -> PTheoremApp n (map resolveArg args) p
      where
        resolveArg = \case
          TermArg t  -> TermArg (resolve t)
          RelArg rt  -> RelArg (resolve rt)
          ProofArg pr -> ProofArg (resolveWithEnv env pr)
    LamP n rt pr p ->
      let env' = env { proofDepth = proofDepth env + 1
                     , proofCtx = Map.insert n (proofDepth env) (proofCtx env) }
      in LamP n (resolveWithEnv env rt) (resolveWithEnv env' pr) p
    AppP p1 p2 p   -> AppP (resolveWithEnv env p1) (resolveWithEnv env p2) p
    TyApp pr rt p  -> TyApp (resolveWithEnv env pr) (resolveWithEnv env rt) p
    TyLam n pr p   -> 
      let env' = env { relDepth = relDepth env + 1
                     , relCtx = Map.insert n (relDepth env) (relCtx env) }
      in TyLam n (resolveWithEnv env' pr) p
    ConvProof t1 pr t2 p -> ConvProof (resolve t1) (resolveWithEnv env pr) (resolve t2) p
    ConvIntro pr p -> ConvIntro (resolveWithEnv env pr) p
    ConvElim pr p  -> ConvElim (resolveWithEnv env pr) p
    Iota t1 t2 p   -> Iota (resolve t1) (resolve t2) p
    RhoElim n t1 t2 p1 p2 p ->
      let env' = env { termDepth = termDepth env + 1
                     , termCtx = Map.insert n (termDepth env) (termCtx env)
                     , proofCtx = Map.insert n (termDepth env) (proofCtx env) }
      in RhoElim n (resolve t1) (resolve t2)
           (resolveWithEnv env p1)
           (resolveWithEnv env' p2) p
    Pair p1 p2 p   -> Pair (resolveWithEnv env p1) (resolveWithEnv env p2) p
    Pi p1 x u v p2 p ->
      let env' = env { proofDepth = proofDepth env + 2
                     , termCtx = Map.insert x (termDepth env) (termCtx env)
                     , proofCtx = Map.insert u (proofDepth env) 
                                    (Map.insert v (proofDepth env + 1) (proofCtx env)) }
      in Pi (resolveWithEnv env p1) x u v
            (resolveWithEnv env' p2) p
    PMacro n as p  -> PMacro n (map (resolveWithEnv env) as) p