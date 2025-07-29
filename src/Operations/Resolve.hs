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
import Core.Context
import Core.Raw (dummyPos)

-- | Generic typeclass for resolving free variables to de Bruijn indices
class ResolveAst a where
  -- | Resolve free variables in the AST using the current context
  resolveWithContext :: Context -> a -> a

-- | Main entry point: resolve all free variables in an AST
resolve :: ResolveAst a => a -> a
resolve = resolveWithContext emptyContext

--------------------------------------------------------------------------------
-- | Instance for Term
--------------------------------------------------------------------------------

instance ResolveAst Term where
  resolveWithContext ctx = \case
    Var n i p   -> Var n i p                      -- Already resolved
    FVar n p    -> case Map.lookup n (termBindings ctx) of  -- Free variable to resolve
      Just (i, _)  -> Var n i p
      Nothing -> error ("unbound term variable \"" ++ n ++ "\" after macro resolution")
    Lam n b p   -> 
      let ctx' = bindTermVar n ctx
      in Lam n (resolveWithContext ctx' b) p
    App f x p   -> App (resolveWithContext ctx f) (resolveWithContext ctx x) p
    TMacro n as p -> TMacro n (map (resolveWithContext ctx) as) p

--------------------------------------------------------------------------------
-- | Instance for RType
--------------------------------------------------------------------------------

instance ResolveAst RType where
  resolveWithContext ctx = \case
    RVar n i p   -> RVar n i p                     -- Already resolved
    FRVar n p    -> case Map.lookup n (relBindings ctx) of   -- Free relational variable to resolve
      Just i  -> RVar n i p
      Nothing -> error ("unbound relational variable \"" ++ n ++ "\"")
    RMacro n as p -> RMacro n (map (resolveWithContext ctx) as) p
    Arr a b p    -> Arr (resolveWithContext ctx a) (resolveWithContext ctx b) p
    All n r p    -> 
      let ctx' = bindRelVar n ctx
      in All n (resolveWithContext ctx' r) p
    Conv r p     -> Conv (resolveWithContext ctx r) p
    Comp a b p   -> Comp (resolveWithContext ctx a) (resolveWithContext ctx b) p
    Prom t p     -> Prom (resolve t) p             -- Terms use their own resolution

--------------------------------------------------------------------------------
-- | Instance for Proof
--------------------------------------------------------------------------------

instance ResolveAst Proof where
  resolveWithContext ctx = \case
    PVar n i p -> PVar n i p                      -- Already resolved
    FPVar n p  -> case Map.lookup n (proofBindings ctx) of   -- Free proof variable to resolve
      Just (i, _, _)  -> PVar n i p
      Nothing -> error ("unbound proof variable \"" ++ n ++ "\"")
    PTheoremApp n args p -> PTheoremApp n (map resolveArg args) p
      where
        resolveArg = \case
          TermArg t  -> TermArg (resolve t)
          RelArg rt  -> RelArg (resolve rt)
          ProofArg pr -> ProofArg (resolveWithContext ctx pr)
    LamP n rt pr p ->
      let dummyJudgment = RelJudgment (Var "dummy" 0 (dummyPos)) (RVar "dummy" 0 (dummyPos)) (Var "dummy" 0 (dummyPos))
          ctx' = bindProofVar n dummyJudgment ctx
      in LamP n (resolveWithContext ctx rt) (resolveWithContext ctx' pr) p
    AppP p1 p2 p   -> AppP (resolveWithContext ctx p1) (resolveWithContext ctx p2) p
    TyApp pr rt p  -> TyApp (resolveWithContext ctx pr) (resolveWithContext ctx rt) p
    TyLam n pr p   -> 
      let ctx' = bindRelVar n ctx
      in TyLam n (resolveWithContext ctx' pr) p
    ConvProof t1 pr t2 p -> ConvProof (resolve t1) (resolveWithContext ctx pr) (resolve t2) p
    ConvIntro pr p -> ConvIntro (resolveWithContext ctx pr) p
    ConvElim pr p  -> ConvElim (resolveWithContext ctx pr) p
    Iota t1 t2 p   -> Iota (resolve t1) (resolve t2) p
    RhoElim n t1 t2 p1 p2 p ->
      let dummyJudgment = RelJudgment (Var "dummy" 0 (dummyPos)) (RVar "dummy" 0 (dummyPos)) (Var "dummy" 0 (dummyPos))
          ctx' = bindTermVar n (bindProofVar n dummyJudgment ctx)
      in RhoElim n (resolve t1) (resolve t2)
           (resolveWithContext ctx p1)
           (resolveWithContext ctx' p2) p
    Pair p1 p2 p   -> Pair (resolveWithContext ctx p1) (resolveWithContext ctx p2) p
    Pi p1 x u v p2 p ->
      let dummyJudgment = RelJudgment (Var "dummy" 0 (dummyPos)) (RVar "dummy" 0 (dummyPos)) (Var "dummy" 0 (dummyPos))
          ctx' = bindTermVar x (bindProofVar u dummyJudgment (bindProofVar v dummyJudgment ctx))
      in Pi (resolveWithContext ctx p1) x u v
            (resolveWithContext ctx' p2) p
    PMacro n as p  -> PMacro n (map (resolveWithContext ctx) as) p

-- | MacroArg resolution instance
instance ResolveAst MacroArg where
  resolveWithContext ctx = \case
    MTerm t -> MTerm (resolveWithContext ctx t)
    MRel r -> MRel (resolveWithContext ctx r)
    MProof p -> MProof (resolveWithContext ctx p)