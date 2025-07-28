{-# LANGUAGE LambdaCase #-}
module Lib.FreeVars (freeVarsInTerm, freeVarsInRType, freeVarsInProof) where

import qualified Data.Map  as M
import qualified Data.Set  as S
import           Lib
import           Data.Maybe (fromMaybe)

------------------------------------------------------------------------
-- Term‑level free variables (binder‑aware)
------------------------------------------------------------------------

freeVarsInTerm :: MacroEnvironment -> Term -> S.Set String
freeVarsInTerm env = go
  where
    go = \case
      Var x _ _          -> S.singleton x
      Lam x b _          -> S.delete x (go b)
      App f a _          -> go f `S.union` go a

      -- binder‑aware macro case ---------------------------------------
      TMacro n args _ ->
        case M.lookup n (macroDefinitions env) of
          Nothing -> S.unions (map go args)   -- should not happen, be conservative
          Just (sig, _) ->
            let binders :: M.Map Int String   -- param‑index ↦ binder name
                binders =
                  M.fromList
                    [ (i, v)
                    | (i,ParamInfo{pBinds=True}, Var v _ _) <- zip3 [0..] sig args ]

                fvArg i pi arg
                  | pBinds pi = S.empty
                  | otherwise =
                      let allowed = S.fromList
                                      [ b | j <- pDeps pi
                                          , Just b <- [M.lookup j binders] ]
                       in S.difference (go arg) allowed
            in S.unions [ fvArg i pi a | (i,pi,a) <- zip3 [0..] sig args ]

------------------------------------------------------------------------
-- Rel‑type free variables (binder‑aware)
------------------------------------------------------------------------

freeVarsInRType :: MacroEnvironment -> RType -> S.Set String
freeVarsInRType env = go
  where
    go = \case
      RVar x _ _         -> S.singleton x
      Arr a b _          -> go a `S.union` go b
      All x t _          -> S.delete x (go t)
      Comp a b _         -> go a `S.union` go b
      Conv r _           -> go r
      Prom t _           -> freeVarsInTerm env t

      -- binder‑aware macro case ---------------------------------------
      RMacro n args _ ->
        case M.lookup n (macroDefinitions env) of
          Nothing -> S.unions (map go args)
          Just (sig, _) ->
            let binders :: M.Map Int String
                binders =
                  M.fromList
                    [ (i, v)
                    | (i,ParamInfo{pBinds=True}, RVar v _ _) <- zip3 [0..] sig args ]

                fvArg i pi arg
                  | pBinds pi = S.empty
                  | otherwise =
                      let allowed = S.fromList
                                      [ b | j <- pDeps pi
                                          , Just b <- [M.lookup j binders] ]
                       in S.difference (go arg) allowed
            in S.unions [ fvArg i pi a | (i,pi,a) <- zip3 [0..] sig args ]

      -- any other node ------------------------------------------------
      _other -> S.empty   -- unreachable but keeps GHC happy

------------------------------------------------------------------------
-- Proof free variables (binder‑aware)
------------------------------------------------------------------------

freeVarsInProof :: MacroEnvironment -> Proof -> S.Set String
freeVarsInProof env = go
  where
    go = \case
      PVar x _ _         -> S.singleton x
      PTheoremApp _ args _ -> S.unions (map goArg args)
      LamP x rt p _     -> S.delete x (freeVarsInRType env rt `S.union` go p)
      AppP p1 p2 _      -> go p1 `S.union` go p2
      TyApp p rt _      -> go p `S.union` freeVarsInRType env rt
      TyLam x p _       -> S.delete x (go p)
      ConvProof t1 p t2 _ -> freeVarsInTerm env t1 `S.union` go p `S.union` freeVarsInTerm env t2
      ConvIntro p _     -> go p
      ConvElim p _      -> go p
      Iota t1 t2 _      -> freeVarsInTerm env t1 `S.union` freeVarsInTerm env t2
      RhoElim x t1 t2 p1 p2 _ -> S.delete x (freeVarsInTerm env t1 `S.union` freeVarsInTerm env t2) `S.union` go p1 `S.union` go p2
      Pi p1 x u v p2 _  -> go p1 `S.union` S.delete x (S.delete u (S.delete v (go p2)))
      Pair p1 p2 _      -> go p1 `S.union` go p2
      
      -- binder‑aware macro case ---------------------------------------
      PMacro n args _ ->
        case M.lookup n (macroDefinitions env) of
          Nothing -> S.unions (map go args)
          Just (sig, _) ->
            let binders :: M.Map Int String
                binders =
                  M.fromList
                    [ (i, v)
                    | (i,ParamInfo{pBinds=True}, PVar v _ _) <- zip3 [0..] sig args ]

                fvArg i pi arg
                  | pBinds pi = S.empty
                  | otherwise =
                      let allowed = S.fromList
                                      [ b | j <- pDeps pi
                                          , Just b <- [M.lookup j binders] ]
                       in S.difference (go arg) allowed
            in S.unions [ fvArg i pi a | (i,pi,a) <- zip3 [0..] sig args ]

    goArg = \case
      TermArg t  -> freeVarsInTerm env t
      RelArg rt  -> freeVarsInRType env rt
      ProofArg p -> go p