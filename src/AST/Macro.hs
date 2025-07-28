{-# LANGUAGE LambdaCase #-}

-- | Macro parameter inference and analysis
-- This module handles the complex analysis of macro parameters to determine
-- binder relationships and dependencies for proper macro application.
module AST.Macro
  ( inferParamInfosTerm
  , inferParamInfosRel
  , inferParamInfosProof
  ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State.Strict
import Data.List (foldl')
import Lib
import Utils (updateAt)

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