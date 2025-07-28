{-# LANGUAGE DefaultSignatures #-}

-- | Generic shifting infrastructure for de Bruijn indices.
-- This module provides a unified interface for shifting operations
-- across all AST types (Term, RType, Proof).

module Operations.Generic.Shift
  ( -- * Typeclass
    ShiftAst(..)
    -- * Generic operations
  , shift
  , shiftWithBoundsCheck
    -- * Specialized operations
  , shiftTermsInRType
  , shiftTermsInRTypeAbove  
  , shiftTermsInRTypeWithBoundsCheck
  , shiftTermsInRTypeAboveWithBoundsCheck
    -- * Proof-specific shifting utilities
  , shiftTermExcept
  , shiftRTypeExcept  
  , shiftFreeRelVars
  ) where

import Core.Syntax (Term(..), RType(..), Proof(..), TheoremArg(..))
import qualified Data.Set as Set

--------------------------------------------------------------------------------
-- | Core typeclass for shifting de Bruijn indices
--------------------------------------------------------------------------------

class ShiftAst a where
  -- | Shift de Bruijn indices above a cutoff by a given amount
  shiftAbove :: Int -> Int -> a -> a
  
  -- | Shift with bounds checking - returns Nothing if any index would go negative
  shiftAboveWithBoundsCheck :: Int -> Int -> a -> Maybe a
  
  -- Default implementation - must be overridden for meaningful bounds checking
  default shiftAboveWithBoundsCheck :: Int -> Int -> a -> Maybe a
  shiftAboveWithBoundsCheck cutoff shiftAmount x = Just (shiftAbove cutoff shiftAmount x)

--------------------------------------------------------------------------------
-- | Derived operations
--------------------------------------------------------------------------------

-- | Shift all free variables by a given amount (cutoff = 0)
shift :: ShiftAst a => Int -> a -> a
shift = shiftAbove 0

-- | Shift with bounds checking (cutoff = 0)
shiftWithBoundsCheck :: ShiftAst a => Int -> a -> Maybe a
shiftWithBoundsCheck = shiftAboveWithBoundsCheck 0

--------------------------------------------------------------------------------
-- | Instance for Term
--------------------------------------------------------------------------------

instance ShiftAst Term where
  shiftAbove cutoff shiftAmount term = case term of
    Var name i pos
      | i >= cutoff -> Var name (i + shiftAmount) pos
      | otherwise -> term
    Lam name body pos -> 
      Lam name (shiftAbove (cutoff + 1) shiftAmount body) pos
    App t1 t2 pos -> 
      App (shiftAbove cutoff shiftAmount t1) (shiftAbove cutoff shiftAmount t2) pos
    TMacro name args pos -> 
      TMacro name (map (shiftAbove cutoff shiftAmount) args) pos
  
  shiftAboveWithBoundsCheck cutoff shiftAmount term = case term of
    Var name i pos ->
      if i >= cutoff
        then let newIdx = i + shiftAmount
             in if newIdx < 0 then Nothing else Just (Var name newIdx pos)
        else Just term
    Lam name body pos -> do
      shiftedBody <- shiftAboveWithBoundsCheck (cutoff + 1) shiftAmount body
      return $ Lam name shiftedBody pos
    App t1 t2 pos -> do
      shiftedT1 <- shiftAboveWithBoundsCheck cutoff shiftAmount t1
      shiftedT2 <- shiftAboveWithBoundsCheck cutoff shiftAmount t2
      return $ App shiftedT1 shiftedT2 pos
    TMacro name args pos -> do
      shiftedArgs <- mapM (shiftAboveWithBoundsCheck cutoff shiftAmount) args
      return $ TMacro name shiftedArgs pos

--------------------------------------------------------------------------------
-- | Instance for RType
--------------------------------------------------------------------------------

instance ShiftAst RType where
  -- For RType, we have two kinds of shifting:
  -- 1. Shifting term variables (in Prom)
  -- 2. Shifting relation variables
  -- This instance does relation variable shifting
  shiftAbove cutoff shiftAmount ty = case ty of
    RVar name i pos
      | i >= cutoff -> RVar name (i + shiftAmount) pos
      | otherwise -> ty
    RMacro name args pos -> 
      RMacro name (map (shiftAbove cutoff shiftAmount) args) pos
    Arr r1 r2 pos -> 
      Arr (shiftAbove cutoff shiftAmount r1) (shiftAbove cutoff shiftAmount r2) pos
    All name r pos -> 
      All name (shiftAbove (cutoff + 1) shiftAmount r) pos
    Conv r pos -> 
      Conv (shiftAbove cutoff shiftAmount r) pos
    Comp r1 r2 pos -> 
      Comp (shiftAbove cutoff shiftAmount r1) (shiftAbove cutoff shiftAmount r2) pos
    Prom term pos -> 
      -- Promoted terms are not affected by relation shifting
      Prom term pos

--------------------------------------------------------------------------------
-- | Instance for Proof  
--------------------------------------------------------------------------------

instance ShiftAst Proof where
  shiftAbove cutoff shiftAmount proof = case proof of
    PVar name i pos
      | i >= cutoff -> PVar name (i + shiftAmount) pos
      | otherwise -> proof
    LamP name ty body pos ->
      LamP name ty (shiftAbove (cutoff + 1) shiftAmount body) pos
    AppP p1 p2 pos ->
      AppP (shiftAbove cutoff shiftAmount p1) (shiftAbove cutoff shiftAmount p2) pos
    TyLam name body pos ->
      TyLam name (shiftAbove cutoff shiftAmount body) pos
    TyApp p ty pos ->
      TyApp (shiftAbove cutoff shiftAmount p) ty pos
    ConvProof t1 p t2 pos ->
      ConvProof t1 (shiftAbove cutoff shiftAmount p) t2 pos
    RhoElim x t1 t2 p1 p2 pos ->
      RhoElim x t1 t2 (shiftAbove cutoff shiftAmount p1) (shiftAbove cutoff shiftAmount p2) pos
    Iota t1 t2 pos ->
      Iota t1 t2 pos
    ConvIntro p pos ->
      ConvIntro (shiftAbove cutoff shiftAmount p) pos
    ConvElim p pos ->
      ConvElim (shiftAbove cutoff shiftAmount p) pos
    Pair p1 p2 pos ->
      Pair (shiftAbove cutoff shiftAmount p1) (shiftAbove cutoff shiftAmount p2) pos
    Pi p x y z q pos ->
      -- Pi introduces three new bindings
      Pi (shiftAbove cutoff shiftAmount p) x y z (shiftAbove (cutoff + 3) shiftAmount q) pos
    PTheoremApp name args pos ->
      PTheoremApp name (map (shiftTheoremArg cutoff shiftAmount) args) pos
    PMacro name args pos ->
      PMacro name (map (shiftAbove cutoff shiftAmount) args) pos
    where
      shiftTheoremArg c s arg = case arg of
        TermArg t -> TermArg t  -- Terms in theorem args unaffected by proof shifting
        RelArg r -> RelArg r    -- Relations in theorem args unaffected by proof shifting
        ProofArg p -> ProofArg (shiftAbove c s p)

--------------------------------------------------------------------------------
-- | Specialized shifting operations for mixed contexts
--------------------------------------------------------------------------------

-- | Shift term variables in an RType (for handling promoted terms)
shiftTermsInRType :: Int -> RType -> RType
shiftTermsInRType shiftAmount = shiftTermsInRTypeAbove 0 shiftAmount

shiftTermsInRTypeAbove :: Int -> Int -> RType -> RType
shiftTermsInRTypeAbove cutoff shiftAmount ty = case ty of
  RVar name idx pos -> RVar name idx pos  -- Relation variables unaffected
  RMacro name args pos -> RMacro name (map (shiftTermsInRTypeAbove cutoff shiftAmount) args) pos
  Arr r1 r2 pos -> Arr (shiftTermsInRTypeAbove cutoff shiftAmount r1) (shiftTermsInRTypeAbove cutoff shiftAmount r2) pos
  All name r pos -> All name (shiftTermsInRTypeAbove cutoff shiftAmount r) pos
  Conv r pos -> Conv (shiftTermsInRTypeAbove cutoff shiftAmount r) pos
  Comp r1 r2 pos -> Comp (shiftTermsInRTypeAbove cutoff shiftAmount r1) (shiftTermsInRTypeAbove cutoff shiftAmount r2) pos
  Prom term pos -> Prom (shiftAbove cutoff shiftAmount term) pos

-- | Shift term variables in RType with bounds checking
shiftTermsInRTypeWithBoundsCheck :: Int -> RType -> Maybe RType
shiftTermsInRTypeWithBoundsCheck shiftAmount = shiftTermsInRTypeAboveWithBoundsCheck 0 shiftAmount

shiftTermsInRTypeAboveWithBoundsCheck :: Int -> Int -> RType -> Maybe RType
shiftTermsInRTypeAboveWithBoundsCheck cutoff shiftAmount ty = case ty of
  RVar name idx pos -> Just $ RVar name idx pos
  RMacro name args pos -> do
    shiftedArgs <- mapM (shiftTermsInRTypeAboveWithBoundsCheck cutoff shiftAmount) args
    return $ RMacro name shiftedArgs pos
  Arr r1 r2 pos -> do
    shiftedR1 <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shiftAmount r1
    shiftedR2 <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shiftAmount r2
    return $ Arr shiftedR1 shiftedR2 pos
  All name r pos -> do
    shiftedR <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shiftAmount r
    return $ All name shiftedR pos
  Conv r pos -> do
    shiftedR <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shiftAmount r
    return $ Conv shiftedR pos
  Comp r1 r2 pos -> do
    shiftedR1 <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shiftAmount r1
    shiftedR2 <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shiftAmount r2
    return $ Comp shiftedR1 shiftedR2 pos
  Prom term pos -> do
    shiftedTerm <- shiftAboveWithBoundsCheck cutoff shiftAmount term
    return $ Prom shiftedTerm pos

--------------------------------------------------------------------------------
-- | Proof-specific shifting utilities (moved from ProofChecker.hs)
--------------------------------------------------------------------------------

-- | shiftTermExcept 𝑃 d t
--   Shift indices by d exactly as 'shiftTerm' does, **except** for variables
--   whose printed name is in the protected set 𝑃.  Those are left unchanged.
shiftTermExcept :: Set.Set String -> Int -> Term -> Term
shiftTermExcept prot d = go 0
  where
    go cut tm = case tm of
      Var v k p
        | Set.member v prot -> Var v k p
        | k >= cut -> Var v (k + d) p
        | otherwise -> tm
      Lam v b p -> Lam v (go (cut + 1) b) p
      App f a p -> App (go cut f) (go cut a) p
      TMacro n as p -> TMacro n (map (go cut) as) p

-- | The same idea for relational types (terms appear under 'Prom').
shiftRTypeExcept :: Set.Set String -> Int -> RType -> RType
shiftRTypeExcept prot d = go
  where
    go rt = case rt of
      Arr a b p -> Arr (go a) (go b) p
      All n b p -> All n (go b) p
      Conv r p -> Conv (go r) p
      Comp a b p -> Comp (go a) (go b) p
      Prom t p -> Prom (shiftTermExcept prot d t) p
      RMacro n as p -> RMacro n (map go as) p
      other -> other

-- | shiftFreeRelVars x d τ bumps indices ≥0 by d, but
-- leaves occurrences of the bound variable x at index 0 unchanged.
shiftFreeRelVars :: String -> Int -> RType -> RType
shiftFreeRelVars x d = go 0
  where
    go lvl ty = case ty of
      RVar y k p
        | k == lvl && y == x -> ty -- bound occurrence
        | k >= lvl -> RVar y (k + d) p -- free variable
        | otherwise -> ty
      All y b p -> All y (go (lvl + 1) b) p
      Arr a b p -> Arr (go lvl a) (go lvl b) p
      Comp a b p -> Comp (go lvl a) (go lvl b) p
      Conv r p -> Conv (go lvl r) p
      RMacro n as p -> RMacro n (map (go lvl) as) p
      Prom t p -> Prom t p