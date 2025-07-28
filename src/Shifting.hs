module Shifting
  ( -- Term shifting
    shiftTerm,
    shiftTermAbove,
    shiftTermWithBoundsCheck,
    shiftTermAboveWithBoundsCheck,
    -- Type shifting for terms
    shiftTermsInRType,
    shiftTermsInRTypeAbove,
    shiftTermsInRTypeWithBoundsCheck,
    shiftTermsInRTypeAboveWithBoundsCheck,
    -- Type shifting for relations
    shiftRelsInRType,
    shiftRelsInRTypeAbove,
    -- Proof shifting
    shiftProof,
    shiftProofAbove,
  )
where

import Lib

-- Term Shifting Operations

-- | Shift all free variables in a term by a given amount
shiftTerm :: Int -> Term -> Term
shiftTerm shift = shiftTermAbove 0 shift

-- | Shift de Bruijn indices above a cutoff
shiftTermAbove :: Int -> Int -> Term -> Term
shiftTermAbove cutoff shift term = case term of
  Var name i pos
    | i >= cutoff -> Var name (i + shift) pos
    | otherwise -> term
  Lam name body pos -> Lam name (shiftTermAbove (cutoff + 1) shift body) pos
  App t1 t2 pos -> App (shiftTermAbove cutoff shift t1) (shiftTermAbove cutoff shift t2) pos
  TMacro name args pos -> TMacro name (map (shiftTermAbove cutoff shift) args) pos

-- | Shift term indices with bounds checking - returns Nothing if any index would go negative
shiftTermWithBoundsCheck :: Int -> Term -> Maybe Term
shiftTermWithBoundsCheck shift = shiftTermAboveWithBoundsCheck 0 shift

-- | Shift term indices above cutoff with bounds checking
shiftTermAboveWithBoundsCheck :: Int -> Int -> Term -> Maybe Term
shiftTermAboveWithBoundsCheck cutoff shift term = case term of
  Var name i pos ->
    if i >= cutoff
      then
        let newIdx = i + shift
         in if newIdx < 0 then Nothing else Just (Var name newIdx pos)
      else Just term
  Lam name body pos -> do
    shiftedBody <- shiftTermAboveWithBoundsCheck (cutoff + 1) shift body
    return $ Lam name shiftedBody pos
  App t1 t2 pos -> do
    shiftedT1 <- shiftTermAboveWithBoundsCheck cutoff shift t1
    shiftedT2 <- shiftTermAboveWithBoundsCheck cutoff shift t2
    return $ App shiftedT1 shiftedT2 pos
  TMacro name args pos -> do
    shiftedArgs <- mapM (shiftTermAboveWithBoundsCheck cutoff shift) args
    return $ TMacro name shiftedArgs pos

-- Type Shifting Operations for Terms

-- | Shift term variable indices in relational types
shiftTermsInRType :: Int -> RType -> RType
shiftTermsInRType shift ty = shiftTermsInRTypeAbove 0 shift ty

-- | Shift term indices that are >= cutoff by shift amount
shiftTermsInRTypeAbove :: Int -> Int -> RType -> RType
shiftTermsInRTypeAbove cutoff shift ty = case ty of
  RVar name idx pos -> RVar name idx pos -- Relation variables are NOT shifted
  RMacro name args pos -> RMacro name (map (shiftTermsInRTypeAbove cutoff shift) args) pos
  Arr t1 t2 pos -> Arr (shiftTermsInRTypeAbove cutoff shift t1) (shiftTermsInRTypeAbove cutoff shift t2) pos
  All name body pos -> All name (shiftTermsInRTypeAbove cutoff shift body) pos -- No change to cutoff for relation binders
  Conv t pos -> Conv (shiftTermsInRTypeAbove cutoff shift t) pos
  Comp t1 t2 pos -> Comp (shiftTermsInRTypeAbove cutoff shift t1) (shiftTermsInRTypeAbove cutoff shift t2) pos
  Prom term pos -> Prom (shiftTermAbove cutoff shift term) pos -- Shift the promoted term

-- | Shift term indices in RType with bounds checking
shiftTermsInRTypeWithBoundsCheck :: Int -> RType -> Maybe RType
shiftTermsInRTypeWithBoundsCheck shift = shiftTermsInRTypeAboveWithBoundsCheck 0 shift

-- | Shift term indices above cutoff with bounds checking
shiftTermsInRTypeAboveWithBoundsCheck :: Int -> Int -> RType -> Maybe RType
shiftTermsInRTypeAboveWithBoundsCheck cutoff shift ty = case ty of
  RVar name idx pos -> Just (RVar name idx pos) -- Relation variables are NOT shifted
  RMacro name args pos -> do
    shiftedArgs <- mapM (shiftTermsInRTypeAboveWithBoundsCheck cutoff shift) args
    return $ RMacro name shiftedArgs pos
  Arr t1 t2 pos -> do
    shiftedT1 <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shift t1
    shiftedT2 <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shift t2
    return $ Arr shiftedT1 shiftedT2 pos
  All name body pos -> do
    shiftedBody <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shift body
    return $ All name shiftedBody pos
  Conv t pos -> do
    shiftedT <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shift t
    return $ Conv shiftedT pos
  Comp t1 t2 pos -> do
    shiftedT1 <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shift t1
    shiftedT2 <- shiftTermsInRTypeAboveWithBoundsCheck cutoff shift t2
    return $ Comp shiftedT1 shiftedT2 pos
  Prom term pos -> do
    shiftedTerm <- shiftTermAboveWithBoundsCheck cutoff shift term
    return $ Prom shiftedTerm pos

-- Type Shifting Operations for Relations

-- | Shift relation variable indices in relational types
shiftRelsInRType :: Int -> RType -> RType
shiftRelsInRType shift ty = shiftRelsInRTypeAbove 0 shift ty

-- | Shift relation indices that are >= cutoff by shift amount
shiftRelsInRTypeAbove :: Int -> Int -> RType -> RType
shiftRelsInRTypeAbove cutoff shift ty = case ty of
  RVar name idx pos
    | idx >= cutoff -> RVar name (idx + shift) pos
    | otherwise -> RVar name idx pos
  RMacro name args pos -> RMacro name (map (shiftRelsInRTypeAbove cutoff shift) args) pos
  Arr t1 t2 pos -> Arr (shiftRelsInRTypeAbove cutoff shift t1) (shiftRelsInRTypeAbove cutoff shift t2) pos
  All name body pos -> All name (shiftRelsInRTypeAbove (cutoff + 1) shift body) pos -- Increment cutoff under All binder
  Conv t pos -> Conv (shiftRelsInRTypeAbove cutoff shift t) pos
  Comp t1 t2 pos -> Comp (shiftRelsInRTypeAbove cutoff shift t1) (shiftRelsInRTypeAbove cutoff shift t2) pos
  Prom term pos -> Prom term pos -- Terms are NOT shifted when shifting relation variables

-- | Shift proof indices by the given amount
shiftProof :: Int -> Proof -> Proof
shiftProof = shiftProofAbove 0

-- | Shift proof indices above a cutoff  
shiftProofAbove :: Int -> Int -> Proof -> Proof
shiftProofAbove cutoff shift proof = case proof of
  PVar name i pos
    | i >= cutoff -> PVar name (i + shift) pos
    | otherwise -> proof
  PTheoremApp name args pos -> PTheoremApp name args pos -- theorem args don't have bound variables
  LamP name rtype body pos -> LamP name rtype (shiftProofAbove (cutoff + 1) shift body) pos
  AppP p1 p2 pos -> AppP (shiftProofAbove cutoff shift p1) (shiftProofAbove cutoff shift p2) pos
  TyApp p rtype pos -> TyApp (shiftProofAbove cutoff shift p) rtype pos
  TyLam name body pos -> TyLam name (shiftProofAbove cutoff shift body) pos -- type lambda doesn't bind proof vars
  ConvProof t1 p t2 pos -> ConvProof t1 (shiftProofAbove cutoff shift p) t2 pos
  ConvIntro p pos -> ConvIntro (shiftProofAbove cutoff shift p) pos
  ConvElim p pos -> ConvElim (shiftProofAbove cutoff shift p) pos
  Iota t1 t2 pos -> Iota t1 t2 pos -- terms don't have proof variables
  RhoElim x t1 t2 p1 p2 pos -> RhoElim x t1 t2 (shiftProofAbove cutoff shift p1) (shiftProofAbove cutoff shift p2) pos
  Pair p1 p2 pos -> Pair (shiftProofAbove cutoff shift p1) (shiftProofAbove cutoff shift p2) pos
  Pi p1 x u v p2 pos -> Pi (shiftProofAbove cutoff shift p1) x u v (shiftProofAbove (cutoff + 3) shift p2) pos -- binds x,u,v
  PMacro name args pos -> PMacro name (map (shiftProofAbove cutoff shift) args) pos
