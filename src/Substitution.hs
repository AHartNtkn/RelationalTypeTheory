module Substitution
  ( substituteMultipleTermVars,
    substituteMultipleTypeVars,
    applySubstitutionsToTerm,
    applySubstitutionsToRType,
    applySubstToJudgment,
    substituteTermVar,
    substituteRelVar,
    substituteTermInRType,
  )
where

import qualified Data.Map as Map
import Errors
import Lib
import Shifting (shiftRelsInRType)

-- | Simultaneously substitute multiple variables in a term
-- This is the correct way to handle cyclic substitutions like a↔b
substituteMultipleTermVars :: [(String, Term)] -> Term -> Term
substituteMultipleTermVars subs term = go term
  where
    subsMap = Map.fromList subs
    go t = case t of
      Var name idx pos -> case Map.lookup name subsMap of
        Just replacement -> replacement
        Nothing -> t
      Lam name body pos
        | Map.member name subsMap -> Lam name body pos -- Variable is shadowed, don't substitute in body
        | otherwise -> Lam name (go body) pos
      App t1 t2 pos -> App (go t1) (go t2) pos
      TMacro name args pos -> TMacro name (map go args) pos

-- | Simultaneously substitute multiple variables in a type
-- This is the ONLY correct way to handle macro parameter substitution
-- Moved from TypeOps.hs to centralize all substitution logic
substituteMultipleTypeVars ::
  -- | [(index, replacement), ...]
  [(Int, RType)] ->
  -- | body
  RType ->
  RType
substituteMultipleTypeVars substitutions body = go 0 body
  where
    go :: Int -> RType -> RType
    go d ty = case ty of
      RVar y k p ->
        case lookup (k - d) substitutions of
          Just replacement -> shiftRelsInRType d replacement -- substitute and shift
          Nothing ->
            -- Decrement index by number of substitutions that are lower-indexed
            let decrementAmount = length $ filter (\(idx, _) -> idx < (k - d)) substitutions
             in if k - d >= 0 && decrementAmount > 0
                  then RVar y (k - decrementAmount) p
                  else ty
      All y t p -> All y (go (d + 1) t) p
      Arr a b p -> Arr (go d a) (go d b) p
      Comp a b p -> Comp (go d a) (go d b) p
      Conv r p -> Conv (go d r) p
      RMacro n as p -> RMacro n (map (go d) as) p
      Prom t p -> Prom t p

-- | Apply theorem argument substitutions to a term (FIXED VERSION)
-- This replaces the broken sequential version in ProofChecker.hs
applySubstitutionsToTerm :: [(Binding, TheoremArg)] -> Term -> Either RelTTError Term
applySubstitutionsToTerm subs term = do
  -- Convert to name-based substitutions and apply simultaneously
  let termSubs = [(name, replacement) | (TermBinding name, TermArg replacement) <- subs]
  return $ substituteMultipleTermVars termSubs term

-- | Apply theorem argument substitutions to a relation type (FIXED VERSION)
-- This replaces the broken sequential version in ProofChecker.hs
applySubstitutionsToRType :: [(Binding, TheoremArg)] -> RType -> Either RelTTError RType
applySubstitutionsToRType subs rtype = do
  -- First apply relation variable substitutions
  relResult <- applyRelSubstitutions subs rtype
  -- Then apply term substitutions within promoted terms
  applyTermSubstitutionsInRType subs relResult
  where
    applyRelSubstitutions :: [(Binding, TheoremArg)] -> RType -> Either RelTTError RType
    applyRelSubstitutions substitutions ty = do
      let relSubs = [(name, replacement) | (RelBinding name, RelArg replacement) <- substitutions]
      return $ substituteMultipleRelVars relSubs ty

    applyTermSubstitutionsInRType :: [(Binding, TheoremArg)] -> RType -> Either RelTTError RType
    applyTermSubstitutionsInRType substitutions ty = do
      let termSubs = [(name, replacement) | (TermBinding name, TermArg replacement) <- substitutions]
      return $ substituteMultipleTermsInRType termSubs ty

-- | Apply theorem argument substitutions to a relational judgment (FIXED VERSION)
-- This replaces the broken version in ProofChecker.hs
applySubstToJudgment :: [(Binding, TheoremArg)] -> RelJudgment -> Either RelTTError RelJudgment
applySubstToJudgment subs (RelJudgment t r t') = do
  t1 <- applySubstitutionsToTerm subs t
  r1 <- applySubstitutionsToRType subs r
  t2 <- applySubstitutionsToTerm subs t'
  return (RelJudgment t1 r1 t2)

-- | Simultaneously substitute multiple relation variables in a type
substituteMultipleRelVars :: [(String, RType)] -> RType -> RType
substituteMultipleRelVars subs rtype = go rtype
  where
    subsMap = Map.fromList subs
    go ty = case ty of
      RVar name idx pos -> case Map.lookup name subsMap of
        Just replacement -> replacement
        Nothing -> ty
      RMacro name args pos -> RMacro name (map go args) pos
      Arr r1 r2 pos -> Arr (go r1) (go r2) pos
      All name r pos
        | Map.member name subsMap -> All name r pos -- Variable is shadowed
        | otherwise -> All name (go r) pos
      Conv r pos -> Conv (go r) pos
      Comp r1 r2 pos -> Comp (go r1) (go r2) pos
      Prom term pos -> Prom term pos -- Terms unchanged in relation substitution

-- | Simultaneously substitute multiple terms within a relational type (for promoted terms)
substituteMultipleTermsInRType :: [(String, Term)] -> RType -> RType
substituteMultipleTermsInRType subs rtype = go rtype
  where
    go ty = case ty of
      RVar _ _ _ -> ty
      RMacro name args pos -> RMacro name (map go args) pos
      Arr r1 r2 pos -> Arr (go r1) (go r2) pos
      All name r pos -> All name (go r) pos
      Conv r pos -> Conv (go r) pos
      Comp r1 r2 pos -> Comp (go r1) (go r2) pos
      Prom term pos -> Prom (substituteMultipleTermVars subs term) pos

-- | Single variable substitution in terms (for compatibility with existing code)
substituteTermVar :: String -> Term -> Term -> Term
substituteTermVar var replacement term = substituteMultipleTermVars [(var, replacement)] term

-- | Single relation variable substitution in types (for compatibility with existing code)
substituteRelVar :: String -> RType -> RType -> RType
substituteRelVar var replacement rtype = substituteMultipleRelVars [(var, replacement)] rtype

-- | Single term substitution in relation types (for compatibility with existing code)
substituteTermInRType :: String -> Term -> RType -> RType
substituteTermInRType var replacement rtype = substituteMultipleTermsInRType [(var, replacement)] rtype