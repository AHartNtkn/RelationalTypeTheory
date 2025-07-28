{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Generic β-η equivalence for terms.
-- This module implements proper β-η equivalence through normalization,
-- which is ONLY used for conversion proofs (ConvProof).
--
-- CRITICAL: This is different from alpha-equivalence!
-- - β-equivalence: (λx.e) t ≡ [t/x]e (beta reduction)
-- - η-equivalence: λx.f x ≡ f when x ∉ FV(f) (eta reduction)
-- - Used ONLY in ConvProof - all other comparisons use alpha-equivalence

module Generic.BetaEta
  ( -- * β-η equivalence
    betaEtaEquality
  , normalizeForBetaEta
    -- * Normalization strategies
  , BetaEtaMode(..)
  ) where

import qualified Data.Set as Set
import Lib (Term(..), MacroEnvironment)
import Generic.Equality (alphaEquality) 
import Generic.Expansion (expandFully, ExpansionResult(..))
import Generic.Substitution (SubstAst(..))
import Errors (RelTTError(..))

--------------------------------------------------------------------------------
-- | Normalization modes for β-η equivalence
--------------------------------------------------------------------------------

data BetaEtaMode = BetaOnly | BetaEtaFull
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- | β-η equivalence checking
--------------------------------------------------------------------------------

-- | Check β-η equivalence of two terms (for conversion proofs only!)
betaEtaEquality :: MacroEnvironment -> Term -> Term -> Either RelTTError Bool
betaEtaEquality env t1 t2 = do
  -- First expand macros, then normalize, then compare
  norm1 <- normalizeForBetaEta env t1
  norm2 <- normalizeForBetaEta env t2
  -- After normalization, use alpha-equivalence for structural comparison
  return $ alphaEquality env norm1 norm2

-- | Normalize a term for β-η equivalence checking
normalizeForBetaEta :: MacroEnvironment -> Term -> Either RelTTError Term
normalizeForBetaEta env term = do
  -- First expand all macros fully
  expanded <- expandFully env term
  let expandedTerm = expandedValue expanded
  -- Then apply β-η normalization
  betaEtaNormalize expandedTerm

--------------------------------------------------------------------------------
-- | β-η normalization implementation
--------------------------------------------------------------------------------

-- | Apply β-η normalization to a term
betaEtaNormalize :: Term -> Either RelTTError Term
betaEtaNormalize term = Right $ betaEtaNormalizeStep term

-- | Single step of β-η normalization (pure function for now)
betaEtaNormalizeStep :: Term -> Term
betaEtaNormalizeStep term = case term of
  -- Variables are already normal
  Var name idx pos -> Var name idx pos
  
  -- Normalize lambda bodies and apply η-reduction
  Lam name body pos -> 
    let normalizedBody = betaEtaNormalizeStep body
    in etaReduce (Lam name normalizedBody pos)
  
  -- Applications: normalize both sides and apply β-reduction
  App fun arg pos -> 
    let normalizedFun = betaEtaNormalizeStep fun
        normalizedArg = betaEtaNormalizeStep arg
    in betaReduce (App normalizedFun normalizedArg pos)
  
  -- Macros should have been expanded already
  TMacro name args pos -> 
    TMacro name (map betaEtaNormalizeStep args) pos

-- | Apply β-reduction: (λx.e) t → [t/x]e
betaReduce :: Term -> Term
betaReduce term = case term of
  App (Lam _ body _) arg _ -> 
    -- Perform substitution [arg/0]body
    case substIndex 0 arg body of
      result -> result
  _ -> term

-- | Apply η-reduction: λx.f x → f (when x not free in f)
etaReduce :: Term -> Term
etaReduce term = case term of
  Lam name (App f (Var varName varIdx _) _) pos 
    | varIdx == 0 && not (occursFree 0 f) -> 
        -- η-reduce: λx.f x → f (shift f down by 1)
        case shiftDown 1 f of
          Just reduced -> reduced
          Nothing -> term  -- Failed to shift, keep original
  _ -> term

-- | Check if a de Bruijn index occurs free in a term
occursFree :: Int -> Term -> Bool
occursFree targetIdx term = case term of
  Var _ idx _ -> idx == targetIdx
  Lam _ body _ -> occursFree (targetIdx + 1) body  -- Adjust for binder
  App t1 t2 _ -> occursFree targetIdx t1 || occursFree targetIdx t2
  TMacro _ args _ -> any (occursFree targetIdx) args

-- | Shift de Bruijn indices down (used in η-reduction)
shiftDown :: Int -> Term -> Maybe Term
shiftDown amount term = shiftDownAbove 0 amount term

-- | Shift indices above cutoff down by amount
shiftDownAbove :: Int -> Int -> Term -> Maybe Term
shiftDownAbove cutoff amount term = case term of
  Var name idx pos
    | idx >= cutoff + amount -> Just $ Var name (idx - amount) pos
    | idx >= cutoff -> Nothing  -- Would go negative
    | otherwise -> Just term
  Lam name body pos -> do
    shiftedBody <- shiftDownAbove (cutoff + 1) amount body
    return $ Lam name shiftedBody pos
  App t1 t2 pos -> do
    shiftedT1 <- shiftDownAbove cutoff amount t1
    shiftedT2 <- shiftDownAbove cutoff amount t2
    return $ App shiftedT1 shiftedT2 pos
  TMacro name args pos -> do
    shiftedArgs <- mapM (shiftDownAbove cutoff amount) args
    return $ TMacro name shiftedArgs pos