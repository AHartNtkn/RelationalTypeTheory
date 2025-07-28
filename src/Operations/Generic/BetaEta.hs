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

module Operations.Generic.BetaEta
  ( -- * β-η equivalence
    betaEtaEquality
  , normalizeForBetaEta
    -- * Normalization strategies
  , BetaEtaMode(..)
  ) where

import Core.Syntax (Term(..), MacroEnvironment)
import Operations.Generic.Equality (alphaEquality) 
import Operations.Generic.Expansion (expandFully, ExpansionResult(..))
import Operations.Generic.Substitution (SubstAst(..))
import Operations.Generic.Shift (ShiftAst(..), shiftAboveWithBoundsCheck)
import Core.Errors (RelTTError(..))

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
        case shiftAboveWithBoundsCheck 0 (-1) f of
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

