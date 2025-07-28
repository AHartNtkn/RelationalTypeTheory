{-# LANGUAGE LambdaCase #-}

-- | Term operations: normalization, equality, expansion, and shifting
-- This module consolidates all term-specific operations that were previously
-- scattered across Normalize.hs and Shifting.hs.
module AST.Term
  ( -- * Normalization
    NormalizationStrategy(..)
  , NormalizationResult(..)
  , normalizeTerm
  , normalizeTermWHNF
  , substituteTerm
    -- * Macro Expansion  
  , TermExpansionMode(..)
  , expandTermMacrosOneStep
  , expandTermMacros
  , expandTermMacrosWHNF
  , renameBinderVars
  , substituteMacroArgs
    -- * Shifting Operations
  , shiftTerm
  , shiftTermAbove
  , shiftTermWithBoundsCheck
  , shiftTermAboveWithBoundsCheck
  ) where

import qualified Data.Set as Set
import Lib
import Generic.Macro (renameBinderVarsG, substituteArgsG)
import Generic.Shift (ShiftAst(..), shift, shiftWithBoundsCheck)
import Generic.Substitution (SubstAst(..))
import Generic.Expansion (expandFully, expandWHNF, ExpansionResult(..), getMacroApp)
import Generic.Equality (EqualityAst(..), alphaEquality)

-- | Strategy for normalization
data NormalizationStrategy
  = FullNormalization -- β + η normalization to normal form
  | WeakHeadNormal -- Normalize to weak head normal form only
  | BetaOnly -- β-reduction only, no η
  deriving (Show, Eq)

-- | Result of normalization with metadata
data NormalizationResult = NormalizationResult
  { normalizedTerm :: Term,
    reductionSteps :: Int,
    wasNormalized :: Bool -- True if any reduction occurred
  }
  deriving (Show, Eq)

-- | Mode of term macro expansion
data TermExpansionMode
  = NoTermExpansion -- Don't expand macros
  | WeakHeadTermExpansion -- Expand to weak head normal form
  | FullTermExpansion -- Fully expand all macros
  deriving (Show, Eq)


-------------------------------------------------------------------
-- Normalization Operations
-------------------------------------------------------------------

-- | Normalize a term according to the given strategy
normalizeTerm :: NormalizationStrategy -> MacroEnvironment -> Term -> NormalizationResult
normalizeTerm strategy env term = 
  -- For now, just expand macros - full normalization would require beta/eta reduction
  case strategy of
    FullNormalization -> 
      case expandFully env term of
        Right result -> NormalizationResult (expandedValue result) (expansionSteps result) (wasExpanded result)
        Left _ -> NormalizationResult term 0 False
    WeakHeadNormal -> 
      case expandWHNF env term of
        Right result -> NormalizationResult (expandedValue result) (expansionSteps result) (wasExpanded result)
        Left _ -> NormalizationResult term 0 False
    BetaOnly -> NormalizationResult term 0 False  -- No beta reduction implemented yet

-- | Normalize a term to weak head normal form
normalizeTermWHNF :: MacroEnvironment -> Term -> NormalizationResult
normalizeTermWHNF = normalizeTerm WeakHeadNormal


-- | Substitute a term for a de Bruijn index
substituteTerm :: Int -> Term -> Term -> Term
substituteTerm index replacement target = substIndex index replacement target


-------------------------------------------------------------------
-- Macro Expansion Operations
-------------------------------------------------------------------

-- | Expand term macros one step
expandTermMacrosOneStep :: MacroEnvironment -> Term -> ExpansionResult Term
expandTermMacrosOneStep env term = 
  case getMacroApp term of
    Nothing -> ExpansionResult term 0 False
    Just _ -> 
      case expandWHNF env term of
        Right result -> 
          ExpansionResult (expandedValue result) (expansionSteps result) (wasExpanded result)
        Left _ -> ExpansionResult term 0 False

-- | Fully expand all term macros
expandTermMacros :: MacroEnvironment -> Term -> ExpansionResult Term
expandTermMacros env term = 
  case expandFully env term of
    Right result -> 
      ExpansionResult (expandedValue result) (expansionSteps result) (wasExpanded result)
    Left _ -> ExpansionResult term 0 False

-- | Expand term macros to weak head normal form
expandTermMacrosWHNF :: MacroEnvironment -> Term -> ExpansionResult Term
expandTermMacrosWHNF env term = 
  case expandWHNF env term of
    Right result -> 
      ExpansionResult (expandedValue result) (expansionSteps result) (wasExpanded result)
    Left _ -> ExpansionResult term 0 False

-- | Rename binder variables in a term (delegated to generic implementation)
renameBinderVars :: [ParamInfo] -> [Term] -> Term -> Term
renameBinderVars sig actuals = renameBinderVarsG sig actuals

-- | Substitute macro arguments in a term (delegated to generic implementation)  
substituteMacroArgs :: [ParamInfo] -> [Term] -> Term -> Term
substituteMacroArgs sig actuals = substituteArgsG sig actuals

-------------------------------------------------------------------
-- Shifting Operations
-------------------------------------------------------------------

-- | Shift all free variables in a term by a given amount
shiftTerm :: Int -> Term -> Term
shiftTerm shiftAmount = shift shiftAmount

-- | Shift de Bruijn indices above a cutoff
shiftTermAbove :: Int -> Int -> Term -> Term
shiftTermAbove cutoff shiftAmount = shiftAbove cutoff shiftAmount

-- | Shift term indices with bounds checking - returns Nothing if any index would go negative
shiftTermWithBoundsCheck :: Int -> Term -> Maybe Term
shiftTermWithBoundsCheck shiftAmount = shiftWithBoundsCheck shiftAmount

-- | Shift term indices above cutoff with bounds checking
shiftTermAboveWithBoundsCheck :: Int -> Int -> Term -> Maybe Term
shiftTermAboveWithBoundsCheck cutoff shiftAmount = shiftAboveWithBoundsCheck cutoff shiftAmount