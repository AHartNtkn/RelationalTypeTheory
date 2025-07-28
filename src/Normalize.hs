module Normalize
  ( normalizeTerm,
    normalizeTermWHNF,
    expandTermMacrosOneStep,
    expandTermMacros,
    expandTermMacrosWHNF,
    NormalizationStrategy (..),
    NormalizationResult (..),
    renameBinderVars,
    substituteMacroArgs,
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (foldl')
import Control.Monad (when)
import Errors
import Lib
import Generic.Shift (shiftAbove)
import Generic.Macro (renameBinderVarsG, substituteArgsG)
import Generic.Expansion (expandFully, expandWHNF, ExpansionResult(..))
import Generic.FreeVars (freeVarsInTerm)
import Generic.Substitution (SubstAst(..))
import Generic.BetaEta (normalizeForBetaEta)
import Environment (noMacros)

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



-- | Normalize a term with macro expansion using β and η reduction to normal form
normalizeTerm :: MacroEnvironment -> Term -> Either RelTTError NormalizationResult
normalizeTerm env term = do
  -- First expand macros
  expansionResult <- expandTermMacros env term
  -- Then normalize
  normalizeTermBetaEtaInternal (expandedValue expansionResult)

-- | Normalize a term with macro expansion to weak head normal form
normalizeTermWHNF :: MacroEnvironment -> Term -> Either RelTTError NormalizationResult
normalizeTermWHNF env term = do
  -- First expand macros to WHNF
  expansionResult <- expandTermMacrosWHNF env term
  -- Then normalize
  normalizeTermWHNFInternal (expandedValue expansionResult)


-- Internal functions (not exported)

-- | Normalize a term using β and η reduction to normal form (internal, no macro expansion)
normalizeTermBetaEtaInternal :: Term -> Either RelTTError NormalizationResult
normalizeTermBetaEtaInternal term = do
  normalized <- normalizeForBetaEta noMacros term
  return $ NormalizationResult normalized 0 (normalized /= term)

-- | Normalize a term to weak head normal form (internal, no macro expansion)
normalizeTermWHNFInternal :: Term -> Either RelTTError NormalizationResult
normalizeTermWHNFInternal term = do
  normalized <- normalizeForBetaEta noMacros term
  return $ NormalizationResult normalized 0 (normalized /= term)




-- | Fully expand all term macros in a term
expandTermMacros :: MacroEnvironment -> Term -> Either RelTTError (ExpansionResult Term)
expandTermMacros = expandFully

-- | Expand term macros to weak head normal form only
expandTermMacrosWHNF :: MacroEnvironment -> Term -> Either RelTTError (ExpansionResult Term)
expandTermMacrosWHNF = expandWHNF




-- | Expand a term macro one step only - just substitute arguments into macro body
expandTermMacrosOneStep :: MacroEnvironment -> Term -> Either RelTTError Term
expandTermMacrosOneStep env (TMacro name args pos) =
  case Map.lookup name (macroDefinitions env) of
    Nothing -> Left $ UnboundMacro name (ErrorContext pos "macro expansion")
    Just (sig, TermMacro body) -> do
      when (length sig /= length args) $
        Left $ MacroArityMismatch name (length sig) (length args) (ErrorContext pos "macro expansion")
      let body1 = renameBinderVars sig args body
          body2 = substituteMacroArgs sig args body1
      Right body2
    Just _ -> Left $ UnboundMacro name (ErrorContext pos "expected term macro")
expandTermMacrosOneStep _ t = Right t

-- | Rename binder variables based on actual arguments
renameBinderVars :: [ParamInfo] -> [Term] -> Term -> Term
renameBinderVars = renameBinderVarsG

-- | Substitute macro arguments respecting binder-parameters
substituteMacroArgs :: [ParamInfo] -> [Term] -> Term -> Term
substituteMacroArgs = substituteArgsG

