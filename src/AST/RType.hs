{-# LANGUAGE LambdaCase #-}

-- | RType operations: expansion, equality, and shifting
-- This module consolidates all RType-specific operations that were previously
-- scattered across TypeOps.hs and Shifting.hs.
module AST.RType
  ( -- * Macro Expansion
    MacroExpansionMode(..)
  , expandMacros
  , expandMacrosWHNF
  , normalizeMacroApplication
  , renameBinderVarsRType
  , substituteMacroArgsRType
    -- * Type Operations
  , typeEquality
    -- * Shifting Operations
  , shiftTermsInRType
  , shiftTermsInRTypeAbove
  , shiftTermsInRTypeWithBoundsCheck
  , shiftTermsInRTypeAboveWithBoundsCheck
  , shiftRelsInRType
  , shiftRelsInRTypeAbove
  ) where

import qualified Data.Set as Set
import Lib
import Generic.Macro (renameBinderVarsG, substituteArgsG)
import Generic.Shift (ShiftAst(..), shift, shiftWithBoundsCheck)
import Generic.Substitution (SubstAst(..))
import Generic.Expansion (expandFully, expandWHNF, ExpansionResult(..))
import Generic.Equality (EqualityAst(..), alphaEquality)
import Text.Megaparsec (initialPos)
import AST.Term (shiftTermAbove, shiftTermAboveWithBoundsCheck)

-- | Mode for macro expansion
data MacroExpansionMode
  = FullExpansion -- Expand all macros completely
  | WeakHeadExpansion -- Expand only head macros to weak head normal form
  | NoExpansion -- Don't expand macros (for structural comparison)
  deriving (Show, Eq)


-------------------------------------------------------------------
-- Macro Expansion Operations
-------------------------------------------------------------------

-- | Expand macros in an RType according to the given mode
expandMacros :: MacroExpansionMode -> MacroEnvironment -> RType -> ExpansionResult RType
expandMacros mode env rtype = 
  case mode of
    FullExpansion -> 
      case expandFully env rtype of
        Right result -> result
        Left _ -> ExpansionResult rtype 0 False
    WeakHeadExpansion -> 
      case expandWHNF env rtype of
        Right result -> result
        Left _ -> ExpansionResult rtype 0 False
    NoExpansion -> ExpansionResult rtype 0 False

-- | Expand macros to weak head normal form
expandMacrosWHNF :: MacroEnvironment -> RType -> ExpansionResult RType
expandMacrosWHNF = expandMacros WeakHeadExpansion

-- | Normalize a macro application by expanding and simplifying
normalizeMacroApplication :: MacroEnvironment -> String -> [RType] -> RType
normalizeMacroApplication env name args = 
  let pos = if null args then initialPos "<generated>" else rtypePos (head args)
      macro = RMacro name args pos
  in case expandFully env macro of
       Right result -> expandedValue result
       Left _ -> macro

-- | Rename binder variables in an RType (delegated to generic implementation)
renameBinderVarsRType :: [ParamInfo] -> [RType] -> RType -> RType
renameBinderVarsRType sig actuals = renameBinderVarsG sig actuals

-- | Substitute macro arguments in an RType (delegated to generic implementation)
substituteMacroArgsRType :: [ParamInfo] -> [RType] -> RType -> RType
substituteMacroArgsRType sig actuals = substituteArgsG sig actuals

-------------------------------------------------------------------
-- Type Operations
-------------------------------------------------------------------

-- | Check if two RTypes are equivalent
typeEquality :: MacroEnvironment -> RType -> RType -> Bool
typeEquality env t1 t2 = alphaEquality env t1 t2



-------------------------------------------------------------------
-- Shifting Operations for Terms in RTypes
-------------------------------------------------------------------

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

-------------------------------------------------------------------
-- Shifting Operations for Relations in RTypes
-------------------------------------------------------------------

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