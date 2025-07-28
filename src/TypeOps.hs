module TypeOps
  ( expandMacros,
    expandMacrosWHNF,
    typeEquality,
    substituteTypeVar,
    normalizeMacroApplication,
    MacroExpansionMode (..),
    renameBinderVarsRType,
    substituteMacroArgsRType,
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (foldl')
import Errors
import Lib
import Normalize (expandTermMacros)
import Generic.Expansion (ExpansionResult(..), expandFully, expandWHNF)
import Generic.Equality (alphaEquality)
import Generic.Shift (shiftTermsInRType, shiftTermsInRTypeAbove, shiftAbove)
import Generic.FreeVars (freeVarsInTerm)
import Environment (noMacros)
import Text.Megaparsec (initialPos)
import Generic.Macro (renameBinderVarsG, substituteArgsG)

-- | Mode for macro expansion
data MacroExpansionMode
  = FullExpansion -- Expand all macros completely
  | WeakHeadExpansion -- Expand only head macros to weak head normal form
  | NoExpansion -- Don't expand macros (for structural comparison)
  deriving (Show, Eq)


-- | Expand macros in a relational type to normal form
expandMacros :: MacroEnvironment -> RType -> Either RelTTError (ExpansionResult RType)
expandMacros = expandFully

-- | Expand macros to weak head normal form only (for efficiency)
expandMacrosWHNF :: MacroEnvironment -> RType -> Either RelTTError (ExpansionResult RType)
expandMacrosWHNF = expandWHNF

-- | Type equality with efficient macro expansion (only to head-normal form when necessary)
typeEquality :: MacroEnvironment -> RType -> RType -> Either RelTTError Bool
typeEquality env t1 t2 = case (t1, t2) of
  -- OPTIMIZATION: Same macro applications - compare arguments without expanding
  (RMacro name1 args1 _, RMacro name2 args2 _)
    | name1 == name2 -> do
        case Map.lookup name1 (macroDefinitions env) of
          Just _ -> do
            -- Same macro, recursively compare arguments
            if length args1 == length args2
              then do
                comparisons <- mapM (uncurry (typeEquality env)) (zip args1 args2)
                return $ and comparisons
              else return False
          Nothing ->
            -- Not a macro, compare non-macro application structurally
            if length args1 == length args2
              then do
                comparisons <- mapM (uncurry (typeEquality env)) (zip args1 args2)
                return $ and comparisons
              else return False

  -- DIFFERENT MACRO HEADS: Expand both to WHNF and compare recursively
  (RMacro name1 _ _, RMacro name2 _ _)
    | name1 /= name2 -> do
        case (Map.lookup name1 (macroDefinitions env), Map.lookup name2 (macroDefinitions env)) of
          (Just _, Just _) -> do
            -- Both are macros, expand both to WHNF
            exp1 <- expandMacrosWHNF env t1
            exp2 <- expandMacrosWHNF env t2
            typeEquality env (expandedValue exp1) (expandedValue exp2)
          (Just _, Nothing) -> do
            -- First is macro, expand it
            exp1 <- expandMacrosWHNF env t1
            typeEquality env (expandedValue exp1) t2
          (Nothing, Just _) -> do
            -- Second is macro, expand it
            exp2 <- expandMacrosWHNF env t2
            typeEquality env t1 (expandedValue exp2)
          (Nothing, Nothing) ->
            -- Neither is macro, different applications are not equal
            return False

  -- ONE MACRO, ONE NON-MACRO: Expand the macro to WHNF
  (RMacro name1 _ _, _) -> do
    case Map.lookup name1 (macroDefinitions env) of
      Just _ -> do
        exp1 <- expandMacrosWHNF env t1
        typeEquality env (expandedValue exp1) t2
      Nothing -> return False -- Non-macro application vs non-application
  (_, RMacro name2 _ _) -> do
    case Map.lookup name2 (macroDefinitions env) of
      Just _ -> do
        exp2 <- expandMacrosWHNF env t2
        typeEquality env t1 (expandedValue exp2)
      Nothing -> return False -- Non-application vs non-macro application

  -- STRUCTURAL CASES: No macro expansion needed
  (RVar _ idx1 _, RVar _ idx2 _) ->
    -- Only de Bruijn index matters for alpha equivalence
    return $ idx1 == idx2
  (Arr t11 t12 _, Arr t21 t22 _) -> do
    eq1 <- typeEquality env t11 t21
    eq2 <- typeEquality env t12 t22
    return $ eq1 && eq2
  (All _ body1 _, All _ body2 _) -> do
    -- Names don't matter for α-equivalence, just structure
    typeEquality env body1 body2
  (Conv ty1 _, Conv ty2 _) ->
    typeEquality env ty1 ty2
  (Comp ty11 ty12 _, Comp ty21 ty22 _) -> do
    eq1 <- typeEquality env ty11 ty21
    eq2 <- typeEquality env ty12 ty22
    return $ eq1 && eq2
  (Prom term1 _, Prom term2 _) -> 
    -- Use alpha equality for promoted terms in types (structural equality)
    return $ alphaEquality env term1 term2
  _ -> return False

-- | Substitute relational variable at given index with type 's' in 'body', keeping
--   de Bruijn indices consistent under *any* nesting of ∀-binders.
substituteTypeVar ::
  -- | index of the bound variable to substitute
  Int ->
  -- | s  — replacement type
  RType ->
  -- | body (under that binder)
  RType ->
  RType
substituteTypeVar targetIndex s body = go 0 body
  where
    -- go d τ  ::  τ under d enclosing binders
    go :: Int -> RType -> RType
    go d ty = case ty of
      RVar y k p
        | k == d + targetIndex -> -- bound occurrence at target index
            shiftAbove d 1 s -- put 's' under the d binders
        | k > d + targetIndex -> RVar y (k - 1) p -- bypass the deleted binder
        | otherwise -> ty -- untouched
      All y t p -> All y (go (d + 1) t) p -- enter another binder
      Arr a b p -> Arr (go d a) (go d b) p
      Comp a b p -> Comp (go d a) (go d b) p
      Conv r p -> Conv (go d r) p
      RMacro n as p -> RMacro n (map (go d) as) p
      Prom t p -> Prom t p -- terms unchanged

-- | Simultaneously substitute multiple variables in a type
--   This is the ONLY correct way to handle macro parameter substitution
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
          Just replacement -> shiftAbove d 1 replacement -- substitute and shift
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


-- | Rename binder variables in RType based on actual arguments
renameBinderVarsRType :: [ParamInfo] -> [RType] -> RType -> RType
renameBinderVarsRType = renameBinderVarsG

-- | Substitute macro arguments respecting binder-parameters (type level)
substituteMacroArgsRType :: [ParamInfo] -> [RType] -> RType -> RType
substituteMacroArgsRType = substituteArgsG

-- | Normalize a macro application by expanding it
normalizeMacroApplication :: MacroEnvironment -> String -> [RType] -> Either RelTTError RType
normalizeMacroApplication env name args = do
  (sig, body) <- case Map.lookup name (macroDefinitions env) of
    Just def -> return def
    Nothing -> Left $ throwMacroError name (initialPos "<generated>") "macro expansion"

  case body of
    RelMacro rtypeBody -> do
      if length sig /= length args
        then
          Left $
            MacroArityMismatch
              name
              (length sig)
              (length args)
              (ErrorContext (initialPos "<generated>") "macro application")
        else do
          -- Apply binder renaming and substitution
          let body1 = renameBinderVarsRType sig args rtypeBody
              body2 = substituteMacroArgsRType sig args body1
          return body2
    TermMacro _ ->
      Left $ throwMacroError name (initialPos "<generated>") "expected relational macro but found term macro"
    ProofMacro _ ->
      Left $ throwMacroError name (initialPos "<generated>") "expected relational macro but found proof macro"


