module TypeOps
  ( expandMacros,
    expandMacrosWHNF,
    typeEquality,
    substituteTypeVar,
    freeTypeVariables,
    normalizeMacroApplication,
    MacroExpansionMode (..),
    ExpansionResult (..),
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Errors
import Lib
import Normalize
import Shifting
import Text.Megaparsec (initialPos)

-- | Mode for macro expansion
data MacroExpansionMode
  = FullExpansion -- Expand all macros completely
  | WeakHeadExpansion -- Expand only head macros to weak head normal form
  | NoExpansion -- Don't expand macros (for structural comparison)
  deriving (Show, Eq)

-- | Result of type expansion/normalization
data ExpansionResult = ExpansionResult
  { expandedType :: RType,
    expansionSteps :: Int,
    wasExpanded :: Bool
  }
  deriving (Show, Eq)

-- | Expand macros in a relational type to normal form
expandMacros :: MacroEnvironment -> RType -> Either RelTTError ExpansionResult
expandMacros env ty = expandWithStepLimit env FullExpansion 1000 ty

-- | Expand macros to weak head normal form only (for efficiency)
expandMacrosWHNF :: MacroEnvironment -> RType -> Either RelTTError ExpansionResult
expandMacrosWHNF env ty = expandWithStepLimit env WeakHeadExpansion 1000 ty

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
            typeEquality env (expandedType exp1) (expandedType exp2)
          (Just _, Nothing) -> do
            -- First is macro, expand it
            exp1 <- expandMacrosWHNF env t1
            typeEquality env (expandedType exp1) t2
          (Nothing, Just _) -> do
            -- Second is macro, expand it
            exp2 <- expandMacrosWHNF env t2
            typeEquality env t1 (expandedType exp2)
          (Nothing, Nothing) ->
            -- Neither is macro, different applications are not equal
            return False

  -- ONE MACRO, ONE NON-MACRO: Expand the macro to WHNF
  (RMacro name1 _ _, _) -> do
    case Map.lookup name1 (macroDefinitions env) of
      Just _ -> do
        exp1 <- expandMacrosWHNF env t1
        typeEquality env (expandedType exp1) t2
      Nothing -> return False -- Non-macro application vs non-application
  (_, RMacro name2 _ _) -> do
    case Map.lookup name2 (macroDefinitions env) of
      Just _ -> do
        exp2 <- expandMacrosWHNF env t2
        typeEquality env t1 (expandedType exp2)
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
  (Prom term1 _, Prom term2 _) -> do
    -- Use term equality for promoted terms
    termEquality env term1 term2
  _ -> return False

-- | Substitute relational variable at given index with type 's' in 'body', keeping
--   de Bruijn indices consistent under *any* nesting of ∀-binders.
substituteTypeVar :: Int      -- ^ index of the bound variable to substitute
                  -> RType    -- ^ s  — replacement type
                  -> RType    -- ^ body (under that binder)
                  -> RType
substituteTypeVar targetIndex s body = go 0 body
  where
    -- go d τ  ::  τ under d enclosing binders
    go :: Int -> RType -> RType
    go d ty = case ty of
      RVar y k p
        | k == d + targetIndex ->            -- bound occurrence at target index
            shiftRelsInRType d s             -- put 's' under the d binders
        | k > d + targetIndex -> RVar y (k-1) p  -- bypass the deleted binder
        | otherwise       -> ty              -- untouched

      All y t p     -> All  y (go (d+1) t) p -- enter another binder
      Arr  a b p    -> Arr  (go d a) (go d b) p
      Comp a b p    -> Comp (go d a) (go d b) p
      Conv r p      -> Conv (go d r) p
      RMacro n as p -> RMacro n (map (go d) as) p
      Prom t  p     -> Prom t p              -- terms unchanged

-- | Simultaneously substitute multiple variables in a type
--   This is the ONLY correct way to handle macro parameter substitution
substituteMultipleTypeVars :: [(Int, RType)] -- ^ [(index, replacement), ...]
                           -> RType          -- ^ body
                           -> RType
substituteMultipleTypeVars substitutions body = go 0 body
  where
    go :: Int -> RType -> RType
    go d ty = case ty of
      RVar y k p ->
        case lookup (k - d) substitutions of
          Just replacement -> shiftRelsInRType d replacement  -- substitute and shift
          Nothing -> 
            -- Decrement index by number of substitutions that are lower-indexed
            let decrementAmount = length $ filter (\(idx, _) -> idx < (k - d)) substitutions
            in if k - d >= 0 && decrementAmount > 0
               then RVar y (k - decrementAmount) p
               else ty
               
      All y t p     -> All  y (go (d+1) t) p
      Arr  a b p    -> Arr  (go d a) (go d b) p
      Comp a b p    -> Comp (go d a) (go d b) p
      Conv r p      -> Conv (go d r) p
      RMacro n as p -> RMacro n (map (go d) as) p
      Prom t  p     -> Prom t p

-- | Get free type variables in a relational type
freeTypeVariables :: RType -> Set.Set String
freeTypeVariables ty = case ty of
  RVar name _ _ -> Set.singleton name
  RMacro name args _ -> Set.insert name $ Set.unions (map freeTypeVariables args)
  Arr t1 t2 _ -> Set.union (freeTypeVariables t1) (freeTypeVariables t2)
  All name body _ -> Set.delete name (freeTypeVariables body)
  Conv t _ -> freeTypeVariables t
  Comp t1 t2 _ -> Set.union (freeTypeVariables t1) (freeTypeVariables t2)
  Prom term _ -> freeVariables term

-- | Normalize a macro application by expanding it
normalizeMacroApplication :: MacroEnvironment -> String -> [RType] -> Either RelTTError RType
normalizeMacroApplication env name args = do
  (params, body) <- case Map.lookup name (macroDefinitions env) of
    Just def -> return def
    Nothing -> Left $ throwMacroError name (initialPos "<generated>") "macro expansion"

  case body of
    RelMacro rtypeBody -> do
      if length params /= length args
        then
          Left $
            MacroArityMismatch
              name
              (length params)
              (length args)
              (ErrorContext (initialPos "<generated>") "macro application")
        else do
          -- Substitute arguments for parameters in body simultaneously
          -- Parameters are indexed in reverse order (most recent = index 0)
          let substitutions = zip [length params - 1, length params - 2 .. 0] args
          return $ substituteMultipleTypeVars substitutions rtypeBody
    TermMacro _ ->
      Left $ throwMacroError name (initialPos "<generated>") "expected relational macro but found term macro"

-- Internal expansion implementation

-- | Expand types with a step limit to prevent infinite loops
expandWithStepLimit :: MacroEnvironment -> MacroExpansionMode -> Int -> RType -> Either RelTTError ExpansionResult
expandWithStepLimit env mode maxSteps ty =
  if maxSteps <= 0
    then Left $ InternalError "Macro expansion step limit exceeded - possible infinite cycle" (ErrorContext (initialPos "<generated>") "macro expansion")
    else expandWithMode env mode maxSteps ty

-- | Expand types with a specific mode
expandWithMode :: MacroEnvironment -> MacroExpansionMode -> Int -> RType -> Either RelTTError ExpansionResult
expandWithMode env mode maxSteps ty = case ty of
  RMacro name args pos -> do
    case Map.lookup name (macroDefinitions env) of
      Nothing -> do
        -- Not a macro, just expand arguments
        expandedArgs <- mapM (expandWithMode env mode maxSteps) args
        let resultArgs = map expandedType expandedArgs
            totalSteps = sum (map expansionSteps expandedArgs)
            anyExpanded = any wasExpanded expandedArgs
        return $ ExpansionResult (RMacro name resultArgs pos) totalSteps anyExpanded
      Just (params, body) -> do
        -- It's a macro - expand it
        case body of
          RelMacro rtypeBody -> do
            if length params /= length args
              then
                Left $
                  MacroArityMismatch
                    name
                    (length params)
                    (length args)
                    (ErrorContext (initialPos "<generated>") "macro expansion")
              else do
                -- Expand arguments first
                expandedArgs <- mapM (expandWithMode env mode maxSteps) args
                let resultArgs = map expandedType expandedArgs
                    argSteps = sum (map expansionSteps expandedArgs)

                -- Substitute arguments into macro body simultaneously
                -- Parameters are indexed in reverse order (most recent = index 0)
                let substitutions = zip [length params - 1, length params - 2 .. 0] resultArgs
                    expandedBody = substituteMultipleTypeVars substitutions rtypeBody

                case mode of
                  NoExpansion ->
                    return $ ExpansionResult (RMacro name resultArgs pos) argSteps True
                  WeakHeadExpansion ->
                    -- For WHNF, just return the substituted body without further expansion
                    return $ ExpansionResult expandedBody (argSteps + 1) True
                  FullExpansion -> do
                    -- Recursively expand the substituted body
                    bodyResult <- expandWithMode env mode (maxSteps - 1) expandedBody
                    return $
                      ExpansionResult
                        (expandedType bodyResult)
                        (argSteps + 1 + expansionSteps bodyResult)
                        True
          TermMacro _ ->
            Left $ throwMacroError name (initialPos "<generated>") "expected relational macro but found term macro"
  Arr t1 t2 pos -> do
    exp1 <- expandWithMode env mode maxSteps t1
    exp2 <- expandWithMode env mode maxSteps t2
    let totalSteps = expansionSteps exp1 + expansionSteps exp2
        anyExpanded = wasExpanded exp1 || wasExpanded exp2
    return $ ExpansionResult (Arr (expandedType exp1) (expandedType exp2) pos) totalSteps anyExpanded
  All name body pos -> do
    expBody <- expandWithMode env mode maxSteps body
    return $ ExpansionResult (All name (expandedType expBody) pos) (expansionSteps expBody) (wasExpanded expBody)
  Conv t pos -> do
    expT <- expandWithMode env mode maxSteps t
    return $ ExpansionResult (Conv (expandedType expT) pos) (expansionSteps expT) (wasExpanded expT)
  Comp t1 t2 pos -> do
    exp1 <- expandWithMode env mode maxSteps t1
    exp2 <- expandWithMode env mode maxSteps t2
    let totalSteps = expansionSteps exp1 + expansionSteps exp2
        anyExpanded = wasExpanded exp1 || wasExpanded exp2
    return $ ExpansionResult (Comp (expandedType exp1) (expandedType exp2) pos) totalSteps anyExpanded
  Prom term pos -> do
    -- Expand term macros within the promoted term
    termResult <- expandTermMacros env term
    return $ ExpansionResult (Prom (expandedTerm termResult) pos) (termExpansionSteps termResult) (wasTermExpanded termResult)
  _ -> return $ ExpansionResult ty 0 False -- No expansion needed
