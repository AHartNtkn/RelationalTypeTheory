module Normalize
  ( normalizeTerm,
    normalizeTermWHNF,
    termEquality,
    termEqualityAlpha,
    substituteTerm,
    shiftTerm,
    shiftTermAbove,
    shiftTermWithBoundsCheck,
    shiftTermAboveWithBoundsCheck,
    freeVariables,
    NormalizationStrategy (..),
    NormalizationResult (..),
  )
where

import qualified Data.Set as Set
import Errors
import Lib
import TermOps

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
  normalizeTermBetaEtaInternal (expandedTerm expansionResult)

-- | Normalize a term with macro expansion to weak head normal form
normalizeTermWHNF :: MacroEnvironment -> Term -> Either RelTTError NormalizationResult
normalizeTermWHNF env term = do
  -- First expand macros to WHNF
  expansionResult <- expandTermMacrosWHNF env term
  -- Then normalize
  normalizeTermWHNFInternal (expandedTerm expansionResult)

-- | Check βη-equality of two terms with macro expansion
termEquality :: MacroEnvironment -> Term -> Term -> Either RelTTError Bool
termEquality env t1 t2 = do
  norm1 <- normalizeTerm env t1
  norm2 <- normalizeTerm env t2
  return $ termEqualityAlpha (normalizedTerm norm1) (normalizedTerm norm2)

-- Internal functions (not exported)

-- | Normalize a term using β and η reduction to normal form (internal, no macro expansion)
normalizeTermBetaEtaInternal :: Term -> Either RelTTError NormalizationResult
normalizeTermBetaEtaInternal = normalizeWithStrategy FullNormalization 1000

-- | Normalize a term to weak head normal form (internal, no macro expansion)
normalizeTermWHNFInternal :: Term -> Either RelTTError NormalizationResult
normalizeTermWHNFInternal = normalizeWithStrategy WeakHeadNormal 1000

-- | Check α-equality of two terms (assuming they're in normal form)
termEqualityAlpha :: Term -> Term -> Bool
termEqualityAlpha t1 t2 = alphaEquivalent t1 t2 0 0

-- | Substitute term s for variable at de Bruijn index 0 in term t
substituteTerm :: Term -> Term -> Either RelTTError Term
substituteTerm s t = substituteAtIndex 0 s t

-- | Shift all free variables in a term by a given amount
shiftTerm :: Int -> Term -> Term
shiftTerm shift = shiftTermAbove 0 shift

-- | Get the set of free variable names in a term
freeVariables :: Term -> Set.Set String
freeVariables = freeVarsAtLevel 0

-- Internal implementation functions

-- | Normalize with a specific strategy and step limit
normalizeWithStrategy :: NormalizationStrategy -> Int -> Term -> Either RelTTError NormalizationResult
normalizeWithStrategy strategy maxSteps term =
  normalizeSteps strategy 0 maxSteps term

-- | Normalization step counter with recursion limit
normalizeSteps :: NormalizationStrategy -> Int -> Int -> Term -> Either RelTTError NormalizationResult
normalizeSteps strategy steps maxSteps term
  | steps >= maxSteps = Left $ throwNormalizationError term (termPos term) "normalization step limit exceeded"
  | otherwise =
      case oneStepReduce strategy term of
        Just reduced -> normalizeSteps strategy (steps + 1) maxSteps reduced
        Nothing ->
          case strategy of
            FullNormalization ->
              -- Try η-reduction
              case etaReduce term of
                Just etaReduced -> normalizeSteps strategy (steps + 1) maxSteps etaReduced
                Nothing -> Right $ NormalizationResult term steps (steps > 0)
            _ -> Right $ NormalizationResult term steps (steps > 0)

-- | Perform one step of β-reduction if possible
oneStepReduce :: NormalizationStrategy -> Term -> Maybe Term
oneStepReduce strategy term = case term of
  App (Lam _ body _) arg _ ->
    -- β-reduction: (λx.t) s → [s/x]t
    case substituteAtIndex 0 arg body of
      Right result -> Just result
      Left _ -> Nothing -- Substitution failed
  App t1 t2 pos ->
    -- Try reducing the function first (call-by-name)
    case oneStepReduce strategy t1 of
      Just t1' -> Just $ App t1' t2 pos
      Nothing ->
        case strategy of
          WeakHeadNormal -> Nothing -- Don't reduce arguments in WHNF
          _ ->
            -- Try reducing the argument
            case oneStepReduce strategy t2 of
              Just t2' -> Just $ App t1 t2' pos
              Nothing -> Nothing
  Lam name body pos ->
    case strategy of
      WeakHeadNormal -> Nothing -- Don't reduce under lambdas in WHNF
      _ ->
        case oneStepReduce strategy body of
          Just body' -> Just $ Lam name body' pos
          Nothing -> Nothing
  Var _ _ _ -> Nothing -- Variables can't be reduced
  TMacro _ _ _ -> Nothing -- Term macros should be expanded before normalization

-- | Perform η-reduction if possible: λx. t x → t (when x not free in t)
etaReduce :: Term -> Maybe Term
etaReduce term = case term of
  Lam name (App body (Var varName idx _) _) _
    | name == varName && idx == 0 && not (isFreeInTerm name (shiftTermAbove 0 (-1) body)) ->
        Just (shiftTermAbove 0 (-1) body)
  Lam name body pos ->
    -- Try to eta-reduce inside the lambda body first
    case etaReduce body of
      Just body' -> Just (Lam name body' pos)
      Nothing -> Nothing
  _ -> Nothing

-- | Substitute term s for de Bruijn index n in term t
substituteAtIndex :: Int -> Term -> Term -> Either RelTTError Term
substituteAtIndex n s t = subst n (shiftTermAbove 0 n s) t
  where
    subst idx replacement term = case term of
      Var name i pos
        | i == idx -> Right replacement
        | i > idx -> Right $ Var name (i - 1) pos -- Shift down unbound variables
        | otherwise -> Right term
      Lam name body pos -> do
        body' <- subst (idx + 1) (shiftTermAbove 0 1 replacement) body
        return $ Lam name body' pos
      App t1 t2 pos -> do
        t1' <- subst idx replacement t1
        t2' <- subst idx replacement t2
        return $ App t1' t2' pos
      TMacro name args pos -> do
        args' <- mapM (subst idx replacement) args
        return $ TMacro name args' pos

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

-- | Check if a variable name is free in a term
isFreeInTerm :: String -> Term -> Bool
isFreeInTerm varName = Set.member varName . freeVarsAtLevel 0

-- | Collect free variable names at a given binding level
freeVarsAtLevel :: Int -> Term -> Set.Set String
freeVarsAtLevel level term = case term of
  Var name i _
    | i >= level -> Set.singleton name
    | otherwise -> Set.empty
  Lam name body _ -> Set.delete name (freeVarsAtLevel (level + 1) body)
  App t1 t2 _ -> Set.union (freeVarsAtLevel level t1) (freeVarsAtLevel level t2)
  TMacro name args _ -> Set.insert name $ Set.unions (map (freeVarsAtLevel level) args)

-- | Check α-equivalence of two terms with binding depth tracking
alphaEquivalent :: Term -> Term -> Int -> Int -> Bool
alphaEquivalent t1 t2 depth1 depth2 = case (t1, t2) of
  (Var name1 i1 _, Var name2 i2 _) ->
    -- For bound variables, check de Bruijn indices
    -- For free variables, check names
    if i1 < depth1 && i2 < depth2
      then i1 == i2 -- Both bound, compare indices
      else
        if i1 >= depth1 && i2 >= depth2
          then name1 == name2 -- Both free, compare names
          else False -- One bound, one free
  (Lam _ body1 _, Lam _ body2 _) ->
    -- Names don't matter for α-equivalence, just structure
    alphaEquivalent body1 body2 (depth1 + 1) (depth2 + 1)
  (App f1 a1 _, App f2 a2 _) ->
    alphaEquivalent f1 f2 depth1 depth2
      && alphaEquivalent a1 a2 depth1 depth2
  (TMacro name1 args1 _, TMacro name2 args2 _) ->
    name1 == name2
      && length args1 == length args2
      && all (\(a1, a2) -> alphaEquivalent a1 a2 depth1 depth2) (zip args1 args2)
  _ -> False
