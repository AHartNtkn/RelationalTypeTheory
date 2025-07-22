module Normalize
  ( normalizeTerm,
    normalizeTermWHNF,
    termEquality,
    termEqualityAlpha,
    substituteTerm,
    freeVariables,
    expandTermMacrosOneStep,
    expandTermMacros,
    expandTermMacrosWHNF,
    NormalizationStrategy (..),
    NormalizationResult (..),
    TermExpansionResult (..),
    TermExpansionMode (..),
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Errors
import Lib
import Shifting

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

-- | Result of term macro expansion
data TermExpansionResult = TermExpansionResult
  { expandedTerm :: Term,
    termExpansionSteps :: Int,
    wasTermExpanded :: Bool
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
  termEqualityAlpha env (normalizedTerm norm1) (normalizedTerm norm2)

-- Internal functions (not exported)

-- | Normalize a term using β and η reduction to normal form (internal, no macro expansion)
normalizeTermBetaEtaInternal :: Term -> Either RelTTError NormalizationResult
normalizeTermBetaEtaInternal = normalizeWithStrategy FullNormalization 1000

-- | Normalize a term to weak head normal form (internal, no macro expansion)
normalizeTermWHNFInternal :: Term -> Either RelTTError NormalizationResult
normalizeTermWHNFInternal = normalizeWithStrategy WeakHeadNormal 1000

-- | Check α-equality of two terms with lazy macro expansion
termEqualityAlpha :: MacroEnvironment -> Term -> Term -> Either RelTTError Bool
termEqualityAlpha env t1 t2 = alphaEquivalentLazy env t1 t2 0 0

-- | Substitute term s for variable at de Bruijn index 0 in term t
substituteTerm :: Term -> Term -> Either RelTTError Term
substituteTerm s t = substituteAtIndex 0 s t

-- | Shift all free variables in a term by a given amount
shiftTerm :: Int -> Term -> Term
shiftTerm shift = shiftTermAbove 0 shift

-- | Get the set of free variable names in a term
freeVariables :: Term -> Set.Set String
freeVariables = freeVarsAtLevel 0

-- | Fully expand all term macros in a term
expandTermMacros :: MacroEnvironment -> Term -> Either RelTTError TermExpansionResult
expandTermMacros env term = expandTermWithStepLimit env FullTermExpansion 1000 term

-- | Expand term macros to weak head normal form only
expandTermMacrosWHNF :: MacroEnvironment -> Term -> Either RelTTError TermExpansionResult
expandTermMacrosWHNF env term = expandTermWithStepLimit env WeakHeadTermExpansion 1000 term

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


-- | Check α-equivalence with lazy macro expansion
alphaEquivalentLazy :: MacroEnvironment -> Term -> Term -> Int -> Int -> Either RelTTError Bool
alphaEquivalentLazy env t1 t2 depth1 depth2 = case (t1, t2) of
  -- Case 1: Neither has a macro at head - compare heads and recurse on sub-parts
  (Var name1 i1 _, Var name2 i2 _) ->
    Right $ if i1 < depth1 && i2 < depth2
      then i1 == i2 -- Both bound, compare indices
      else
        if i1 >= depth1 && i2 >= depth2
          then name1 == name2 -- Both free, compare names
          else False -- One bound, one free
  
  (Lam _ body1 _, Lam _ body2 _) ->
    -- Heads match (both lambdas), recurse on bodies
    alphaEquivalentLazy env body1 body2 (depth1 + 1) (depth2 + 1)
  
  (App f1 a1 _, App f2 a2 _) -> do
    -- Heads match (both apps), recurse on function and argument
    fEq <- alphaEquivalentLazy env f1 f2 depth1 depth2
    aEq <- alphaEquivalentLazy env a1 a2 depth1 depth2
    return $ fEq && aEq
  
  -- Case 2: Both are macros
  (TMacro name1 args1 _, TMacro name2 args2 _) ->
    if name1 == name2 && length args1 == length args2
      then do
        -- Same macro - compare arguments
        results <- sequence $ zipWith (\a1 a2 -> alphaEquivalentLazy env a1 a2 depth1 depth2) args1 args2
        return $ and results
      else do
        -- Different macros - expand left one only
        expanded1 <- expandTermMacrosOneStep env t1
        alphaEquivalentLazy env expanded1 t2 depth1 depth2
  
  -- Case 3: Only left is a macro - expand it
  (TMacro _ _ _, _) -> do
    expanded1 <- expandTermMacrosOneStep env t1
    alphaEquivalentLazy env expanded1 t2 depth1 depth2
  
  -- Case 3: Only right is a macro - expand it
  (_, TMacro _ _ _) -> do
    expanded2 <- expandTermMacrosOneStep env t2
    alphaEquivalentLazy env t1 expanded2 depth1 depth2
  
  -- Different constructors
  _ -> Right False

-- | Expand a term macro one step only - just substitute arguments into macro body
expandTermMacrosOneStep :: MacroEnvironment -> Term -> Either RelTTError Term
expandTermMacrosOneStep env term = case term of
  TMacro name args pos -> do
    case Map.lookup name (macroDefinitions env) of
      Nothing ->
        Left $ UnboundMacro name (ErrorContext pos "term macro expansion")
      Just (params, body) -> do
        case body of
          TermMacro termBody -> do
            if length params /= length args
              then
                Left $
                  MacroArityMismatch
                    name
                    (length params)
                    (length args)
                    (ErrorContext pos "term macro expansion")
              else do
                -- Substitute arguments into macro body using de Bruijn indices
                -- Parameters are bound in reverse order: first param gets highest index
                let expandedBody = substituteMacroArgs (length params - 1) args termBody
                return expandedBody
          RelMacro _ ->
            Left $ UnboundMacro name (ErrorContext pos "expected term macro but found relational macro")
  _ -> Right term -- Not a macro, return as-is

-- | Substitute macro arguments using de Bruijn indices
-- The first parameter has the highest index, last parameter has index 0
substituteMacroArgs :: Int -> [Term] -> Term -> Term
substituteMacroArgs maxIdx args term = 
  foldl (\t (idx, arg) -> 
    case substituteAtIndex idx arg t of
      Right result -> result
      Left _ -> error "Macro substitution failed"
  ) term (zip [maxIdx, maxIdx-1..0] args)

-- | Expand terms with a step limit to prevent infinite loops
expandTermWithStepLimit :: MacroEnvironment -> TermExpansionMode -> Int -> Term -> Either RelTTError TermExpansionResult
expandTermWithStepLimit env mode maxSteps term =
  if maxSteps <= 0
    then Left $ InternalError "Term macro expansion step limit exceeded - possible infinite cycle" (ErrorContext (termPos term) "term macro expansion")
    else expandTermWithMode env mode maxSteps term

-- | Expand terms with a specific mode
expandTermWithMode :: MacroEnvironment -> TermExpansionMode -> Int -> Term -> Either RelTTError TermExpansionResult
expandTermWithMode env mode maxSteps term = case term of
  TMacro name args pos -> do
    case Map.lookup name (macroDefinitions env) of
      Nothing ->
        -- Undefined macro - this is an error
        Left $ UnboundMacro name (ErrorContext pos "term macro expansion")
      Just (params, body) -> do
        -- It's a macro - check if it's a term macro
        case body of
          TermMacro termBody -> do
            if length params /= length args
              then
                Left $
                  MacroArityMismatch
                    name
                    (length params)
                    (length args)
                    (ErrorContext pos "term macro expansion")
              else do
                -- Expand arguments first
                expandedArgs <- mapM (expandTermWithMode env mode maxSteps) args
                let resultArgs = map expandedTerm expandedArgs
                    argSteps = sum (map termExpansionSteps expandedArgs)

                -- Substitute arguments into macro body using de Bruijn indices
                -- Parameters are bound in reverse order: first param gets highest index
                let expandedBody = substituteMacroArgs (length params - 1) resultArgs termBody

                case mode of
                  NoTermExpansion ->
                    return $ TermExpansionResult (TMacro name resultArgs pos) argSteps True
                  WeakHeadTermExpansion ->
                    -- For WHNF, just return the substituted body without further expansion
                    return $ TermExpansionResult expandedBody (argSteps + 1) True
                  FullTermExpansion -> do
                    -- Recursively expand the substituted body
                    bodyResult <- expandTermWithMode env mode (maxSteps - 1) expandedBody
                    return $
                      TermExpansionResult
                        (expandedTerm bodyResult)
                        (argSteps + 1 + termExpansionSteps bodyResult)
                        True
          RelMacro _ ->
            Left $ UnboundMacro name (ErrorContext pos "expected term macro but found relational macro")
  Var _ _ _ ->
    -- Variables don't expand
    return $ TermExpansionResult term 0 False
  Lam name body pos -> do
    -- Expand inside lambda body
    bodyResult <- expandTermWithMode env mode maxSteps body
    if wasTermExpanded bodyResult
      then
        return $
          TermExpansionResult
            (Lam name (expandedTerm bodyResult) pos)
            (termExpansionSteps bodyResult)
            True
      else return $ TermExpansionResult term 0 False
  App t1 t2 pos -> do
    -- Expand both parts of application
    exp1 <- expandTermWithMode env mode maxSteps t1
    exp2 <- expandTermWithMode env mode maxSteps t2
    let totalSteps = termExpansionSteps exp1 + termExpansionSteps exp2
        anyExpanded = wasTermExpanded exp1 || wasTermExpanded exp2
    if anyExpanded
      then return $ TermExpansionResult (App (expandedTerm exp1) (expandedTerm exp2) pos) totalSteps True
      else return $ TermExpansionResult term 0 False
