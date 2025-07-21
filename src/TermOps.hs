module TermOps
  ( expandTermMacros,
    expandTermMacrosWHNF,
    TermExpansionResult (..),
    TermExpansionMode (..),
  )
where

import qualified Data.Map as Map
import Errors
import Lib

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

-- | Fully expand all term macros in a term
expandTermMacros :: MacroEnvironment -> Term -> Either RelTTError TermExpansionResult
expandTermMacros env term = expandTermWithStepLimit env FullTermExpansion 1000 term

-- | Expand term macros to weak head normal form only
expandTermMacrosWHNF :: MacroEnvironment -> Term -> Either RelTTError TermExpansionResult
expandTermMacrosWHNF env term = expandTermWithStepLimit env WeakHeadTermExpansion 1000 term

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

                -- Substitute arguments into macro body
                let substitutions = zip params resultArgs
                    expandedBody = foldr (uncurry substituteTermVarInTerm) termBody substitutions

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

-- | Substitute a term for a variable in another term
substituteTermVarInTerm :: String -> Term -> Term -> Term
substituteTermVarInTerm var replacement term = case term of
  Var name _ _ | name == var -> replacement
  Var _ _ _ -> term
  Lam name _ _ | name == var -> term -- Variable is shadowed
  Lam name body pos -> Lam name (substituteTermVarInTerm var replacement body) pos
  App t1 t2 pos ->
    App
      (substituteTermVarInTerm var replacement t1)
      (substituteTermVarInTerm var replacement t2)
      pos
  TMacro name args pos -> TMacro name (map (substituteTermVarInTerm var replacement) args) pos
