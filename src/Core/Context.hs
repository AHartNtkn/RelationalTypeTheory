module Core.Context
  ( -- Context type and constructor
    Context(..),
    -- Context creation and manipulation
    emptyContext,
    emptyTypeEnvironment,
    extendTermContext,
    extendRelContext,
    extendProofContext,
    extendTypeEnvironment,
    extendMacroContext,
    extendTheoremContext,
    -- Variable lookup
    lookupTerm,
    lookupRel,
    lookupProof,
    lookupTypeVar,
    lookupMacro,
    lookupTheorem,
    -- Context utilities
    shiftContext,
    isFreshInContext,
    contextSize,
    validateContext,
    boundVarsInContext,
    freshVar,
    freshVarPair,
    -- Elaboration functions (moved from Parser.Context)
    bindTermVar,
    bindRelVar,
    bindProofVar,
    ElaborateM,
    -- Context building functions (moved from Interface.REPL)
    buildContextFromModuleInfo,
    buildContextFromBindings,
    inferParamKind,
    -- Dependency-aware context extension
    insertBinder,
    buildDependentContexts,
    extractVarNameFromMacroArg,
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Core.Errors
import Core.Syntax
import Operations.Generic.Shift (shift, shiftTermsInRType)
import Core.Raw (dummyPos)
import Text.Megaparsec (initialPos)
import Control.Monad.Reader
import Control.Monad.Except
import Data.List (foldl')


-- | Built-in macro fixities
builtinFixities :: [(String,Fixity)]
builtinFixities =
  [ ("∀_._"        , Prefix  3)   -- quantifier  (prefix, closes with '.')
  , ("λ_._"        , Prefix  3)
  , ("Λ_._"        , Prefix  3)
  , ("λ_:_._"      , Prefix  3)
  , ("_{_}"        , Postfix 4)   -- type application
  , ("_˘"          , Postfix 8)   -- converse
  , ("_∘_"         , Infixr  6)   -- composition
  , ("_→_"         , Infixr  2)   -- function arrow
  , ("ι⟨_,_⟩"      , Prefix  7)   -- iota
  , ("_,_"         , Infixr  1)
  , ("_⇃_⇂_"       , Prefix  4)
  , ("π_-_._._._"  , Prefix  4)
  , ("ρ{_._,_}_-_" , Prefix  4)
  ]

-- | Helper to create simple ParamInfo for non-cross-category macros
simpleParams :: VarKind -> [String] -> [ParamInfo]
simpleParams kind names = [ParamInfo n kind False [] | n <- names]

-- | Built-in macro bodies with parameter lists
builtinMacroBodies :: [(String, [ParamInfo], MacroBody)]
builtinMacroBodies =
  [ ("λ_._"       , [ParamInfo "x" TermK True [], ParamInfo "t" TermK False [0]]     , TermMacro $ Lam "x" (Var "t" 0 dummyPos) dummyPos)
  , ("∀_._"       , [ParamInfo "X" RelK True [], ParamInfo "T" RelK False [0]]       , RelMacro $ All "X" (RVar "T" 0 dummyPos) dummyPos)
  , ("_˘"         , simpleParams RelK ["R"]           , RelMacro $ Conv (RVar "R" 0 dummyPos) dummyPos)
  , ("_∘_"        , simpleParams RelK ["R","S"]       , RelMacro $ Comp (RVar "R" 1 dummyPos) (RVar "S" 0 dummyPos) dummyPos)
  , ("_→_"        , simpleParams RelK ["A","B"]       , RelMacro $ Arr (RVar "A" 1 dummyPos) (RVar "B" 0 dummyPos) dummyPos)
  , ("ι⟨_,_⟩"     , simpleParams TermK ["t1","t2"]    , ProofMacro $ Iota (Var "t1" 1 dummyPos) (Var "t2" 0 dummyPos) dummyPos)
  , ("_,_"        , simpleParams ProofK ["p","q"]     , ProofMacro $ Pair (PVar "p" 1 dummyPos) (PVar "q" 0 dummyPos) dummyPos)
  , ("λ_:_._"     , [ParamInfo "x" TermK True [], ParamInfo "T" RelK False [], ParamInfo "p" ProofK False [0]]  , ProofMacro $ LamP "x" (RVar "T" 1 dummyPos) (PVar "p" 0 dummyPos) dummyPos)
  , ("Λ_._"       , [ParamInfo "X" RelK True [], ParamInfo "p" ProofK False [0]]      , ProofMacro $ TyLam "X" (PVar "p" 0 dummyPos) dummyPos)
  , ("_{_}"       , [ParamInfo "p" ProofK False [], ParamInfo "R" RelK False []]      , ProofMacro $ TyApp (PVar "p" 1 dummyPos) (RVar "R" 0 dummyPos) dummyPos)
  , ("_⇃_⇂_"      , [ParamInfo "t1" TermK False [], ParamInfo "p" ProofK False [], ParamInfo "t2" TermK False []], ProofMacro $ ConvProof (Var "t1" 2 dummyPos) (PVar "p" 1 dummyPos) (Var "t2" 0 dummyPos) dummyPos)
  , ("π_-_._._._" , [ParamInfo "p" ProofK False [], ParamInfo "x" TermK True [], ParamInfo "u" ProofK True [], ParamInfo "v" ProofK True [], ParamInfo "q" ProofK False [1,2,3]], ProofMacro $ Pi (PVar "p" 4 dummyPos) "x" "u" "v" (PVar "q" 0 dummyPos) dummyPos)
  , ("ρ{_._,_}_-_" , [ParamInfo "x" TermK True [], ParamInfo "t1" TermK False [0], ParamInfo "t2" TermK False [0], ParamInfo "p" ProofK False [], ParamInfo "q" ProofK False []], ProofMacro $ RhoElim "x" (Var "t1" 3 dummyPos) (Var "t2" 2 dummyPos) (PVar "p" 1 dummyPos) (PVar "q" 0 dummyPos) dummyPos)
  ]

-- | Create context with builtins loaded (standard starting point)
emptyContext :: Context
emptyContext = 
  let builtinMacros = Map.fromList [(n, (pInfo, body)) | (n, pInfo, body) <- builtinMacroBodies]
      builtinFixityMap = Map.fromList builtinFixities
  in Context 
  { termBindings = Map.empty
  , relBindings = Map.empty
  , proofBindings = Map.empty
  , termDepth = 0
  , relDepth = 0
  , proofDepth = 0
  , macroDefinitions = builtinMacros
  , macroFixities = builtinFixityMap
  , theoremDefinitions = Map.empty
  , gensymCounter = 0
  }

-- | Create an empty type environment
emptyTypeEnvironment :: TypeEnvironment
emptyTypeEnvironment = TypeEnvironment Map.empty

-- | Extend context with a term binding
extendTermContext :: String -> RType -> Context -> Context
extendTermContext name ty ctx =
  let newIndex = 0
      shiftedTerms = Map.map (\(idx, mty) -> (idx + 1, mty)) (termBindings ctx)
   in ctx
        { termBindings = Map.insert name (newIndex, Just ty) shiftedTerms
        }

-- | Extend context with a relation binding
extendRelContext :: String -> Context -> Context
extendRelContext name ctx =
  let newIndex = 0
      shiftedRels = Map.map (+ 1) (relBindings ctx)
   in ctx {relBindings = Map.insert name newIndex shiftedRels}

-- | Extend context with a proof binding
extendProofContext :: String -> RelJudgment -> Context -> Context
extendProofContext name judgment ctx =
  let proofIdx = 0
      termDepthWhenStored = Map.size (termBindings ctx)
      shiftedProofs = Map.map (\(i, md, mj) -> (i + 1, md, mj)) (proofBindings ctx)
   in ctx
        { proofBindings = Map.insert name (proofIdx, Just termDepthWhenStored, Just judgment) shiftedProofs
        }

-- | Extend type environment with a type variable binding
extendTypeEnvironment :: String -> RType -> TypeEnvironment -> TypeEnvironment
extendTypeEnvironment name ty env =
  env {typeVarBindings = Map.insert name ty (typeVarBindings env)}

-- | Look up a term variable in the context
lookupTerm :: String -> Context -> Either RelTTError (Int, RType)
lookupTerm name ctx =
  case Map.lookup name (termBindings ctx) of
    Just (index, Just ty) -> Right (index, ty)
    Just (index, Nothing) -> Left $ InternalError ("Term " ++ name ++ " has no type information") (ErrorContext (initialPos "<context>") "term lookup")
    Nothing -> Left $ throwUnboundVar name (initialPos "<context>") "term lookup"

-- | Look up a relation variable in the context
lookupRel :: String -> Context -> Either RelTTError Int
lookupRel name ctx =
  case Map.lookup name (relBindings ctx) of
    Just idx -> Right idx
    Nothing -> Left $ throwUnboundVar name (initialPos "<context>") "relation lookup"

-- | Look up a proof variable in the context
lookupProof :: String -> Context -> Either RelTTError (Int, RelJudgment)
lookupProof name ctx =
  case Map.lookup name (proofBindings ctx) of
    Just (proofIdx, Just storedDepth, Just judgment) -> do
      let currentDepth = Map.size (termBindings ctx)
          termShift = currentDepth - storedDepth
          RelJudgment t1 rt t2 = judgment
          shiftedJudgment =
            RelJudgment
              (shift termShift t1)
              (shiftTermsInRType termShift rt)
              (shift termShift t2)
      Right (proofIdx, shiftedJudgment)
    Just (proofIdx, Nothing, Just _) -> Left $ InternalError ("Proof " ++ name ++ " has no depth information") (ErrorContext (initialPos "<context>") "proof lookup")
    Just (proofIdx, _, Nothing) -> Left $ InternalError ("Proof " ++ name ++ " has no judgment information") (ErrorContext (initialPos "<context>") "proof lookup")
    Nothing -> Left $ throwUnboundVar name (initialPos "<context>") "proof lookup"

-- | Look up a type variable in the environment
lookupTypeVar :: String -> TypeEnvironment -> Either RelTTError RType
lookupTypeVar name env =
  case Map.lookup name (typeVarBindings env) of
    Just ty -> Right ty
    Nothing -> Left $ UnboundTypeVariable name (ErrorContext (initialPos "<context>") "type variable lookup")

-- | Look up a macro in the context
lookupMacro :: String -> Context -> Either RelTTError MacroSig
lookupMacro name ctx =
  case Map.lookup name (macroDefinitions ctx) of
    Just macroSig -> Right macroSig
    Nothing -> Left $ UnboundMacro name (ErrorContext (initialPos "<context>") "macro lookup")

-- | Look up a theorem in the context
lookupTheorem :: String -> Context -> Either RelTTError ([Binding], RelJudgment, Proof)
lookupTheorem name ctx =
  case Map.lookup name (theoremDefinitions ctx) of
    Just theorem -> Right theorem
    Nothing -> Left $ UnknownTheorem name (ErrorContext (initialPos "<context>") "theorem lookup")

-- | Shift all de Bruijn indices in a context by a given amount
shiftContext :: Int -> Context -> Context
shiftContext shiftAmount ctx =
  let shiftedTerms = Map.map (\(idx, mty) -> (idx + shiftAmount, mty)) (termBindings ctx)
      shiftedRels = Map.map (+ shiftAmount) (relBindings ctx)
      shiftedProofs = Map.map (\(idx, md, mj) -> (idx + shiftAmount, md, mj)) (proofBindings ctx)
   in ctx { termBindings = shiftedTerms, relBindings = shiftedRels, proofBindings = shiftedProofs }

-- | Check if a variable name is fresh (not bound) in the context
isFreshInContext :: String -> Context -> Bool
isFreshInContext name ctx =
  not (Map.member name (termBindings ctx))
    && not (Map.member name (relBindings ctx))
    && not (Map.member name (proofBindings ctx))

-- | Get the total number of bindings in a context
contextSize :: Context -> Int
contextSize ctx =
  Map.size (termBindings ctx)
    + Map.size (relBindings ctx)
    + Map.size (proofBindings ctx)

-- | Validate that a context is well-formed
validateContext :: Context -> Either RelTTError ()
validateContext ctx = do
  -- Check that all de Bruijn indices are valid
  let termIndices = Map.elems $ Map.map fst (termBindings ctx)
      relIndices = Map.elems (relBindings ctx)
      proofIndices = Map.elems $ Map.map (\(i, _, _) -> i) (proofBindings ctx)
      allIndices = termIndices ++ relIndices ++ proofIndices
      maxIndex = if null allIndices then -1 else maximum allIndices
      minIndex = if null allIndices then 0 else minimum allIndices

  if minIndex < 0
    then Left $ InvalidDeBruijnIndex minIndex (ErrorContext (initialPos "<context>") "context validation")
    else
      if maxIndex >= contextSize ctx
        then Left $ InvalidDeBruijnIndex maxIndex (ErrorContext (initialPos "<context>") "context validation")
        else Right ()

-- | Get all bound variable names in a context
boundVarsInContext :: Context -> Set.Set String
boundVarsInContext ctx =
  Set.unions [ Set.fromList (Map.keys (termBindings ctx))
             , Set.fromList (Map.keys (relBindings ctx))
             , Set.fromList (Map.keys (proofBindings ctx))
             ]

-- | Generate a fresh variable name and return updated context
freshVar :: String -> Context -> (String, Context)
freshVar prefix ctx =
  let counter = gensymCounter ctx
      newName = prefix ++ show counter
      newCtx = ctx {gensymCounter = counter + 1}
   in (newName, newCtx)

-- | Generate a pair of fresh variable names with the same counter and return updated context
freshVarPair :: String -> String -> Context -> (String, String, Context)
freshVarPair prefix1 prefix2 ctx =
  let counter = gensymCounter ctx
      name1 = prefix1 ++ show counter
      name2 = prefix2 ++ show counter
      newCtx = ctx {gensymCounter = counter + 1}
   in (name1, name2, newCtx)

-- | Extend context with a macro definition (requires explicit parameter info)
extendMacroContext :: String -> [ParamInfo] -> MacroBody -> Fixity -> Context -> Context
extendMacroContext name pInfo body fixity ctx =
  ctx { macroDefinitions = Map.insert name (pInfo, body) (macroDefinitions ctx)
      , macroFixities = Map.insert name fixity (macroFixities ctx)
      }


-- | Extend context with a theorem definition  
extendTheoremContext :: String -> [Binding] -> RelJudgment -> Proof -> Context -> Context
extendTheoremContext name bindings judgment proof ctx =
  ctx { theoremDefinitions = Map.insert name (bindings, judgment, proof) (theoremDefinitions ctx) }

-- | Elaboration monad (moved from Parser.Context)
type ElaborateM = ReaderT Context (Except RelTTError)

-- | Helper functions for shifting maps during binding
shiftIntMap :: Map.Map k Int -> Map.Map k Int
shiftIntMap = Map.map (+1)

shiftProofMap :: Map.Map String (Int, Maybe Int, Maybe RelJudgment) -> Map.Map String (Int, Maybe Int, Maybe RelJudgment)
shiftProofMap = Map.map (\(i, md, mj) -> (i+1, md, mj))

-- | Bind a new term variable in the context (for elaboration)
bindTermVar :: String -> Context -> Context
bindTermVar x ctx =
  ctx { termBindings = Map.insert x (0, Nothing) (Map.map (\(i, mty) -> (i+1, mty)) (termBindings ctx))
      , termDepth = termDepth ctx + 1 }

-- | Bind a new relational variable in the context (for elaboration)
bindRelVar :: String -> Context -> Context
bindRelVar r ctx =
  ctx { relBindings = Map.insert r 0 (shiftIntMap (relBindings ctx))
      , relDepth = relDepth ctx + 1 }

-- | Bind a new proof variable in the context (for elaboration)
bindProofVar :: String -> RelJudgment -> Context -> Context
bindProofVar p j ctx =
  ctx { proofBindings = Map.insert p (0, Nothing, Just j) (shiftProofMap (proofBindings ctx))
      , proofDepth = proofDepth ctx + 1 }

--------------------------------------------------------------------------------
-- | Context building functions
--------------------------------------------------------------------------------

-- | Build unified context from ModuleInfo
buildContextFromModuleInfo :: (String -> Fixity) -> Context -> ModuleInfo -> Context
buildContextFromModuleInfo fixityOracle baseContext moduleInfo = 
  let macros = loadedMacros moduleInfo
      theorems = loadedTheorems moduleInfo
      -- Extend base context with macros
      contextWithMacros = Map.foldrWithKey addMacro baseContext macros
      -- Extend with theorems  
      contextWithTheorems = Map.foldrWithKey addTheorem contextWithMacros theorems
  in contextWithTheorems
  where
    addMacro name (params, body) ctx = extendMacroContext name params body (fixityOracle name) ctx
    addTheorem name (bindings, judgment, proof) ctx = extendTheoremContext name bindings judgment proof ctx

-- | Build context from bindings
buildContextFromBindings :: [Binding] -> Context
buildContextFromBindings bindings = foldl addBinding emptyContext bindings
  where
    addBinding ctx (TermBinding name) = extendTermContext name (RMacro "Type" [] (initialPos "<repl>")) ctx
    addBinding ctx (RelBinding name) = extendRelContext name ctx
    addBinding ctx (ProofBinding name judgment) = extendProofContext name judgment ctx

-- | Helper function to infer parameter kind from macro body
inferParamKind :: MacroBody -> VarKind
inferParamKind (TermMacro _) = TermK
inferParamKind (RelMacro _) = RelK  
inferParamKind (ProofMacro _) = ProofK


--------------------------------------------------------------------------------
-- | Dependency-aware context extension for macro binders
--------------------------------------------------------------------------------

-- | Extract variable name from a MacroArg
extractVarNameFromMacroArg :: MacroArg -> Maybe String
extractVarNameFromMacroArg (MTerm (Var n _ _)) = Just n
extractVarNameFromMacroArg (MTerm (FVar n _)) = Just n
extractVarNameFromMacroArg (MRel (RVar n _ _)) = Just n
extractVarNameFromMacroArg (MRel (FRVar n _)) = Just n
extractVarNameFromMacroArg (MProof (PVar n _ _)) = Just n
extractVarNameFromMacroArg (MProof (FPVar n _)) = Just n
extractVarNameFromMacroArg _ = Nothing

-- | One-step binder insertion (used internally)
insertBinder :: ParamInfo -> MacroArg -> Context -> Context
insertBinder param arg ctx
  | pBinds param = case (pKind param, extractVarNameFromMacroArg arg) of
      (TermK, Just name) -> bindTermVar name ctx
      (RelK, Just name) -> bindRelVar name ctx
      (ProofK, Just name) -> 
        let dummyJudgment = RelJudgment 
              (Var "⊥" 0 dummyPos) 
              (RVar "⊥" 0 dummyPos) 
              (Var "⊥" 0 dummyPos)
        in bindProofVar name dummyJudgment ctx
      _ -> ctx  -- Non-variable binders are errors, handled elsewhere
  | otherwise = ctx

-- | Build Γᵢ for every parameter and the final Γ⁺ containing all binders.
--
--   The list at index i is the context that must be used when elaborating argument i.
--
buildDependentContexts
  :: [ParamInfo] -> [MacroArg]
  -> Context                           -- Γ₀
  -> ([Context]      -- Γ₀ … Γₙ₋₁
     , Context)      -- Γ⁺
buildDependentContexts params args gamma0 = (ctxPerArg, finalCtx)
  where
    -- Accumulate binders seen so far
    step (binderEnv, ctx) (idx, (p, a)) =
      let ctxForThis =
            foldl' (\c j ->
                     case Map.lookup j binderEnv of
                       Just (paramInfo, arg) -> insertBinder paramInfo arg c
                       Nothing -> c)
                   gamma0
                   (pDeps p)
          ctx'      = if pBinds p then insertBinder p a ctx else ctx
          env'      = if pBinds p then Map.insert idx (p, a) binderEnv
                                  else binderEnv
      in  (env', ctx', ctxForThis)

    (_, finalCtx, ctxListRev) =
      foldl' (\(e, c, acc) x -> let (e', c', ctxI) = step (e, c) x
                               in  (e', c', ctxI:acc))
             (Map.empty, gamma0, [])
             (zip [0..] (zip params args))

    ctxPerArg = reverse ctxListRev
