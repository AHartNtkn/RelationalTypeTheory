module Context
  ( emptyTypingContext,
    emptyTypeEnvironment,
    extendTermContext,
    extendRelContext,
    extendProofContext,
    extendTypeEnvironment,
    extendTheoremEnvironment,
    lookupTerm,
    lookupRel,
    lookupProof,
    lookupTypeVar,
    lookupMacro,
    lookupTheorem,
    shiftContext,
    isFreshInContext,
    contextSize,
    validateContext,
    boundVarsInContext,
    freshVar,
    freshVarPair,
    -- Re-export from Lib to avoid conflicts
    noMacros,
    noTheorems,
    extendMacroEnvironment,
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Errors
import Lib
import Lib.FreeVars (freeVarsInTerm, freeVarsInRType)
import Shifting (shiftTerm, shiftTermsInRType)
import Text.Megaparsec (initialPos)


-- | Create an empty typing context
emptyTypingContext :: TypingContext
emptyTypingContext = TypingContext Map.empty Map.empty Map.empty 0

-- | Create an empty type environment
emptyTypeEnvironment :: TypeEnvironment
emptyTypeEnvironment = TypeEnvironment Map.empty


-- | Extend context with a term binding
extendTermContext :: String -> RType -> TypingContext -> TypingContext
extendTermContext name ty ctx =
  let newIndex = 0
      shiftedTerms = Map.map (\(idx, t) -> (idx + 1, t)) (termBindings ctx)
   in ctx
        { termBindings = Map.insert name (newIndex, ty) shiftedTerms
        }

-- | Extend context with a relation binding
extendRelContext :: String -> TypingContext -> TypingContext
extendRelContext name ctx =
  let newIndex = 0
      shiftedRels = Map.map (+ 1) (relBindings ctx)
   in ctx {relBindings = Map.insert name newIndex shiftedRels}

-- | Extend context with a proof binding
extendProofContext :: String -> RelJudgment -> TypingContext -> TypingContext
extendProofContext name judgment ctx =
  let proofIdx = 0
      termDepthWhenStored = Map.size (termBindings ctx)
      shiftedProofs = Map.map (\(i, d, j) -> (i + 1, d, j)) (proofBindings ctx)
   in ctx
        { proofBindings = Map.insert name (proofIdx, termDepthWhenStored, judgment) shiftedProofs
        }

-- | Extend type environment with a type variable binding
extendTypeEnvironment :: String -> RType -> TypeEnvironment -> TypeEnvironment
extendTypeEnvironment name ty env =
  env {typeVarBindings = Map.insert name ty (typeVarBindings env)}


-- | Extend theorem environment with a theorem definition
extendTheoremEnvironment :: String -> [Binding] -> RelJudgment -> Proof -> TheoremEnvironment -> TheoremEnvironment
extendTheoremEnvironment name bindings judgment proof env =
  env {theoremDefinitions = Map.insert name (bindings, judgment, proof) (theoremDefinitions env)}

-- | Look up a term variable in the context
lookupTerm :: String -> TypingContext -> Either RelTTError (Int, RType)
lookupTerm name ctx =
  case Map.lookup name (termBindings ctx) of
    Just result -> Right result
    Nothing -> Left $ throwUnboundVar name (initialPos "<context>") "term lookup"

-- | Look up a relation variable in the context
lookupRel :: String -> TypingContext -> Either RelTTError Int
lookupRel name ctx =
  case Map.lookup name (relBindings ctx) of
    Just idx -> Right idx
    Nothing -> Left $ throwUnboundVar name (initialPos "<context>") "relation lookup"

-- | Look up a proof variable in the context
lookupProof :: String -> TypingContext -> Either RelTTError (Int, RelJudgment)
lookupProof name ctx =
  case Map.lookup name (proofBindings ctx) of
    Just (proofIdx, storedDepth, judgment) -> do
      let currentDepth = Map.size (termBindings ctx)
          termShift = currentDepth - storedDepth
          RelJudgment t1 rt t2 = judgment
          shiftedJudgment =
            RelJudgment
              (shiftTerm termShift t1)
              (shiftTermsInRType termShift rt)
              (shiftTerm termShift t2)
      Right (proofIdx, shiftedJudgment)
    Nothing -> Left $ throwUnboundVar name (initialPos "<context>") "proof lookup"

-- | Look up a type variable in the environment
lookupTypeVar :: String -> TypeEnvironment -> Either RelTTError RType
lookupTypeVar name env =
  case Map.lookup name (typeVarBindings env) of
    Just ty -> Right ty
    Nothing -> Left $ UnboundTypeVariable name (ErrorContext (initialPos "<context>") "type variable lookup")

-- | Look up a macro in the environment
lookupMacro :: String -> MacroEnvironment -> Either RelTTError ([String], MacroBody)
lookupMacro name env =
  case Map.lookup name (macroDefinitions env) of
    Just (sig, body) -> Right (map pName sig, body)
    Nothing -> Left $ throwMacroError name (initialPos "<context>") "macro lookup"

-- | Look up a theorem in the environment
lookupTheorem :: String -> TheoremEnvironment -> Either RelTTError ([Binding], RelJudgment, Proof)
lookupTheorem name env =
  case Map.lookup name (theoremDefinitions env) of
    Just def -> Right def
    Nothing -> Left $ throwUnboundVar name (initialPos "<context>") "theorem lookup"

-- | Shift all de Bruijn indices in a context by a given amount
shiftContext :: Int -> TypingContext -> TypingContext
shiftContext shift ctx =
  let shiftedTerms = Map.map (\(idx, ty) -> (idx + shift, ty)) (termBindings ctx)
      shiftedRels = Map.map (+ shift) (relBindings ctx)
      shiftedProofs = Map.map (\(idx, d, j) -> (idx + shift, d, j)) (proofBindings ctx)
   in TypingContext shiftedTerms shiftedRels shiftedProofs (gensymCounter ctx)

-- | Check if a variable name is fresh (not bound) in the context
isFreshInContext :: String -> TypingContext -> Bool
isFreshInContext name ctx =
  not (Map.member name (termBindings ctx))
    && not (Map.member name (relBindings ctx))
    && not (Map.member name (proofBindings ctx))

-- | Get the total number of bindings in a context
contextSize :: TypingContext -> Int
contextSize ctx =
  Map.size (termBindings ctx)
    + Map.size (relBindings ctx)
    + Map.size (proofBindings ctx)

-- | Validate that a context is well-formed
validateContext :: TypingContext -> Either RelTTError ()
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


-- | Get all bound variable names in a typing context
boundVarsInContext :: TypingContext -> Set.Set String
boundVarsInContext ctx =
  Set.unions [ Set.fromList (Map.keys (termBindings ctx))
             , Set.fromList (Map.keys (relBindings ctx))
             , Set.fromList (Map.keys (proofBindings ctx))
             ]

-- | Generate a fresh variable name and return updated context
freshVar :: String -> TypingContext -> (String, TypingContext)
freshVar prefix ctx =
  let counter = gensymCounter ctx
      newName = prefix ++ show counter
      newCtx = ctx {gensymCounter = counter + 1}
   in (newName, newCtx)

-- | Generate a pair of fresh variable names with the same counter and return updated context
freshVarPair :: String -> String -> TypingContext -> (String, String, TypingContext)
freshVarPair prefix1 prefix2 ctx =
  let counter = gensymCounter ctx
      name1 = prefix1 ++ show counter
      name2 = prefix2 ++ show counter
      newCtx = ctx {gensymCounter = counter + 1}
   in (name1, name2, newCtx)
