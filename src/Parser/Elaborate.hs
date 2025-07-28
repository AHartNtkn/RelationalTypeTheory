{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module Parser.Elaborate
  ( elaborate
  , elaborateDeclaration
  , elaborateTerm
  , elaborateRType
  , elaborateProof
  , elaborateJudgment
  , emptyCtxWithBuiltins
  , isPostfixOperator
  , elaborateDeclarations
  , Tok(..)
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as Map
import Text.Megaparsec (SourcePos)

import Core.Syntax
import Core.Raw
import Parser.Mixfix (splitMixfix, mixfixKeywords)
import Operations.Generic.Macro (elabMacroAppG)
import Operations.Generic.Token (toTok, hasOperatorG, Tok(..))
import Operations.Generic.Mixfix (MixfixAst(..), reparseG)
import Core.Errors (RelTTError(..), ErrorContext(..))
import Parser.Context
import Operations.Builtins (macroEnvWithBuiltins)

shiftIntMap = Map.map (+1)

shiftProofMap :: Map.Map String (Int,RelJudgment)
              -> Map.Map String (Int,RelJudgment)
shiftProofMap = Map.map (\(i,j) -> (i+1,j))

bindTermVar :: String -> ElaborateContext -> ElaborateContext
bindTermVar x ctx =
  ctx { boundVars = Map.insert x 0 (shiftIntMap (boundVars ctx))
      , termDepth = termDepth ctx + 1 }

bindRelVar :: String -> ElaborateContext -> ElaborateContext
bindRelVar r ctx =
  ctx { boundRelVars = Map.insert r 0 (shiftIntMap (boundRelVars ctx))
      , relDepth  = relDepth  ctx + 1 }

bindProofVar :: String -> RelJudgment -> ElaborateContext -> ElaborateContext
bindProofVar p j ctx =
  ctx { boundProofVars = Map.insert p (0,j) (shiftProofMap (boundProofVars ctx))
      , proofDepth = proofDepth ctx + 1 }

-- | Helper function to look up a macro definition
lookupMacro :: String -> MacroEnvironment -> SourcePos -> String -> Either RelTTError MacroSig
lookupMacro name env pos context =
  case Map.lookup name (macroDefinitions env) of
    Nothing -> Left $ UnknownMacro name (ErrorContext pos context)
    Just sig -> Right sig

emptyCtxWithBuiltins :: ElaborateContext  
emptyCtxWithBuiltins = ElaborateContext
  { macroEnv = macroEnvWithBuiltins
  , theoremEnv = TheoremEnvironment Map.empty
  , termDepth = 0
  , relDepth = 0
  , proofDepth = 0
  , boundVars = Map.empty
  , boundRelVars = Map.empty
  , boundProofVars = Map.empty
  }

-- Check if an operator is postfix in the macro environment
isPostfixOperator :: String -> MacroEnvironment -> Bool
isPostfixOperator op env = 
  case Map.lookup op (macroFixities env) of
    Just (Postfix _) -> True
    _ -> False 

-- Main elaboration function
elaborate :: ElaborateContext -> RawDeclaration
          -> Either RelTTError           Declaration
elaborate ctx rawDecl =
  runExcept (runReaderT (elaborateDeclaration rawDecl) ctx)

elaborateDeclaration :: RawDeclaration -> ElaborateM Declaration
elaborateDeclaration (RawMacro name params body) = do
  ctx <- ask
  let pNames = map nameString params

      -- Using the centralized binder functions

      ctxTerm  = foldl (flip bindTermVar) ctx pNames   -- last parameter = index 0
      ctxRel   = foldl (flip bindRelVar ) ctx pNames
      ctxProof = ctx  -- proof macros can reference any variables
  -------------------------------------------------------------------------
  elaboratedBody <- case body of
    RawTermBody _ -> local (const ctxTerm) (elaborateMacroBody body)
    RawRelBody  _ -> local (const ctxRel ) (elaborateMacroBody body)
    RawProofBody _ -> local (const ctxProof) (elaborateMacroBody body)

  pure $ MacroDef (nameString name) pNames elaboratedBody
  
elaborateDeclaration (RawTheorem name bindings judgment proof) = do
  -- Elaborate bindings and extend context
  (elaboratedBindings, newCtx) <- elaborateBindings bindings
  -- Elaborate judgment and proof in extended context
  elaboratedJudgment <- local (const newCtx) (elaborateJudgment judgment)
  elaboratedProof <- local (const newCtx) (elaborateProof proof)
  return $ TheoremDef (nameString name) elaboratedBindings elaboratedJudgment elaboratedProof

elaborateDeclaration (RawFixityDecl fixity name) = do
  ctx <- ask
  let env0 = macroEnv ctx
      env1 = env0 { macroFixities = Map.insert (nameString name) fixity
                                         (macroFixities env0) }
  local (\c -> c { macroEnv = env1 })
        (pure (FixityDecl fixity (nameString name)))

elaborateDeclaration (RawImportDecl (RawImportModule path)) = do
  pure (ImportDecl (ImportModule path))

-- | Elaborate a list of raw declarations
elaborateDeclarations :: ElaborateContext -> [RawDeclaration] -> Either RelTTError [Declaration]
elaborateDeclarations ctx rawDecls = runExcept (runReaderT (mapM elaborateDeclaration rawDecls) ctx)

elaborateMacroBody :: RawMacroBody -> ElaborateM MacroBody
elaborateMacroBody (RawTermBody rawTerm) = do
  elaboratedTerm <- elaborateTerm rawTerm
  return $ TermMacro elaboratedTerm
elaborateMacroBody (RawRelBody rawRType) = do
  elaboratedRType <- elaborateRType rawRType
  return $ RelMacro elaboratedRType
elaborateMacroBody (RawProofBody rawProof) = do
  elaboratedProof <- elaborateProof rawProof
  return $ ProofMacro elaboratedProof

elaborateBindings :: [RawBinding] -> ElaborateM ([Binding], ElaborateContext)
elaborateBindings bindings = do
  ctx <- ask
  foldM elaborateBinding ([], ctx) bindings
  where
    elaborateBinding (acc, ctx) (RawTermBinding name) = do
      let binding = TermBinding (nameString name)
      let newCtx = bindTermVar (nameString name) ctx
      return (acc ++ [binding], newCtx)
    
    elaborateBinding (acc, ctx) (RawRelBinding name) = do
      let binding = RelBinding (nameString name)
      -- Theorem parameters should NOT increment relDepth - they're just added to lookup context
      let newCtx = ctx { boundRelVars = Map.insert (nameString name) (relDepth ctx) (boundRelVars ctx) }
      return (acc ++ [binding], newCtx)
    
    elaborateBinding (acc, ctx) (RawProofBinding name rawJudgment) = do
      elaboratedJudgment <- local (const ctx) (elaborateJudgment rawJudgment)
      let binding = ProofBinding (nameString name) elaboratedJudgment
      let newCtx = bindProofVar (nameString name) elaboratedJudgment ctx
      return (acc ++ [binding], newCtx)

elaborateJudgment :: RawJudgment -> ElaborateM RelJudgment
elaborateJudgment (RawJudgment rawTerm1 rawRType rawTerm2) = do
  term1 <- elaborateTerm rawTerm1
  rtype <- elaborateRType rawRType
  term2 <- elaborateTerm rawTerm2
  return $ RelJudgment term1 rtype term2

----------------------------------------------------------------------
--  Core elaboration functions
----------------------------------------------------------------------

elaborateTerm :: RawTerm -> ElaborateM Term
elaborateTerm (RTVar name pos) = do
  ctx <- ask
  case Map.lookup (nameString name) (boundVars ctx) of
    Just bindingDepth ->
      return $ Var (nameString name) bindingDepth pos
    Nothing -> 
      -- Try looking up as a macro with zero arguments
      case Map.lookup (nameString name) (macroDefinitions (macroEnv ctx)) of
        Just ([], macroBody) -> 
          -- Macro with zero arguments - create TMacro node
          case macroBody of
            TermMacro _ -> return $ TMacro (nameString name) [] pos
            RelMacro _ -> throwError $ UnboundVariable ("Relational macro " ++ nameString name ++ " used in term context") (ErrorContext pos "variable lookup")
            ProofMacro _ -> throwError $ UnboundVariable ("Proof macro " ++ nameString name ++ " used in term context") (ErrorContext pos "variable lookup")
        Just (params, _) -> 
          -- Macro exists but requires arguments
          throwError $ MacroArityMismatch (nameString name) (length params) 0 (ErrorContext pos "macro arity check")
        Nothing -> throwError $ UnboundVariable ("Unknown term variable: " ++ nameString name) (ErrorContext pos "variable lookup")

elaborateTerm (RTLam name rawBody pos) = do
  ctx <- ask
  let varName = nameString name
  let newCtx = bindTermVar varName ctx
  body <- local (const newCtx) (elaborateTerm rawBody)
  return $ Lam varName body pos

elaborateTerm raw@(RTApp _ _ pos) = do
  ctx <- ask
  let flattened = flattenApps raw
      ops = mixfixKeywords (macroEnv ctx)
      toks = map (toTok ops) flattened
  -- Check if this contains mixfix operators
  if hasOperatorG toks
    then -- Contains mixfix operators - use mixfix parsing
      reparseG elaborateTerm pos flattened
    else -- No mixfix operators - check for simple macro application
      case flattened of
        (RTVar name _ : args) -> do
          let macroName = nameString name
          case Map.lookup macroName (boundVars ctx) of
            Just _ -> elaborateAppLeft raw  -- Bound variable - regular function application
            Nothing -> 
              case Map.lookup macroName (macroDefinitions (macroEnv ctx)) of
                Nothing -> elaborateAppLeft raw  -- Not a macro - regular function application
                Just (params, _) -> smartAppT macroName params args pos  -- Macro application
        _ -> elaborateAppLeft raw  -- Not a simple application - regular function application
  where
    elaborateAppLeft (RTApp rawFunc rawArg _) = do
      func <- elaborateTerm rawFunc
      arg <- elaborateTerm rawArg
      return $ App func arg pos
    elaborateAppLeft other = elaborateTerm other
    
    smartAppT macroName params args macroPos = do
      let paramCount = length params
          argCount = length args
      -- Terms allow over-application but not under-application
      when (argCount < paramCount) $
        throwError $ MacroArityMismatch macroName paramCount argCount 
                     (ErrorContext macroPos "macro application")
      
      -- Split arguments into macro args and extra args
      let (macroRawArgs, extraRawArgs) = splitAt paramCount args
      
      -- Elaborate macro arguments
      elaboratedMacroArgs <- mapM elaborateTerm macroRawArgs
      let macroApp = TMacro macroName elaboratedMacroArgs macroPos
      
      -- Apply any extra arguments via function application
      foldM (\acc rawArg -> do
        elaboratedArg <- elaborateTerm rawArg
        return $ App acc elaboratedArg macroPos) macroApp extraRawArgs

elaborateTerm (RTMacro nm args pos) = do
  let name = nameString nm
  ctx <- ask
  case lookupMacro name (macroEnv ctx) pos "macro lookup" of
    Left err -> throwError err
    Right (sig, TermMacro body) -> do
      elaboratedArgs <- mapM elaborateTerm args
      case elabMacroAppG (macroEnv ctx) name sig body elaboratedArgs of
        Right result -> return result
        Left err -> throwError $ InvalidMixfixPattern ("Term macro application failed for " ++ name ++ ": " ++ show err) (ErrorContext pos "term macro application")
    Right (_, RelMacro _) -> throwError $ InvalidMixfixPattern ("Relational macro " ++ name ++ " used in term context") (ErrorContext pos "term macro application")
    Right (_, ProofMacro _) -> throwError $ InvalidMixfixPattern ("Proof macro " ++ name ++ " used in term context") (ErrorContext pos "term macro application")

elaborateRType :: RawRType -> ElaborateM RType
elaborateRType (RRVar name pos) = do
  ctx <- ask
  case Map.lookup (nameString name) (boundRelVars ctx) of
    Just bindingDepth -> 
      return $ RVar (nameString name) bindingDepth pos
    Nothing -> 
      -- Try looking up as a term variable (which can be promoted to relation)
      case Map.lookup (nameString name) (boundVars ctx) of
        Just bindingDepth ->
          return $ Prom (Var (nameString name) bindingDepth pos) pos
        Nothing -> 
          -- Try looking up as a macro with zero arguments
          case Map.lookup (nameString name) (macroDefinitions (macroEnv ctx)) of
            Just ([], macroBody) -> 
              -- Macro with zero arguments - create RMacro node or promote TMacro
              case macroBody of
                TermMacro _ -> return $ Prom (TMacro (nameString name) [] pos) pos
                RelMacro _ -> return $ RMacro (nameString name) [] pos
                ProofMacro _ -> throwError $ UnboundVariable ("Proof macro " ++ nameString name ++ " used in relational type context") (ErrorContext pos "variable lookup")
            Just (params, _) -> 
              -- Macro exists but requires arguments
              throwError $ MacroArityMismatch (nameString name) (length params) 0 (ErrorContext pos "macro arity check")
            Nothing -> throwError $ UnboundVariable ("Unknown relational variable: " ++ nameString name) (ErrorContext pos "variable lookup")

elaborateRType (RRArr rawLeft rawRight pos) = do
  left <- elaborateRType rawLeft
  right <- elaborateRType rawRight
  return $ Arr left right pos

elaborateRType (RRAll name rawBody pos) = do
  ctx <- ask
  let varName = nameString name
  let newCtx = bindRelVar varName ctx
  body <- local (const newCtx) (elaborateRType rawBody)
  return $ All varName body pos

-- | Juxtaposition in relational types is *only* allowed to form a
--   (prefix or infix) macro application.  Anything left over after
--   re‑parsing is therefore an error.
elaborateRType raw@(RRApp _ _ pos) = do
  ctx  <- ask
  let flattened = flattenApps raw
      ops = mixfixKeywords (macroEnv ctx)
      toks = map (toTok ops) flattened
  -- Check if this contains mixfix operators
  if hasOperatorG toks
    then -- Contains mixfix operators - use mixfix parsing
      reparseG elaborateRType pos flattened
    else -- No mixfix operators - check for simple macro application
      case flattened of
        (RRVar name _ : args) -> do
          let macroName = nameString name
          case Map.lookup macroName (macroDefinitions (macroEnv ctx)) of
            Nothing -> throwError $ InvalidMixfixPattern "bare application is illegal for Rel" (ErrorContext pos "relational macro application")
            Just (params, _) -> smartAppR macroName params args pos
        _ -> throwError $ InvalidMixfixPattern "bare application is illegal for Rel" (ErrorContext pos "relational macro application")
  where
    smartAppR macroName params args macroPos = do
      let paramCount = length params
          argCount = length args
      -- Relations require exact arity match
      when (paramCount /= argCount) $
        throwError $ MacroArityMismatch macroName paramCount argCount
                     (ErrorContext macroPos "relational macro application")
      
      -- Elaborate all arguments and create macro application
      elaboratedArgs <- mapM elaborateRType args
      return $ RMacro macroName elaboratedArgs macroPos

elaborateRType raw@(RRComp _ _ pos) = do
  ctx <- ask
  let ops = mixfixKeywords (macroEnv ctx)
      toks = map (toTok ops) (flattenApps raw)
  case hasOperatorG toks of
    False -> elaborateCompLeft raw
    True  -> reparseG elaborateRType pos (flattenApps raw)
  where
    elaborateCompLeft (RRComp rawLeft rawRight _) = do
      left <- elaborateRType rawLeft
      right <- elaborateRType rawRight
      return $ Comp left right pos
    elaborateCompLeft other = elaborateRType other

elaborateRType (RRConv rawRType pos) = do
  rtype <- elaborateRType rawRType
  return $ Conv rtype pos

elaborateRType (RRMacro nm args pos) = do
  let name = nameString nm
  ctx <- ask
  case lookupMacro name (macroEnv ctx) pos "macro lookup" of
    Left err -> throwError err
    Right (sig, RelMacro body) -> do
      elaboratedArgs <- mapM elaborateRType args
      case elabMacroAppG (macroEnv ctx) name sig body elaboratedArgs of
        Right result -> return result
        Left err -> throwError $ InvalidMixfixPattern ("Relational macro application failed for " ++ name ++ ": " ++ show err) (ErrorContext pos "relational macro application")
    Right (_, TermMacro _) -> throwError $ InvalidMixfixPattern ("Term macro " ++ name ++ " used in relational context") (ErrorContext pos "relational macro application")
    Right (_, ProofMacro _) -> throwError $ InvalidMixfixPattern ("Proof macro " ++ name ++ " used in relational context") (ErrorContext pos "relational macro application")

elaborateRType (RRProm rawTerm pos) = do
  term <- elaborateTerm rawTerm
  return $ Prom term pos

elaborateProof :: RawProof -> ElaborateM Proof
elaborateProof (RPVar name pos) = do
  ctx <- ask
  case Map.lookup (nameString name) (boundProofVars ctx) of
    Just (bindingDepth, _) ->
      return $ PVar (nameString name) bindingDepth pos
    Nothing -> throwError $ UnboundVariable ("Unknown proof variable: " ++ nameString name) (ErrorContext pos "variable lookup")

elaborateProof raw@(RPApp _ _ pos) = do
  ctx  <- ask
  let flattened = flattenApps raw
      ops = mixfixKeywords (macroEnv ctx)
      toks = map (toTok ops) flattened
  -- Check if this contains mixfix operators
  if hasOperatorG toks
    then -- Contains mixfix operators - use mixfix parsing
      reparseG elaborateProof pos flattened
    else -- No mixfix operators - check for simple macro application or regular application
      case flattened of
        [rawFunc, rawArg] -> do
          -- Simple binary application - handle directly
          func <- elaborateProof rawFunc
          arg <- elaborateProof rawArg
          return $ AppP func arg pos
        (RPVar name _ : args) -> do
          let macroName = nameString name
          case Map.lookup macroName (macroDefinitions (macroEnv ctx)) of
            Nothing -> throwError $ InvalidMixfixPattern "bare application is illegal for Proof" (ErrorContext pos "proof macro application")
            Just (params, _) -> smartAppP macroName params args pos
        _ -> throwError $ InvalidMixfixPattern "bare application is illegal for Proof" (ErrorContext pos "proof macro application")
  where
    smartAppP macroName params args macroPos = do
      let paramCount = length params
          argCount = length args
      -- Proofs allow over-application but not under-application
      when (argCount < paramCount) $
        throwError $ MacroArityMismatch macroName paramCount argCount 
                     (ErrorContext macroPos "macro application")
      
      -- Split arguments into macro args and extra args
      let (macroRawArgs, extraRawArgs) = splitAt paramCount args
      
      -- Elaborate macro arguments
      elaboratedMacroArgs <- mapM elaborateProof macroRawArgs
      let macroApp = PMacro macroName elaboratedMacroArgs macroPos
      
      -- Apply any extra arguments via function application
      foldM (\acc rawArg -> do
        elaboratedArg <- elaborateProof rawArg
        return $ AppP acc elaboratedArg macroPos) macroApp extraRawArgs

elaborateProof (RPTheorem name rawArgs pos) = do
  ctx <- ask
  let theoremName = nameString name
  case Map.lookup theoremName (theoremDefinitions (theoremEnv ctx)) of
    Nothing -> throwError $ UnknownTheorem theoremName (ErrorContext pos "theorem lookup")
    Just (bindings, _, _) -> do
      when (length bindings /= length rawArgs) $
        throwError $ TheoremArityMismatch theoremName (length bindings) (length rawArgs) (ErrorContext pos "variable lookup")
      args <- mapM elaborateArg rawArgs
      return $ PTheoremApp theoremName args pos

elaborateProof (RPLamP name rawRType rawBody pos) = do
  ctx <- ask
  elaboratedRType <- elaborateRType rawRType
  let varName = nameString name
  -- Create a dummy judgment for the proof variable
  let judgment = RelJudgment (Var "dummy" 0 pos) elaboratedRType (Var "dummy" 0 pos)
  let newCtx = bindProofVar varName judgment ctx
  body <- local (const newCtx) (elaborateProof rawBody)
  return $ LamP varName elaboratedRType body pos

elaborateProof (RPLamT name rawBody pos) = do
  ctx <- ask
  let varName = nameString name
  let newCtx = bindRelVar varName ctx
  body <- local (const newCtx) (elaborateProof rawBody)
  return $ TyLam varName body pos

elaborateProof (RPAppT rawProof rawRType pos) = do
  proof <- elaborateProof rawProof
  rtype <- elaborateRType rawRType
  return $ TyApp proof rtype pos

elaborateProof (RPConv rawTerm1 rawProof rawTerm2 pos) = do
  term1 <- elaborateTerm rawTerm1
  proof <- elaborateProof rawProof
  term2 <- elaborateTerm rawTerm2
  return $ ConvProof term1 proof term2 pos

elaborateProof (RPIota rawTerm1 rawTerm2 pos) = do
  term1 <- elaborateTerm rawTerm1
  term2 <- elaborateTerm rawTerm2
  return $ Iota term1 term2 pos

elaborateProof (RPRho x rawT1 rawT2 rawP1 rawP2 pos) = do
  ctx <- ask
  let ctxWithX = bindTermVar (nameString x) ctx
  t1 <- local (const ctxWithX) (elaborateTerm rawT1)
  t2 <- local (const ctxWithX) (elaborateTerm rawT2)
  p1 <- elaborateProof rawP1     --  x NOT in scope here
  p2 <- elaborateProof rawP2
  return $ RhoElim (nameString x) t1 t2 p1 p2 pos

elaborateProof (RPPi rawProof x u v rawQ pos) = do
  p <- elaborateProof rawProof
  ctx <- ask
  -- Bind x as a term variable
  let xName = nameString x
      uName = nameString u
      vName = nameString v
      dummyJudgment = RelJudgment (Var "dummy" 0 pos) (RVar "dummy" 0 pos) (Var "dummy" 0 pos)
      ctxWithX  = bindTermVar  xName ctx
      ctxWithU  = bindProofVar uName dummyJudgment ctxWithX
      ctxWithUV = bindProofVar vName dummyJudgment ctxWithU
  -- Elaborate q in the extended context
  q <- local (const ctxWithUV) (elaborateProof rawQ)
  return $ Pi p xName uName vName q pos

elaborateProof (RPConvIntro rawProof pos) = do
  proof <- elaborateProof rawProof
  return $ ConvIntro proof pos

elaborateProof (RPConvElim rawProof pos) = do
  proof <- elaborateProof rawProof
  return $ ConvElim proof pos

elaborateProof (RPPair rawProof1 rawProof2 pos) = do
  proof1 <- elaborateProof rawProof1
  proof2 <- elaborateProof rawProof2
  return $ Pair proof1 proof2 pos

elaborateProof (RPMixfix nm args pos) = do
  let name = nameString nm
  ctx <- ask
  case lookupMacro name (macroEnv ctx) pos "macro lookup" of
    Left err -> throwError err
    Right (sig, ProofMacro body) -> do
      elaboratedArgs <- mapM elaborateProof args
      case elabMacroAppG (macroEnv ctx) name sig body elaboratedArgs of
        Right result -> return result
        Left err -> throwError $ InvalidMixfixPattern ("Proof macro application failed for " ++ name ++ ": " ++ show err) (ErrorContext pos "proof macro application")
    Right (_, TermMacro _) -> throwError $ InvalidMixfixPattern ("Term macro " ++ name ++ " used in proof context") (ErrorContext pos "proof macro application")
    Right (_, RelMacro _) -> throwError $ InvalidMixfixPattern ("Relational macro " ++ name ++ " used in proof context") (ErrorContext pos "proof macro application")

elaborateArg :: RawArg -> ElaborateM TheoremArg
elaborateArg (RawTermArg rawTerm) = do
  term <- elaborateTerm rawTerm
  return $ TermArg term
elaborateArg (RawRelArg rawRType) = do
  rtype <- elaborateRType rawRType
  return $ RelArg rtype
elaborateArg (RawProofArg rawProof) = do
  proof <- elaborateProof rawProof
  return $ ProofArg proof