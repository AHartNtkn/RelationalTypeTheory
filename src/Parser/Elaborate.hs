{-# LANGUAGE OverloadedStrings, FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
module Parser.Elaborate
  ( elaborate
  , elaborateDeclaration
  , elaborateJudgment
  , emptyCtxWithBuiltins
  , elaborateDeclarations
  -- Re-export generic elaborate functions for tests
  , elaborateTerm
  , elaborateRType
  , elaborateProof
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as Map

import Core.Syntax
import Core.Raw
import qualified Operations.Generic.Elaborate as Generic
import Core.Errors (RelTTError(..))
import Parser.Context (ElaborateM, ElaborateContext(..), bindTermVar, bindRelVar, bindProofVar)
import Operations.Builtins (macroEnvWithBuiltins)


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
  elaboratedProof <- local (const newCtx) (Generic.elaborate proof)
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

elaborateMacroBody :: RawMacroBody -> ElaborateM MacroBody
elaborateMacroBody (RawTermBody rawTerm) = do
  elaboratedTerm <- Generic.elaborate rawTerm
  return $ TermMacro elaboratedTerm
elaborateMacroBody (RawRelBody rawRType) = do
  elaboratedRType <- Generic.elaborate rawRType
  return $ RelMacro elaboratedRType
elaborateMacroBody (RawProofBody rawProof) = do
  elaboratedProof <- Generic.elaborate rawProof
  return $ ProofMacro elaboratedProof

elaborateJudgment :: RawJudgment -> ElaborateM RelJudgment
elaborateJudgment (RawJudgment rawTerm1 rawRType rawTerm2) = do
  term1 <- Generic.elaborate rawTerm1
  rtype <- Generic.elaborate rawRType
  term2 <- Generic.elaborate rawTerm2
  return $ RelJudgment term1 rtype term2

-- | Re-export generic elaborate functions for tests
elaborateTerm :: RawTerm -> ElaborateM Term
elaborateTerm = Generic.elaborate

elaborateRType :: RawRType -> ElaborateM RType
elaborateRType = Generic.elaborate

elaborateProof :: RawProof -> ElaborateM Proof
elaborateProof = Generic.elaborate


