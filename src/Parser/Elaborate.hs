{-# LANGUAGE OverloadedStrings, FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
module Parser.Elaborate
  ( elaborate
  , elaborateDeclaration
  , elaborateJudgment
  , emptyContext
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
import Core.Context (ElaborateM, emptyContext, extendParameterContext, inferParamKind)

-- Helper function to extract VarKind from RawBinding
rawBindingToVarKind :: RawBinding -> VarKind
rawBindingToVarKind (RawTermBinding _) = TermK
rawBindingToVarKind (RawRelBinding _) = RelK
rawBindingToVarKind (RawProofBinding _ _) = ProofK

-- Helper function to extract name from RawBinding
rawBindingName :: RawBinding -> String
rawBindingName (RawTermBinding name) = nameString name
rawBindingName (RawRelBinding name) = nameString name
rawBindingName (RawProofBinding name _) = nameString name

-- Main elaboration function
elaborate :: Context -> RawDeclaration
          -> Either RelTTError           Declaration
elaborate ctx rawDecl =
  runExcept (runReaderT (elaborateDeclaration rawDecl) ctx)

elaborateDeclaration :: RawDeclaration -> ElaborateM Declaration
elaborateDeclaration (RawMacroDef name params body) = do
  ctx <- ask
  let pNames = map nameString params
  -- For macro parameters, assume they have RelK kind (most common case)
  -- This is a simplification - a more sophisticated system would infer this
  let paramKind = RelK -- Default assumption for macro parameters
      paramCtx = foldr (\pName ctxAcc -> extendParameterContext pName paramKind ctxAcc) ctx pNames
  -- Elaborate the body with parameters in parameter context
  local (const paramCtx) $ do
    elaboratedBody <- elaborateMacroBody body
    pure $ MacroDef (nameString name) pNames elaboratedBody
  
elaborateDeclaration (RawTheorem name bindings judgment proof) = do
  -- Add parameters to parameter context for macro expansion
  ctx <- ask
  let paramCtx = foldr (\binding ctx -> extendParameterContext (rawBindingName binding) (rawBindingToVarKind binding) ctx) ctx bindings
  local (const paramCtx) $ do
    -- Elaborate bindings (parameters remain as free variables in output)
    elaboratedBindings <- mapM elaborateBinding bindings
    -- Elaborate judgment and proof with parameters in parameter context
    elaboratedJudgment <- elaborateJudgment judgment
    elaboratedProof <- Generic.elaborate proof
    return $ TheoremDef (nameString name) elaboratedBindings elaboratedJudgment elaboratedProof
  where
    elaborateBinding (RawTermBinding name) = return $ TermBinding (nameString name)
    elaborateBinding (RawRelBinding name) = return $ RelBinding (nameString name)
    elaborateBinding (RawProofBinding name rawJudgment) = do
      elaboratedJudgment <- elaborateJudgment rawJudgment
      return $ ProofBinding (nameString name) elaboratedJudgment

elaborateDeclaration (RawFixityDecl fixity name) = do
  ctx <- ask
  local (\c -> c { macroFixities = Map.insert (nameString name) fixity
                                        (macroFixities c) })
        (pure (FixityDecl fixity (nameString name)))

elaborateDeclaration (RawImportDecl (RawImportModule path)) = do
  pure (ImportDecl (ImportModule path))

-- | Elaborate a list of raw declarations
elaborateDeclarations :: Context -> [RawDeclaration] -> Either RelTTError [Declaration]
elaborateDeclarations ctx rawDecls = runExcept (runReaderT (mapM elaborateDeclaration rawDecls) ctx)


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
elaborateTerm :: Raw -> ElaborateM Term
elaborateTerm = Generic.elaborate

elaborateRType :: Raw -> ElaborateM RType
elaborateRType = Generic.elaborate

elaborateProof :: Raw -> ElaborateM Proof
elaborateProof = Generic.elaborate

