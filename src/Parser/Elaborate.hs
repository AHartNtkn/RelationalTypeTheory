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
import Core.Context (ElaborateM, emptyContext)

-- Main elaboration function
elaborate :: Context -> RawDeclaration
          -> Either RelTTError           Declaration
elaborate ctx rawDecl =
  runExcept (runReaderT (elaborateDeclaration rawDecl) ctx)

elaborateDeclaration :: RawDeclaration -> ElaborateM Declaration
elaborateDeclaration (RawMacroDef name params body) = do
  ctx <- ask
  let pNames = map nameString params
  -- Don't bind parameters - macro bodies should keep parameter references as free variables
  elaboratedBody <- elaborateMacroBody body
  pure $ MacroDef (nameString name) pNames elaboratedBody
  
elaborateDeclaration (RawTheorem name bindings judgment proof) = do
  -- Elaborate bindings but don't extend context - theorem bodies should keep parameter references as free variables
  elaboratedBindings <- mapM elaborateBinding bindings
  -- Elaborate judgment and proof in original context (parameters become free vars)
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

