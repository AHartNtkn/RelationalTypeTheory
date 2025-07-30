{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Unified elaboration infrastructure for all AST types.
-- This module provides a single elaborate function that can produce any target type
-- based on context and type inference.

module Operations.Generic.Elaborate
  ( -- * Core elaboration function
    elaborate
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as Map

import Core.Syntax (Term(..), RType(..), Proof(..), MacroArg(..), MacroBody(..), ParamInfo(..), VarKind(..))
import Core.Raw
import Core.Errors
import Core.Context
import Operations.Generic.Mixfix (MixfixAst(..), reparseG, mixfixKeywords)
import Operations.Generic.Token (toTok, hasOperatorG)

--------------------------------------------------------------------------------
-- | Main elaboration function - context-driven typing
--------------------------------------------------------------------------------

-- | Elaborate Raw into any target type based on context
class ElaborateTarget a where
  elaborate :: Raw -> ElaborateM a

--------------------------------------------------------------------------------
-- | Term elaboration
--------------------------------------------------------------------------------

instance ElaborateTarget Term where
  elaborate = \case
    RawVar name pos -> handleVar name pos
    
    RawParens inner _pos -> elaborate inner  -- Simply elaborate the inner term
    
    raw@(RawApp _ _ pos) -> 
      handleAppGeneric raw pos termAppFallback termMacroHandler
      where
        termAppFallback (RawApp rawFunc rawArg _) = do
          func <- elaborate rawFunc
          arg <- elaborate rawArg
          return $ App func arg pos
        termAppFallback other = elaborate other
        
        termMacroHandler args macroName params macroPos = do
          ctx <- ask
          -- Check if it's a bound term variable first
          case Map.lookup macroName (termBindings ctx) of
            Just _ -> do
              -- Bound variable - reconstruct as application and use fallback
              let rawApp = foldl (\acc arg -> RawApp acc arg macroPos) (RawVar (Name macroName) macroPos) args
              termAppFallback rawApp
            Nothing -> do
              macroArgs <- elaborateArgsForMacro args params
              return $ TMacro macroName macroArgs macroPos
    

--------------------------------------------------------------------------------
-- | RType elaboration  
--------------------------------------------------------------------------------

instance ElaborateTarget RType where
  elaborate = \case
    RawVar name pos -> handleVar name pos
    
    RawParens inner _pos -> elaborate inner  -- Simply elaborate the inner relation type
    
    raw@(RawApp _ _ pos) ->
      handleAppGeneric raw pos relAppFallback relMacroHandler
      where
        relAppFallback _ = throwError $ InvalidMixfixPattern "bare application is illegal for Rel" 
                                       (ErrorContext pos "relational macro application")
        
        relMacroHandler args macroName params macroPos = do
          macroArgs <- elaborateArgsForMacro args params
          return $ RMacro macroName macroArgs macroPos
    

--------------------------------------------------------------------------------
-- | Proof elaboration
--------------------------------------------------------------------------------

instance ElaborateTarget Proof where
  elaborate = \case
    RawVar name pos -> handleVar name pos
    
    RawParens inner _pos -> elaborate inner  -- Simply elaborate the inner proof
    
    raw@(RawApp _ _ pos) -> 
      handleAppGeneric raw pos proofAppFallback proofMacroHandler
      where
        proofAppFallback rawApp = case flattenApps rawApp of
          [rawFunc, rawArg] -> do
            -- Simple binary application
            func <- elaborate rawFunc
            arg <- elaborate rawArg
            return $ AppP func arg pos
          rawFunc : rawArgs -> do
            -- Multi-argument application - left-associate
            func <- elaborate rawFunc
            args <- mapM elaborate rawArgs
            return $ foldl (\acc arg -> AppP acc arg pos) func args
          [] -> throwError $ InvalidMixfixPattern "empty application list" 
                            (ErrorContext pos "proof application")
        
        proofMacroHandler args macroName params macroPos = do
          macroArgs <- elaborateArgsForMacro args params
          return $ PMacro macroName macroArgs macroPos
    

--------------------------------------------------------------------------------
-- | Generic helpers
--------------------------------------------------------------------------------

-- | Generic variable lookup that works for all target types
class VarHandler a where
  getBoundVars :: Context -> Map.Map String Int
  mkBoundVar :: String -> Int -> SourcePos -> a
  mkFreeVar :: String -> SourcePos -> a
  mkMacroApp :: String -> [MacroArg] -> SourcePos -> a
  isValidMacroKind :: MacroBody -> Bool

instance VarHandler Term where
  getBoundVars ctx = Map.map fst (termBindings ctx)
  mkBoundVar = Var
  mkFreeVar = FVar
  mkMacroApp = TMacro
  isValidMacroKind (TermMacro _) = True
  isValidMacroKind _ = False

instance VarHandler RType where
  getBoundVars = relBindings
  mkBoundVar = RVar
  mkFreeVar = FRVar
  mkMacroApp = RMacro
  isValidMacroKind (RelMacro _) = True
  isValidMacroKind (TermMacro _) = True  -- Terms can be promoted
  isValidMacroKind _ = False

instance VarHandler Proof where
  getBoundVars ctx = Map.map (\(i, _, _) -> i) (proofBindings ctx)
  mkBoundVar = PVar
  mkFreeVar = FPVar
  mkMacroApp = PMacro
  isValidMacroKind (ProofMacro _) = True
  isValidMacroKind _ = False

-- | Single generic variable handler
handleVar :: forall a. VarHandler a => Name -> SourcePos -> ElaborateM a
handleVar name pos = do
  ctx <- ask
  let varName = nameString name
      boundVarsMap = getBoundVars @a ctx
  
  case Map.lookup varName boundVarsMap of
    Just bindingDepth ->
      return $ mkBoundVar @a varName bindingDepth pos
    Nothing -> 
      -- Try looking up as a macro with zero arguments
      case Map.lookup varName (macroDefinitions ctx) of
        Just ([], macroBody) -> 
          if isValidMacroKind @a macroBody
            then return $ mkMacroApp @a varName [] pos
            else throwError $ UnboundVariable 
                   ("Wrong macro kind " ++ varName ++ " used in context") 
                   (ErrorContext pos "variable lookup")
        Just (params, _) -> 
          throwError $ MacroArityMismatch varName (length params) 0 
                       (ErrorContext pos "macro arity check")
        Nothing -> 
          -- Unknown variable - emit as free variable
          return $ mkFreeVar @a varName pos

-- | Generic application handler
handleAppGeneric :: forall a. ElaborateTarget a => Raw -> SourcePos -> (Raw -> ElaborateM a) -> ([Raw] -> String -> [ParamInfo] -> SourcePos -> ElaborateM a) -> ElaborateM a
handleAppGeneric raw pos fallback macroHandler = do
  ctx <- ask
  let flattened = flattenApps raw
      ops = mixfixKeywords ctx
      toks = map (toTok ops) flattened
  
  if hasOperatorG toks
    then reparseG elaborate pos flattened
    else case flattened of
      (firstRaw : args) -> do
        case extractVarName firstRaw of
          Just macroName -> do
            case Map.lookup macroName (macroDefinitions ctx) of
              Nothing -> fallback raw
              Just (params, _) -> macroHandler args macroName params pos
          Nothing -> fallback raw
      _ -> fallback raw

-- | Extract variable name from Raw
extractVarName :: Raw -> Maybe String
extractVarName (RawVar name _) = Just (nameString name)
extractVarName _ = Nothing

-- | Elaborate arguments for macro based on parameter kinds
elaborateArgsForMacro :: [Raw] -> [ParamInfo] -> ElaborateM [MacroArg]
elaborateArgsForMacro args params = do
  -- Phase 1: Extract binder variable names for dependency analysis
  let binderArgs = 
        [ if pBinds param 
          then case arg of
            RawVar name _ -> case pKind param of
              TermK -> MTerm (FVar (nameString name) dummyPos)
              RelK -> MRel (FRVar (nameString name) dummyPos)
              ProofK -> MProof (FPVar (nameString name) dummyPos)
            _ -> MProof (FPVar "placeholder" dummyPos)  -- Non-variable binder
          else MProof (FPVar "placeholder" dummyPos)  -- Placeholder for non-binders
        | (arg, param) <- zip args params
        ]
  
  -- Build dependency-aware contexts
  ctx <- ask
  let (argContexts, _) = buildDependentContexts params binderArgs ctx
  
  -- Phase 2: Elaborate each argument with its specific dependency context
  sequence 
    [ local (const (argContexts !! i)) (elaborateByKind arg param)
    | (i, (arg, param)) <- zip [0..] (zip args params)
    ]
  where
    elaborateByKind :: Raw -> ParamInfo -> ElaborateM MacroArg
    elaborateByKind arg param = case extractVarName arg of
      Just varName -> case pKind param of
        TermK -> do
          term <- elaborate (RawVar (Name varName) dummyPos) :: ElaborateM Term
          return $ MTerm term
        RelK -> do
          rel <- elaborate (RawVar (Name varName) dummyPos) :: ElaborateM RType
          return $ MRel rel
        ProofK -> do
          proof <- elaborate (RawVar (Name varName) dummyPos) :: ElaborateM Proof
          return $ MProof proof
      Nothing -> case pKind param of
        TermK -> do
          term <- elaborate arg :: ElaborateM Term
          return $ MTerm term
        RelK -> do
          rel <- elaborate arg :: ElaborateM RType
          return $ MRel rel
        ProofK -> do
          proof <- elaborate arg :: ElaborateM Proof
          return $ MProof proof



