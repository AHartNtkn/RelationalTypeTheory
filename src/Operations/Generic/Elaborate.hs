{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Generic elaboration infrastructure for all AST types.
-- This module unifies elaboration of RawTerm/RawRType/RawProof into Term/RType/Proof.

module Operations.Generic.Elaborate
  ( -- * Core typeclass
    ElaborateAst(..)
    -- * Main elaboration function
  , elaborate
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as Map

import Core.Syntax
import Core.Raw
import Core.Errors
import Core.Context
import Operations.Generic.Mixfix (MixfixAst(..), reparseG)
import Operations.Generic.Token (toTok, hasOperatorG)
import Parser.Mixfix (mixfixKeywords)
import Operations.Generic.Macro (elabMacroAppG, MacroAst(..))
import Operations.Resolve (ResolveAst)

--------------------------------------------------------------------------------
-- | Core typeclass for AST elaboration
--------------------------------------------------------------------------------

class MixfixAst raw => ElaborateAst raw typed | raw -> typed where
  -- | Elaborate constructor-specific cases
  elaborateSpecial :: raw -> ElaborateM typed
  
  -- | Get the appropriate bound variables context (used by handleVar)
  getBoundVarsCtx :: Context -> Map.Map String Int
  
  -- | Create a bound variable node (used by handleVar)
  mkBoundVar :: String -> Int -> SourcePos -> typed
  
  -- | Create a free variable node (used by handleVar)
  mkFreeVar :: String -> SourcePos -> typed
  
  -- | Create a macro application node (used by handleMacroApp)
  mkMacroApp :: String -> [MacroArg] -> SourcePos -> typed
  
  -- | Check if a macro body has the right type (used by handleVar)
  isValidMacroKind :: MacroBody -> Bool
  
  -- | Extract the body from a macro if it's the right type (used by handleExplicitMacro)
  extractMacroBody :: MacroBody -> Maybe typed
  
  -- | Make an application node for over-application (used by handleMacroApp)
  makeApp :: typed -> typed -> SourcePos -> typed
  
  -- | Check if over-application is allowed (used by handleMacroApp)
  allowOverApp :: Bool
  
  -- | Extract variable name if this is a variable node (used by handleAppGeneric)
  extractVarName :: raw -> Maybe String

--------------------------------------------------------------------------------
-- | Main elaboration function
--------------------------------------------------------------------------------

elaborate :: ElaborateAst raw typed => raw -> ElaborateM typed
elaborate = elaborateSpecial

--------------------------------------------------------------------------------
-- | Term instance
--------------------------------------------------------------------------------

instance ElaborateAst RawTerm Term where
  getBoundVarsCtx ctx = Map.map fst (termBindings ctx)
  mkBoundVar = Var
  mkFreeVar = FVar
  mkMacroApp name args pos = TMacro name args pos
  
  isValidMacroKind (TermMacro _) = True
  isValidMacroKind _ = False
  
  extractMacroBody (TermMacro t) = Just t
  extractMacroBody _ = Nothing
  
  makeApp = App
  allowOverApp = True
  
  extractVarName (RTVar name _) = Just (nameString name)
  extractVarName _ = Nothing
  
  elaborateSpecial = \case
    RTVar name pos -> handleVar @RawTerm @Term name pos
    
    RTParens inner _pos -> elaborate inner  -- Simply elaborate the inner term, parentheses preserve structure during mixfix
    
    raw@(RTApp _ _ pos) -> 
      handleAppGeneric raw pos elaborateAppLeft termMacroHandler
      where
        elaborateAppLeft (RTApp rawFunc rawArg _) = do
          func <- elaborate rawFunc
          arg <- elaborate rawArg
          return $ App func arg pos
        elaborateAppLeft other = elaborate other
        
        termMacroHandler args macroName params macroPos = do
          ctx <- ask
          -- Check if it's a bound variable first
          case Map.lookup macroName (termBindings ctx) of
            Just _ -> elaborateAppLeft raw  -- Bound variable - use regular application
            Nothing -> do
              elaboratedArgs <- mapM elaborate args
              handleMacroApp @RawTerm @Term macroName params elaboratedArgs macroPos
    
    RTMacro nm args pos -> handleExplicitMacro nm args pos

--------------------------------------------------------------------------------
-- | RType instance
--------------------------------------------------------------------------------

instance ElaborateAst RawRType RType where
  getBoundVarsCtx = relBindings
  mkBoundVar = RVar
  mkFreeVar = FRVar
  mkMacroApp name args pos = RMacro name args pos
  
  isValidMacroKind (RelMacro _) = True
  isValidMacroKind (TermMacro _) = True  -- Terms can be promoted
  isValidMacroKind _ = False
  
  extractMacroBody (RelMacro r) = Just r
  extractMacroBody _ = Nothing
  
  makeApp _ _ _ = error "RType does not support application"
  allowOverApp = False
  
  extractVarName (RRVar name _) = Just (nameString name)
  extractVarName _ = Nothing
  
  elaborateSpecial = \case
    RRVar name pos -> handleVar @RawRType @RType name pos
    
    RRParens inner _pos -> elaborate inner  -- Simply elaborate the inner relation type, parentheses preserve structure during mixfix
    
    raw@(RRApp _ _ pos) ->
      handleAppGeneric raw pos relFallback relMacroHandler
      where
        relFallback _ = throwError $ InvalidMixfixPattern "bare application is illegal for Rel" 
                                   (ErrorContext pos "relational macro application")
        
        relMacroHandler args macroName params macroPos = do
          elaboratedArgs <- mapM elaborate args
          handleMacroApp @RawRType @RType macroName params elaboratedArgs macroPos
    
    RRMacro nm args pos -> handleExplicitMacro nm args pos

--------------------------------------------------------------------------------
-- | Proof instance
--------------------------------------------------------------------------------

instance ElaborateAst RawProof Proof where
  getBoundVarsCtx ctx = Map.map (\(i, _, _) -> i) (proofBindings ctx)
  mkBoundVar = PVar
  mkFreeVar = FPVar
  mkMacroApp name args pos = PMacro name args pos
  
  isValidMacroKind (ProofMacro _) = True
  isValidMacroKind _ = False
  
  extractMacroBody (ProofMacro p) = Just p
  extractMacroBody _ = Nothing
  
  makeApp = AppP
  allowOverApp = True
  
  extractVarName (RPVar name _) = Just (nameString name)
  extractVarName _ = Nothing
  
  elaborateSpecial = \case
    RPVar name pos -> handleVar @RawProof @Proof name pos
    
    RPParens inner _pos -> elaborate inner  -- Simply elaborate the inner proof, parentheses preserve structure during mixfix
    
    raw@(RPApp _ _ pos) ->
      handleAppGeneric raw pos proofFallback proofMacroHandler
      where
        proofFallback rawApp = case flattenApps rawApp of
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
          handleMacroAppCrossCategory macroName params args macroPos
    
    RPMixfix nm args pos -> handleExplicitMacro nm args pos

--------------------------------------------------------------------------------
-- | Generic helpers shared across all instances
--------------------------------------------------------------------------------

-- | Handle macro application with cross-category support
handleMacroAppCrossCategory :: String -> [ParamInfo] -> [RawProof] -> SourcePos -> ElaborateM Proof
handleMacroAppCrossCategory macroName params args macroPos = do
  -- Check arity
  when (length params /= length args) $
    throwError $ MacroArityMismatch macroName (length params) (length args)
                 (ErrorContext macroPos "macro application")
  
  -- Elaborate each argument according to its parameter kind
  macroArgs <- zipWithM elaborateByKind args params
  
  -- Create the macro application
  return $ PMacro macroName macroArgs macroPos
  where
    elaborateByKind :: RawProof -> ParamInfo -> ElaborateM MacroArg
    elaborateByKind (RPVar name pos) param = case pKind param of
      TermK -> do
        -- Convert to term variable and elaborate
        term <- elaborate (RTVar name pos) :: ElaborateM Term
        return $ MTerm term
      RelK -> do
        -- Convert to relation variable and elaborate
        rel <- elaborate (RRVar name pos) :: ElaborateM RType
        return $ MRel rel
      ProofK -> do
        -- Elaborate as proof
        proof <- elaborate (RPVar name pos) :: ElaborateM Proof
        return $ MProof proof
    elaborateByKind arg _ = do
      -- Non-variable: must be proof
      proof <- elaborate arg
      return $ MProof proof

-- | Handle variable lookup generically
handleVar :: forall raw typed. ElaborateAst raw typed => Name -> SourcePos -> ElaborateM typed
handleVar name pos = do
  ctx <- ask
  let varName = nameString name
      boundVarsMap = getBoundVarsCtx @raw @typed ctx
  
  case Map.lookup varName boundVarsMap of
    Just bindingDepth ->
      return $ mkBoundVar @raw @typed varName bindingDepth pos
    Nothing -> 
      -- Try looking up as a macro with zero arguments
      case Map.lookup varName (macroDefinitions (ctx)) of
        Just ([], macroBody) -> 
          if isValidMacroKind @raw @typed macroBody
            then return $ mkMacroApp @raw @typed varName [] pos
            else throwError $ UnboundVariable 
                   ("Wrong macro kind " ++ varName ++ " used in context") 
                   (ErrorContext pos "variable lookup")
        Just (params, _) -> 
          throwError $ MacroArityMismatch varName (length params) 0 
                       (ErrorContext pos "macro arity check")
        Nothing -> 
          -- Unknown variable - emit as free variable
          return $ mkFreeVar @raw @typed varName pos

-- | Generic application handler that factors out common structure
handleAppGeneric :: forall raw typed. (ElaborateAst raw typed, Eq raw, Show raw) 
                 => raw 
                 -> SourcePos 
                 -> (raw -> ElaborateM typed)  -- ^ fallback for non-macro applications
                 -> ([raw] -> String -> [ParamInfo] -> SourcePos -> ElaborateM typed)  -- ^ macro application handler
                 -> ElaborateM typed
handleAppGeneric raw pos fallback macroHandler = do
  ctx <- ask
  let flattened = flattenApps raw
      ops = mixfixKeywords (ctx)
      toks = map (toTok ops) flattened
  
  if hasOperatorG toks
    then reparseG elaborate pos flattened
    else case flattened of
      (firstRaw : args) -> do
        case extractVarName @raw @typed firstRaw of
          Just macroName -> do
            case Map.lookup macroName (macroDefinitions (ctx)) of
              Nothing -> fallback raw
              Just (params, _) -> macroHandler args macroName params pos
          Nothing -> fallback raw
      _ -> fallback raw

-- | Handle macro application with potential over-application
handleMacroApp :: forall raw typed. (ElaborateAst raw typed, MacroAst typed) => String -> [ParamInfo] -> [typed] -> SourcePos -> ElaborateM typed
handleMacroApp macroName params args macroPos = do
  let paramCount = length params
      argCount = length args
      overAppAllowed = allowOverApp @raw @typed
  
  -- Check arity constraints
  if overAppAllowed
    then when (argCount < paramCount) $
           throwError $ MacroArityMismatch macroName paramCount argCount 
                        (ErrorContext macroPos "macro application")
    else when (paramCount /= argCount) $
           throwError $ MacroArityMismatch macroName paramCount argCount
                        (ErrorContext macroPos "macro application")
  
  -- Convert typed arguments to MacroArg
  let macroArgsToConvert = take paramCount args
      macroArgs = map (toArg @typed) macroArgsToConvert
  
  -- Split arguments if over-application is allowed
  if overAppAllowed && argCount > paramCount
    then do
      let extraArgs = drop paramCount args
          macroApp = mkMacroApp @raw @typed macroName macroArgs macroPos
      foldM (\acc arg -> return $ makeApp @raw @typed acc arg macroPos) macroApp extraArgs
    else
      return $ mkMacroApp @raw @typed macroName macroArgs macroPos

-- | Handle explicit macro calls
handleExplicitMacro :: forall raw typed. (ElaborateAst raw typed, MacroAst typed, ResolveAst typed) => Name -> [raw] -> SourcePos -> ElaborateM typed
handleExplicitMacro nm args pos = do
  let name = nameString nm
  ctx <- ask
  case Map.lookup name (macroDefinitions (ctx)) of
    Nothing -> throwError $ UnknownMacro name (ErrorContext pos "macro lookup")
    Just (sig, macroBody) -> 
      case extractMacroBody @raw @typed macroBody of
        Just body -> do
          elaboratedArgs <- mapM elaborate args
          case elabMacroAppG ctx name sig body elaboratedArgs of
            Right result -> return result
            Left err -> throwError $ InvalidMixfixPattern 
                         ("Macro application failed for " ++ name ++ ": " ++ show err) 
                         (ErrorContext pos "macro application")
        Nothing -> throwError $ InvalidMixfixPattern 
                    ("Wrong macro kind " ++ name ++ " used in context") 
                    (ErrorContext pos "macro application")
