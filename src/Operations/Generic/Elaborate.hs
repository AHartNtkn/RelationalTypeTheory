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
import Data.Proxy
import Text.Megaparsec (SourcePos)

import Core.Syntax
import Core.Raw
import Core.Errors
import Parser.Context
import Operations.Generic.Mixfix (MixfixAst(..), reparseG)
import Operations.Generic.Token (toTok, hasOperatorG)
import Parser.Mixfix (mixfixKeywords)
import Operations.Generic.Macro (elabMacroAppG, MacroAst)
import Operations.Resolve (ResolveAst)

--------------------------------------------------------------------------------
-- | Core typeclass for AST elaboration
--------------------------------------------------------------------------------

class MixfixAst raw => ElaborateAst raw typed | raw -> typed where
  -- | Elaborate constructor-specific cases
  elaborateSpecial :: raw -> ElaborateM typed
  
  -- | Get the appropriate bound variables context (used by handleVar)
  getBoundVarsCtx :: ElaborateContext -> Map.Map String Int
  
  -- | Create a bound variable node (used by handleVar)
  mkBoundVar :: String -> Int -> SourcePos -> typed
  
  -- | Create a free variable node (used by handleVar)
  mkFreeVar :: String -> SourcePos -> typed
  
  -- | Create a macro application node (used by handleMacroApp)
  mkMacroApp :: String -> [typed] -> SourcePos -> typed
  
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
  getBoundVarsCtx = boundVars
  mkBoundVar = Var
  mkFreeVar = FVar
  mkMacroApp = TMacro
  
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
    
    RTLam name rawBody pos -> do
      ctx <- ask
      let varName = nameString name
          newCtx = ctx { boundVars = Map.insert varName 0 (Map.map (+1) (boundVars ctx))
                       , termDepth = termDepth ctx + 1 }
      body <- local (const newCtx) (elaborate rawBody)
      return $ Lam varName body pos
    
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
          case Map.lookup macroName (boundVars ctx) of
            Just _ -> elaborateAppLeft raw  -- Bound variable - use regular application
            Nothing -> do
              elaboratedArgs <- mapM elaborate args
              handleMacroApp @RawTerm @Term macroName params elaboratedArgs macroPos
    
    RTMacro nm args pos -> handleExplicitMacro nm args pos

--------------------------------------------------------------------------------
-- | RType instance
--------------------------------------------------------------------------------

instance ElaborateAst RawRType RType where
  getBoundVarsCtx = boundRelVars
  mkBoundVar = RVar
  mkFreeVar = FRVar
  mkMacroApp = RMacro
  
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
    
    RRArr rawLeft rawRight pos -> do
      left <- elaborate rawLeft
      right <- elaborate rawRight
      return $ Arr left right pos
    
    RRAll name rawBody pos -> do
      ctx <- ask
      let varName = nameString name
          newCtx = ctx { boundRelVars = Map.insert varName 0 (Map.map (+1) (boundRelVars ctx))
                       , relDepth = relDepth ctx + 1 }
      body <- local (const newCtx) (elaborate rawBody)
      return $ All varName body pos
    
    raw@(RRApp _ _ pos) ->
      handleAppGeneric raw pos relFallback relMacroHandler
      where
        relFallback _ = throwError $ InvalidMixfixPattern "bare application is illegal for Rel" 
                                   (ErrorContext pos "relational macro application")
        
        relMacroHandler args macroName params macroPos = do
          elaboratedArgs <- mapM elaborate args
          handleMacroApp @RawRType @RType macroName params elaboratedArgs macroPos
    
    raw@(RRComp _ _ pos) -> do
      ctx <- ask
      let ops = mixfixKeywords (macroEnv ctx)
          toks = map (toTok ops) (flattenApps raw)
      if hasOperatorG toks
        then reparseG elaborate pos (flattenApps raw)
        else case raw of
          RRComp rawLeft rawRight _ -> do
            left <- elaborate rawLeft
            right <- elaborate rawRight
            return $ Comp left right pos
          _ -> elaborate raw
    
    RRConv rawRType pos -> do
      rtype <- elaborate rawRType
      return $ Conv rtype pos
    
    RRMacro nm args pos -> handleExplicitMacro nm args pos
    
    RRProm rawTerm pos -> do
      term <- elaborate rawTerm
      return $ Prom term pos

--------------------------------------------------------------------------------
-- | Proof instance
--------------------------------------------------------------------------------

instance ElaborateAst RawProof Proof where
  getBoundVarsCtx ctx = Map.map fst (boundProofVars ctx)
  mkBoundVar = PVar
  mkFreeVar = FPVar
  mkMacroApp = PMacro
  
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
          elaboratedArgs <- mapM elaborate args
          handleMacroApp @RawProof @Proof macroName params elaboratedArgs macroPos
    
    RPTheorem name rawArgs pos -> do
      ctx <- ask
      let theoremName = nameString name
      case Map.lookup theoremName (theoremDefinitions (theoremEnv ctx)) of
        Nothing -> throwError $ UnknownTheorem theoremName (ErrorContext pos "theorem lookup")
        Just (bindings, _, _) -> do
          when (length bindings /= length rawArgs) $
            throwError $ TheoremArityMismatch theoremName (length bindings) (length rawArgs) 
                        (ErrorContext pos "theorem arity check")
          args <- mapM elaborateArg rawArgs
          return $ PTheoremApp theoremName args pos
    
    RPLamP name rawRType rawBody pos -> do
      ctx <- ask
      elaboratedRType <- elaborate rawRType
      let varName = nameString name
          judgment = RelJudgment (Var "dummy" 0 pos) elaboratedRType (Var "dummy" 0 pos)
          newCtx = ctx { boundProofVars = Map.insert varName (0, judgment) 
                                           (Map.map (\(i,j) -> (i+1,j)) (boundProofVars ctx))
                       , proofDepth = proofDepth ctx + 1 }
      body <- local (const newCtx) (elaborate rawBody)
      return $ LamP varName elaboratedRType body pos
    
    RPLamT name rawBody pos -> do
      ctx <- ask
      let varName = nameString name
          newCtx = ctx { boundRelVars = Map.insert varName 0 (Map.map (+1) (boundRelVars ctx))
                       , relDepth = relDepth ctx + 1 }
      body <- local (const newCtx) (elaborate rawBody)
      return $ TyLam varName body pos
    
    RPAppT rawProof rawRType pos -> do
      proof <- elaborate rawProof
      rtype <- elaborate rawRType
      return $ TyApp proof rtype pos
    
    RPConv rawTerm1 rawProof rawTerm2 pos -> do
      term1 <- elaborate rawTerm1
      proof <- elaborate rawProof
      term2 <- elaborate rawTerm2
      return $ ConvProof term1 proof term2 pos
    
    RPIota rawTerm1 rawTerm2 pos -> do
      term1 <- elaborate rawTerm1
      term2 <- elaborate rawTerm2
      return $ Iota term1 term2 pos
    
    RPRho x rawT1 rawT2 rawP1 rawP2 pos -> do
      ctx <- ask
      let xName = nameString x
          ctxWithX = ctx { boundVars = Map.insert xName 0 (Map.map (+1) (boundVars ctx))
                         , termDepth = termDepth ctx + 1 }
      t1 <- local (const ctxWithX) (elaborate rawT1)
      t2 <- local (const ctxWithX) (elaborate rawT2)
      p1 <- elaborate rawP1
      p2 <- elaborate rawP2
      return $ RhoElim xName t1 t2 p1 p2 pos
    
    RPPi rawProof x u v rawQ pos -> do
      p <- elaborate rawProof
      ctx <- ask
      let xName = nameString x
          uName = nameString u
          vName = nameString v
          dummyJudgment = RelJudgment (Var "dummy" 0 pos) (RVar "dummy" 0 pos) (Var "dummy" 0 pos)
          ctxWithX = ctx { boundVars = Map.insert xName 0 (Map.map (+1) (boundVars ctx))
                         , termDepth = termDepth ctx + 1 }
          ctxWithU = ctxWithX { boundProofVars = Map.insert uName (0, dummyJudgment)
                                                   (Map.map (\(i,j) -> (i+1,j)) (boundProofVars ctxWithX))
                              , proofDepth = proofDepth ctxWithX + 1 }
          ctxWithUV = ctxWithU { boundProofVars = Map.insert vName (1, dummyJudgment)
                                                    (boundProofVars ctxWithU)
                               , proofDepth = proofDepth ctxWithU + 1 }
      q <- local (const ctxWithUV) (elaborate rawQ)
      return $ Pi p xName uName vName q pos
    
    RPConvIntro rawProof pos -> do
      proof <- elaborate rawProof
      return $ ConvIntro proof pos
    
    RPConvElim rawProof pos -> do
      proof <- elaborate rawProof
      return $ ConvElim proof pos
    
    RPPair rawProof1 rawProof2 pos -> do
      proof1 <- elaborate rawProof1
      proof2 <- elaborate rawProof2
      return $ Pair proof1 proof2 pos
    
    RPMixfix nm args pos -> handleExplicitMacro nm args pos

--------------------------------------------------------------------------------
-- | Generic helpers shared across all instances
--------------------------------------------------------------------------------

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
      case Map.lookup varName (macroDefinitions (macroEnv ctx)) of
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
      ops = mixfixKeywords (macroEnv ctx)
      toks = map (toTok ops) flattened
  
  if hasOperatorG toks
    then reparseG elaborate pos flattened
    else case flattened of
      (firstRaw : args) -> do
        case extractVarName @raw @typed firstRaw of
          Just macroName -> do
            case Map.lookup macroName (macroDefinitions (macroEnv ctx)) of
              Nothing -> fallback raw
              Just (params, _) -> macroHandler args macroName params pos
          Nothing -> fallback raw
      _ -> fallback raw

-- | Handle macro application with potential over-application
handleMacroApp :: forall raw typed. ElaborateAst raw typed => String -> [ParamInfo] -> [typed] -> SourcePos -> ElaborateM typed
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
  
  -- Split arguments if over-application is allowed
  if overAppAllowed && argCount > paramCount
    then do
      let (macroArgs, extraArgs) = splitAt paramCount args
          macroApp = mkMacroApp @raw @typed macroName macroArgs macroPos
      foldM (\acc arg -> return $ makeApp @raw @typed acc arg macroPos) macroApp extraArgs
    else
      return $ mkMacroApp @raw @typed macroName args macroPos

-- | Handle explicit macro calls
handleExplicitMacro :: forall raw typed. (ElaborateAst raw typed, MacroAst typed, ResolveAst typed) => Name -> [raw] -> SourcePos -> ElaborateM typed
handleExplicitMacro nm args pos = do
  let name = nameString nm
  ctx <- ask
  case Map.lookup name (macroDefinitions (macroEnv ctx)) of
    Nothing -> throwError $ UnknownMacro name (ErrorContext pos "macro lookup")
    Just (sig, macroBody) -> 
      case extractMacroBody @raw @typed macroBody of
        Just body -> do
          elaboratedArgs <- mapM elaborate args
          case elabMacroAppG (macroEnv ctx) name sig body elaboratedArgs of
            Right result -> return result
            Left err -> throwError $ InvalidMixfixPattern 
                         ("Macro application failed for " ++ name ++ ": " ++ show err) 
                         (ErrorContext pos "macro application")
        Nothing -> throwError $ InvalidMixfixPattern 
                    ("Wrong macro kind " ++ name ++ " used in context") 
                    (ErrorContext pos "macro application")

-- | Helper to elaborate theorem arguments
elaborateArg :: RawArg -> ElaborateM TheoremArg
elaborateArg (RawTermArg rawTerm) = TermArg <$> elaborate rawTerm
elaborateArg (RawRelArg rawRType) = RelArg <$> elaborate rawRType  
elaborateArg (RawProofArg rawProof) = ProofArg <$> elaborate rawProof