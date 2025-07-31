{-# LANGUAGE LambdaCase #-}

-- | Generic resolution of free variables to de Bruijn indices
-- This module provides a generic resolution system that converts free variables
-- in macro bodies to proper de Bruijn indices based on the binder context.

module Operations.Resolve
  ( ResolveAst(..)
  , resolve
  ) where

import qualified Data.Map as Map
import Control.Monad (zipWithM)
import Data.List (foldl')
import Core.Syntax
import Core.Context
import Core.Raw (dummyPos)
import Core.Errors

-- | Resolve macro arguments using dependency-aware contexts
resolveMacroArgs :: Context -> String -> [MacroArg] -> Either RelTTError [MacroArg]
resolveMacroArgs ctx macroName args = do
  case Map.lookup macroName (macroDefinitions ctx) of
    Nothing -> Left $ UnboundMacro macroName (ErrorContext dummyPos "macro resolution")
    Just (sig, _) -> do
      -- Build contexts for each argument based on dependencies
      let buildArgContext i param =
            foldl' addBinder ctx [j | j <- pDeps param, j < length args]
            where
              addBinder c j 
                | not (pBinds (sig !! j)) = c  -- Only binders contribute to context
                | otherwise = case (pKind (sig !! j), args !! j) of
                    (TermK, MTerm (Var n _ _)) -> bindTermVar n c
                    (TermK, MTerm (FVar n _)) -> bindTermVar n c  
                    (RelK, MRel (RVar n _ _)) -> bindRelVar n c
                    (RelK, MRel (FRVar n _)) -> bindRelVar n c
                    (ProofK, MProof (PVar n _ _)) -> bindProofVar n dummyJudgment c
                    (ProofK, MProof (FPVar n _)) -> bindProofVar n dummyJudgment c
                    _ -> c  -- Mismatched kinds or complex args, skip
              dummyJudgment = RelJudgment (Var "⊥" 0 dummyPos) (RVar "⊥" 0 dummyPos) (Var "⊥" 0 dummyPos)
      
      argContexts <- mapM (\(i, param) -> return $ buildArgContext i param) (zip [0..] sig)
      -- DEBUG: Show what contexts we're building
      zipWithM resolveWithContext argContexts args

-- | Generic typeclass for resolving free variables to de Bruijn indices
class ResolveAst a where
  -- | Resolve free variables in the AST using the current context
  resolveWithContext :: Context -> a -> Either RelTTError a

-- | Main entry point: resolve all free variables in an AST
resolve :: ResolveAst a => a -> Either RelTTError a
resolve = resolveWithContext emptyContext

--------------------------------------------------------------------------------
-- | Instance for Term
--------------------------------------------------------------------------------

instance ResolveAst Term where
  resolveWithContext ctx = \case
    Var n i p   -> Right $ Var n i p                      -- Already resolved
    FVar n p    -> case Map.lookup n (termBindings ctx) of  -- Free variable to resolve
      Just (i, _)  -> Right $ Var n i p                   -- Bound variable -> de Bruijn index
      Nothing -> case lookupParameter n ctx of            -- Check parameter context
        Just TermK -> Right $ FVar n p                    -- Parameter -> keep as free variable
        _ -> Left $ UnboundVariable n (ErrorContext p "term variable resolution")
    Lam n b p   -> do
      let ctx' = bindTermVar n ctx
      resolvedBody <- resolveWithContext ctx' b
      Right $ Lam n resolvedBody p
    App f x p   -> do
      resolvedF <- resolveWithContext ctx f
      resolvedX <- resolveWithContext ctx x
      Right $ App resolvedF resolvedX p
    TMacro n as p -> Right $ TMacro n as p

--------------------------------------------------------------------------------
-- | Instance for RType
--------------------------------------------------------------------------------

instance ResolveAst RType where
  resolveWithContext ctx = \case
    RVar n i p   -> Right $ RVar n i p                     -- Already resolved
    FRVar n p    -> case Map.lookup n (relBindings ctx) of   -- Free relational variable to resolve
      Just i  -> Right $ RVar n i p                        -- Bound variable -> de Bruijn index
      Nothing -> case lookupParameter n ctx of             -- Check parameter context
        Just RelK -> Right $ FRVar n p                     -- Parameter -> keep as free variable
        _ -> Left $ UnboundTypeVariable n (ErrorContext p "relational variable resolution")
    RMacro n as p -> Right $ RMacro n as p
    Arr a b p    -> do
      resolvedA <- resolveWithContext ctx a
      resolvedB <- resolveWithContext ctx b
      Right $ Arr resolvedA resolvedB p
    All n r p    -> do
      let ctx' = bindRelVar n ctx
      resolvedR <- resolveWithContext ctx' r
      Right $ All n resolvedR p
    Conv r p     -> do
      resolvedR <- resolveWithContext ctx r
      Right $ Conv resolvedR p
    Comp a b p   -> do
      resolvedA <- resolveWithContext ctx a
      resolvedB <- resolveWithContext ctx b
      Right $ Comp resolvedA resolvedB p
    Prom t p     -> do
      resolvedT <- resolve t             -- Terms use their own resolution
      Right $ Prom resolvedT p

--------------------------------------------------------------------------------
-- | Instance for Proof
--------------------------------------------------------------------------------

instance ResolveAst Proof where
  resolveWithContext ctx = \case
    PVar n i p -> Right $ PVar n i p                      -- Already resolved
    FPVar n p  -> case Map.lookup n (proofBindings ctx) of   -- Free proof variable to resolve
      Just (i, _, _)  -> Right $ PVar n i p               -- Bound variable -> de Bruijn index
      Nothing -> case lookupParameter n ctx of            -- Check parameter context
        Just ProofK -> Right $ FPVar n p                  -- Parameter -> keep as free variable
        _ -> Left $ UnboundVariable n (ErrorContext p "proof variable resolution")
    PTheoremApp n args p -> do
      resolvedArgs <- mapM resolveArg args
      Right $ PTheoremApp n resolvedArgs p
      where
        resolveArg = \case
          TermArg t  -> TermArg <$> resolve t
          RelArg rt  -> RelArg <$> resolve rt
          ProofArg pr -> ProofArg <$> resolveWithContext ctx pr
    LamP n rt pr p -> do
      let dummyJudgment = RelJudgment (Var "dummy" 0 (dummyPos)) (RVar "dummy" 0 (dummyPos)) (Var "dummy" 0 (dummyPos))
          ctx' = bindProofVar n dummyJudgment ctx
      resolvedRt <- resolveWithContext ctx rt
      resolvedPr <- resolveWithContext ctx' pr
      Right $ LamP n resolvedRt resolvedPr p
    AppP p1 p2 p -> do
      resolvedP1 <- resolveWithContext ctx p1
      resolvedP2 <- resolveWithContext ctx p2
      Right $ AppP resolvedP1 resolvedP2 p
    TyApp pr rt p -> do
      resolvedPr <- resolveWithContext ctx pr
      resolvedRt <- resolveWithContext ctx rt
      Right $ TyApp resolvedPr resolvedRt p
    TyLam n pr p -> do
      let ctx' = bindRelVar n ctx
      resolvedPr <- resolveWithContext ctx' pr
      Right $ TyLam n resolvedPr p
    ConvProof t1 pr t2 p -> do
      resolvedT1 <- resolve t1
      resolvedPr <- resolveWithContext ctx pr
      resolvedT2 <- resolve t2
      Right $ ConvProof resolvedT1 resolvedPr resolvedT2 p
    ConvIntro pr p -> do
      resolvedPr <- resolveWithContext ctx pr
      Right $ ConvIntro resolvedPr p
    ConvElim pr p -> do
      resolvedPr <- resolveWithContext ctx pr
      Right $ ConvElim resolvedPr p
    Iota t1 t2 p -> do
      resolvedT1 <- resolve t1
      resolvedT2 <- resolve t2
      Right $ Iota resolvedT1 resolvedT2 p
    RhoElim n t1 t2 p1 p2 p -> do
      let dummyJudgment = RelJudgment (Var "dummy" 0 (dummyPos)) (RVar "dummy" 0 (dummyPos)) (Var "dummy" 0 (dummyPos))
          ctx' = bindTermVar n (bindProofVar n dummyJudgment ctx)
      resolvedT1 <- resolve t1
      resolvedT2 <- resolve t2
      resolvedP1 <- resolveWithContext ctx p1
      resolvedP2 <- resolveWithContext ctx' p2
      Right $ RhoElim n resolvedT1 resolvedT2 resolvedP1 resolvedP2 p
    Pair p1 p2 p -> do
      resolvedP1 <- resolveWithContext ctx p1
      resolvedP2 <- resolveWithContext ctx p2
      Right $ Pair resolvedP1 resolvedP2 p
    Pi p1 x u v p2 p -> do
      let dummyJudgment = RelJudgment (Var "dummy" 0 (dummyPos)) (RVar "dummy" 0 (dummyPos)) (Var "dummy" 0 (dummyPos))
          ctx' = bindTermVar x (bindProofVar u dummyJudgment (bindProofVar v dummyJudgment ctx))
      resolvedP1 <- resolveWithContext ctx p1
      resolvedP2 <- resolveWithContext ctx' p2
      Right $ Pi resolvedP1 x u v resolvedP2 p
    PMacro n as p -> Right $ PMacro n as p

-- | MacroArg resolution instance
instance ResolveAst MacroArg where
  resolveWithContext ctx = \case
    MTerm t -> MTerm <$> resolveWithContext ctx t
    MRel r -> MRel <$> resolveWithContext ctx r
    MProof p -> MProof <$> resolveWithContext ctx p