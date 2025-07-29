{-# LANGUAGE LambdaCase #-}

-- | Generic free variable analysis infrastructure
-- This consolidates the duplicated binder-aware logic across Term, RType, and Proof
module Operations.Generic.FreeVars
  ( -- | Generic free variable analysis
    FreeVarsAst(..)
  , freeVars
  ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Core.Syntax

--------------------------------------------------------------------------------
-- | Typeclass for AST nodes that support free variable analysis
--------------------------------------------------------------------------------

class FreeVarsAst a where
  -- | Extract variable name if this node is a variable, Nothing otherwise
  extractVarName :: a -> Maybe String
  -- | Core free variable analysis (without macro handling)
  freeVarsCore :: (MacroEnvironment -> a -> S.Set String) -> MacroEnvironment -> a -> S.Set String
  -- | Extract macro name and arguments if this is a macro application
  extractMacro :: a -> Maybe (String, [a])

--------------------------------------------------------------------------------
-- | Generic binder-aware free variable analysis
--------------------------------------------------------------------------------

freeVars :: FreeVarsAst a => MacroEnvironment -> a -> S.Set String
freeVars env node = 
  case extractMacro node of
    Nothing -> freeVarsCore freeVars env node
    Just (macroName, args) ->
      case M.lookup macroName (macroDefinitions env) of
        Nothing -> S.unions (map (freeVars env) args)  -- conservative fallback
        Just (sig, _) ->
          let -- Extract binder names from arguments
              binders :: M.Map Int String
              binders = M.fromList
                [ (i, varName)
                | (i, ParamInfo{pBinds=True}, arg) <- zip3 [0..] sig args
                , Just varName <- [extractVarName arg]
                ]
              
              -- Analyze each argument considering binder dependencies
              fvArg i paramInfo arg
                | pBinds paramInfo = S.empty  -- binder parameters don't contribute free vars
                | otherwise =
                    let allowed = S.fromList
                          [ binderName 
                          | depIndex <- pDeps paramInfo
                          , Just binderName <- [M.lookup depIndex binders]
                          ]
                    in S.difference (freeVars env arg) allowed
                    
          in S.unions [fvArg i paramInfo arg | (i, paramInfo, arg) <- zip3 ([0..] :: [Int]) sig args]

--------------------------------------------------------------------------------
-- | Instances for the three AST categories  
--------------------------------------------------------------------------------

instance FreeVarsAst Term where
  extractVarName (Var x _ _) = Just x
  extractVarName (FVar x _) = Just x    -- Free variables also have names
  extractVarName _ = Nothing
  
  extractMacro (TMacro name args _) = Just (name, args)
  extractMacro _ = Nothing
  
  freeVarsCore recurse env = \case
    Var x _ _   -> S.singleton x
    FVar x _    -> S.singleton x          -- Free variables contribute to free variable set
    Lam x b _   -> S.delete x (recurse env b)
    App f a _   -> recurse env f `S.union` recurse env a
    TMacro _ _ _ -> error "TMacro should be handled by extractMacro"

instance FreeVarsAst RType where
  extractVarName (RVar x _ _) = Just x
  extractVarName (FRVar x _) = Just x   -- Free variables also have names
  extractVarName _ = Nothing
  
  extractMacro (RMacro name args _) = Just (name, args)
  extractMacro _ = Nothing
  
  freeVarsCore recurse env = \case
    RVar x _ _  -> S.singleton x
    FRVar x _   -> S.singleton x          -- Free variables contribute to free variable set
    Arr a b _   -> recurse env a `S.union` recurse env b
    All x t _   -> S.delete x (recurse env t)
    Comp a b _  -> recurse env a `S.union` recurse env b
    Conv r _    -> recurse env r
    Prom t _    -> freeVars env t  -- delegate to term analysis
    RMacro _ _ _ -> error "RMacro should be handled by extractMacro"

instance FreeVarsAst Proof where
  extractVarName (PVar x _ _) = Just x
  extractVarName (FPVar x _) = Just x   -- Free variables also have names
  extractVarName _ = Nothing
  
  extractMacro (PMacro name args _) = Just (name, args)
  extractMacro _ = Nothing
  
  freeVarsCore recurse env = \case
    PVar x _ _          -> S.singleton x
    FPVar x _           -> S.singleton x  -- Free variables contribute to free variable set
    PTheoremApp _ args _ -> S.unions (map goArg args)
      where
        goArg = \case
          TermArg t  -> freeVars env t
          RelArg rt  -> freeVars env rt
          ProofArg p -> recurse env p
    LamP x rt p _       -> S.delete x (freeVars env rt `S.union` recurse env p)
    AppP p1 p2 _        -> recurse env p1 `S.union` recurse env p2
    TyApp p rt _        -> recurse env p `S.union` freeVars env rt
    TyLam x p _         -> S.delete x (recurse env p)
    ConvProof t1 p t2 _ -> freeVars env t1 `S.union` recurse env p `S.union` freeVars env t2
    ConvIntro p _       -> recurse env p
    ConvElim p _        -> recurse env p
    Iota t1 t2 _        -> freeVars env t1 `S.union` freeVars env t2
    RhoElim x t1 t2 p1 p2 _ -> S.delete x (freeVars env t1 `S.union` freeVars env t2) `S.union` recurse env p1 `S.union` recurse env p2
    Pi p1 x u v p2 _    -> recurse env p1 `S.union` S.delete x (S.delete u (S.delete v (recurse env p2)))
    Pair p1 p2 _        -> recurse env p1 `S.union` recurse env p2
    PMacro _ _ _         -> error "PMacro should be handled by extractMacro"

