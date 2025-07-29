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
  
  extractMacro (TMacro name args _) = Just (name, [t | MTerm t <- args])
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
  
  extractMacro (RMacro name args _) = Just (name, [r | MRel r <- args])
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
  
  extractMacro (PMacro name args _) = Just (name, [p | MProof p <- args])
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
    LamP x _ b _        -> S.delete x (recurse env b)
    AppP f a _          -> recurse env f `S.union` recurse env a
    TyApp p _ _          -> recurse env p
    TyLam x b _         -> S.delete x (recurse env b)
    ConvProof _ p _ _    -> recurse env p
    ConvIntro p _       -> recurse env p
    ConvElim p _        -> recurse env p
    Iota _ _ _           -> S.empty  -- No free variables in iota
    RhoElim x _ _ p1 p2 _ -> S.delete x (recurse env p1) `S.union` recurse env p2
    Pair p1 p2 _        -> recurse env p1 `S.union` recurse env p2
    Pi p1 x u v p2 _    -> recurse env p1 `S.union` S.delete x (S.delete u (S.delete v (recurse env p2)))
    PMacro _ _ _         -> error "PMacro should be handled by extractMacro"

-- | MacroArg free variables instance
instance FreeVarsAst MacroArg where
  extractVarName = \case
    MTerm t -> extractVarName t
    MRel r -> extractVarName r
    MProof p -> extractVarName p
    
  extractMacro _ = Nothing  -- MacroArgs are not macros themselves
  
  freeVarsCore _recurse env = \case
    MTerm t -> freeVars env t
    MRel r -> freeVars env r  
    MProof p -> freeVars env p

