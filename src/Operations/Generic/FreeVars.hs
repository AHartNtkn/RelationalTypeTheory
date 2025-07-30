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
import Operations.Generic.Expansion (ExpandAst(..))

--------------------------------------------------------------------------------
-- | Typeclass for AST nodes that support free variable analysis
--------------------------------------------------------------------------------

class (ExpandAst a) => FreeVarsAst a where
  -- | Extract variable name if this node is a variable, Nothing otherwise
  extractVarName :: a -> Maybe String
  -- | Core free variable analysis (without macro handling)
  freeVarsCore :: (Context -> a -> S.Set String) -> Context -> a -> S.Set String

--------------------------------------------------------------------------------
-- | Generic binder-aware free variable analysis
--------------------------------------------------------------------------------

freeVars :: FreeVarsAst a => Context -> a -> S.Set String
freeVars ctx node = 
  case getMacroApp node of
    Nothing -> freeVarsCore freeVars ctx node
    Just (macroName, args, _pos) ->
      case M.lookup macroName (macroDefinitions ctx) of
        Nothing -> S.unions (map (freeVars ctx) args)  -- conservative fallback
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
                    in S.difference (freeVars ctx arg) allowed
                    
          in S.unions [fvArg i paramInfo arg | (i, paramInfo, arg) <- zip3 ([0..] :: [Int]) sig args]

--------------------------------------------------------------------------------
-- | Instances for the three AST categories  
--------------------------------------------------------------------------------

instance FreeVarsAst Term where
  extractVarName (Var x _ _) = Just x
  extractVarName (FVar x _) = Just x    -- Free variables also have names
  extractVarName _ = Nothing
  
  freeVarsCore recurse ctx = \case
    Var x _ _   -> S.singleton x
    FVar x _    -> S.singleton x          -- Free variables contribute to free variable set
    Lam x b _   -> S.delete x (recurse ctx b)
    App f a _   -> recurse ctx f `S.union` recurse ctx a
    TMacro _ _ _ -> error "TMacro should be handled by getMacroApp"

instance FreeVarsAst RType where
  extractVarName (RVar x _ _) = Just x
  extractVarName (FRVar x _) = Just x   -- Free variables also have names
  extractVarName _ = Nothing
  
  freeVarsCore recurse ctx = \case
    RVar x _ _  -> S.singleton x
    FRVar x _   -> S.singleton x          -- Free variables contribute to free variable set
    Arr a b _   -> recurse ctx a `S.union` recurse ctx b
    All x t _   -> S.delete x (recurse ctx t)
    Comp a b _  -> recurse ctx a `S.union` recurse ctx b
    Conv r _    -> recurse ctx r
    Prom t _    -> freeVars ctx t  -- delegate to term analysis
    RMacro _ _ _ -> error "RMacro should be handled by getMacroApp"

instance FreeVarsAst Proof where
  extractVarName (PVar x _ _) = Just x
  extractVarName (FPVar x _) = Just x   -- Free variables also have names
  extractVarName _ = Nothing
  
  freeVarsCore recurse ctx = \case
    PVar x _ _          -> S.singleton x
    FPVar x _           -> S.singleton x  -- Free variables contribute to free variable set
    PTheoremApp _ args _ -> S.unions (map goArg args)
      where
        goArg = \case
          TermArg t  -> freeVars ctx t
          RelArg rt  -> freeVars ctx rt
          ProofArg p -> recurse ctx p
    LamP x _ b _        -> S.delete x (recurse ctx b)
    AppP f a _          -> recurse ctx f `S.union` recurse ctx a
    TyApp p _ _          -> recurse ctx p
    TyLam x b _         -> S.delete x (recurse ctx b)
    ConvProof _ p _ _    -> recurse ctx p
    ConvIntro p _       -> recurse ctx p
    ConvElim p _        -> recurse ctx p
    Iota _ _ _           -> S.empty  -- No free variables in iota
    RhoElim x _ _ p1 p2 _ -> S.delete x (recurse ctx p1) `S.union` recurse ctx p2
    Pair p1 p2 _        -> recurse ctx p1 `S.union` recurse ctx p2
    Pi p1 x u v p2 _    -> recurse ctx p1 `S.union` S.delete x (S.delete u (S.delete v (recurse ctx p2)))
    PMacro _ _ _         -> error "PMacro should be handled by getMacroApp"

-- | MacroArg free variables instance
instance FreeVarsAst MacroArg where
  extractVarName = \case
    MTerm t -> extractVarName t
    MRel r -> extractVarName r
    MProof p -> extractVarName p
  
  freeVarsCore _recurse ctx = \case
    MTerm t -> freeVars ctx t
    MRel r -> freeVars ctx r  
    MProof p -> freeVars ctx p

