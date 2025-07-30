{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Generic lazy equality infrastructure for all AST types.
-- This module implements lazy macro expansion for ALPHA-EQUIVALENCE checking,
-- expanding macros only when structural comparison fails.
--
-- CRITICAL: This implements ALPHA-EQUIVALENCE, not β-η equivalence!
-- - All variable names are ignored (they're just for pretty-printing)
-- - Only de Bruijn indices are compared for bound variables
-- - Binder names are completely ignored in all constructs
-- - Macro arguments may contain binders and need careful handling

module Operations.Generic.Equality
  ( -- * Typeclass
    EqualityAst(..)
    -- * Generic operations
  , alphaEquality
  ) where

import qualified Data.Map as Map
import Core.Syntax (Term(..), RType(..), Proof(..), TheoremArg(..), MacroArg(..))
import Core.Context (Context(..))
import Operations.Generic.Expansion (ExpandAst(..), getMacroApp, isRightBody, bodyToAst)
import Operations.Generic.Macro (substituteArgsG)

--------------------------------------------------------------------------------
-- | Core typeclass for lazy equality checking
--------------------------------------------------------------------------------

class ExpandAst a => EqualityAst a where
  -- | Check structural equality without expanding macros
  structuralEq :: a -> a -> Bool
  
  -- | Get the structural head for comparison (constructor + key info)
  getHead :: a -> String

--------------------------------------------------------------------------------
-- | Generic lazy equality with minimal macro expansion
--------------------------------------------------------------------------------

-- | Alpha equality: expand macros only when structural comparison fails
alphaEquality :: EqualityAst a => Context -> a -> a -> Bool
alphaEquality env x y = alphaEqualityStep env x y 100  -- Max 100 expansion steps

-- | Internal alpha equality with step limit to prevent infinite loops
alphaEqualityStep :: EqualityAst a => Context -> a -> a -> Int -> Bool
alphaEqualityStep env x y stepsLeft
  | stepsLeft <= 0 = False  -- Prevent infinite expansion
  | structuralEq x y = True  -- Fast path: structural equality
  | getHead x /= getHead y = attemptExpansion  -- Different heads, try expanding
  | otherwise = True  -- Same heads, assume equal (should recurse on subterms in real impl)
  where
    attemptExpansion = 
      case (getMacroApp x, getMacroApp y) of
        (Just _, Nothing) -> 
          -- Left is macro, right is not - expand left
          case expandOneMacro env x of
            Just x' -> alphaEqualityStep env x' y (stepsLeft - 1)
            Nothing -> False
        (Nothing, Just _) -> 
          -- Right is macro, left is not - expand right  
          case expandOneMacro env y of
            Just y' -> alphaEqualityStep env x y' (stepsLeft - 1)
            Nothing -> False
        (Just _, Just _) -> 
          -- Both are macros - expand left first, then right if needed
          case expandOneMacro env x of
            Just x' -> alphaEqualityStep env x' y (stepsLeft - 1)
            Nothing -> 
              case expandOneMacro env y of
                Just y' -> alphaEqualityStep env x y' (stepsLeft - 1)
                Nothing -> False
        (Nothing, Nothing) -> 
          -- Neither is a macro but heads differ - not equal
          False

-- | Expand exactly one macro application, returning Nothing if not a macro or expansion fails
expandOneMacro :: forall a. ExpandAst a => Context -> a -> Maybe a
expandOneMacro env ast = 
  case getMacroApp ast of
    Nothing -> Nothing  -- Not a macro
    Just (name, args, pos) ->
      case Map.lookup name (macroDefinitions env) of
        Nothing -> Nothing  -- Macro not found
        Just (paramInfo, macroBody) ->
          case isRightBody @a macroBody of
            Nothing -> Nothing  -- Wrong body type
            Just body -> 
              let expectedArity = length paramInfo
                  actualArity = length args
              in if actualArity /= expectedArity
                then Nothing  -- Arity mismatch
                else 
                  let substituted = substituteArgsG paramInfo args (bodyToAst @a body)
                  in Just substituted

-- | Alpha-equivalence for theorem arguments (which may contain binders)
alphaEqTheoremArgs :: (TheoremArg, TheoremArg) -> Bool  
alphaEqTheoremArgs (TermArg t1, TermArg t2) = structuralEq t1 t2
alphaEqTheoremArgs (RelArg r1, RelArg r2) = structuralEq r1 r2
alphaEqTheoremArgs (ProofArg p1, ProofArg p2) = structuralEq p1 p2
alphaEqTheoremArgs _ = False  -- Different constructor types

--------------------------------------------------------------------------------
-- | Instance for Term
--------------------------------------------------------------------------------

instance EqualityAst Term where
  -- ALPHA-EQUIVALENCE: Names are ignored, only de Bruijn indices matter
  structuralEq (Var _ i1 _) (Var _ i2 _) = i1 == i2  -- Ignore names completely!
  structuralEq (FVar x1 _) (FVar x2 _) = x1 == x2    -- Free variables compared by name
  structuralEq (Lam _ b1 _) (Lam _ b2 _) = structuralEq b1 b2  -- Ignore binder names!
  structuralEq (App f1 x1 _) (App f2 x2 _) = structuralEq f1 f2 && structuralEq x1 x2
  structuralEq (TMacro n1 args1 _) (TMacro n2 args2 _) = 
    n1 == n2 && length args1 == length args2 && all (uncurry structuralEq) (zip args1 args2)
  structuralEq _ _ = False
  
  -- Heads ignore variable names for alpha-equivalence
  getHead (Var _ i _) = "Var:" ++ show i  -- Use index, not name
  getHead (FVar x _) = "FVar:" ++ x       -- Free variables use name
  getHead (Lam _ _ _) = "Lam"  -- Don't include binder name
  getHead (App _ _ _) = "App"
  getHead (TMacro n _ _) = "TMacro:" ++ n

--------------------------------------------------------------------------------
-- | Instance for RType
--------------------------------------------------------------------------------

instance EqualityAst RType where
  -- ALPHA-EQUIVALENCE: Names are ignored, only de Bruijn indices matter
  structuralEq (RVar _ i1 _) (RVar _ i2 _) = i1 == i2  -- Ignore names completely!
  structuralEq (FRVar x1 _) (FRVar x2 _) = x1 == x2   -- Free variables compared by name
  structuralEq (RMacro n1 args1 _) (RMacro n2 args2 _) = 
    n1 == n2 && length args1 == length args2 && all (uncurry structuralEq) (zip args1 args2)
  structuralEq (Arr r1 s1 _) (Arr r2 s2 _) = structuralEq r1 r2 && structuralEq s1 s2
  structuralEq (All _ r1 _) (All _ r2 _) = structuralEq r1 r2  -- Ignore quantifier names!
  structuralEq (Conv r1 _) (Conv r2 _) = structuralEq r1 r2
  structuralEq (Comp r1 s1 _) (Comp r2 s2 _) = structuralEq r1 r2 && structuralEq s1 s2
  structuralEq (Prom t1 _) (Prom t2 _) = t1 == t2  -- Terms use structural equality for now
  structuralEq _ _ = False
  
  -- Heads ignore variable names for alpha-equivalence
  getHead (RVar _ i _) = "RVar:" ++ show i  -- Use index, not name
  getHead (FRVar x _) = "FRVar:" ++ x       -- Free variables use name
  getHead (RMacro n _ _) = "RMacro:" ++ n
  getHead (Arr _ _ _) = "Arr" 
  getHead (All _ _ _) = "All"  -- Don't include binder name
  getHead (Conv _ _) = "Conv"
  getHead (Comp _ _ _) = "Comp"
  getHead (Prom _ _) = "Prom"

--------------------------------------------------------------------------------
-- | Instance for Proof
--------------------------------------------------------------------------------

instance EqualityAst Proof where
  -- ALPHA-EQUIVALENCE: Names are ignored, only de Bruijn indices matter
  structuralEq (PVar _ i1 _) (PVar _ i2 _) = i1 == i2  -- Ignore names completely!
  structuralEq (FPVar x1 _) (FPVar x2 _) = x1 == x2   -- Free variables compared by name
  structuralEq (PMacro n1 args1 _) (PMacro n2 args2 _) = 
    n1 == n2 && length args1 == length args2 && all (uncurry structuralEq) (zip args1 args2)
  structuralEq (LamP _ ty1 p1 _) (LamP _ ty2 p2 _) = 
    ty1 == ty2 && structuralEq p1 p2  -- Ignore binder names!
  structuralEq (AppP p1 q1 _) (AppP p2 q2 _) = structuralEq p1 p2 && structuralEq q1 q2
  structuralEq (TyLam _ p1 _) (TyLam _ p2 _) = structuralEq p1 p2  -- Ignore type binder names!
  structuralEq (TyApp p1 ty1 _) (TyApp p2 ty2 _) = structuralEq p1 p2 && ty1 == ty2
  structuralEq (ConvProof t1 p1 s1 _) (ConvProof t2 p2 s2 _) = 
    t1 == t2 && structuralEq p1 p2 && s1 == s2
  structuralEq (ConvIntro p1 _) (ConvIntro p2 _) = structuralEq p1 p2
  structuralEq (ConvElim p1 _) (ConvElim p2 _) = structuralEq p1 p2
  structuralEq (RhoElim _ t1 s1 p1 q1 _) (RhoElim _ t2 s2 p2 q2 _) = 
    t1 == t2 && s1 == s2 && structuralEq p1 p2 && structuralEq q1 q2  -- Ignore variable names!
  structuralEq (Iota t1 s1 _) (Iota t2 s2 _) = t1 == t2 && s1 == s2
  structuralEq (Pair p1 q1 _) (Pair p2 q2 _) = structuralEq p1 p2 && structuralEq q1 q2
  structuralEq (Pi p1 _ _ _ q1 _) (Pi p2 _ _ _ q2 _) = 
    structuralEq p1 p2 && structuralEq q1 q2  -- Ignore all binder names!
  structuralEq (PTheoremApp n1 args1 _) (PTheoremApp n2 args2 _) = 
    n1 == n2 && length args1 == length args2 && all alphaEqTheoremArgs (zip args1 args2)
  structuralEq _ _ = False
  
  -- Heads ignore variable names for alpha-equivalence
  getHead (PVar _ i _) = "PVar:" ++ show i  -- Use index, not name
  getHead (FPVar x _) = "FPVar:" ++ x       -- Free variables use name
  getHead (PMacro n _ _) = "PMacro:" ++ n
  getHead (LamP _ _ _ _) = "LamP"  -- Don't include binder name
  getHead (AppP _ _ _) = "AppP"
  getHead (TyLam _ _ _) = "TyLam"  -- Don't include type binder name
  getHead (TyApp _ _ _) = "TyApp"
  getHead (ConvProof _ _ _ _) = "ConvProof"
  getHead (ConvIntro _ _) = "ConvIntro"
  getHead (ConvElim _ _) = "ConvElim"
  getHead (RhoElim _ _ _ _ _ _) = "RhoElim"  -- Don't include variable name
  getHead (Iota _ _ _) = "Iota"
  getHead (Pair _ _ _) = "Pair"
  getHead (Pi _ _ _ _ _ _) = "Pi"  -- Don't include binder names
  getHead (PTheoremApp n _ _) = "PTheoremApp:" ++ n

-- | EqualityAst instance for MacroArg
instance EqualityAst MacroArg where
  structuralEq (MTerm t1) (MTerm t2) = structuralEq t1 t2
  structuralEq (MRel r1) (MRel r2) = structuralEq r1 r2
  structuralEq (MProof p1) (MProof p2) = structuralEq p1 p2
  structuralEq _ _ = False
  
  getHead (MTerm t) = "MTerm:" ++ getHead t
  getHead (MRel r) = "MRel:" ++ getHead r
  getHead (MProof p) = "MProof:" ++ getHead p