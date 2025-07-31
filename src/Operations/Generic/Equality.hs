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
  ( alphaEquality
  ) where

import qualified Data.Map as Map
import Core.Syntax
import Core.Context (Context(..))
import Operations.Generic.Expansion (ExpandAst(..), getMacroApp, isRightBody, bodyToAst)
import Operations.Generic.Macro (elabMacroAppG)
import Operations.Generic.Substitution (SubstInto)

--------------------------------------------------------------------------------
-- | Alpha equivalence type class for proper recursive equality
--------------------------------------------------------------------------------

-- | Alpha equivalence type class that handles recursive constructor checking
class AlphaEquiv a where
  alphaEquiv :: Context -> Int -> a -> a -> Bool

-- | Instance for RType - handles all relational type constructors
instance AlphaEquiv RType where
  alphaEquiv env stepsLeft r1 r2 = case (r1, r2) of
    -- Free relation variables - must have same name
    (FRVar x _, FRVar y _) -> x == y
    
    -- Bound relation variables - must have same de Bruijn index
    (RVar _ i _, RVar _ j _) -> i == j
    
    -- Universal quantification - ignore binder names, check bodies recursively
    (All _ body1 _, All _ body2 _) -> 
      alphaEqualityStep env body1 body2 stepsLeft
    
    -- Arrow types - check both argument and result types recursively
    (Arr arg1 res1 _, Arr arg2 res2 _) -> 
      alphaEqualityStep env arg1 arg2 stepsLeft &&
      alphaEqualityStep env res1 res2 stepsLeft
    
    -- Composition - check both operands recursively
    (Comp r1a r1b _, Comp r2a r2b _) ->
      alphaEqualityStep env r1a r2a stepsLeft &&
      alphaEqualityStep env r1b r2b stepsLeft
    
    -- Converse - check operand recursively
    (Conv r1 _, Conv r2 _) ->
      alphaEqualityStep env r1 r2 stepsLeft
    
    -- Promotion - check term recursively
    (Prom t1 _, Prom t2 _) ->
      alphaEqualityStep env t1 t2 stepsLeft
    
    -- Macros - handled by expansion in alphaEqualityStep
    (RMacro _ _ _, _) -> False  -- Should be handled by macro expansion
    (_, RMacro _ _ _) -> False  -- Should be handled by macro expansion
    
    -- Different constructors
    _ -> False

-- | Instance for Term - handles all term constructors  
instance AlphaEquiv Term where
  alphaEquiv env stepsLeft t1 t2 = case (t1, t2) of
    -- Free term variables - must have same name
    (FVar x _, FVar y _) -> x == y
    
    -- Bound term variables - must have same de Bruijn index
    (Var _ i _, Var _ j _) -> i == j
    
    -- Lambda abstractions - ignore binder names, check bodies recursively
    (Lam _ body1 _, Lam _ body2 _) ->
      alphaEqualityStep env body1 body2 stepsLeft
    
    -- Applications - check both function and argument recursively
    (App f1 a1 _, App f2 a2 _) ->
      alphaEqualityStep env f1 f2 stepsLeft &&
      alphaEqualityStep env a1 a2 stepsLeft
    
    -- Macros - handled by expansion in alphaEqualityStep
    (TMacro _ _ _, _) -> False  -- Should be handled by macro expansion
    (_, TMacro _ _ _) -> False  -- Should be handled by macro expansion
    
    -- Different constructors
    _ -> False

-- | Instance for Proof - handles all proof constructors
instance AlphaEquiv Proof where
  alphaEquiv env stepsLeft p1 p2 = case (p1, p2) of
    -- Free proof variables - must have same name
    (FPVar x _, FPVar y _) -> x == y
    
    -- Bound proof variables - must have same de Bruijn index
    (PVar _ i _, PVar _ j _) -> i == j
    
    -- Proof lambda abstractions - ignore binder names, check bodies recursively
    (LamP _ rtype1 body1 _, LamP _ rtype2 body2 _) ->
      alphaEqualityStep env rtype1 rtype2 stepsLeft &&
      alphaEqualityStep env body1 body2 stepsLeft
    
    -- Proof applications - check both function and argument recursively
    (AppP f1 a1 _, AppP f2 a2 _) ->
      alphaEqualityStep env f1 f2 stepsLeft &&
      alphaEqualityStep env a1 a2 stepsLeft
    
    -- Type lambda abstractions - ignore binder names, check bodies recursively
    (TyLam _ body1 _, TyLam _ body2 _) ->
      alphaEqualityStep env body1 body2 stepsLeft
    
    -- Type applications - check both proof and type recursively
    (TyApp p1 r1 _, TyApp p2 r2 _) ->
      alphaEqualityStep env p1 p2 stepsLeft &&
      alphaEqualityStep env r1 r2 stepsLeft
    
    -- Conversion proofs - check all components recursively
    (ConvProof t1a p1 t1b _, ConvProof t2a p2 t2b _) ->
      alphaEqualityStep env t1a t2a stepsLeft &&
      alphaEqualityStep env p1 p2 stepsLeft &&
      alphaEqualityStep env t1b t2b stepsLeft
    
    -- Converse introduction - check operand recursively
    (ConvIntro p1 _, ConvIntro p2 _) ->
      alphaEqualityStep env p1 p2 stepsLeft
    
    -- Converse elimination - check operand recursively
    (ConvElim p1 _, ConvElim p2 _) ->
      alphaEqualityStep env p1 p2 stepsLeft
    
    -- Iota (term promotion) - check both terms recursively
    (Iota t1a t1b _, Iota t2a t2b _) ->
      alphaEqualityStep env t1a t2a stepsLeft &&
      alphaEqualityStep env t1b t2b stepsLeft
    
    -- Rho elimination - ignore binder names, check all components recursively
    (RhoElim _ t1a t1b p1a p1b _, RhoElim _ t2a t2b p2a p2b _) ->
      alphaEqualityStep env t1a t2a stepsLeft &&
      alphaEqualityStep env t1b t2b stepsLeft &&
      alphaEqualityStep env p1a p2a stepsLeft &&
      alphaEqualityStep env p1b p2b stepsLeft
    
    -- Composition introduction (pairs) - check both proofs recursively
    (Pair p1a p1b _, Pair p2a p2b _) ->
      alphaEqualityStep env p1a p2a stepsLeft &&
      alphaEqualityStep env p1b p2b stepsLeft
    
    -- Pi elimination - ignore binder names, check all components recursively
    (Pi p1a _ _ _ p1b _, Pi p2a _ _ _ p2b _) ->
      alphaEqualityStep env p1a p2a stepsLeft &&
      alphaEqualityStep env p1b p2b stepsLeft
    
    -- Theorem applications - check name and arguments recursively
    (PTheoremApp n1 args1 _, PTheoremApp n2 args2 _) ->
      n1 == n2 && length args1 == length args2 &&
      all (uncurry (alphaEquiv env stepsLeft)) (zip args1 args2)
    
    -- Macros - handled by expansion in alphaEqualityStep
    (PMacro _ _ _, _) -> False  -- Should be handled by macro expansion
    (_, PMacro _ _ _) -> False  -- Should be handled by macro expansion
    
    -- Different constructors
    _ -> False

-- | Instance for TheoremArg - handles all theorem argument types
instance AlphaEquiv TheoremArg where
  alphaEquiv env stepsLeft arg1 arg2 = case (arg1, arg2) of
    (TermArg t1, TermArg t2) -> alphaEqualityStep env t1 t2 stepsLeft
    (RelArg r1, RelArg r2) -> alphaEqualityStep env r1 r2 stepsLeft
    (ProofArg p1, ProofArg p2) -> alphaEqualityStep env p1 p2 stepsLeft
    _ -> False  -- Different types

-- | Instance for MacroArg - handles all macro argument types
instance AlphaEquiv MacroArg where
  alphaEquiv env stepsLeft arg1 arg2 = case (arg1, arg2) of
    (MTerm t1, MTerm t2) -> alphaEqualityStep env t1 t2 stepsLeft
    (MRel r1, MRel r2) -> alphaEqualityStep env r1 r2 stepsLeft
    (MProof p1, MProof p2) -> alphaEqualityStep env p1 p2 stepsLeft
    _ -> False  -- Different types

--------------------------------------------------------------------------------
-- | Generic lazy equality with minimal macro expansion
--------------------------------------------------------------------------------

-- | Alpha equality: expand macros lazily when structural comparison fails
alphaEquality :: (AlphaEquiv a, ExpandAst a, SubstInto MacroArg a) => Context -> a -> a -> Bool
alphaEquality env x y = alphaEqualityStep env x y 100  -- Max 100 expansion steps

-- | Internal alpha equality with step limit to prevent infinite loops
alphaEqualityStep :: (AlphaEquiv a, ExpandAst a, SubstInto MacroArg a) => Context -> a -> a -> Int -> Bool
alphaEqualityStep env x y stepsLeft
  | stepsLeft <= 0 = False  -- Prevent infinite expansion
  | otherwise = 
      case (getMacroApp x, getMacroApp y) of
        (Nothing, Nothing) -> 
          -- Neither is a macro - use proper alpha equivalence
          alphaEquiv env stepsLeft x y
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
        (Just (xName, xArgs, _), Just (yName, yArgs, _)) -> 
          -- Both are macros
          if xName == yName && length xArgs == length yArgs
          then -- Same macro name and arity - check alpha equality of arguments
               all (uncurry (alphaEquiv env (stepsLeft - 1))) (zip xArgs yArgs)
          else -- Different macros - expand left first, then right if needed
               case expandOneMacro env x of
                 Just x' -> alphaEqualityStep env x' y (stepsLeft - 1)
                 Nothing -> 
                   case expandOneMacro env y of
                     Just y' -> alphaEqualityStep env x y' (stepsLeft - 1)
                     Nothing -> False

-- | Expand exactly one macro application, returning Nothing if not a macro or expansion fails
expandOneMacro :: forall a. (ExpandAst a, SubstInto MacroArg a) => Context -> a -> Maybe a
expandOneMacro env ast = 
  case getMacroApp ast of
    Nothing -> Nothing  -- Not a macro
    Just (name, args, _pos) ->
      case Map.lookup name (macroDefinitions env) of
        Nothing -> Nothing  -- Macro not found
        Just (paramInfo, macroBody) ->
          case isRightBody @a macroBody of
            Nothing -> Nothing  -- Wrong body type
            Just body -> 
              case elabMacroAppG env name paramInfo (bodyToAst @a body) args of
                Right result -> Just result
                Left _ -> Nothing  -- Expansion failed


