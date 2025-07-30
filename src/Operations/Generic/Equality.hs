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
-- | Helper functions for macro argument equality
--------------------------------------------------------------------------------

-- | Alpha equality for heterogeneous macro arguments
alphaEqualityMacroArg :: Context -> Int -> MacroArg -> MacroArg -> Bool
alphaEqualityMacroArg env stepsLeft arg1 arg2 = case (arg1, arg2) of
  (MTerm t1, MTerm t2) -> alphaEqualityStep env t1 t2 stepsLeft
  (MRel r1, MRel r2) -> alphaEqualityStep env r1 r2 stepsLeft
  (MProof p1, MProof p2) -> alphaEqualityStep env p1 p2 stepsLeft
  _ -> False  -- Different types

--------------------------------------------------------------------------------
-- | Generic lazy equality with minimal macro expansion
--------------------------------------------------------------------------------

-- | Alpha equality: expand macros lazily when structural comparison fails
alphaEquality :: (Eq a, ExpandAst a, SubstInto MacroArg a) => Context -> a -> a -> Bool
alphaEquality env x y = alphaEqualityStep env x y 100  -- Max 100 expansion steps

-- | Internal alpha equality with step limit to prevent infinite loops
alphaEqualityStep :: (Eq a, ExpandAst a, SubstInto MacroArg a) => Context -> a -> a -> Int -> Bool
alphaEqualityStep env x y stepsLeft
  | stepsLeft <= 0 = False  -- Prevent infinite expansion
  | otherwise = 
      case (getMacroApp x, getMacroApp y) of
        (Nothing, Nothing) -> 
          -- Neither is a macro - use structural equality
          x == y
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
               all (uncurry (alphaEqualityMacroArg env (stepsLeft - 1))) (zip xArgs yArgs)
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


