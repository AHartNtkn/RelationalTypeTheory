{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

-- | Generic substitution infrastructure for all AST types.
-- This module unifies substitution operations across Term, RType, and Proof.

module Operations.Generic.Substitution
  ( -- * Typeclasses
    SubstInto(..)
  , AstCore(..)
    -- * Theorem substitution (free variables)
  , applyTheoremFreeVarSubsToTerm
  , applyTheoremFreeVarSubsToRType
  , applyTheoremFreeVarSubsToJudgment
  ) where

import Core.Syntax (Term(..), RType(..), Proof(..), TheoremArg(..), RelJudgment(..), Binding(..), MacroArg(..))
import Operations.Generic.Shift (ShiftAst(..), shift)
import Core.Errors (RelTTError(..))

--------------------------------------------------------------------------------
-- | Two-parameter substitution typeclass
--------------------------------------------------------------------------------

-- | Substitute values of type `a` into expressions of type `b`
class SubstInto a b where
  -- | Substitute de Bruijn index with replacement (capture-avoiding)
  substIndex :: Int -> a -> b -> b
  -- | Substitute free variable by name with replacement
  substFreeVar :: String -> a -> b -> b

--------------------------------------------------------------------------------
-- | Core AST operations typeclass
--------------------------------------------------------------------------------

-- | Core operations that all AST types should support
class AstCore a where
  -- | Extract variable name if this node is a variable, Nothing otherwise
  varNameOf :: a -> Maybe String

--------------------------------------------------------------------------------
-- | SubstInto instances
--------------------------------------------------------------------------------

-- | Substitute terms into terms
instance SubstInto Term Term where
  substIndex targetIdx replacement = go 0
    where
      go depth term = case term of
        Var name i pos
          | i == depth + targetIdx -> shift depth replacement
          | i > depth + targetIdx -> Var name (i - 1) pos
          | otherwise -> term
        FVar{} -> term
        Lam name body pos -> Lam name (go (depth + 1) body) pos
        App t1 t2 pos -> App (go depth t1) (go depth t2) pos
        TMacro name args pos -> TMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm (go depth t)
                  MRel r -> MRel r
                  MProof p -> MProof p

  substFreeVar targetName replacement = go
    where
      go term = case term of
        FVar name pos | name == targetName -> replacement
        FVar{} -> term
        Var{} -> term
        Lam n b p -> Lam n (go b) p
        App l r p -> App (go l) (go r) p
        TMacro n as p -> TMacro n (map substMacroArg as) p
          where substMacroArg = \case
                  MTerm t -> MTerm (go t)
                  MRel r -> MRel r
                  MProof p -> MProof p

-- | Substitute relation types into relation types
instance SubstInto RType RType where
  substIndex targetIdx replacement = go 0
    where
      go depth ty = case ty of
        RVar name i pos
          | i == depth + targetIdx -> shift depth replacement
          | i > depth + targetIdx -> RVar name (i - 1) pos
          | otherwise -> ty
        FRVar{} -> ty
        RMacro name args pos -> RMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm t
                  MRel r -> MRel (go depth r)
                  MProof p -> MProof p
        Arr r1 r2 pos -> Arr (go depth r1) (go depth r2) pos
        All name r pos -> All name (go (depth + 1) r) pos
        Conv r pos -> Conv (go depth r) pos
        Comp r1 r2 pos -> Comp (go depth r1) (go depth r2) pos
        Prom term pos -> Prom term pos

  substFreeVar targetName replacement = go
    where
      go rt = case rt of
        FRVar name pos | name == targetName -> replacement
        FRVar{} -> rt
        RVar{} -> rt
        RMacro n as p -> RMacro n (map substMacroArg as) p
          where substMacroArg = \case
                  MTerm t -> MTerm t
                  MRel r -> MRel (go r)
                  MProof p -> MProof p
        Arr a b p -> Arr (go a) (go b) p
        All n r p -> All n (go r) p
        Conv r p -> Conv (go r) p
        Comp a b p -> Comp (go a) (go b) p
        Prom t p -> Prom t p

-- | Substitute terms into relation types (for promoted terms)
instance SubstInto Term RType where
  substIndex _ _ rtype = rtype  -- de Bruijn substitution doesn't cross type boundaries
  
  substFreeVar targetName replacement = go
    where
      go rt = case rt of
        RVar _ _ _ -> rt
        FRVar _ _ -> rt
        RMacro name args pos -> RMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm (substFreeVar targetName replacement t)
                  MRel r -> MRel (go r)
                  MProof p -> MProof p
        Arr r1 r2 pos -> Arr (go r1) (go r2) pos
        All name r pos -> All name (go r) pos
        Conv r pos -> Conv (go r) pos
        Comp r1 r2 pos -> Comp (go r1) (go r2) pos
        Prom term pos -> Prom (substFreeVar targetName replacement term) pos

-- | Substitute proofs into proofs
instance SubstInto Proof Proof where
  substIndex targetIdx replacement = go 0
    where
      go depth proof = case proof of
        PVar name i pos
          | i == depth + targetIdx -> shift depth replacement
          | i > depth + targetIdx -> PVar name (i - 1) pos
          | otherwise -> proof
        FPVar{} -> proof
        LamP name ty body pos -> LamP name ty (go (depth + 1) body) pos
        AppP p1 p2 pos -> AppP (go depth p1) (go depth p2) pos
        TyLam name body pos -> TyLam name (go (depth + 1) body) pos
        TyApp p ty pos -> TyApp (go depth p) ty pos
        ConvProof t1 p t2 pos -> ConvProof t1 (go depth p) t2 pos
        RhoElim x t1 t2 p1 p2 pos -> RhoElim x t1 t2 (go depth p1) (go depth p2) pos
        Iota t1 t2 pos -> Iota t1 t2 pos
        ConvIntro p pos -> ConvIntro (go depth p) pos
        ConvElim p pos -> ConvElim (go depth p) pos
        Pair p1 p2 pos -> Pair (go depth p1) (go depth p2) pos
        Pi p x y z q pos -> Pi (go depth p) x y z (go (depth + 3) q) pos
        PTheoremApp name args pos -> PTheoremApp name args pos
        PMacro name args pos -> PMacro name args pos

  substFreeVar targetName replacement = go
    where
      go pr = case pr of
        FPVar name pos | name == targetName -> replacement
        FPVar{} -> pr
        PVar{} -> pr
        LamP n t b p -> LamP n t (go b) p
        TyLam n b p -> TyLam n (go b) p
        RhoElim x t u p1 p2 p -> RhoElim x t u (go p1) (go p2) p
        Pi p1 x u v p2 p -> Pi (go p1) x u v (go p2) p
        AppP l r p -> AppP (go l) (go r) p
        TyApp q t p -> TyApp (go q) t p
        ConvProof t q u p -> ConvProof t (go q) u p
        ConvIntro q p -> ConvIntro (go q) p
        ConvElim q p -> ConvElim (go q) p
        Pair l r p -> Pair (go l) (go r) p
        PMacro n as p -> PMacro n as p
        other -> other

-- | Substitute MacroArgs into MacroArgs
instance SubstInto MacroArg MacroArg where
  substIndex targetIdx replacement = \case
    MTerm t -> case replacement of
      MTerm repl -> MTerm (substIndex targetIdx repl t)
      _ -> MTerm t
    MRel r -> case replacement of
      MRel repl -> MRel (substIndex targetIdx repl r)
      _ -> MRel r
    MProof p -> case replacement of
      MProof repl -> MProof (substIndex targetIdx repl p)
      _ -> MProof p

  substFreeVar targetName replacement = \case
    MTerm t -> case replacement of
      MTerm repl -> MTerm (substFreeVar targetName repl t)
      _ -> MTerm t
    MRel r -> case replacement of
      MRel repl -> MRel (substFreeVar targetName repl r)
      _ -> MRel r
    MProof p -> case replacement of
      MProof repl -> MProof (substFreeVar targetName repl p)
      _ -> MProof p

--------------------------------------------------------------------------------
-- | AstCore instances
--------------------------------------------------------------------------------

-- | AstCore instance for Term
instance AstCore Term where
  varNameOf (Var v _ _) = Just v
  varNameOf (FVar v _)  = Just v
  varNameOf _           = Nothing

-- | AstCore instance for RType
instance AstCore RType where
  varNameOf (RVar v _ _) = Just v
  varNameOf (FRVar v _)  = Just v
  varNameOf _            = Nothing

-- | AstCore instance for Proof
instance AstCore Proof where
  varNameOf (PVar v _ _) = Just v
  varNameOf (FPVar v _)  = Just v
  varNameOf _            = Nothing

-- | AstCore instance for MacroArg
instance AstCore MacroArg where
  varNameOf = \case
    MTerm t -> varNameOf t
    MRel r -> varNameOf r
    MProof p -> varNameOf p



--------------------------------------------------------------------------------
-- | Free variable theorem substitution operations
--------------------------------------------------------------------------------

-- | Apply theorem argument substitutions to term using free variable substitution
applyTheoremFreeVarSubsToTerm :: [(String, TheoremArg)] -> Term -> Either RelTTError Term
applyTheoremFreeVarSubsToTerm subs term = 
  return $ foldl applySub term subs
  where
    applySub acc (paramName, TermArg replacement) = substFreeVar paramName replacement acc
    applySub acc (paramName, _) = acc  -- Only TermArg affects Term

-- | Apply theorem argument substitutions to relation type using free variable substitution
applyTheoremFreeVarSubsToRType :: [(String, TheoremArg)] -> RType -> Either RelTTError RType
applyTheoremFreeVarSubsToRType subs rtype = 
  return $ foldl applySub rtype subs
  where
    applySub acc (paramName, RelArg replacement) = substFreeVar paramName replacement acc
    applySub acc (paramName, TermArg replacement) = substFreeVar paramName replacement acc -- Terms into RType
    applySub acc (paramName, _) = acc  -- ProofArg doesn't affect RType

-- | Apply theorem substitutions to a relational judgment using free variable substitution
applyTheoremFreeVarSubsToJudgment :: [(String, TheoremArg)] -> RelJudgment -> Either RelTTError RelJudgment
applyTheoremFreeVarSubsToJudgment subs (RelJudgment leftTerm relType rightTerm) = do
  leftTerm' <- applyTheoremFreeVarSubsToTerm subs leftTerm
  relType' <- applyTheoremFreeVarSubsToRType subs relType
  rightTerm' <- applyTheoremFreeVarSubsToTerm subs rightTerm
  return (RelJudgment leftTerm' relType' rightTerm')

--------------------------------------------------------------------------------
-- | Mixed substitution operations
--------------------------------------------------------------------------------

