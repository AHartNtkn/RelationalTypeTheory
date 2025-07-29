{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}

-- | Generic substitution infrastructure for all AST types.
-- This module unifies substitution operations across Term, RType, and Proof.

module Operations.Generic.Substitution
  ( -- * Typeclasses
    SubstAst(..)
    -- * Generic operations
  , substMultiple
    -- * Theorem substitution
  , applyTheoremsSubsToTerm
  , applyTheoremSubsToRType
  , applyTheoremSubsToJudgment
  ) where

import Core.Syntax (Term(..), RType(..), Proof(..), TheoremArg(..), RelJudgment(..), Binding(..), MacroArg(..))
import Operations.Generic.Shift (ShiftAst(..), shift)
import Core.Errors (RelTTError(..))

--------------------------------------------------------------------------------
-- | Core typeclass for de Bruijn index substitution
--------------------------------------------------------------------------------

class ShiftAst a => SubstAst a where
  -- | Substitute de Bruijn index with a term (capture-avoiding)
  -- substIndex targetIndex replacement body
  substIndex :: Int -> a -> a -> a

--------------------------------------------------------------------------------
-- | Generic operations
--------------------------------------------------------------------------------

-- | Apply multiple de Bruijn substitutions
substMultiple :: SubstAst a => [(Int, a)] -> a -> a
substMultiple [] body = body
substMultiple ((idx, repl):rest) body = 
  substMultiple (adjustIndices idx rest) (substIndex idx repl body)
  where
    -- Adjust indices after a substitution
    adjustIndices :: Int -> [(Int, a)] -> [(Int, a)]
    adjustIndices removed = map $ \(i, r) -> 
      if i > removed then (i - 1, r) else (i, r)

--------------------------------------------------------------------------------
-- | Instance for Term
--------------------------------------------------------------------------------

instance SubstAst Term where
  substIndex targetIdx replacement = go 0
    where
      go depth term = case term of
        Var name i pos
          | i == depth + targetIdx -> shift depth replacement
          | i > depth + targetIdx -> Var name (i - 1) pos
          | otherwise -> term
        FVar{} -> term                   -- Free variables not affected by substitution
        Lam name body pos ->
          Lam name (go (depth + 1) body) pos
        App t1 t2 pos ->
          App (go depth t1) (go depth t2) pos
        TMacro name args pos ->
          TMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm (go depth t)
                  MRel r -> MRel r  -- Relations unaffected by term substitution
                  MProof p -> MProof p  -- Proofs unaffected by term substitution

--------------------------------------------------------------------------------
-- | Instance for RType
--------------------------------------------------------------------------------

instance SubstAst RType where
  substIndex targetIdx replacement = go 0
    where
      go depth ty = case ty of
        RVar name i pos
          | i == depth + targetIdx -> shift depth replacement
          | i > depth + targetIdx -> RVar name (i - 1) pos
          | otherwise -> ty
        FRVar{} -> ty                    -- Free variables not affected by substitution
        RMacro name args pos ->
          RMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm t  -- Terms unaffected by relational substitution
                  MRel r -> MRel (go depth r)
                  MProof p -> MProof p  -- Proofs unaffected by relational substitution
        Arr r1 r2 pos ->
          Arr (go depth r1) (go depth r2) pos
        All name r pos ->
          All name (go (depth + 1) r) pos
        Conv r pos ->
          Conv (go depth r) pos
        Comp r1 r2 pos ->
          Comp (go depth r1) (go depth r2) pos
        Prom term pos ->
          -- Promoted terms are not affected by relation substitution
          Prom term pos

--------------------------------------------------------------------------------
-- | Instance for Proof
--------------------------------------------------------------------------------

instance SubstAst Proof where
  substIndex targetIdx replacement = go 0
    where
      go depth proof = case proof of
        PVar name i pos
          | i == depth + targetIdx -> shift depth replacement
          | i > depth + targetIdx -> PVar name (i - 1) pos
          | otherwise -> proof
        FPVar{} -> proof                 -- Free variables not affected by substitution
        LamP name ty body pos ->
          LamP name ty (go (depth + 1) body) pos
        AppP p1 p2 pos ->
          AppP (go depth p1) (go depth p2) pos
        TyLam name body pos ->
          TyLam name (go (depth + 1) body) pos
        TyApp p ty pos ->
          TyApp (go depth p) ty pos
        ConvProof t1 p t2 pos ->
          ConvProof t1 (go depth p) t2 pos
        RhoElim x t1 t2 p1 p2 pos ->
          RhoElim x t1 t2 (go depth p1) (go depth p2) pos
        Iota t1 t2 pos ->
          Iota t1 t2 pos
        ConvIntro p pos ->
          ConvIntro (go depth p) pos
        ConvElim p pos ->
          ConvElim (go depth p) pos
        Pair p1 p2 pos ->
          Pair (go depth p1) (go depth p2) pos
        Pi p x y z q pos ->
          -- Pi introduces 3 new bindings
          Pi (go depth p) x y z (go (depth + 3) q) pos
        PTheoremApp name args pos ->
          PTheoremApp name (map (goArg depth) args) pos
        PMacro name args pos ->
          PMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm t  -- Terms unaffected by proof substitution
                  MRel r -> MRel r  -- Relations unaffected by proof substitution
                  MProof p -> MProof (go depth p)
        where
          goArg depthArg arg = case arg of
            TermArg t -> TermArg t  -- Not affected by proof substitution
            RelArg r -> RelArg r    -- Not affected by proof substitution
            ProofArg p -> ProofArg (go depthArg p)

-- | SubstAst instance for MacroArg
-- MacroArg substitution works by delegating to the wrapped type
-- Only when the replacement has the same wrapper type
instance SubstAst MacroArg where
  substIndex targetIdx replacement = \case
    MTerm t -> case replacement of
      MTerm repl -> MTerm (substIndex targetIdx repl t)
      _ -> MTerm t  -- No substitution if types don't match
    MRel r -> case replacement of
      MRel repl -> MRel (substIndex targetIdx repl r)
      _ -> MRel r  -- No substitution if types don't match
    MProof p -> case replacement of
      MProof repl -> MProof (substIndex targetIdx repl p)
      _ -> MProof p  -- No substitution if types don't match

--------------------------------------------------------------------------------
-- | Theorem substitution operations (telescope-based)
--------------------------------------------------------------------------------

-- | Apply theorem argument substitutions to term by telescope position
applyTheoremsSubsToTerm :: [(Binding, TheoremArg)] -> Term -> Either RelTTError Term
applyTheoremsSubsToTerm subs term = do
  let termSubs = extractTermSubstitutions subs
  return $ substMultiple termSubs term

-- | Apply theorem argument substitutions to relation type by telescope position  
applyTheoremSubsToRType :: [(Binding, TheoremArg)] -> RType -> Either RelTTError RType
applyTheoremSubsToRType subs rtype = do
  let relSubs = extractRelSubstitutions subs
      termSubs = extractTermSubstitutions subs
  -- First apply relation substitutions, then term substitutions in promoted terms
  let afterRelSubs = substMultiple relSubs rtype
  return $ applyTermSubsInRType termSubs afterRelSubs

-- | Apply theorem substitutions to a relational judgment
applyTheoremSubsToJudgment :: [(Binding, TheoremArg)] -> RelJudgment -> Either RelTTError RelJudgment
applyTheoremSubsToJudgment subs (RelJudgment leftTerm relType rightTerm) = do
  leftTerm' <- applyTheoremsSubsToTerm subs leftTerm
  relType' <- applyTheoremSubsToRType subs relType
  rightTerm' <- applyTheoremsSubsToTerm subs rightTerm
  return (RelJudgment leftTerm' relType' rightTerm')

-- | Extract term substitutions from theorem arguments (by telescope position)
extractTermSubstitutions :: [(Binding, TheoremArg)] -> [(Int, Term)]
extractTermSubstitutions subs = 
  let termBindings = [(i, t) | (i, (TermBinding _, TermArg t)) <- zip [0..] subs]
      -- Convert telescope positions to de Bruijn indices (reverse order)
      termCount = length termBindings
  in [(termCount - 1 - i, t) | (i, t) <- termBindings]

-- | Extract relation substitutions from theorem arguments (by telescope position)
extractRelSubstitutions :: [(Binding, TheoremArg)] -> [(Int, RType)]
extractRelSubstitutions subs = 
  let relBindings = [(i, r) | (i, (RelBinding _, RelArg r)) <- zip [0..] subs]
      -- Convert telescope positions to de Bruijn indices (reverse order)
      relCount = length relBindings  
  in [(relCount - 1 - i, r) | (i, r) <- relBindings]

-- | Apply term substitutions within RType (for promoted terms)
applyTermSubsInRType :: [(Int, Term)] -> RType -> RType
applyTermSubsInRType termSubs rtype = case rtype of
  RVar _ _ _ -> rtype
  FRVar _ _ -> rtype                     -- Free relation variables unaffected
  RMacro name args pos -> RMacro name (map substMacroArg args) pos
    where substMacroArg = \case
            MTerm t -> MTerm (foldl (flip $ uncurry substIndex) t termSubs)
            MRel r -> MRel (applyTermSubsInRType termSubs r)
            MProof p -> MProof p  -- Proofs unaffected by term substitution
  Arr r1 r2 pos -> Arr (applyTermSubsInRType termSubs r1) (applyTermSubsInRType termSubs r2) pos
  All name r pos -> All name (applyTermSubsInRType termSubs r) pos
  Conv r pos -> Conv (applyTermSubsInRType termSubs r) pos
  Comp r1 r2 pos -> Comp (applyTermSubsInRType termSubs r1) (applyTermSubsInRType termSubs r2) pos
  Prom term pos -> Prom (substMultiple termSubs term) pos

--------------------------------------------------------------------------------
-- | Mixed substitution operations
--------------------------------------------------------------------------------

