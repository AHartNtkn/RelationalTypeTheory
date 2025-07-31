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
import Operations.Generic.Shift (shift)
import Core.Errors (RelTTError(..))

--------------------------------------------------------------------------------
-- | Two-parameter substitution typeclass
--------------------------------------------------------------------------------

-- | Substitute values of type `a` into expressions of type `b`
class SubstInto a b where
  -- | Substitute de Bruijn index with replacement (capture-avoiding)
  substIndex :: Int -> a -> b -> b
  -- | Apply multiple renamings and substitutions in a single pass
  -- First argument: bound variable renamings [(oldName, newName)]  
  -- Second argument: free variable substitutions [(varName, replacement)]
  -- This is only applied during macro expanstion, where variables appearing
  -- in binders cannot appear elsewhere. This means we don't need to apply
  -- the renamings to free variables, just the bound variables.
  substBatch :: [(String, String)] -> [(String, a)] -> b -> b

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

  substBatch renamings substitutions = go
    where
      go term = case term of
        FVar name pos -> 
          case lookup name substitutions of
            Just replacement -> replacement
            Nothing -> term
        Var{} -> term
        Lam name body pos -> 
          let newName = case lookup name renamings of
                         Just renamed -> renamed
                         Nothing -> name
          in Lam newName (go body) pos
        App t1 t2 pos -> App (go t1) (go t2) pos
        TMacro name args pos -> TMacro name (map substMacroArg args) pos
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

  substBatch renamings substitutions = go
    where
      go rt = case rt of
        FRVar name pos -> 
          case lookup name substitutions of
            Just replacement -> replacement
            Nothing -> rt
        RVar{} -> rt
        RMacro name args pos -> RMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm t
                  MRel r -> MRel (go r)
                  MProof p -> MProof p
        Arr r1 r2 pos -> Arr (go r1) (go r2) pos
        All name r pos -> 
          let newName = case lookup name renamings of
                         Just renamed -> renamed
                         Nothing -> name
          in All newName (go r) pos
        Conv r pos -> Conv (go r) pos
        Comp r1 r2 pos -> Comp (go r1) (go r2) pos
        Prom term pos -> Prom term pos

-- | Substitute terms into relation types (for promoted terms)
instance SubstInto Term RType where
  substIndex _ _ rtype = rtype  -- de Bruijn substitution doesn't cross type boundaries
  
  substBatch renamings substitutions = go
    where
      go rt = case rt of
        RVar _ _ _ -> rt
        FRVar _ _ -> rt
        RMacro name args pos -> RMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm (substBatch renamings substitutions t)
                  MRel r -> MRel (go r)
                  MProof p -> MProof p
        Arr r1 r2 pos -> Arr (go r1) (go r2) pos
        All name r pos -> 
          let newName = case lookup name renamings of
                         Just renamed -> renamed
                         Nothing -> name
          in All newName (go r) pos
        Conv r pos -> Conv (go r) pos
        Comp r1 r2 pos -> Comp (go r1) (go r2) pos
        Prom term pos -> Prom (substBatch renamings substitutions term) pos

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

  substBatch renamings substitutions = go
    where
      go pr = case pr of
        FPVar name pos -> 
          case lookup name substitutions of
            Just replacement -> replacement
            Nothing -> pr
        PVar{} -> pr
        LamP name ty body pos -> 
          let newName = case lookup name renamings of
                         Just renamed -> renamed
                         Nothing -> name
          in LamP newName ty (go body) pos
        TyLam name body pos -> 
          let newName = case lookup name renamings of
                         Just renamed -> renamed
                         Nothing -> name
          in TyLam newName (go body) pos
        RhoElim x t1 t2 p1 p2 pos -> 
          let newX = case lookup x renamings of
                      Just renamed -> renamed
                      Nothing -> x
          in RhoElim newX t1 t2 (go p1) (go p2) pos
        Pi p1 x u v p2 pos -> 
          let newX = case lookup x renamings of
                      Just renamed -> renamed
                      Nothing -> x
              newU = case lookup u renamings of
                      Just renamed -> renamed
                      Nothing -> u
              newV = case lookup v renamings of
                      Just renamed -> renamed
                      Nothing -> v
          in Pi (go p1) newX newU newV (go p2) pos
        AppP p1 p2 pos -> AppP (go p1) (go p2) pos
        TyApp p ty pos -> TyApp (go p) ty pos
        ConvProof t1 p t2 pos -> ConvProof t1 (go p) t2 pos
        ConvIntro p pos -> ConvIntro (go p) pos
        ConvElim p pos -> ConvElim (go p) pos
        Pair p1 p2 pos -> Pair (go p1) (go p2) pos
        PMacro name args pos -> PMacro name args pos
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

  substBatch renamings substitutions = \case
    MTerm t -> case lookup "MTerm" substitutions of
      Just (MTerm repl) -> MTerm repl
      _ -> MTerm (substBatch renamings [(name, arg) | (name, MTerm arg) <- substitutions] t)
    MRel r -> case lookup "MRel" substitutions of  
      Just (MRel repl) -> MRel repl
      _ -> MRel (substBatch renamings [(name, arg) | (name, MRel arg) <- substitutions] r)
    MProof p -> case lookup "MProof" substitutions of
      Just (MProof repl) -> MProof repl
      _ -> MProof (substBatch renamings [(name, arg) | (name, MProof arg) <- substitutions] p)

-- | Substitute MacroArgs into Terms (heterogeneous substitution)
instance SubstInto MacroArg Term where
  substIndex targetIdx replacement = go 0
    where
      go depth term = case term of
        Var name i pos
          | i == depth + targetIdx -> 
              case replacement of
                MTerm repl -> shift depth repl
                _ -> term  -- Wrong type, no substitution
          | i > depth + targetIdx -> Var name (i - 1) pos
          | otherwise -> term
        FVar{} -> term
        Lam name body pos -> Lam name (go (depth + 1) body) pos
        App t1 t2 pos -> App (go depth t1) (go depth t2) pos
        TMacro name args pos -> TMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm (go depth t)
                  MRel r -> MRel r  -- No cross-boundary substitution
                  MProof p -> MProof p

  substBatch renamings substitutions = go
    where
      go term = case term of
        FVar name pos -> 
          case lookup name substitutions of
            Just (MTerm replacement) -> replacement
            Just actualArg -> error $ "Substitution type mismatch in term substitution: variable " ++ name ++ " expected MTerm but got " ++ show actualArg
            Nothing -> 
              case lookup name renamings of
                Just newName -> FVar newName pos
                Nothing -> term
        Var name i pos -> 
          case lookup name renamings of
            Just newName -> Var newName i pos
            Nothing -> term
        Lam name body pos -> 
          let newName = case lookup name renamings of
                         Just renamed -> renamed
                         Nothing -> name
          in Lam newName (go body) pos
        App t1 t2 pos -> App (go t1) (go t2) pos
        TMacro name args pos -> TMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm (go t)
                  MRel r -> MRel (substBatch renamings substitutions r)
                  MProof p -> MProof (substBatch renamings substitutions p)

-- | Substitute MacroArgs into RTypes (heterogeneous substitution)
instance SubstInto MacroArg RType where
  substIndex targetIdx replacement = go 0
    where
      go depth rtype = case rtype of
        RVar name i pos
          | i == depth + targetIdx -> 
              case replacement of
                MRel repl -> shift depth repl
                _ -> rtype  -- Wrong type, no substitution
          | i > depth + targetIdx -> RVar name (i - 1) pos
          | otherwise -> rtype
        FRVar{} -> rtype
        All name r pos -> All name (go (depth + 1) r) pos
        Arr r1 r2 pos -> Arr (go depth r1) (go depth r2) pos
        Comp r1 r2 pos -> Comp (go depth r1) (go depth r2) pos
        Conv r pos -> Conv (go depth r) pos
        Prom term pos -> Prom term pos  -- No cross-boundary substitution
        RMacro name args pos -> RMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm t  -- No cross-boundary substitution
                  MRel r -> MRel (go depth r)
                  MProof p -> MProof p

  substBatch renamings substitutions = go
    where
      go rtype = case rtype of
        FRVar name pos -> 
          case lookup name substitutions of
            Just (MRel replacement) -> replacement
            Just actualArg -> error $ "Substitution type mismatch in relational type substitution: variable " ++ name ++ " expected MRel but got " ++ show actualArg
            Nothing -> 
              case lookup name renamings of
                Just newName -> FRVar newName pos
                Nothing -> rtype
        RVar name i pos -> 
          case lookup name renamings of
            Just newName -> RVar newName i pos
            Nothing -> rtype
        All name r pos -> 
          let newName = case lookup name renamings of
                         Just renamed -> renamed
                         Nothing -> name
          in All newName (go r) pos
        Arr r1 r2 pos -> Arr (go r1) (go r2) pos
        Comp r1 r2 pos -> Comp (go r1) (go r2) pos
        Conv r pos -> Conv (go r) pos
        Prom term pos -> Prom (substBatch renamings substitutions term) pos
        RMacro name args pos -> RMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm (substBatch renamings substitutions t)
                  MRel r -> MRel (go r)
                  MProof p -> MProof (substBatch renamings substitutions p)

-- | Substitute MacroArgs into Proofs (heterogeneous substitution)
instance SubstInto MacroArg Proof where
  substIndex targetIdx replacement = go 0
    where
      go depth proof = case proof of
        PVar name i pos
          | i == depth + targetIdx -> 
              case replacement of
                MProof repl -> shift depth repl
                _ -> proof  -- Wrong type, no substitution
          | i > depth + targetIdx -> PVar name (i - 1) pos
          | otherwise -> proof
        FPVar{} -> proof
        LamP name ty body pos -> LamP name ty (go (depth + 1) body) pos
        AppP p1 p2 pos -> AppP (go depth p1) (go depth p2) pos
        TyLam name body pos -> TyLam name (go (depth + 1) body) pos
        TyApp p ty pos -> TyApp (go depth p) ty pos  -- No cross-boundary substitution
        ConvProof t1 p t2 pos -> ConvProof t1 (go depth p) t2 pos  -- No cross-boundary substitution
        RhoElim x t1 t2 p1 p2 pos -> RhoElim x t1 t2 (go depth p1) (go depth p2) pos  -- No cross-boundary substitution
        Iota t1 t2 pos -> Iota t1 t2 pos  -- No cross-boundary substitution
        ConvIntro p pos -> ConvIntro (go depth p) pos
        ConvElim p pos -> ConvElim (go depth p) pos
        Pair p1 p2 pos -> Pair (go depth p1) (go depth p2) pos
        Pi p x y z q pos -> Pi (go depth p) x y z (go (depth + 3) q) pos  -- x, y, z bind
        PTheoremApp name args pos -> PTheoremApp name args pos
        PMacro name args pos -> PMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm t  -- No cross-boundary substitution
                  MRel r -> MRel r
                  MProof p -> MProof (go depth p)

  substBatch renamings substitutions = go
    where
      go proof = case proof of
        FPVar name pos -> 
          case lookup name substitutions of
            Just (MProof replacement) -> replacement
            Just actualArg -> error $ "Substitution type mismatch in proof substitution: variable " ++ name ++ " expected MProof but got " ++ show actualArg
            Nothing -> 
              case lookup name renamings of
                Just newName -> FPVar newName pos
                Nothing -> proof
        PVar name i pos -> 
          case lookup name renamings of
            Just newName -> PVar newName i pos
            Nothing -> proof
        LamP name ty body pos -> 
          let newName = case lookup name renamings of
                         Just renamed -> renamed
                         Nothing -> name
          in LamP newName (substBatch renamings substitutions ty) (go body) pos
        AppP p1 p2 pos -> AppP (go p1) (go p2) pos
        TyLam name body pos -> 
          let newName = case lookup name renamings of
                         Just renamed -> renamed
                         Nothing -> name
          in TyLam newName (go body) pos
        TyApp p ty pos -> TyApp (go p) (substBatch renamings substitutions ty) pos
        ConvProof t1 p t2 pos -> 
          ConvProof (substBatch renamings substitutions t1) (go p) (substBatch renamings substitutions t2) pos
        RhoElim x t1 t2 p1 p2 pos -> 
          let newName = case lookup x renamings of
                         Just renamed -> renamed
                         Nothing -> x
          in RhoElim newName (substBatch renamings substitutions t1) (substBatch renamings substitutions t2) (go p1) (go p2) pos
        Iota t1 t2 pos -> Iota (substBatch renamings substitutions t1) (substBatch renamings substitutions t2) pos
        ConvIntro p pos -> ConvIntro (go p) pos
        ConvElim p pos -> ConvElim (go p) pos
        Pair p1 p2 pos -> Pair (go p1) (go p2) pos
        Pi p x y z q pos -> 
          let newX = case lookup x renamings of
                       Just renamed -> renamed
                       Nothing -> x
              newY = case lookup y renamings of
                       Just renamed -> renamed
                       Nothing -> y
              newZ = case lookup z renamings of
                       Just renamed -> renamed
                       Nothing -> z
          in Pi (go p) newX newY newZ (go q) pos
        PTheoremApp name args pos -> PTheoremApp name args pos
        PMacro name args pos -> PMacro name (map substMacroArg args) pos
          where substMacroArg = \case
                  MTerm t -> MTerm (substBatch renamings substitutions t)
                  MRel r -> MRel (substBatch renamings substitutions r)
                  MProof p -> MProof (go p)

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
  return $ substBatch [] termSubs term
  where
    termSubs = [(paramName, replacement) | (paramName, TermArg replacement) <- subs]

-- | Apply theorem argument substitutions to relation type using free variable substitution
applyTheoremFreeVarSubsToRType :: [(String, TheoremArg)] -> RType -> Either RelTTError RType
applyTheoremFreeVarSubsToRType subs rtype = 
  return $ substBatch [] termSubs (substBatch [] relSubs rtype)
  where
    relSubs = [(paramName, replacement) | (paramName, RelArg replacement) <- subs]
    termSubs = [(paramName, replacement) | (paramName, TermArg replacement) <- subs]

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

