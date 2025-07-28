{-# LANGUAGE LambdaCase #-}

-- | Unified, binder-aware macro application for Term, RType and Proof.
-- This module provides a generic infrastructure that eliminates code duplication
-- across the three AST categories while maintaining identical public APIs.

module Generic.Macro
  ( -- | Typeclass for generic macro operations
    MacroAst(..)
    -- | Generic helper algorithms
  , renameBinderVarsG
  , substituteArgsG
    -- | Top-level elaborator for all AST categories
  , elabMacroAppG
  ) where

import           Text.Megaparsec                (initialPos)
import           Errors
import           Lib
import           Generic.Shift (ShiftAst(..), shift, shiftAbove)

--------------------------------------------------------------------------------
-- | Minimal operations that any AST category must provide for macro processing
--------------------------------------------------------------------------------

class MacroAst a where
  -- | de Bruijn shift free variables by given amount
  shiftN      :: Int -> a -> a
  -- | Capture-avoiding substitution [arg/index]body (total function)
  substIndex  :: Int -> a -> a -> a
  -- | Extract variable name if this node is a variable, Nothing otherwise
  varNameOf   :: a -> Maybe String
  -- | Rename binder variable names (α-conversion only, indices untouched)
  mapBinders  :: (String -> String) -> a -> a


--------------------------------------------------------------------------------
-- | Term instance
--------------------------------------------------------------------------------

instance MacroAst Term where
  shiftN           = shift
  substIndex = substIndex  -- Use the generic implementation
  varNameOf (Var v _ _) = Just v
  varNameOf _           = Nothing
  mapBinders f = go
    where
      go tm = case tm of
        Lam n b p      -> Lam (f n) (go b) p
        App l r p      -> App (go l) (go r) p
        TMacro n as p  -> TMacro n (map go as) p
        other          -> other

--------------------------------------------------------------------------------
-- | Relational type instance  
--------------------------------------------------------------------------------

instance MacroAst RType where
  shiftN           = shiftAbove 0
  substIndex targetIndex s body = go 0 body
    where
      -- go d τ  ::  τ under d enclosing binders
      go :: Int -> RType -> RType
      go d ty = case ty of
        RVar y k p
          | k == d + targetIndex -> -- bound occurrence at target index
              shiftAbove d 1 s -- put 's' under the d binders
          | k > d + targetIndex -> RVar y (k - 1) p -- bypass the deleted binder
          | otherwise -> ty -- untouched
        All y t p -> All y (go (d + 1) t) p -- enter another binder
        Arr a b p -> Arr (go d a) (go d b) p
        Comp a b p -> Comp (go d a) (go d b) p
        Conv r p -> Conv (go d r) p
        RMacro n as p -> RMacro n (map (go d) as) p
        Prom t p -> Prom t p -- terms unchanged
  varNameOf (RVar v _ _) = Just v
  varNameOf _            = Nothing
  mapBinders f = go
    where
      go rt = case rt of
        All n b p      -> All (f n) (go b) p
        Arr a b p      -> Arr (go a) (go b) p
        Comp a b p     -> Comp (go a) (go b) p
        Conv r p       -> Conv (go r) p
        RMacro n as p  -> RMacro n (map go as) p
        other          -> other

--------------------------------------------------------------------------------
-- | Proof instance with complete capture-avoiding substitution
--------------------------------------------------------------------------------

-- | Capture-avoiding substitution [s/n]body for proof terms
substProofIndex :: Int -> Proof -> Proof -> Proof
substProofIndex n s = sub 0
  where
    sub lvl pr = case pr of
      PVar v k p
        | k == lvl + n -> shiftAbove lvl 1 s
        | k >  lvl + n -> PVar v (k - 1) p
        | otherwise    -> pr
      LamP v t b p     -> LamP v t (sub (lvl+1) b) p
      AppP l r p       -> AppP (sub lvl l) (sub lvl r) p
      TyLam v b p      -> TyLam v (sub lvl b) p
      TyApp q t p      -> TyApp (sub lvl q) t p
      ConvProof t q u p -> ConvProof t (sub lvl q) u p
      ConvIntro q p    -> ConvIntro (sub lvl q) p
      ConvElim  q p    -> ConvElim  (sub lvl q) p
      Pair l r p       -> Pair (sub lvl l) (sub lvl r) p
      RhoElim x t u p1 p2 p -> RhoElim x t u (sub lvl p1) (sub lvl p2) p
      Pi p1 x u v p2 p      -> Pi (sub lvl p1) x u v (sub (lvl+3) p2) p
      PMacro n as p    -> PMacro n (map (sub lvl) as) p
      PTheoremApp n as p -> PTheoremApp n as p
      Iota t1 t2 p     -> Iota t1 t2 p

instance MacroAst Proof where
  shiftN      = shift
  substIndex  = substProofIndex
  varNameOf (PVar v _ _) = Just v
  varNameOf _            = Nothing
  mapBinders f = go
    where
      go pr = case pr of
        LamP n t b p          -> LamP (f n) t (go b) p
        TyLam n b p           -> TyLam (f n) (go b) p
        RhoElim x t u p1 p2 p -> RhoElim (f x) t u (go p1) (go p2) p
        Pi p1 x u v p2 p      -> Pi (go p1) (f x) (f u) (f v) (go p2) p
        AppP l r p            -> AppP (go l) (go r) p
        TyApp q t p           -> TyApp (go q) t p
        ConvProof t q u p     -> ConvProof t (go q) u p
        ConvIntro q p         -> ConvIntro (go q) p
        ConvElim  q p         -> ConvElim  (go q) p
        Pair l r p            -> Pair (go l) (go r) p
        PMacro n as p         -> PMacro n (map go as) p
        other                 -> other

--------------------------------------------------------------------------------
-- | Generic helper functions
--------------------------------------------------------------------------------

-- | Count how many parameter binders occur to the left of index j
binderPrefixCount :: [ParamInfo] -> Int -> Int
binderPrefixCount sig j =
  length [ () | (k,ParamInfo{pBinds=True}) <- zip [0..] sig, k < j ]

-- | α-rename each binder parameter to the printed name of its actual argument
renameBinderVarsG :: MacroAst a => [ParamInfo] -> [a] -> a -> a
renameBinderVarsG sig actuals =
  let renameOne acc (j,ParamInfo{pBinds=True}) =
        case varNameOf (actuals !! j) of
          Just new -> mapBinders (\n -> if n == pName (sig!!j) then new else n) acc
          Nothing  -> error "binder argument must be a variable"
      renameOne acc _ = acc
  in  \body -> foldl renameOne body (zip [0..] sig)

-- | Positional substitution for value parameters (capture-avoiding, index-based)
substituteArgsG :: MacroAst a => [ParamInfo] -> [a] -> a -> a
substituteArgsG sig actuals =
  let doOne acc (j,pi,arg)
        | pBinds pi = acc
        | otherwise =
            let k     = binderPrefixCount sig j
                arg'  = shiftN k arg
                idx   = length sig - 1 - j
            in  substIndex idx arg' acc
  in  \body -> foldl doOne body (zip3 [0..] sig actuals)

--------------------------------------------------------------------------------
-- | Top-level macro elaborator (used by Elaborate.hs)
--------------------------------------------------------------------------------

elabMacroAppG
  :: (MacroAst a)
  => MacroEnvironment
  -> String              -- ^ macro name
  -> [ParamInfo]         -- ^ signature from environment
  -> a                   -- ^ stored macro body
  -> [a]                 -- ^ elaborated actual arguments
  -> Either RelTTError a
elabMacroAppG env name sig body actuals
  | length sig /= length actuals =
      Left $ MacroArityMismatch name (length sig) (length actuals)
             (ErrorContext (initialPos "<elab>") "macro application")
  | otherwise =
      let body1 = renameBinderVarsG sig actuals body
          body2 = substituteArgsG   sig actuals body1
      in  Right body2