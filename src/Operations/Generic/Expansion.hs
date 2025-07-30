{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

-- | Generic macro expansion infrastructure for all AST types.
-- This module provides a unified interface for expanding macros in Terms and RTypes.

module Operations.Generic.Expansion
  ( -- * Typeclass
    ExpandAst(..)
    -- * Expansion modes
  , ExpansionMode(..)
    -- * Result types
  , ExpansionResult(..)
    -- * Generic operations
  , expandWithLimit
  , expandFully
  , expandWHNF
  ) where

import qualified Data.Map as Map
import Core.Syntax
import Core.Errors (RelTTError(..), ErrorContext(..))
import Text.Megaparsec (initialPos, SourcePos)
import Operations.Generic.Macro (MacroAst(..), elabMacroAppG)
import Operations.Resolve (ResolveAst)

--------------------------------------------------------------------------------
-- | Expansion modes
--------------------------------------------------------------------------------

data ExpansionMode = FullExpansion | WeakHeadExpansion
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- | Generic expansion result
--------------------------------------------------------------------------------

data ExpansionResult a = ExpansionResult
  { expandedValue :: a
  , expansionSteps :: Int
  , wasExpanded :: Bool
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- | Core typeclass for macro expansion
--------------------------------------------------------------------------------

class (MacroAst a, ResolveAst a) => ExpandAst a where
  -- | Associated type for macro bodies
  type MacroBodyType a
  
  -- | Extract macro name and arguments if this is a macro application
  getMacroApp :: a -> Maybe (String, [a], SourcePos)
  
  -- | Construct a macro application node
  mkMacroApp :: String -> [a] -> SourcePos -> a
  
  -- | Check if a macro body has the right type for this AST
  isRightBody :: MacroBody -> Maybe (MacroBodyType a)
  
  -- | Convert macro body to AST after substitution
  bodyToAst :: MacroBodyType a -> a
  
  -- | Expand recursively into subterms (for full expansion)
  expandSubterms :: Context -> ExpansionMode -> a -> Either RelTTError a

--------------------------------------------------------------------------------
-- | Generic operations
--------------------------------------------------------------------------------

-- | Expand with step limit
expandWithLimit :: ExpandAst a => Context -> ExpansionMode -> Int -> a -> Either RelTTError (ExpansionResult a)
expandWithLimit env mode maxSteps ast = 
  if maxSteps <= 0
    then Left $ InternalError "Macro expansion step limit exceeded" (ErrorContext (initialPos "<expansion>") "expansion")
    else expandStep env mode maxSteps 0 ast

-- | Fully expand all macros
expandFully :: ExpandAst a => Context -> a -> Either RelTTError (ExpansionResult a)
expandFully env = expandWithLimit env FullExpansion 1000

-- | Expand to weak head normal form
expandWHNF :: ExpandAst a => Context -> a -> Either RelTTError (ExpansionResult a)
expandWHNF env = expandWithLimit env WeakHeadExpansion 1000

--------------------------------------------------------------------------------
-- | Internal expansion logic
--------------------------------------------------------------------------------

expandStep :: forall a. ExpandAst a => Context -> ExpansionMode -> Int -> Int -> a -> Either RelTTError (ExpansionResult a)
expandStep env mode remainingSteps stepsSoFar ast = 
  case getMacroApp ast of
    Just (name, args, pos) ->
      case Map.lookup name (macroDefinitions env) of
        Nothing -> 
          -- Not a macro, but might need to expand subterms
          case mode of
            FullExpansion -> do
              expanded <- expandSubterms env mode ast
              return $ ExpansionResult expanded stepsSoFar False
            WeakHeadExpansion ->
              return $ ExpansionResult ast stepsSoFar False
        
        Just (paramInfo, macroBody) ->
          case isRightBody @a macroBody of
            Nothing -> 
              Left $ InternalError ("Wrong macro body type for " ++ name) (ErrorContext pos "expansion")
            Just body -> do
              -- Expand arguments if needed
              expandedArgs <- case mode of
                FullExpansion -> mapM (expandFully env) args >>= return . map expandedValue
                WeakHeadExpansion -> return args
              
              -- Use elabMacroAppG for substitution (single source of truth for arity checking)
              substituted <- case elabMacroAppG env name paramInfo (bodyToAst @a body) expandedArgs of
                Right result -> return result
                Left err -> Left err
              
              -- Continue expansion
              if remainingSteps <= 1
                then Left $ InternalError "Macro expansion step limit exceeded" (ErrorContext pos "expansion")
                else expandStep env mode (remainingSteps - 1) (stepsSoFar + 1) substituted
    
    Nothing ->
      -- Not a macro application
      case mode of
        FullExpansion -> do
          expanded <- expandSubterms env mode ast
          return $ ExpansionResult expanded stepsSoFar (stepsSoFar > 0)
        WeakHeadExpansion ->
          return $ ExpansionResult ast stepsSoFar (stepsSoFar > 0)

--------------------------------------------------------------------------------
-- | Instance for Term
--------------------------------------------------------------------------------

instance ExpandAst Term where
  type MacroBodyType Term = Term
  
  getMacroApp (TMacro name args pos) = Just (name, [t | MTerm t <- args], pos)
  getMacroApp _ = Nothing
  
  mkMacroApp name termArgs pos = TMacro name (map MTerm termArgs) pos
  
  isRightBody (TermMacro body) = Just body
  isRightBody _ = Nothing
  
  bodyToAst = id
  
  expandSubterms env mode term = case term of
    Var _ _ _ -> Right term
    FVar _ _ -> Right term               -- Free variables don't expand
    Lam name body pos -> do
      expandedBody <- expandWithLimit env mode 1000 body
      return $ Lam name (expandedValue expandedBody) pos
    App t1 t2 pos -> do
      exp1 <- expandWithLimit env mode 1000 t1
      exp2 <- expandWithLimit env mode 1000 t2
      return $ App (expandedValue exp1) (expandedValue exp2) pos
    TMacro _ _ _ -> Right term  -- Already handled by main logic

--------------------------------------------------------------------------------
-- | Instance for RType
--------------------------------------------------------------------------------

instance ExpandAst RType where
  type MacroBodyType RType = RType
  
  getMacroApp (RMacro name args pos) = Just (name, [r | MRel r <- args], pos)
  getMacroApp _ = Nothing
  
  mkMacroApp name relArgs pos = RMacro name (map MRel relArgs) pos
  
  isRightBody (RelMacro body) = Just body
  isRightBody _ = Nothing
  
  bodyToAst = id
  
  expandSubterms env mode rtype = case rtype of
    RVar _ _ _ -> Right rtype
    FRVar _ _ -> Right rtype             -- Free relation variables don't expand
    RMacro _ _ _ -> Right rtype  -- Already handled by main logic
    Arr r1 r2 pos -> do
      exp1 <- expandWithLimit env mode 1000 r1
      exp2 <- expandWithLimit env mode 1000 r2
      return $ Arr (expandedValue exp1) (expandedValue exp2) pos
    All name r pos -> do
      expResult <- expandWithLimit env mode 1000 r
      return $ All name (expandedValue expResult) pos
    Conv r pos -> do
      expResult <- expandWithLimit env mode 1000 r
      return $ Conv (expandedValue expResult) pos
    Comp r1 r2 pos -> do
      exp1 <- expandWithLimit env mode 1000 r1
      exp2 <- expandWithLimit env mode 1000 r2
      return $ Comp (expandedValue exp1) (expandedValue exp2) pos
    Prom term pos -> 
      -- For now, don't expand terms inside promotions
      Right rtype

--------------------------------------------------------------------------------
-- | Instance for Proof
--------------------------------------------------------------------------------

instance ExpandAst Proof where
  type MacroBodyType Proof = Proof
  
  getMacroApp (PMacro name args pos) = Just (name, [p | MProof p <- args], pos)
  getMacroApp _ = Nothing
  
  mkMacroApp name proofArgs pos = PMacro name (map MProof proofArgs) pos
  
  isRightBody (ProofMacro body) = Just body
  isRightBody _ = Nothing
  
  bodyToAst = id
  
  expandSubterms env mode proof = case proof of
    PVar _ _ _ -> Right proof
    FPVar _ _ -> Right proof             -- Free proof variables don't expand
    PTheoremApp _ _ _ -> Right proof  -- Theorem applications don't expand
    Iota _ _ _ -> Right proof  -- Terms in iota don't expand
    PMacro _ _ _ -> Right proof  -- Already handled by main logic
    LamP name rtype body pos -> do
      expandedBody <- expandWithLimit env mode 1000 body
      return $ LamP name rtype (expandedValue expandedBody) pos
    AppP p1 p2 pos -> do
      exp1 <- expandWithLimit env mode 1000 p1
      exp2 <- expandWithLimit env mode 1000 p2
      return $ AppP (expandedValue exp1) (expandedValue exp2) pos
    TyLam name body pos -> do
      expandedBody <- expandWithLimit env mode 1000 body
      return $ TyLam name (expandedValue expandedBody) pos
    TyApp p rtype pos -> do
      expResult <- expandWithLimit env mode 1000 p
      return $ TyApp (expandedValue expResult) rtype pos
    ConvProof t1 p t2 pos -> do
      expResult <- expandWithLimit env mode 1000 p
      return $ ConvProof t1 (expandedValue expResult) t2 pos
    ConvIntro p pos -> do
      expResult <- expandWithLimit env mode 1000 p
      return $ ConvIntro (expandedValue expResult) pos
    ConvElim p pos -> do
      expResult <- expandWithLimit env mode 1000 p
      return $ ConvElim (expandedValue expResult) pos
    RhoElim x t1 t2 p1 p2 pos -> do
      exp1 <- expandWithLimit env mode 1000 p1
      exp2 <- expandWithLimit env mode 1000 p2
      return $ RhoElim x t1 t2 (expandedValue exp1) (expandedValue exp2) pos
    Pair p1 p2 pos -> do
      exp1 <- expandWithLimit env mode 1000 p1
      exp2 <- expandWithLimit env mode 1000 p2
      return $ Pair (expandedValue exp1) (expandedValue exp2) pos
    Pi p1 x u v p2 pos -> do
      exp1 <- expandWithLimit env mode 1000 p1
      exp2 <- expandWithLimit env mode 1000 p2
      return $ Pi (expandedValue exp1) x u v (expandedValue exp2) pos

-- | ExpandAst instance for MacroArg
instance ExpandAst MacroArg where
  type MacroBodyType MacroArg = MacroArg
  
  -- MacroArgs are not themselves macro applications
  getMacroApp _ = Nothing
  
  -- This should never be called since MacroArgs don't have macros
  mkMacroApp _ _ _ = error "MacroArg cannot be a macro application"
  
  -- This should never be called since MacroArgs don't expand
  isRightBody _ = Nothing
  
  -- Identity conversion 
  bodyToAst = id
  
  -- Delegate expansion to the wrapped type
  expandSubterms env mode = \case
    MTerm t -> MTerm <$> expandSubterms env mode t
    MRel r -> MRel <$> expandSubterms env mode r
    MProof p -> MProof <$> expandSubterms env mode p