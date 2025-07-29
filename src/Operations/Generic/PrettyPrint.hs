{-# LANGUAGE LambdaCase #-}

-- | Generic pretty printing infrastructure for all AST types.
-- This module provides a unified interface for pretty printing Terms, RTypes, and Proofs
-- while eliminating code duplication and maintaining consistent formatting.

module Operations.Generic.PrettyPrint
  ( -- * Typeclass
    PrettyAst(..)
    -- * Configuration
  , PrettyConfig(..)
  , defaultPrettyConfig
    -- * Generic operations
  , prettyWithConfig
  , prettyDefault
  , prettyWithParens
    -- * Common formatting utilities
  , formatVariable
  , formatBinder
  , formatApplication
  , chooseSymbol
  ) where

import Core.Syntax
import Data.List (intercalate)

-- | MacroArg pretty printing instance
instance PrettyAst MacroArg where
  prettyWithConfigCore config = \case
    MTerm t -> prettyWithConfigCore config t
    MRel r -> prettyWithConfigCore config r  
    MProof p -> prettyWithConfigCore config p
    
  needsParens = \case
    MTerm t -> needsParens t
    MRel r -> needsParens r
    MProof p -> needsParens p

-- | Configuration for pretty printing
data PrettyConfig = PrettyConfig
  { useUnicode :: Bool,
    showIndices :: Bool,
    indentSize :: Int,
    lineWidth :: Int
  }
  deriving (Show, Eq)

defaultPrettyConfig :: PrettyConfig
defaultPrettyConfig =
  PrettyConfig
    { useUnicode = True,
      showIndices = False,
      indentSize = 2,
      lineWidth = 80
    }

--------------------------------------------------------------------------------
-- | Core typeclass for pretty printing
--------------------------------------------------------------------------------

class PrettyAst a where
  -- | Pretty print with configuration
  prettyWithConfigCore :: PrettyConfig -> a -> String
  
  -- | Determine if parentheses are needed in a given context
  needsParens :: a -> Bool

--------------------------------------------------------------------------------
-- | Generic operations
--------------------------------------------------------------------------------

-- | Pretty print with configuration
prettyWithConfig :: PrettyAst a => PrettyConfig -> a -> String
prettyWithConfig = prettyWithConfigCore

-- | Pretty print with default configuration
prettyDefault :: PrettyAst a => a -> String
prettyDefault = prettyWithConfig defaultPrettyConfig

-- | Add parentheses if needed
prettyWithParens :: PrettyAst a => PrettyConfig -> a -> String
prettyWithParens config ast
  | needsParens ast = "(" ++ prettyWithConfig config ast ++ ")"
  | otherwise = prettyWithConfig config ast

--------------------------------------------------------------------------------
-- | Common formatting utilities
--------------------------------------------------------------------------------

-- | Format a variable name with optional de Bruijn index
formatVariable :: PrettyConfig -> String -> Int -> String
formatVariable config name idx
  | showIndices config = name ++ "_" ++ show idx
  | otherwise = name

-- | Format a binder construct (lambda, forall, etc.)
formatBinder :: PrettyConfig -> String -> String -> String -> String -> String
formatBinder config unicodeSymbol asciiSymbol binderName body =
  let symbol = chooseSymbol config unicodeSymbol asciiSymbol
  in symbol ++ binderName ++ ". " ++ body

-- | Format a function application
formatApplication :: PrettyConfig -> String -> String -> String
formatApplication _config func arg = func ++ " " ++ arg

-- | Choose between Unicode and ASCII symbol based on configuration
chooseSymbol :: PrettyConfig -> String -> String -> String
chooseSymbol config unicode ascii
  | useUnicode config = unicode
  | otherwise = ascii

--------------------------------------------------------------------------------
-- | Instance for Term
--------------------------------------------------------------------------------

instance PrettyAst Term where
  prettyWithConfigCore config = \case
    Var name idx _ -> formatVariable config name idx
    FVar name _ -> name                 -- Free variables just show their name
    
    Lam name body _ -> 
      let lambda = chooseSymbol config "λ" "\\"
          bodyStr = prettyWithConfig config body
      in lambda ++ name ++ ". " ++ bodyStr
    
    App t1 t2 _ ->
      let t1' = case t1 of
            Lam _ _ _ -> "(" ++ prettyWithConfig config t1 ++ ")"
            _ -> prettyWithConfig config t1
          t2' = prettyWithParens config t2
      in formatApplication config t1' t2'
    
    TMacro name args _ 
      | null args -> name
      | otherwise -> name ++ " " ++ intercalate " " (map (prettyWithParens config) args)

  needsParens = \case
    Lam _ _ _ -> True
    App _ _ _ -> True
    _ -> False

--------------------------------------------------------------------------------
-- | Instance for RType
--------------------------------------------------------------------------------

instance PrettyAst RType where
  prettyWithConfigCore config = \case
    RVar name idx _ -> formatVariable config name idx
    FRVar name _ -> name                -- Free variables just show their name
    
    RMacro name args _ 
      | null args -> name
      | otherwise -> name ++ " " ++ intercalate " " (map (prettyWithParens config) args)
    
    Arr r1 r2 _ ->
      let arrow = chooseSymbol config "→" "->"
          r1' = prettyWithParens config r1
          r2' = prettyWithConfig config r2
      in r1' ++ " " ++ arrow ++ " " ++ r2'
    
    All name body _ ->
      let forallSym = chooseSymbol config "∀" "forall"
          bodyStr = prettyWithConfig config body
      in formatBinder config forallSym "forall" name bodyStr
    
    Comp r1 r2 _ ->
      let comp = chooseSymbol config "∘" "o"
          r1' = prettyWithParens config r1
          r2' = prettyWithParens config r2
      in r1' ++ " " ++ comp ++ " " ++ r2'
    
    Conv r _ ->
      let conv = chooseSymbol config "˘" "^"
          r' = prettyWithParens config r
      in r' ++ conv
    
    Prom t _ -> prettyWithConfig config t -- Hide promotion from user

  needsParens = \case
    Arr _ _ _ -> True
    All _ _ _ -> True
    Comp _ _ _ -> True
    Prom (Lam _ _ _) _ -> True
    _ -> False

--------------------------------------------------------------------------------
-- | Instance for Proof
--------------------------------------------------------------------------------

instance PrettyAst Proof where
  prettyWithConfigCore config = \case
    PVar name idx _ -> formatVariable config name idx
    FPVar name _ -> name                -- Free variables just show their name
    
    PTheoremApp name args _ 
      | null args -> name
      | otherwise -> name ++ " " ++ unwords (map (prettyTheoremArgG config) args)
    
    LamP name rtype body _ ->
      let lambda = chooseSymbol config "λ" "\\"
          rtypeStr = prettyWithConfig config rtype
          bodyStr = prettyWithConfig config body
      in lambda ++ name ++ ":" ++ rtypeStr ++ ". " ++ bodyStr
    
    AppP p1 p2 _ ->
      let p1' = prettyWithParens config p1
          p2' = prettyWithParens config p2
      in formatApplication config p1' p2'
    
    TyLam name body _ ->
      let lambda = chooseSymbol config "Λ" "Lambda"
          bodyStr = prettyWithConfig config body
      in lambda ++ name ++ ". " ++ bodyStr
    
    TyApp p rtype _ ->
      let p' = prettyWithParens config p
          r' = prettyWithConfig config rtype
      in p' ++ "{" ++ r' ++ "}"
    
    Iota t1 t2 _ ->
      let iota = chooseSymbol config "ι" "iota"
          t1' = prettyWithConfig config t1
          t2' = prettyWithConfig config t2
      in iota ++ "⟨" ++ t1' ++ ", " ++ t2' ++ "⟩"
    
    ConvProof t1 p t2 _ ->
      let t1' = prettyWithConfig config t1
          p' = prettyWithConfig config p
          t2' = prettyWithConfig config t2
      in t1' ++ " ⇃ " ++ p' ++ " ⇂ " ++ t2'
    
    RhoElim binding1 term1 term2 proof1 proof2 _ ->
      let rho = chooseSymbol config "ρ" "rho"
          t1' = prettyWithConfig config term1
          t2' = prettyWithConfig config term2
          p1' = prettyWithConfig config proof1
          p2' = prettyWithConfig config proof2
      in rho ++ "{" ++ binding1 ++ "." ++ t1' ++ ", " ++ t2' ++ "} " ++ p1' ++ " - " ++ p2'
    
    Pi p1 x u v p2 _ ->
      let piSymbol = chooseSymbol config "π" "pi"
          p1' = prettyWithConfig config p1
          p2' = prettyWithConfig config p2
          bindingStr = x ++ "." ++ u ++ "." ++ v
      in piSymbol ++ " " ++ p1' ++ " - " ++ bindingStr ++ "." ++ p2'
    
    ConvIntro p _ ->
      let unionI = chooseSymbol config "∪ᵢ" "unionI"
          p' = prettyWithConfig config p
      in unionI ++ " " ++ p'
    
    ConvElim p _ ->
      let unionE = chooseSymbol config "∪ₑ" "unionE"
          p' = prettyWithConfig config p
      in unionE ++ " " ++ p'
    
    Pair p1 p2 _ ->
      let p1' = prettyWithConfig config p1
          p2' = prettyWithConfig config p2
      in "⟨" ++ p1' ++ ", " ++ p2' ++ "⟩"
    
    PMacro name args _ 
      | null args -> name
      | otherwise -> name ++ " " ++ intercalate " " (map (prettyWithParens config) args)

  needsParens = \case
    LamP _ _ _ _ -> True
    AppP _ _ _ -> True
    TyLam _ _ _ -> True
    RhoElim _ _ _ _ _ _ -> True
    Pi _ _ _ _ _ _ -> True
    ConvProof _ _ _ _ -> True
    _ -> False

--------------------------------------------------------------------------------
-- | Helper for theorem arguments (to avoid circular imports)
--------------------------------------------------------------------------------

prettyTheoremArgG :: PrettyConfig -> TheoremArg -> String
prettyTheoremArgG config = \case
  TermArg t -> prettyWithConfig config t
  RelArg r -> prettyWithConfig config r  
  ProofArg p -> prettyWithConfig config p