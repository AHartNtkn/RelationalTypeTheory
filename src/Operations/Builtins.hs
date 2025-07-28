-- | Built-in macros and fixities for the RelTT language
-- This module contains all the built-in syntactic sugar macros that provide
-- convenient notation for common RelTT constructs.
module Operations.Builtins
  ( builtinFixities
  , builtinMacroBodies
  , macroEnvWithBuiltins
  ) where

import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Core.Syntax
import Core.Environment (extendMacroEnvironment, noMacros)
import Parser.Mixfix (defaultFixity)
import Core.Raw (dummyPos)

-- | Authoritative fixities for the built‑in macros
builtinFixities :: [(String,Fixity)]
builtinFixities =
  [ ("∀_._"        , Prefix  4)   -- quantifier  (prefix, closes with '.')
  , ("λ_._"        , Prefix  4)
  , ("Λ_._"        , Prefix  4)
  , ("λ_:_._"      , Prefix  4)
  , ("_{_}"        , Postfix 4)   -- type application
  , ("_˘"          , Postfix 8)   -- converse
  , ("_∘_"         , Infixr  6)   -- composition
  , ("_→_"         , Infixr  2)   -- function arrow
  , ("ι⟨_,_⟩"      , Prefix  7)   -- iota
  , ("_,_"         , Infixr  1)
  , ("_⇃_⇂_"       , Prefix  4)
  , ("π_-_._._._"  , Prefix  4)
  ]

-- | Built-in macro bodies with parameter lists
builtinMacroBodies :: [(String, [String], MacroBody)]
builtinMacroBodies =
  [ ("λ_._"       , ["x","t"]      , TermMacro $ Lam "x" (Var "t" 0 dummyPos) dummyPos)
  , ("∀_._"       , ["X","T"]      , RelMacro $ All "X" (RVar "T" 0 dummyPos) dummyPos)
  , ("_˘"         , ["R"]          , RelMacro $ Conv (RVar "R" 0 dummyPos) dummyPos)
  , ("_∘_"        , ["R","S"]      , RelMacro $ Comp (RVar "R" 1 dummyPos) (RVar "S" 0 dummyPos) dummyPos)
  , ("_→_"        , ["A","B"]      , RelMacro $ Arr (RVar "A" 1 dummyPos) (RVar "B" 0 dummyPos) dummyPos)
  , ("ι⟨_,_⟩"     , ["t1","t2"]    , ProofMacro $ Iota (Var "t1" 1 dummyPos) (Var "t2" 0 dummyPos) dummyPos)
  , ("_,_"        , ["p","q"]      , ProofMacro $ Pair (PVar "p" 1 dummyPos) (PVar "q" 0 dummyPos) dummyPos)
  , ("λ_:_._"     , ["x","T","p"]  , ProofMacro $ LamP "x" (RVar "T" 1 dummyPos) (PVar "p" 0 dummyPos) dummyPos)
  , ("Λ_._"       , ["X","p"]      , ProofMacro $ TyLam "X" (PVar "p" 0 dummyPos) dummyPos)
  , ("_{_}"       , ["p","R"]      , ProofMacro $ TyApp (PVar "p" 1 dummyPos) (RVar "R" 0 dummyPos) dummyPos)
  , ("_⇃_⇂_"      , ["t1","p","t2"], ProofMacro $ ConvProof (Var "t1" 2 dummyPos) (PVar "p" 1 dummyPos) (Var "t2" 0 dummyPos) dummyPos)
  , ("π_-_._._._" , ["p","x","u","v","q"], ProofMacro $ Pi (PVar "p" 4 dummyPos) "x" "u" "v" (PVar "q" 0 dummyPos) dummyPos)
  ]

-- | Create a macro environment with all built-in macros
macroEnvWithBuiltins :: MacroEnvironment
macroEnvWithBuiltins =
  foldl' (\e (n,ps,b) ->
            let fx = fromMaybe (defaultFixity n) (lookup n builtinFixities)
                result = extendMacroEnvironment n ps b fx e
            in  result)
         noMacros
         builtinMacroBodies