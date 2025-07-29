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
import Core.Environment (extendMacroEnvironmentWithParams, noMacros)
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

-- | Helper to create simple ParamInfo for non-cross-category macros
simpleParams :: VarKind -> [String] -> [ParamInfo]
simpleParams kind names = [ParamInfo n kind False [] | n <- names]

-- | Built-in macro bodies with parameter lists
builtinMacroBodies :: [(String, [ParamInfo], MacroBody)]
builtinMacroBodies =
  [ ("λ_._"       , [ParamInfo "x" TermK True [], ParamInfo "t" TermK False [0]]     , TermMacro $ Lam "x" (Var "t" 0 dummyPos) dummyPos)
  , ("∀_._"       , [ParamInfo "X" RelK True [], ParamInfo "T" RelK False [0]]       , RelMacro $ All "X" (RVar "T" 0 dummyPos) dummyPos)
  , ("_˘"         , simpleParams RelK ["R"]           , RelMacro $ Conv (RVar "R" 0 dummyPos) dummyPos)
  , ("_∘_"        , simpleParams RelK ["R","S"]       , RelMacro $ Comp (RVar "R" 1 dummyPos) (RVar "S" 0 dummyPos) dummyPos)
  , ("_→_"        , simpleParams RelK ["A","B"]       , RelMacro $ Arr (RVar "A" 1 dummyPos) (RVar "B" 0 dummyPos) dummyPos)
  , ("ι⟨_,_⟩"     , simpleParams TermK ["t1","t2"]    , ProofMacro $ Iota (Var "t1" 1 dummyPos) (Var "t2" 0 dummyPos) dummyPos)
  , ("_,_"        , simpleParams ProofK ["p","q"]     , ProofMacro $ Pair (PVar "p" 1 dummyPos) (PVar "q" 0 dummyPos) dummyPos)
  , ("λ_:_._"     , [ParamInfo "x" TermK True [], ParamInfo "T" RelK False [], ParamInfo "p" ProofK False [0]]  , ProofMacro $ LamP "x" (RVar "T" 1 dummyPos) (PVar "p" 0 dummyPos) dummyPos)
  , ("Λ_._"       , [ParamInfo "X" RelK True [], ParamInfo "p" ProofK False [0]]      , ProofMacro $ TyLam "X" (PVar "p" 0 dummyPos) dummyPos)
  , ("_{_}"       , [ParamInfo "p" ProofK False [], ParamInfo "R" RelK False []]      , ProofMacro $ TyApp (PVar "p" 1 dummyPos) (RVar "R" 0 dummyPos) dummyPos)
  , ("_⇃_⇂_"      , [ParamInfo "t1" TermK False [], ParamInfo "p" ProofK False [], ParamInfo "t2" TermK False []], ProofMacro $ ConvProof (Var "t1" 2 dummyPos) (PVar "p" 1 dummyPos) (Var "t2" 0 dummyPos) dummyPos)
  , ("π_-_._._._" , [ParamInfo "p" ProofK False [], ParamInfo "x" TermK True [], ParamInfo "u" ProofK True [1], ParamInfo "v" ProofK True [1], ParamInfo "q" ProofK False [1,2,3]], ProofMacro $ Pi (PVar "p" 4 dummyPos) "x" "u" "v" (PVar "q" 0 dummyPos) dummyPos)
  ]

-- | Create a macro environment with all built-in macros
macroEnvWithBuiltins :: MacroEnvironment
macroEnvWithBuiltins =
  foldl' (\e (n,params,b) ->
            let fx = fromMaybe (defaultFixity n) (lookup n builtinFixities)
                result = extendMacroEnvironmentWithParams n params b fx e
            in  result)
         noMacros
         builtinMacroBodies