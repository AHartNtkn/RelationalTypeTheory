{-# LANGUAGE LambdaCase #-}

-- | Environment management utilities for macros and theorems
module Environment
  ( extendMacroEnvironment
  , noMacros
  , noTheorems
  ) where

import qualified Data.Map as Map
import Control.Monad.State.Strict
import Data.List (foldl')
import Lib
import AST.Macro (inferParamInfosTerm, inferParamInfosRel, inferParamInfosProof)

-- | Insert / overwrite a macro together with its (possibly default)
--   fixity.  Used by the elaborator **and** by the test helper in
--   MixfixSpec.
extendMacroEnvironment
  :: String              -- ^ name  (mix‑fix or ordinary)
  -> [String]            -- ^ parameters
  -> MacroBody
  -> Fixity              -- ^ chosen fixity
  -> MacroEnvironment -> MacroEnvironment
extendMacroEnvironment n ps body fix env =
  let pInfo = case body of
                TermMacro tm  -> inferParamInfosTerm ps tm
                RelMacro  rt  -> inferParamInfosRel  ps rt
                ProofMacro pr -> inferParamInfosProof ps pr
  in env { macroDefinitions = Map.insert n (pInfo, body) (macroDefinitions env)
         , macroFixities    = Map.insert n fix            (macroFixities    env)
         }

-- | Empty environments used by tests.
noMacros :: MacroEnvironment
noMacros = MacroEnvironment Map.empty Map.empty

noTheorems :: TheoremEnvironment
noTheorems = TheoremEnvironment Map.empty