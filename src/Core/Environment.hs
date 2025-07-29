{-# LANGUAGE LambdaCase #-}

-- | Environment management utilities for macros and theorems
module Core.Environment
  ( extendMacroEnvironment
  , extendMacroEnvironmentWithParams
  , noMacros
  , noTheorems
  ) where

import qualified Data.Map as Map
import Core.Syntax
import Operations.Generic.Macro (inferParamInfosG)

-- | Insert / overwrite a macro together with its (possibly default)
--   fixity.  Used by the elaborator **and** by the test helper in
--   MixfixSpec.
extendMacroEnvironment
  :: String              -- ^ name  (mix‑fix or ordinary)
  -> [String]            -- ^ parameters
  -> MacroBody
  -> Fixity              -- ^ chosen fixity
  -> MacroEnvironment -> MacroEnvironment
extendMacroEnvironment n ps body fixity env =
  let pInfo = case body of
                TermMacro tm  -> inferParamInfosG ps tm
                RelMacro  rt  -> inferParamInfosG ps rt
                ProofMacro pr -> inferParamInfosG ps pr
  in env { macroDefinitions = Map.insert n (pInfo, body) (macroDefinitions env)
         , macroFixities    = Map.insert n fixity            (macroFixities    env)
         }

-- | Extend macro environment with explicit parameter info (for cross-category macros)
extendMacroEnvironmentWithParams
  :: String              -- ^ name
  -> [ParamInfo]         -- ^ explicit parameter info
  -> MacroBody
  -> Fixity
  -> MacroEnvironment -> MacroEnvironment
extendMacroEnvironmentWithParams n pInfo body fixity env =
  env { macroDefinitions = Map.insert n (pInfo, body) (macroDefinitions env)
      , macroFixities    = Map.insert n fixity (macroFixities env)
      }

-- | Empty environments used by tests.
noMacros :: MacroEnvironment
noMacros = MacroEnvironment Map.empty Map.empty

noTheorems :: TheoremEnvironment
noTheorems = TheoremEnvironment Map.empty