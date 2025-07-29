module Parser.Context
  ( ElaborateM
  , ElaborateContext(..)
  , bindTermVar
  , bindRelVar
  , bindProofVar
  ) where

import qualified Data.Map as Map
import Control.Monad.Reader
import Control.Monad.Except

import Core.Syntax
import Core.Errors

-- | Context for elaboration - contains macro and theorem environments
data ElaborateContext = ElaborateContext
  { macroEnv :: MacroEnvironment
  , theoremEnv :: TheoremEnvironment
  , termDepth :: Int  -- current lambda depth for terms
  , relDepth :: Int   -- current forall depth for relations
  , proofDepth :: Int -- current lambda depth for proofs
  , boundVars :: Map.Map String Int  -- variable name -> de Bruijn index (distance from binding site)
  , boundRelVars :: Map.Map String Int  -- relational variable name -> de Bruijn index
  , boundProofVars :: Map.Map String (Int, RelJudgment)  -- proof var -> (index, judgment)
  } deriving (Show, Eq)

-- | Elaboration monad
type ElaborateM = ReaderT ElaborateContext (Except RelTTError)

-- | Helper functions for context manipulation

-- | Shift all integers in a map by +1
shiftIntMap :: Map.Map k Int -> Map.Map k Int
shiftIntMap = Map.map (+1)

-- | Shift proof variable mappings by +1  
shiftProofMap :: Map.Map String (Int, RelJudgment) -> Map.Map String (Int, RelJudgment)
shiftProofMap = Map.map (\(i,j) -> (i+1,j))

-- | Bind a new term variable in the context
bindTermVar :: String -> ElaborateContext -> ElaborateContext
bindTermVar x ctx =
  ctx { boundVars = Map.insert x 0 (shiftIntMap (boundVars ctx))
      , termDepth = termDepth ctx + 1 }

-- | Bind a new relational variable in the context
bindRelVar :: String -> ElaborateContext -> ElaborateContext
bindRelVar r ctx =
  ctx { boundRelVars = Map.insert r 0 (shiftIntMap (boundRelVars ctx))
      , relDepth  = relDepth  ctx + 1 }

-- | Bind a new proof variable in the context
bindProofVar :: String -> RelJudgment -> ElaborateContext -> ElaborateContext
bindProofVar p j ctx =
  ctx { boundProofVars = Map.insert p (0,j) (shiftProofMap (boundProofVars ctx))
      , proofDepth = proofDepth ctx + 1 }