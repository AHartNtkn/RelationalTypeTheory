module Parser.Context
  ( ElaborateM
  , ElaborateContext(..)
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