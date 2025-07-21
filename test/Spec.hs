{-# LANGUAGE OverloadedStrings #-}

-- Import all test modules

import qualified ContextSpec
import qualified ErrorsSpec
import qualified IntegrationSpec
import qualified NormalizeSpec
import qualified ParserSpec
import qualified PrettyPrintSpec
import qualified ProofCheckerSpec
import qualified REPLSpec
import qualified TermOpsSpec
import Test.Hspec
import qualified TwoPhaseParsingSpec
import qualified TypeOpsSpec

main :: IO ()
main = hspec $ do
  -- Parser tests
  describe "Parser Tests" ParserSpec.spec

  -- Core infrastructure tests
  describe "Normalization" NormalizeSpec.spec
  describe "Term Operations" TermOpsSpec.spec
  describe "Type Operations" TypeOpsSpec.spec
  describe "Context Management" ContextSpec.spec
  describe "Error Handling" ErrorsSpec.spec
  describe "Proof Checking" ProofCheckerSpec.spec
  describe "Pretty Printing" PrettyPrintSpec.spec
  describe "REPL System" REPLSpec.spec
  describe "Two-Phase Parsing" TwoPhaseParsingSpec.spec
  describe "Integration Tests" IntegrationSpec.spec
