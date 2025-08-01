{-# LANGUAGE OverloadedStrings #-}

-- Import all test modules

import qualified ComprehensiveTheoremAppSpec
import qualified ContextSpec
import qualified ErrorsSpec
import qualified IntegrationSpec
import qualified MixfixSpec
import qualified NormalizeSpec
import qualified NotPreservesBoolBugSpec
import qualified PTheoremAppSpec
import qualified ParserSpec
import qualified PrettyPrintSpec
import qualified ProofCheckerSpec
import qualified REPLSpec
import qualified SubstitutionBugSpec
import qualified TermOpsSpec
import Test.Hspec
import qualified TheoremApplicationSpec
import qualified TheoremArgSpec
import qualified TheoremArgValidationSpec
import qualified TheoremReferenceParsingSpec
import qualified TwoPhaseParsingSpec
import qualified TypeOpsSpec

main :: IO ()
main = hspec $ do
  -- Parser tests
  describe "Parser Tests" ParserSpec.spec
  describe "Mixfix Operators" MixfixSpec.spec

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
  describe "Theorem Application" TheoremApplicationSpec.spec
  describe "Theorem Arguments" TheoremArgSpec.spec
  describe "Theorem Argument Validation" TheoremArgValidationSpec.spec
  describe "Theorem Reference Parsing" TheoremReferenceParsingSpec.spec
  describe "PTheoremApp Proof Checking" PTheoremAppSpec.spec
  describe "Comprehensive Theorem Applications" ComprehensiveTheoremAppSpec.spec
  describe "Not Preserves Bool Bug" NotPreservesBoolBugSpec.spec
  describe "Substitution Order Bug" SubstitutionBugSpec.spec
  describe "Integration Tests" IntegrationSpec.spec
