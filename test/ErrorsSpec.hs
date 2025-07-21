{-# LANGUAGE OverloadedStrings #-}

module ErrorsSpec (spec) where

import Errors
import Lib
import Test.Hspec
import Text.Megaparsec (SourcePos (..), initialPos, mkPos, sourceColumn, sourceLine, sourceName, unPos)

spec :: Spec
spec = do
  errorFormattingSpec
  errorContextSpec
  comprehensiveErrorBoundarySpec

-- | Test error formatting and display
errorFormattingSpec :: Spec
errorFormattingSpec = describe "error formatting" $ do
  it "formats unbound variable errors clearly" $ do
    let err = UnboundVariable "undefined_var" (ErrorContext (initialPos "test") "variable lookup")
        formatted = formatError err
    formatted `shouldContain` "Unbound variable: undefined_var"
    formatted `shouldContain` "variable lookup"

  it "formats type mismatch errors with both types" $ do
    let expected = RMacro "Bool" [] (initialPos "test")
        actual = RMacro "Int" [] (initialPos "test")
        err = TypeMismatch expected actual (ErrorContext (initialPos "test") "type inference")
        formatted = formatError err
    formatted `shouldContain` "Type mismatch"
    formatted `shouldContain` "Expected:"
    formatted `shouldContain` "Actual:"
    formatted `shouldContain` "type inference"

  it "includes source location when available" $ do
    let pos = SourcePos "test.rt" (mkPos 42) (mkPos 15)
        ctx = ErrorContext pos "parsing"
        err = UnboundVariable "x" ctx
        formatted = formatError err
    formatted `shouldContain` "test.rt"
    formatted `shouldContain` "42"
    formatted `shouldContain` "15"

  it "formats macro arity errors with counts" $ do
    let err = MacroArityMismatch "List" 1 3 (ErrorContext (initialPos "test") "macro expansion")
        formatted = formatError err
    formatted `shouldContain` "List"
    formatted `shouldContain` "expects 1"
    formatted `shouldContain` "got 3"

-- | Test error context functionality
errorContextSpec :: Spec
errorContextSpec = describe "error context" $ do
  it "creates error context with source location" $ do
    let ctx = ErrorContext (initialPos "test") "test operation"
    sourceName (errorLocation ctx) `shouldBe` "test"
    errorContext ctx `shouldBe` "test operation"

  it "creates error context with specific source location" $ do
    let pos = SourcePos "source.rt" (mkPos 10) (mkPos 5)
        ctx = ErrorContext pos "parsing operation"
    let p = errorLocation ctx
    unPos (sourceLine p) `shouldBe` 10
    unPos (sourceColumn p) `shouldBe` 5
    sourceName p `shouldBe` "source.rt"

  it "formats context with location information" $ do
    let pos = SourcePos "main.rt" (mkPos 25) (mkPos 8)
        ctx = ErrorContext pos "type checking"
        err = InternalError "test error" ctx
        formatted = formatError err
    formatted `shouldContain` "main.rt:25:8"

-- | Test comprehensive error boundary conditions from the paper
comprehensiveErrorBoundarySpec :: Spec
comprehensiveErrorBoundarySpec = describe "comprehensive error boundary tests" $ do
  variableBindingErrorsSpec
  typeSystemErrorsSpec
  macroSystemErrorsSpec
  normalizationErrorsSpec
  proofCheckingErrorsSpec
  contextManagementErrorsSpec

-- | Test all variable and binding related errors
variableBindingErrorsSpec :: Spec
variableBindingErrorsSpec = describe "variable and binding errors" $ do
  it "detects unbound term variables" $ do
    let err = UnboundVariable "nonexistent" (ErrorContext (initialPos "test") "term lookup")
    formatError err `shouldContain` "Unbound variable: nonexistent"

  it "detects unbound type variables" $ do
    let err = UnboundTypeVariable "X" (ErrorContext (initialPos "test") "type variable lookup")
    formatError err `shouldContain` "Unbound type variable: X"

  it "detects unbound macros" $ do
    let err = UnboundMacro "UndefinedMacro" (ErrorContext (initialPos "test") "macro lookup")
    formatError err `shouldContain` "Unbound macro: UndefinedMacro"

  it "detects duplicate bindings in contexts" $ do
    let err = DuplicateBinding "x" (ErrorContext (initialPos "test") "context extension")
    formatError err `shouldContain` "Duplicate binding: x"

  it "detects invalid de Bruijn indices" $ do
    let err = InvalidDeBruijnIndex 999 (ErrorContext (initialPos "test") "variable reference")
    formatError err `shouldContain` "Invalid de Bruijn index: 999"

-- | Test type system related errors
typeSystemErrorsSpec :: Spec
typeSystemErrorsSpec = describe "type system errors" $ do
  it "detects type mismatches in applications" $ do
    let expected = Arr (RMacro "Int" [] (initialPos "test")) (RMacro "Bool" [] (initialPos "test")) (initialPos "test")
        actual = RMacro "String" [] (initialPos "test")
        err = TypeMismatch expected actual (ErrorContext (initialPos "test") "function application")
    let formatted = formatError err
    formatted `shouldContain` "Type mismatch"
    formatted `shouldContain` "Int"
    formatted `shouldContain` "String"

  it "detects invalid type applications" $ do
    let badType = RMacro "NotAFunction" [] (initialPos "test")
        err = InvalidTypeApplication badType (ErrorContext (initialPos "test") "type application")
    formatError err `shouldContain` "Invalid type application"

  it "validates type variable scope violations" $ do
    -- Test when type variable is used outside its scope
    let err = UnboundTypeVariable "Y" (ErrorContext (initialPos "test") "quantifier scope validation")
    formatError err `shouldContain` "Unbound type variable: Y"

  it "detects malformed arrow types" $ do
    let err = UnboundTypeVariable "Undefined" (ErrorContext (initialPos "test") "arrow type construction")
    formatError err `shouldContain` "Unbound type variable: Undefined"

-- | Test macro system errors
macroSystemErrorsSpec :: Spec
macroSystemErrorsSpec = describe "macro system errors" $ do
  it "detects macro arity mismatches - too few arguments" $ do
    let err = MacroArityMismatch "BiMacro" 2 1 (ErrorContext (initialPos "test") "macro application")
    let formatted = formatError err
    formatted `shouldContain` "BiMacro"
    formatted `shouldContain` "expects 2"
    formatted `shouldContain` "got 1"

  it "detects macro arity mismatches - too many arguments" $ do
    let err = MacroArityMismatch "SimpleId" 0 3 (ErrorContext (initialPos "test") "macro application")
    let formatted = formatError err
    formatted `shouldContain` "SimpleId"
    formatted `shouldContain` "expects 0"
    formatted `shouldContain` "got 3"

  it "detects nested macro expansion failures" $ do
    let err = UnboundMacro "InnerMacro" (ErrorContext (initialPos "test") "nested macro expansion")
    formatError err `shouldContain` "Unbound macro: InnerMacro"

-- | Test normalization and term manipulation errors
normalizationErrorsSpec :: Spec
normalizationErrorsSpec = describe "normalization errors" $ do
  it "detects infinite normalization sequences" $ do
    let problematicTerm =
          App
            (Lam "x" (App (Var "x" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
            (Lam "x" (App (Var "x" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
            (initialPos "test")
        err = InfiniteNormalization problematicTerm (ErrorContext (initialPos "test") "beta reduction")
    formatError err `shouldContain` "Infinite normalization"

  it "detects substitution errors with variable capture" $ do
    let problematicTerm = Lam "x" (Var "y" (-1) (initialPos "test")) (initialPos "test")
        err = SubstitutionError "y" problematicTerm (ErrorContext (initialPos "test") "variable substitution")
    let formatted = formatError err
    formatted `shouldContain` "Substitution error"
    formatted `shouldContain` "variable y"

  it "detects invalid term structures during normalization" $ do
    let err = InvalidDeBruijnIndex (-999) (ErrorContext (initialPos "test") "term validation")
    formatError err `shouldContain` "Invalid de Bruijn index"

-- | Test proof checking specific errors from the paper
proofCheckingErrorsSpec :: Spec
proofCheckingErrorsSpec = describe "proof checking errors" $ do
  it "detects proof typing mismatches" $ do
    let expectedJudgment = RelJudgment (Var "x" 0 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" 0 (initialPos "test"))
        actualJudgment = RelJudgment (Var "x" 0 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "y" 0 (initialPos "test"))
        err = ProofTypingError (PVar "dummy" 0 (initialPos "test")) expectedJudgment actualJudgment (ErrorContext (initialPos "test") "proof inference")
    let formatted = formatError err
    formatted `shouldContain` "Proof error"
    formatted `shouldContain` "Expected judgment:"
    formatted `shouldContain` "Actual judgment:"

  it "detects term conversion failures in proof conversion" $ do
    let t1 = Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")
        t1' = Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test") -- α-equivalent, should work
        t2 = Var "a" (-1) (initialPos "test")
        t2' = Var "b" (-1) (initialPos "test") -- Not equivalent
        err = TermConversionError t1 t1' t2 t2' (ErrorContext (initialPos "test") "proof conversion")
    formatError err `shouldContain` "Term conversion error"

  it "detects converse elimination on non-converse types" $ do
    let nonConverseType = RMacro "RegularType" [] (initialPos "test")
        dummyJudgment = RelJudgment (Var "x" 0 (initialPos "test")) nonConverseType (Var "y" 0 (initialPos "test"))
        err = ConverseError (PVar "dummy" 0 (initialPos "test")) dummyJudgment (ErrorContext (initialPos "test") "converse elimination")
    formatError err `shouldContain` "Converse elimination error"

  it "detects rho elimination with wrong promoted type" $ do
    let wrongType = RMacro "NotPromoted" [] (initialPos "test")
        dummyJudgment = RelJudgment (Var "x" 0 (initialPos "test")) wrongType (Var "y" 0 (initialPos "test"))
        err = RhoEliminationNonPromotedError (PVar "dummy" 0 (initialPos "test")) dummyJudgment (ErrorContext (initialPos "test") "rho elimination validation")
    formatError err `shouldContain` "Rho elimination error"

  it "detects composition with mismatched middle terms" $ do
    let middleTerm1 = Var "x" 0 (initialPos "test")
        middleTerm2 = Var "y" 0 (initialPos "test") -- Should be the same term
        err = CompositionError (PVar "p1" 0 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) middleTerm1 middleTerm2 (ErrorContext (initialPos "test") "composition introduction")
    formatError err `shouldContain` "Composition error"

-- | Test context management errors
contextManagementErrorsSpec :: Spec
contextManagementErrorsSpec = describe "context management errors" $ do
  it "detects invalid context states" $ do
    let err = InvalidContext "malformed binding structure" (ErrorContext (initialPos "test") "context validation")
    formatError err `shouldContain` "Invalid context"

  it "detects context inconsistencies" $ do
    let err = ContextInconsistency "binding index mismatch" (ErrorContext (initialPos "test") "context coherence check")
    formatError err `shouldContain` "Context inconsistency"

  it "validates context extension failures" $ do
    let err = DuplicateBinding "shadowed_var" (ErrorContext (initialPos "test") "context extension")
    formatError err `shouldContain` "Duplicate binding: shadowed_var"

  it "detects invalid scope nesting" $ do
    let err = InvalidDeBruijnIndex 5 (ErrorContext (initialPos "test") "scope validation")
    formatError err `shouldContain` "Invalid de Bruijn index: 5"
