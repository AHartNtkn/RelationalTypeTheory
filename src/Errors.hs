{-# LANGUAGE ScopedTypeVariables #-}

module Errors
  ( RelTTError (..),
    SourcePos,
    ErrorContext (..),
    formatError,
    getSourceContext,
    throwUnboundVar,
    throwTypeMismatch,
    throwMacroError,
    throwNormalizationError,
  )
where

import Control.Exception (IOException, catch)
import Lib
import PrettyPrint (prettyTerm, prettyRType, prettyProof, prettyRelJudgment)
import System.IO.Unsafe (unsafePerformIO)
import Text.Megaparsec (SourcePos, sourceColumn, sourceLine, sourceName, unPos)

-- | Context information for where an error occurred
data ErrorContext = ErrorContext
  { errorLocation :: SourcePos,
    errorContext :: String -- Description of what was being done
  }
  deriving (Show, Eq)

-- | Comprehensive error types for RelTT operations
data RelTTError
  = -- Variable and binding errors
    UnboundVariable String ErrorContext
  | UnboundTypeVariable String ErrorContext
  | UnboundMacro String ErrorContext
  | DuplicateBinding String ErrorContext
  | -- Type-related errors
    TypeMismatch RType RType ErrorContext -- expected, actual
  | InvalidTypeApplication RType ErrorContext
  | MacroArityMismatch String Int Int ErrorContext -- macro name, expected, actual
  | -- Term normalization errors
    InfiniteNormalization Term ErrorContext
  | SubstitutionError String Term ErrorContext -- variable name, term
  | InvalidDeBruijnIndex Int ErrorContext
  | -- Context errors
    InvalidContext String ErrorContext
  | ContextInconsistency String ErrorContext
  | -- Proof checking errors
    ProofTypingError Proof RelJudgment RelJudgment (Maybe (RelJudgment, RelJudgment)) (Maybe (RelTTError, RelTTError)) ErrorContext -- proof, expected, actual, optional (normalized expected, normalized actual), optional (expected norm error, actual norm error)
  | LeftConversionError Term Term RelJudgment Term Term Proof ErrorContext -- proof_left, target_left, proof_judgment, target_left, target_right, actual_proof
  | RightConversionError Term Term RelJudgment Term Term Proof ErrorContext -- proof_right, target_right, proof_judgment, target_left, target_right, actual_proof
  | ConverseError Proof RelJudgment ErrorContext -- proof, actual judgment
  | RhoEliminationNonPromotedError Proof RelJudgment ErrorContext -- proof, actual judgment
  | RhoEliminationTypeMismatchError Proof RelJudgment RelJudgment ErrorContext -- proof, expected, actual
  | CompositionError Proof Proof Term Term ErrorContext -- proof1, proof2, middle term1, middle term2
  | PiEliminationError Proof RelJudgment ErrorContext -- proof, actual judgment (should be composition type)
  | -- General errors
    InternalError String ErrorContext
  deriving (Show, Eq)

-- | Format an error for human-readable display
formatError :: RelTTError -> String
formatError err = case err of
  UnboundVariable var ctx ->
    "Unbound variable: " ++ var ++ prettyContext ctx
  UnboundTypeVariable var ctx ->
    "Unbound type variable: " ++ var ++ prettyContext ctx
  UnboundMacro name ctx ->
    "Unbound macro: " ++ name ++ prettyContext ctx
  DuplicateBinding name ctx ->
    "Duplicate binding: " ++ name ++ prettyContext ctx
  TypeMismatch expected actual ctx ->
    "Type mismatch:\n"
      ++ "  Expected: "
      ++ prettyRType expected
      ++ "\n"
      ++ "  Actual: "
      ++ prettyRType actual
      ++ prettyContext ctx
  InvalidTypeApplication rtype ctx ->
    "Invalid type application: " ++ prettyRType rtype ++ prettyContext ctx
  MacroArityMismatch name expected actual ctx ->
    "Macro arity mismatch for "
      ++ name
      ++ ":\n"
      ++ "  Expected: "
      ++ show expected
      ++ " arguments\n"
      ++ "  Actual: "
      ++ show actual
      ++ " arguments"
      ++ prettyContext ctx
  InfiniteNormalization term ctx ->
    "Infinite normalization for term: " ++ prettyTerm term ++ prettyContext ctx
  SubstitutionError var term ctx ->
    "Substitution error for variable " ++ var ++ " in term: " ++ prettyTerm term ++ prettyContext ctx
  InvalidDeBruijnIndex idx ctx ->
    "Invalid de Bruijn index: " ++ show idx ++ prettyContext ctx
  InvalidContext msg ctx ->
    "Invalid context: " ++ msg ++ prettyContext ctx
  ContextInconsistency msg ctx ->
    "Context inconsistency: " ++ msg ++ prettyContext ctx
  ProofTypingError proof expected actual normalizedForms normErrors ctx ->
    "Proof error: proof "
      ++ prettyProof proof
      ++ " has wrong judgment\n"
      ++ "  Expected judgment: "
      ++ prettyRelJudgment expected
      ++ "\n"
      ++ "  Actual judgment: "
      ++ prettyRelJudgment actual
      ++ case normalizedForms of
        Nothing -> case normErrors of
          Nothing -> "\n  WARNING: Normalization failed - unable to show expanded macro forms"
          Just (expectedErr, actualErr) ->
            "\n  WARNING: Normalization failed:\n"
              ++ "    Expected normalization error: " ++ formatError expectedErr ++ "\n"
              ++ "    Actual normalization error: " ++ formatError actualErr
        Just (normExpected, normActual) ->
          "\n  Expected judgment (normalized): "
            ++ prettyRelJudgment normExpected
            ++ "\n  Actual judgment (normalized): "
            ++ prettyRelJudgment normActual
      ++ prettyContext ctx
  LeftConversionError proofLeft targetLeft proofJudgment targetLeft' targetRight actualProof ctx ->
    "Left conversion error: expected "
      ++ prettyTerm targetLeft
      ++ " but got "
      ++ prettyTerm proofLeft
      ++ " - these terms are not β-η equivalent\n"
      ++ "  In conversion: "
      ++ prettyTerm targetLeft'
      ++ " ⇃ "
      ++ prettyProof actualProof
      ++ " ⇂ "
      ++ prettyTerm targetRight
      ++ "\n  Where proof "
      ++ prettyProof actualProof
      ++ " proves: "
      ++ prettyRelJudgment proofJudgment
      ++ prettyContext ctx
  RightConversionError proofRight targetRight proofJudgment targetLeft targetRight' actualProof ctx ->
    "Right conversion error: expected "
      ++ prettyTerm targetRight
      ++ " but got "
      ++ prettyTerm proofRight
      ++ " - these terms are not β-η equivalent\n"
      ++ "  In conversion: "
      ++ prettyTerm targetLeft
      ++ " ⇃ "
      ++ prettyProof actualProof
      ++ " ⇂ "
      ++ prettyTerm targetRight'
      ++ "\n  Where proof "
      ++ prettyProof actualProof
      ++ " proves: "
      ++ prettyRelJudgment proofJudgment
      ++ prettyContext ctx
  ConverseError proof judgment ctx ->
    "Converse elimination error: proof " ++ prettyProof proof ++ " must prove judgment with converse relation, but proves " ++ prettyRelJudgment judgment ++ prettyContext ctx
  RhoEliminationNonPromotedError proof judgment ctx ->
    "Rho elimination error: first proof " ++ prettyProof proof ++ " must prove a judgment with promoted relation, but proves " ++ prettyRelJudgment judgment ++ prettyContext ctx
  RhoEliminationTypeMismatchError proof expected actual ctx ->
    "Rho elimination error: second proof "
      ++ prettyProof proof
      ++ " proves wrong judgment"
      ++ prettyContext ctx
      ++ "\n  Expected judgment: "
      ++ prettyRelJudgment expected
      ++ "\n  Actual judgment:   "
      ++ prettyRelJudgment actual
  CompositionError proof1 proof2 t1 t2 ctx ->
    "Composition error: proofs " ++ prettyProof proof1 ++ " and " ++ prettyProof proof2 ++ " have mismatched middle terms\n" ++
    "  First proof middle term:  " ++ prettyTerm t1 ++ "\n" ++
    "  Second proof middle term: " ++ prettyTerm t2 ++ "\n" ++
    "  Middle terms must be alpha-equivalent for composition to be valid" ++ prettyContext ctx
  PiEliminationError proof actual ctx ->
    "Pi elimination error: proof " ++ prettyProof proof ++ " must have composition type for pi elimination\n" ++
    "  Actual judgment: " ++ prettyRelJudgment actual ++ "\n" ++
    "  Expected: judgment with composition type (R ∘ S)" ++ prettyContext ctx
  InternalError msg ctx ->
    "Internal error: " ++ msg ++ prettyContext ctx


-- | Get source context for error reporting (similar to Megaparsec format)
getSourceContext :: String -> Int -> Int -> String
getSourceContext filename lineNum colNum =
  let sourceLines = readSourceLines filename
      locationInfo = filename ++ ":" ++ show lineNum ++ ":" ++ show colNum ++ ":"
   in case sourceLines of
        Nothing -> "  at " ++ locationInfo
        Just fileLines ->
          if lineNum <= length fileLines && lineNum > 0
            then
              let sourceLineText = fileLines !! (lineNum - 1)
                  lineNumStr = show lineNum
                  padding = replicate (length lineNumStr) ' '
                  pointer = replicate (colNum - 1) ' ' ++ "^"
               in locationInfo
                    ++ "\n"
                    ++ padding
                    ++ " |\n"
                    ++ lineNumStr
                    ++ " | "
                    ++ sourceLineText
                    ++ "\n"
                    ++ padding
                    ++ " | "
                    ++ pointer
            else "  at " ++ locationInfo

-- | Safely read source file lines
readSourceLines :: String -> Maybe [String]
readSourceLines filename = unsafePerformIO $ do
  (Just . lines <$> readFile filename) `catch` (\(_ :: IOException) -> return Nothing)

-- | Helper functions for creating common errors with position information
throwUnboundVar :: String -> SourcePos -> String -> RelTTError
throwUnboundVar var pos context =
  UnboundVariable var (ErrorContext pos context)

throwTypeMismatch :: RType -> RType -> SourcePos -> String -> RelTTError
throwTypeMismatch expected actual pos context =
  TypeMismatch expected actual (ErrorContext pos context)

throwMacroError :: String -> SourcePos -> String -> RelTTError
throwMacroError name pos context =
  UnboundMacro name (ErrorContext pos context)

throwNormalizationError :: Term -> SourcePos -> String -> RelTTError
throwNormalizationError term pos context =
  InfiniteNormalization term (ErrorContext pos context)

-- | Pretty print context for error messages
prettyContext :: ErrorContext -> String
prettyContext (ErrorContext pos _) =
  let filename = sourceName pos
      line = unPos (sourceLine pos)
      col = unPos (sourceColumn pos)
   in "\n" ++ getSourceContext filename line col

