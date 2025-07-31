{-# LANGUAGE ScopedTypeVariables #-}

module Core.Errors
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
import Core.Syntax
import System.IO.Unsafe (unsafePerformIO)
import Text.Megaparsec (SourcePos, sourceColumn, sourceLine, sourceName, unPos)
import Operations.Generic.PrettyPrint (prettyDefault)

-- | Pretty print a relational judgment
prettyRelJudgment :: RelJudgment -> String
prettyRelJudgment (RelJudgment t1 rtype t2) =
  prettyDefault t1 ++ " [" ++ prettyDefault rtype ++ "] " ++ prettyDefault t2

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
  | UnknownMacro String ErrorContext
  | UnknownTheorem String ErrorContext
  | TheoremArityMismatch String Int Int ErrorContext
  | InvalidMixfixPattern String ErrorContext
  | CircularMacroReference String ErrorContext
  | MacroElaborationError String String ErrorContext -- macro name, error details
  | -- Term normalization errors
    InfiniteNormalization Term ErrorContext
  | SubstitutionError String Term ErrorContext -- variable name, term
  | SubstitutionTypeMismatch String String String ErrorContext -- variable name, expected type, actual type
  | InvalidDeBruijnIndex Int ErrorContext
  | -- Context errors
    InvalidContext String ErrorContext
  | ContextInconsistency String ErrorContext
  | -- Proof checking errors
    ProofTypingError Proof RelJudgment RelJudgment (Maybe (RelJudgment, RelJudgment)) ErrorContext -- proof, expected, actual, optional (normalized expected, normalized actual)
  | LeftConversionError Term Term ErrorContext -- expected, actual
  | RightConversionError Term Term ErrorContext -- expected, actual
  | ConverseError Proof RelJudgment ErrorContext -- proof, actual judgment
  | RhoEliminationNonPromotedError Proof RelJudgment ErrorContext -- proof, actual judgment
  | RhoEliminationTypeMismatchError Proof RelJudgment RelJudgment ErrorContext -- proof, expected, actual
  | CompositionError Proof Proof Term Term ErrorContext -- proof1, proof2, middle term1, middle term2
  | -- Module system errors
    FileNotFound String ErrorContext -- module path
  | ModuleParseError String String ErrorContext -- module path, parse error message  
  | CircularDependency [String] ErrorContext -- module paths
  | ImportResolutionError String String ErrorContext -- module path, error message
  | DuplicateExport String String ErrorContext -- module path, export name
  | ModuleElaborationError String String ErrorContext -- module path, elaboration error
  | -- General errors
    InternalError String ErrorContext
  deriving (Show, Eq)

-- | Format an error for human-readable display
formatError :: RelTTError -> String
formatError err = case err of
  UnboundVariable var ctx ->
    formatWithContext ctx $ "Unbound variable: " ++ var
  UnboundTypeVariable var ctx ->
    formatWithContext ctx $ "Unbound type variable: " ++ var
  UnboundMacro name ctx ->
    formatWithContext ctx $ "Unbound macro: " ++ name
  DuplicateBinding name ctx ->
    formatWithContext ctx $ "Duplicate binding: " ++ name
  TypeMismatch expected actual ctx ->
    formatWithContext ctx $
      "Type mismatch:\n  Expected: "
        ++ prettyDefault expected
        ++ "\n  Actual:   "
        ++ prettyDefault actual
  InvalidTypeApplication ty ctx ->
    formatWithContext ctx $ "Invalid type application: " ++ prettyDefault ty
  MacroArityMismatch name expected actual ctx ->
    formatWithContext ctx $
      "Macro "
        ++ name
        ++ " expects "
        ++ show expected
        ++ " arguments, but got "
        ++ show actual
  UnknownMacro name ctx ->
    formatWithContext ctx $ "Unknown macro: " ++ name
  UnknownTheorem name ctx ->
    formatWithContext ctx $ "Unknown theorem: " ++ name
  TheoremArityMismatch name expected actual ctx ->
    formatWithContext ctx $
      "Theorem "
        ++ name
        ++ " expects "
        ++ show expected
        ++ " arguments, but got "
        ++ show actual
  InvalidMixfixPattern msg ctx ->
    formatWithContext ctx $ "Invalid mixfix pattern: " ++ msg
  CircularMacroReference name ctx ->
    formatWithContext ctx $ "Circular macro reference in: " ++ name
  MacroElaborationError name details ctx ->
    formatWithContext ctx $ "Macro elaboration error in " ++ name ++ ": " ++ details
  InfiniteNormalization term ctx ->
    formatWithContext ctx $ "Infinite normalization for term: " ++ prettyDefault term
  SubstitutionError var term ctx ->
    formatWithContext ctx $
      "Substitution error for variable " ++ var ++ " in term: " ++ prettyDefault term
  SubstitutionTypeMismatch var expected actual ctx ->
    formatWithContext ctx $
      "Substitution type mismatch for variable " ++ var ++ ": expected " ++ expected ++ " but got " ++ actual
  InvalidDeBruijnIndex idx ctx ->
    formatWithContext ctx $ "Invalid de Bruijn index: " ++ show idx
  InvalidContext msg ctx ->
    formatWithContext ctx $ "Invalid context: " ++ msg
  ContextInconsistency msg ctx ->
    formatWithContext ctx $ "Context inconsistency: " ++ msg
  ProofTypingError proof expected actual normalizedForms ctx ->
    formatWithContext ctx $
      "Proof error: proof "
        ++ prettyDefault proof
        ++ " has wrong judgment\n  Expected judgment: "
        ++ prettyRelJudgment expected
        ++ "\n  Actual judgment:   "
        ++ prettyRelJudgment actual
        ++ case normalizedForms of
          Nothing -> ""
          Just (normExpected, normActual) ->
            "\n  Expected judgment (normalized): "
              ++ prettyRelJudgment normExpected
              ++ "\n  Actual judgment (normalized):   "
              ++ prettyRelJudgment normActual
  LeftConversionError expected actual ctx ->
    formatWithContext ctx $
      "Left conversion error: expected "
        ++ prettyDefault expected
        ++ " but got "
        ++ prettyDefault actual
        ++ " - these terms are not β-η equivalent"
  RightConversionError expected actual ctx ->
    formatWithContext ctx $
      "Right conversion error: expected "
        ++ prettyDefault expected
        ++ " but got "
        ++ prettyDefault actual
        ++ " - these terms are not β-η equivalent"
  ConverseError proof judgment ctx ->
    formatWithContext ctx $ "Converse elimination error: proof " ++ prettyDefault proof ++ " must prove judgment with converse relation, but proves " ++ prettyRelJudgment judgment
  RhoEliminationNonPromotedError proof judgment ctx ->
    formatWithContext ctx $ "Rho elimination error: first proof " ++ prettyDefault proof ++ " must prove a judgment with promoted relation, but proves " ++ prettyRelJudgment judgment
  RhoEliminationTypeMismatchError proof expected actual ctx ->
    formatWithContext ctx $
      "Rho elimination error: second proof "
        ++ prettyDefault proof
        ++ " proves wrong judgment\n  Expected judgment: "
        ++ prettyRelJudgment expected
        ++ "\n  Actual judgment:   "
        ++ prettyRelJudgment actual
  CompositionError proof1 proof2 term1 term2 ctx ->
    formatWithContext ctx $
      "Composition error: proofs " ++ prettyDefault proof1 ++ " and " ++ prettyDefault proof2 ++ " have mismatched middle terms: " ++ prettyDefault term1 ++ " ≢ " ++ prettyDefault term2
  FileNotFound path ctx ->
    formatWithContext ctx $ "Module file not found: " ++ path
  ModuleParseError path msg ctx ->
    formatWithContext ctx $ "Parse error in module " ++ path ++ ":\\n" ++ msg
  CircularDependency paths ctx ->
    formatWithContext ctx $ "Circular dependency detected: " ++ show paths
  ImportResolutionError path msg ctx ->
    formatWithContext ctx $ "Import resolution error in " ++ path ++ ": " ++ msg
  DuplicateExport path name ctx ->
    formatWithContext ctx $ "Duplicate export '" ++ name ++ "' in module " ++ path
  ModuleElaborationError path msg ctx ->
    formatWithContext ctx $ "Elaboration error in module " ++ path ++ ": " ++ msg
  InternalError msg ctx ->
    formatWithContext ctx $ "Internal error: " ++ msg

-- | Helper to format error with context information
formatWithContext :: ErrorContext -> String -> String
formatWithContext ctx msg =
  let pos = errorLocation ctx
      filename = sourceName pos
      line = unPos (sourceLine pos)
      col = unPos (sourceColumn pos)
      sourceContext = getSourceContext filename line col
      contextDesc = errorContext ctx
   in "Error in " ++ contextDesc ++ ": " ++ msg ++ "\n" ++ sourceContext

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
