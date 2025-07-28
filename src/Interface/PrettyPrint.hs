module Interface.PrettyPrint
  ( -- * Re-export from generic module
    prettyTerm,
    prettyRType,
    prettyProof,
    prettyTermWithConfig,
    prettyRTypeWithConfig,
    prettyProofWithConfig,
    PrettyConfig (..),
    defaultPrettyConfig,
    prettyWithConfig,
    -- * Non-generic pretty printing functions
    prettyRelJudgment,
    prettyDeclaration,
    prettyBinding,
    prettyError,
    prettyImportDeclaration,
    prettyExportDeclaration,
    prettyRelJudgmentWithConfig,
    prettyDeclarationWithConfig,
    prettyTheoremArgWithConfig,
  )
where

import Data.List (intercalate)
import Core.Errors (RelTTError(..), ErrorContext(..), getSourceContext)
import Core.Syntax
import Text.Megaparsec (sourceColumn, sourceLine, sourceName, unPos)
import Operations.Generic.PrettyPrint (PrettyConfig(..), defaultPrettyConfig, prettyWithConfig, prettyDefault)

-- Re-export generic functions with original names
prettyTerm :: Term -> String
prettyTerm = prettyDefault

prettyRType :: RType -> String
prettyRType = prettyDefault

prettyProof :: Proof -> String
prettyProof = prettyDefault

prettyTermWithConfig :: PrettyConfig -> Term -> String
prettyTermWithConfig = prettyWithConfig

prettyRTypeWithConfig :: PrettyConfig -> RType -> String
prettyRTypeWithConfig = prettyWithConfig

prettyProofWithConfig :: PrettyConfig -> Proof -> String
prettyProofWithConfig = prettyWithConfig

-- Pretty print relational judgments
prettyRelJudgment :: RelJudgment -> String
prettyRelJudgment = prettyRelJudgmentWithConfig defaultPrettyConfig

prettyRelJudgmentWithConfig :: PrettyConfig -> RelJudgment -> String
prettyRelJudgmentWithConfig config (RelJudgment t1 rtype t2) =
  let t1' = prettyWithConfig config t1
      r' = prettyWithConfig config rtype
      t2' = prettyWithConfig config t2
   in t1' ++ " [" ++ r' ++ "] " ++ t2'

-- Pretty print bindings
prettyBinding :: Binding -> String
prettyBinding binding = case binding of
  TermBinding name -> "(" ++ name ++ " : Term)"
  RelBinding name -> "(" ++ name ++ " : Rel)"
  ProofBinding name judgment -> "(" ++ name ++ " : " ++ prettyRelJudgment judgment ++ ")"

-- Pretty print declarations
prettyDeclaration :: Declaration -> String
prettyDeclaration = prettyDeclarationWithConfig defaultPrettyConfig

prettyDeclarationWithConfig :: PrettyConfig -> Declaration -> String
prettyDeclarationWithConfig config decl = case decl of
  MacroDef name params body ->
    let paramStr = if null params then "" else " " ++ intercalate " " params
        bodyStr = case body of
          TermMacro term -> prettyWithConfig config term
          RelMacro rtype -> prettyWithConfig config rtype
          ProofMacro proof -> prettyWithConfig config proof
     in name ++ paramStr ++ " ≔ " ++ bodyStr ++ ";"
  TheoremDef name bindings judgment proof ->
    let turnstile = if useUnicode config then "⊢" else "|-"
        bindingStr =
          if null bindings
            then ""
            else " " ++ unwords (map prettyBinding bindings)
        judgmentStr = prettyRelJudgmentWithConfig config judgment
        proofStr = prettyWithConfig config proof
     in turnstile ++ " " ++ name ++ bindingStr ++ " : " ++ judgmentStr ++ " ≔ " ++ proofStr ++ ";"
  ImportDecl importDecl -> prettyImportDeclaration importDecl
  ExportDecl exportDecl -> prettyExportDeclaration exportDecl
  FixityDecl fixity name -> prettyFixity fixity ++ " " ++ name ++ ";"

-- | Pretty print fixity declarations
prettyFixity :: Fixity -> String
prettyFixity fixity = case fixity of
  Infixl level -> "infixl " ++ show level
  Infixr level -> "infixr " ++ show level
  InfixN level -> "infix " ++ show level
  Prefix level -> "prefix " ++ show level
  Postfix level -> "postfix " ++ show level
  Closed level -> "closed " ++ show level

-- Pretty print import declarations
prettyImportDeclaration :: ImportDeclaration -> String
prettyImportDeclaration importDecl = case importDecl of
  ImportModule path -> "import \"" ++ path ++ "\";"
  ImportModuleAs path alias -> "import \"" ++ path ++ "\" as " ++ alias ++ ";"
  ImportOnly path names -> "import \"" ++ path ++ "\" (" ++ intercalate ", " names ++ ");"

-- Pretty print export declarations
prettyExportDeclaration :: ExportDeclaration -> String
prettyExportDeclaration (ExportSymbols names) = "export " ++ intercalate ", " names ++ ";"

-- Pretty print errors
prettyError :: RelTTError -> String
prettyError err = case err of
  UnboundVariable name ctx ->
    "Unbound variable: " ++ name ++ prettyContext ctx
  UnboundTypeVariable name ctx ->
    "Unbound type variable: " ++ name ++ prettyContext ctx
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
  ProofTypingError proof expected actual normalizedForms ctx ->
    "Proof error: proof "
      ++ prettyProof proof
      ++ " has wrong judgment\n"
      ++ "  Expected judgment: "
      ++ prettyRelJudgment expected
      ++ "\n"
      ++ "  Actual judgment: "
      ++ prettyRelJudgment actual
      ++ case normalizedForms of
        Nothing -> ""
        Just (normExpected, normActual) ->
          "\n  Expected judgment (normalized): "
            ++ prettyRelJudgment normExpected
            ++ "\n  Actual judgment (normalized): "
            ++ prettyRelJudgment normActual
      ++ prettyContext ctx
  LeftConversionError expected actual ctx ->
    "Left conversion error: expected "
      ++ prettyTerm expected
      ++ " but got "
      ++ prettyTerm actual
      ++ " - these terms are not β-η equivalent"
      ++ prettyContext ctx
  RightConversionError expected actual ctx ->
    "Right conversion error: expected "
      ++ prettyTerm expected
      ++ " but got "
      ++ prettyTerm actual
      ++ " - these terms are not β-η equivalent"
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
    "Composition error: proofs " ++ prettyProof proof1 ++ " and " ++ prettyProof proof2 ++ " have mismatched middle terms " ++ prettyTerm t1 ++ " and " ++ prettyTerm t2 ++ prettyContext ctx
  UnknownMacro name ctx ->
    "Unknown macro: " ++ name ++ prettyContext ctx
  UnknownTheorem name ctx ->
    "Unknown theorem: " ++ name ++ prettyContext ctx
  TheoremArityMismatch name expected actual ctx ->
    "Theorem arity mismatch for " ++ name ++ ": expected " ++ show expected ++ " arguments, got " ++ show actual ++ prettyContext ctx
  InvalidMixfixPattern pattern ctx ->
    "Invalid mixfix pattern: " ++ pattern ++ prettyContext ctx
  CircularMacroReference name ctx ->
    "Circular macro reference: " ++ name ++ prettyContext ctx
  FileNotFound path ctx ->
    "File not found: " ++ path ++ prettyContext ctx
  ModuleParseError path msg ctx ->
    "Module parse error in " ++ path ++ ": " ++ msg ++ prettyContext ctx
  CircularDependency paths ctx ->
    "Circular dependency: " ++ intercalate " -> " paths ++ prettyContext ctx
  ImportResolutionError path msg ctx ->
    "Import resolution error in " ++ path ++ ": " ++ msg ++ prettyContext ctx
  DuplicateExport path name ctx ->
    "Duplicate export in " ++ path ++ ": " ++ name ++ prettyContext ctx
  ModuleElaborationError path msg ctx ->
    "Module elaboration error in " ++ path ++ ": " ++ msg ++ prettyContext ctx
  InternalError msg ctx ->
    "Internal error: " ++ msg ++ prettyContext ctx

-- Pretty print theorem arguments
prettyTheoremArgWithConfig :: PrettyConfig -> TheoremArg -> String
prettyTheoremArgWithConfig config arg = case arg of
  TermArg term -> "(" ++ prettyWithConfig config term ++ ")"
  RelArg rtype -> "(" ++ prettyWithConfig config rtype ++ ")"
  ProofArg proof -> "(" ++ prettyWithConfig config proof ++ ")"

-- Helper function to pretty print error context
prettyContext :: ErrorContext -> String
prettyContext (ErrorContext pos _) =
  let filename = sourceName pos
      line = unPos (sourceLine pos)
      col = unPos (sourceColumn pos)
   in "\n" ++ getSourceContext filename line col

