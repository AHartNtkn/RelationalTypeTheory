module PrettyPrint
  ( prettyTerm,
    prettyRType,
    prettyProof,
    prettyRelJudgment,
    prettyDeclaration,
    prettyBinding,
    prettyError,
    prettyImportDeclaration,
    prettyExportDeclaration,
    PrettyConfig (..),
    defaultPrettyConfig,
    prettyWithConfig,
    prettyTermWithConfig,
    prettyRTypeWithConfig,
    prettyProofWithConfig,
    prettyRelJudgmentWithConfig,
    prettyDeclarationWithConfig,
  )
where

import Data.List (intercalate)
import Errors
import Lib
import Text.Megaparsec (sourceColumn, sourceLine, sourceName, unPos)

-- Configuration for pretty printing
data PrettyConfig = PrettyConfig
  { useUnicode :: Bool,
    showIndices :: Bool,
    indentSize :: Int,
    lineWidth :: Int
  }
  deriving (Show, Eq)

defaultPrettyConfig :: PrettyConfig
defaultPrettyConfig =
  PrettyConfig
    { useUnicode = True,
      showIndices = False,
      indentSize = 2,
      lineWidth = 80
    }

-- Pretty print with configuration
prettyWithConfig :: PrettyConfig -> (PrettyConfig -> a -> String) -> a -> String
prettyWithConfig config f x = f config x

-- Pretty print terms
prettyTerm :: Term -> String
prettyTerm = prettyTermWithConfig defaultPrettyConfig

prettyTermWithConfig :: PrettyConfig -> Term -> String
prettyTermWithConfig config term = case term of
  Var name idx _ ->
    if showIndices config
      then name ++ "_" ++ show idx
      else name
  Lam name body _ ->
    let lambda = if useUnicode config then "λ" else "\\"
     in lambda ++ name ++ ". " ++ prettyTermWithConfig config body
  App t1 t2 _ ->
    let t1' = case t1 of
          Lam _ _ _ -> "(" ++ prettyTermWithConfig config t1 ++ ")"
          _ -> prettyTermWithConfig config t1
        t2' = prettyTermWithParens config t2 -- Parens needed on right for complex terms
     in t1' ++ " " ++ t2'
  TMacro name args _ ->
    if null args
      then name
      else name ++ " " ++ intercalate " " (map (prettyTermWithParens config) args)

-- Add parentheses when needed for terms
prettyTermWithParens :: PrettyConfig -> Term -> String
prettyTermWithParens config term = case term of
  Lam _ _ _ -> "(" ++ prettyTermWithConfig config term ++ ")"
  App _ _ _ -> "(" ++ prettyTermWithConfig config term ++ ")"
  _ -> prettyTermWithConfig config term

-- Pretty print relational types
prettyRType :: RType -> String
prettyRType = prettyRTypeWithConfig defaultPrettyConfig

prettyRTypeWithConfig :: PrettyConfig -> RType -> String
prettyRTypeWithConfig config rtype = case rtype of
  RVar name idx _ ->
    if showIndices config
      then name ++ "_" ++ show idx
      else name
  RMacro name args _ ->
    if null args
      then name
      else name ++ " " ++ intercalate " " (map (prettyRTypeWithParens config) args)
  Arr r1 r2 _ ->
    let arrow = if useUnicode config then "→" else "->"
        r1' = prettyRTypeWithParens config r1
        r2' = prettyRTypeWithConfig config r2
     in r1' ++ " " ++ arrow ++ " " ++ r2'
  All name body _ ->
    let forallSym = if useUnicode config then "∀" else "forall"
     in forallSym ++ name ++ ". " ++ prettyRTypeWithConfig config body
  Comp r1 r2 _ ->
    let comp = if useUnicode config then "∘" else "o"
        r1' = prettyRTypeWithParens config r1
        r2' = prettyRTypeWithParens config r2
     in r1' ++ " " ++ comp ++ " " ++ r2'
  Conv r _ ->
    let conv = if useUnicode config then "˘" else "^"
        r' = prettyRTypeWithParens config r
     in r' ++ conv
  Prom t _ ->
    let t' = prettyTermWithConfig config t
     in t' -- Hide promotion from user - just show the term

-- Add parentheses when needed for types
prettyRTypeWithParens :: PrettyConfig -> RType -> String
prettyRTypeWithParens config rtype = case rtype of
  Arr _ _ _ -> "(" ++ prettyRTypeWithConfig config rtype ++ ")"
  All _ _ _ -> "(" ++ prettyRTypeWithConfig config rtype ++ ")"
  Comp _ _ _ -> "(" ++ prettyRTypeWithConfig config rtype ++ ")"
  Prom (Lam _ _ _) _ -> "(" ++ prettyRTypeWithConfig config rtype ++ ")" -- Add parentheses around promoted lambdas
  _ -> prettyRTypeWithConfig config rtype

-- Pretty print proofs
prettyProof :: Proof -> String
prettyProof = prettyProofWithConfig defaultPrettyConfig

prettyProofWithConfig :: PrettyConfig -> Proof -> String
prettyProofWithConfig config proof = case proof of
  PVar name idx _ ->
    if showIndices config
      then name ++ "_" ++ show idx
      else name
  PTheorem name _ -> name
  LamP name rtype body _ ->
    let lambda = if useUnicode config then "λ" else "\\"
     in lambda ++ name ++ ":" ++ prettyRTypeWithConfig config rtype ++ ". " ++ prettyProofWithConfig config body
  AppP p1 p2 _ ->
    let p1' = prettyProofWithParens config p1
        p2' = prettyProofWithParens config p2
     in p1' ++ " " ++ p2'
  TyLam name body _ ->
    let lambda = if useUnicode config then "Λ" else "Lambda"
     in lambda ++ name ++ ". " ++ prettyProofWithConfig config body
  TyApp p rtype _ ->
    let p' = prettyProofWithParens config p
        r' = prettyRTypeWithConfig config rtype
     in p' ++ "{" ++ r' ++ "}"
  Iota t1 t2 _ ->
    let iota = if useUnicode config then "ι" else "iota"
     in iota ++ "⟨" ++ prettyTermWithConfig config t1 ++ ", " ++ prettyTermWithConfig config t2 ++ "⟩"
  ConvProof t1 p t2 _ ->
    let t1' = prettyTermWithConfig config t1
        p' = prettyProofWithConfig config p
        t2' = prettyTermWithConfig config t2
     in t1' ++ " ⇃ " ++ p' ++ " ⇂ " ++ t2'
  RhoElim binding1 term1 term2 proof1 proof2 _ ->
    let rho = if useUnicode config then "ρ" else "rho"
     in rho
          ++ "{"
          ++ binding1
          ++ "."
          ++ prettyTermWithConfig config term1
          ++ ", "
          ++ prettyTermWithConfig config term2
          ++ "} "
          ++ prettyProofWithConfig config proof1
          ++ " - "
          ++ prettyProofWithConfig config proof2
  Pi p1 x u v p2 _ ->
    let piSymbol = if useUnicode config then "π" else "pi"
        bindingStr = x ++ "." ++ u ++ "." ++ v
     in piSymbol ++ " " ++ prettyProofWithConfig config p1 ++ " - " ++ bindingStr ++ "." ++ prettyProofWithConfig config p2
  ConvIntro p _ ->
    let unionI = if useUnicode config then "∪ᵢ" else "unionI"
     in unionI ++ " " ++ prettyProofWithConfig config p
  ConvElim p _ ->
    let unionE = if useUnicode config then "∪ₑ" else "unionE"
     in unionE ++ " " ++ prettyProofWithConfig config p
  Pair p1 p2 _ ->
    "(" ++ prettyProofWithConfig config p1 ++ ", " ++ prettyProofWithConfig config p2 ++ ")"

-- Add parentheses when needed for proofs
prettyProofWithParens :: PrettyConfig -> Proof -> String
prettyProofWithParens config proof = case proof of
  LamP _ _ _ _ -> "(" ++ prettyProofWithConfig config proof ++ ")"
  AppP _ _ _ -> "(" ++ prettyProofWithConfig config proof ++ ")"
  TyLam _ _ _ -> "(" ++ prettyProofWithConfig config proof ++ ")"
  ConvProof _ _ _ _ -> "(" ++ prettyProofWithConfig config proof ++ ")"
  RhoElim _ _ _ _ _ _ -> "(" ++ prettyProofWithConfig config proof ++ ")"
  Pi _ _ _ _ _ _ -> "(" ++ prettyProofWithConfig config proof ++ ")"
  _ -> prettyProofWithConfig config proof

-- Pretty print relational judgments
prettyRelJudgment :: RelJudgment -> String
prettyRelJudgment = prettyRelJudgmentWithConfig defaultPrettyConfig

prettyRelJudgmentWithConfig :: PrettyConfig -> RelJudgment -> String
prettyRelJudgmentWithConfig config (RelJudgment t1 rtype t2) =
  let t1' = prettyTermWithConfig config t1
      r' = prettyRTypeWithConfig config rtype
      t2' = prettyTermWithConfig config t2
   in t1' ++ " [" ++ r' ++ "] " ++ t2'

-- Pretty print bindings
prettyBinding :: Binding -> String
prettyBinding binding = case binding of
  TermBinding name -> name
  RelBinding name -> name
  ProofBinding name judgment -> name ++ " : " ++ prettyRelJudgment judgment

-- Pretty print declarations
prettyDeclaration :: Declaration -> String
prettyDeclaration = prettyDeclarationWithConfig defaultPrettyConfig

prettyDeclarationWithConfig :: PrettyConfig -> Declaration -> String
prettyDeclarationWithConfig config decl = case decl of
  MacroDef name params body ->
    let paramStr = if null params then "" else " " ++ intercalate " " params
        bodyStr = case body of
          TermMacro term -> prettyTermWithConfig config term
          RelMacro rtype -> prettyRTypeWithConfig config rtype
     in name ++ paramStr ++ " := " ++ bodyStr ++ ";"
  TheoremDef name bindings judgment proof ->
    let turnstile = if useUnicode config then "⊢" else "|-"
        bindingStr =
          if null bindings
            then ""
            else "[" ++ intercalate ", " (map prettyBinding bindings) ++ "] "
        judgmentStr = prettyRelJudgmentWithConfig config judgment
        proofStr = prettyProofWithConfig config proof
     in turnstile ++ " " ++ name ++ " : " ++ bindingStr ++ judgmentStr ++ " := " ++ proofStr ++ ";"
  ImportDecl importDecl -> prettyImportDeclaration importDecl
  ExportDecl exportDecl -> prettyExportDeclaration exportDecl

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
  ProofTypingError proof expected actual ctx ->
    "Proof error: proof "
      ++ prettyProof proof
      ++ " has wrong judgment\n"
      ++ "  Expected judgment: "
      ++ prettyRelJudgment expected
      ++ "\n"
      ++ "  Actual judgment: "
      ++ prettyRelJudgment actual
      ++ prettyContext ctx
  TermConversionError t1 t1' t2 t2' ctx ->
    "Term conversion error:\n"
      ++ "  Expected: "
      ++ prettyTerm t1
      ++ " ≡ "
      ++ prettyTerm t1'
      ++ "\n"
      ++ "  Actual: "
      ++ prettyTerm t2
      ++ " ≡ "
      ++ prettyTerm t2'
      ++ "\n"
      ++ "  These terms are not β-η equivalent"
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
  InternalError msg ctx ->
    "Internal error: " ++ msg ++ prettyContext ctx

-- Helper function to pretty print error context
prettyContext :: ErrorContext -> String
prettyContext (ErrorContext pos _) =
  let filename = sourceName pos
      line = unPos (sourceLine pos)
      col = unPos (sourceColumn pos)
   in "\n" ++ getSourceContext filename line col
