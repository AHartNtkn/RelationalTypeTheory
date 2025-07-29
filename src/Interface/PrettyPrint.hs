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
    prettyImportDeclaration,
    prettyExportDeclaration,
    prettyRelJudgmentWithConfig,
    prettyDeclarationWithConfig,
    prettyTheoremArgWithConfig,
  )
where

import Data.List (intercalate)
import Core.Syntax
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


-- Pretty print theorem arguments
prettyTheoremArgWithConfig :: PrettyConfig -> TheoremArg -> String
prettyTheoremArgWithConfig config arg = case arg of
  TermArg term -> "(" ++ prettyWithConfig config term ++ ")"
  RelArg rtype -> "(" ++ prettyWithConfig config rtype ++ ")"
  ProofArg proof -> "(" ++ prettyWithConfig config proof ++ ")"


