{-# LANGUAGE OverloadedStrings #-}
-- | Raw parser using the new grammar-based mixfix system
--
-- This module provides the main parsing entry points for RelTT source files,
-- implementing the unified Raw AST with full mixfix support.
module Parser.Raw 
  ( raw
  , rawDeclaration  
  , rawJudgment
  , rawBinding
  , parseFile
  , -- Re-export parser types for compatibility
    RawParser
  ) where

import           Control.Monad (when, void)
import           Control.Monad.Reader
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Void (Void)
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- Import core system
import           Core.Raw
import           Core.Syntax (VarKind(..))
import           Parser.Lexer

-- Import new mixfix system
import           Mixfix.Core
import           Mixfix.Env
import           Mixfix.Parse  
import           Mixfix.Util
import           Mixfix.Recover
import           Mixfix.Pretty

-- | Parser type for Raw expressions with mixfix environment
type RawParser = ParsecT Void Text (Reader Env)

------------------------------------------------------------
-- Core expression parsing
------------------------------------------------------------

-- | Parse a raw expression using the mixfix system
raw :: RawParser (Node Raw)
raw = exprP 1  -- Start with minimum precedence

-- | Parse expression at specific precedence level  
rawExpr :: Int -> RawParser (Node Raw)
rawExpr = exprP

------------------------------------------------------------
-- MixfixCat-specific implementations
------------------------------------------------------------

-- | Leaf parser for Raw category
instance MixfixCat Raw => Parser (Leaf Raw) where
leafParser = choice
  [ RawLeafNode . RawVarLeaf . Name <$> identifier
  , RawLeafNode . RawLitLeaf <$> literalText
  ] <?> "identifier or literal"

-- | Atom parser for Raw category  
atom :: RawParser (Node Raw)
atom = choice
  [ mkLeaf <$> leafParser
  , between (symbol "(") (symbol ")") (exprP 1)
  ] <?> "atom"

------------------------------------------------------------
-- Declaration parsing
------------------------------------------------------------

-- | Parse a top-level declaration
rawDeclaration :: RawParser RawDeclaration
rawDeclaration = choice
  [ rawMacro
  , rawTheorem  
  , rawImportDecl
  ] <?> "declaration"

-- | Parse a macro definition with new mixfix support
rawMacro :: RawParser RawDeclaration  
rawMacro = do
  _ <- symbol "macro"
  name <- Name <$> identifier
  params <- many (Name <$> identifier)
  _ <- symbol ":"
  
  -- Parse macro signature and body
  holeTypes <- parseMacroSignature
  _ <- symbol ":="
  body <- rawMacroBody
  _ <- symbol ";"
  
  -- Register the macro in the environment (would need proper implementation)
  return $ RawMacroDef name params body

-- | Parse a theorem declaration
rawTheorem :: RawParser RawDeclaration
rawTheorem = do
  _ <- symbol "⊢" <|> symbol "|-"
  name <- Name <$> identifier
  bindings <- many rawBinding
  _ <- symbol ":"
  judgment <- rawJudgment
  _ <- symbol ":="
  proof <- raw
  _ <- symbol ";"
  return $ RawTheorem name bindings judgment (extractRaw proof)

-- | Parse import declaration
rawImportDecl :: RawParser RawDeclaration
rawImportDecl = do
  _ <- symbol "import"
  path <- stringLiteral
  _ <- symbol ";"
  return $ RawImportDecl (RawImportModule path)

------------------------------------------------------------
-- Macro body and signature parsing
------------------------------------------------------------

-- | Parse macro body
rawMacroBody :: RawParser RawMacroBody
rawMacroBody = choice
  [ RawTermBody . extractRaw <$> try (raw <* lookAhead (symbol ";"))
  , RawRelBody . extractRaw <$> try (raw <* lookAhead (symbol ";"))  
  , RawProofBody . extractRaw <$> (raw <* lookAhead (symbol ";"))
  ] <?> "macro body"

-- | Parse macro signature (placeholder - needs full implementation)
parseMacroSignature :: RawParser [Text]
parseMacroSignature = do
  -- This would parse the full macro signature with typed holes
  -- For now, return empty list
  return []

------------------------------------------------------------
-- Judgment and binding parsing
------------------------------------------------------------

-- | Parse a relational judgment
rawJudgment :: RawParser RawJudgment
rawJudgment = do
  t1 <- raw
  r <- brackets raw
  t2 <- raw
  return $ RawJudgment (extractRaw t1) (extractRaw r) (extractRaw t2)

-- | Parse a parameter binding
rawBinding :: RawParser RawBinding
rawBinding = parens $ do
  name <- Name <$> identifier
  _ <- symbol ":"
  choice
    [ RawTermBinding name <$ (symbol "Term" <|> symbol "term")
    , RawRelBinding name <$ (symbol "Rel" <|> symbol "rel")
    , RawProofBinding name <$> rawJudgment
    ] <?> "binding type"

------------------------------------------------------------
-- File parsing
------------------------------------------------------------

-- | Parse an entire file
parseFile :: RawParser [RawDeclaration]
parseFile = do
  skipSpace
  decls <- many rawDeclaration
  eof
  return decls

------------------------------------------------------------
-- Helper parsers
------------------------------------------------------------

-- | Parse an identifier
identifier :: RawParser String
identifier = lexeme $ do
  first <- letterChar <|> char '_'
  rest <- many (alphaNumChar <|> char '_' <|> char '\'')
  let ident = first : rest
  when (ident `elem` reservedWords) $
    fail $ "Unexpected reserved word: " ++ ident
  return ident

-- | Parse a string literal  
stringLiteral :: RawParser String
stringLiteral = lexeme $ between (char '"') (char '"') $
  many (noneOf ['"', '\\'] <|> (char '\\' >> anySingle))

-- | Parse literal text
literalText :: RawParser Text
literalText = T.pack <$> choice
  [ stringLiteral
  , some alphaNumChar
  ]

-- | Reserved words
reservedWords :: [String]
reservedWords = 
  [ "macro", "theorem", "import", "Term", "term", "Rel", "rel"
  , "if", "then", "else", "let", "in", "where"
  ]

-- | Parse a symbol with whitespace handling
symbol :: Text -> RawParser Text
symbol s = lexeme (string s)

-- | Apply lexeme to handle whitespace
lexeme :: RawParser a -> RawParser a
lexeme p = p <* skipSpace

-- | Skip whitespace and comments
skipSpace :: RawParser ()
skipSpace = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

-- | Parse parentheses
parens :: RawParser a -> RawParser a
parens = between (symbol "(") (symbol ")")

-- | Parse square brackets
brackets :: RawParser a -> RawParser a  
brackets = between (symbol "[") (symbol "]")

-- | Parse braces
braces :: RawParser a -> RawParser a
braces = between (symbol "{") (symbol "}")

------------------------------------------------------------
-- Utility functions
------------------------------------------------------------

-- | Extract Raw from Node Raw (for compatibility)
extractRaw :: Node Raw -> Raw
extractRaw (RawNode raw) = raw

-- | Create a Node Raw from Raw (for compatibility)
wrapRaw :: Raw -> Node Raw
wrapRaw = RawNode

-- | Convert SourcePos to Span
posToSpan :: SourcePos -> Span
posToSpan pos = (pos, pos)

-- | Get span from Raw
rawSpan :: Raw -> Span
rawSpan (RawVar _ span) = span
rawSpan (RawApp _ _ span) = span
rawSpan (RawParens _ span) = span
rawSpan (RawMixfix _ _ span) = span

------------------------------------------------------------
-- Built-in macros and operators
------------------------------------------------------------

-- | Initialize built-in macros for RelTT
initBuiltinMacros :: Env -> Env
initBuiltinMacros env = env
  -- This would add built-in operators like:
  -- - Application (space)
  -- - Lambda abstraction (λ x . body)
  -- - Arrow types (A → B)  
  -- - Composition (∘)
  -- - Converse (˘)
  -- - Promotion (⌈⌉)
  -- - Iota (ι⟨_,_⟩)
  -- For now, just return unchanged environment

------------------------------------------------------------
-- Error recovery integration
------------------------------------------------------------

-- | Parse with error recovery
parseWithRecovery :: RawParser (Node Raw) -> RawParser (Node Raw)
parseWithRecovery parser = 
  recoverWith defaultRecoveryConfig parser

-- | Parse declaration with recovery
parseDeclarationWithRecovery :: RawParser RawDeclaration -> RawParser RawDeclaration
parseDeclarationWithRecovery parser = do
  result <- observing parser
  case result of
    Right decl -> return decl
    Left err -> do
      -- Skip to next declaration boundary
      _ <- manyTill anySingle (try (symbol ";") <|> eof)
      -- Return a dummy declaration (would need proper error node)
      fail "Parse error in declaration"