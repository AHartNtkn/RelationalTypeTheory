{-# LANGUAGE OverloadedStrings #-}
module Parser.Raw 
  ( raw
  , rawDeclaration
  , rawJudgment
  , rawBinding
  , parseFile
  ) where

import Data.Void
import Control.Monad (when)
import           Parser.Lexer
import Core.Raw
import Core.Syntax (Fixity(..))
import Text.Megaparsec
-- application is now parsed explicitly, so we do not need Expr here
import qualified Text.Megaparsec.Char.Lexer as L
import Data.List     (foldl1')

type P = Parsec Void String

-- Helper to extract the SourcePos from Raw
posR :: Raw -> SourcePos
posR (RawVar   _ p)   = p
posR (RawApp   _ _ p) = p
posR (RawParens _ p)  = p

-- Helper to capture position information

-- | Run a sub-parser and attach the source position *after*
--   that sub-parser. Gives the position of the first character
--   belonging to the construct, which is what the elaborator
--   expects.
withPosAfter :: (a -> SourcePos -> b) -> P a -> P b
withPosAfter ctor p = do
  x   <- p
  pos <- getSourcePos
  pure (ctor x pos)

-------------------------------------------------------------------------------
-- Entry points for parsing different syntactic categories
-------------------------------------------------------------------------------

raw :: P Raw
raw = rawExpr

rawDeclaration :: P RawDeclaration
rawDeclaration = fixityDecl <|> rawTheorem <|> rawMacro <|> rawImportDecl

rawJudgment :: P RawJudgment
rawJudgment = do
  t1 <- raw
  r <- brackets raw
  t2 <- raw  
  return $ RawJudgment t1 r t2

rawBinding :: P RawBinding
rawBinding = parens $ do
  name <- identName
  _ <- symbol ":"
  choice
    [ RawTermBinding  name <$  (symbol "Term" <|> symbol "term")
    , RawRelBinding   name <$  (symbol "Rel"  <|> symbol "rel")
    , RawProofBinding name <$> rawJudgment
    ]

parseFile :: P [RawDeclaration]
parseFile = do
  sc
  decls <- many rawDeclaration
  eof
  return decls

-------------------------------------------------------------------------------
-- Raw expressions
-------------------------------------------------------------------------------

rawExpr :: P Raw
rawExpr = do
  atoms <- some rawAtom         -- 1 +  atoms
  pure (foldl1' mk atoms)
  where
    mk l r = RawApp l r (posR r)

rawAtom :: P Raw
rawAtom = choice
  [ withPosAfter RawVar (identName <* notFollowedBy (symbol ":")) -- avoid "x :"
  , withPosAfter RawParens (parens rawExpr)
  ] <?> "raw atom"

-------------------------------------------------------------------------------
-- Declaration parsing
-------------------------------------------------------------------------------

rawMacro :: P RawDeclaration
rawMacro = do
  name <- identName
  params <- many identName
  _ <- coloneqq
  body <- rawMacroBody
  _ <- symbol ";"
  return $ RawMacroDef name params body

-- | The order matters!  We have to try the *longer* grammar (terms) first,
-- otherwise something like   "unknown_macro x"   is half‑parsed as a
-- relational variable and the trailing argument triggers an unexpected‑token
-- error.  Switching the order fixes bug #4.
rawMacroBody :: P RawMacroBody
rawMacroBody =
  -- Try term first (must be followed immediately by ';')
  -- Then try relational type (must be followed immediately by ';')  
  -- Finally try proof (must be followed immediately by ';')
  -- This prevents ambiguous parses and ensures correct classification
      (RawTermBody  <$> try (raw  <* lookAhead (symbol ";")))
  <|> (RawRelBody   <$> try (raw <* lookAhead (symbol ";")))
  <|> (RawProofBody <$> (raw <* lookAhead (symbol ";")))

rawTheorem :: P RawDeclaration  
rawTheorem = do
  _ <- symbol "⊢" <|> symbol "|-"
  name <- identName
  bindings <- many rawBinding
  _ <- symbol ":"
  judgment <- rawJudgment
  _ <- coloneqq  
  proof <- raw
  _ <- symbol ";"
  return $ RawTheorem name bindings judgment proof

fixityDecl :: P RawDeclaration
fixityDecl = label "fixity declaration" $ do
  fixity <- choice
    [ Infixl  <$> prefix "infixl"
    , Infixr  <$> prefix "infixr"
    , InfixN  <$> prefix "infix"
    , Prefix  <$> prefix "prefix"
    , Postfix <$> prefix "postfix"
    ]
  name <- identName
  _ <- symbol ";"
  pure (RawFixityDecl fixity name)
 where
  prefix kw = do
    _ <- symbol kw
    n <- L.decimal <* sc
    when (n < 0 || n > 9) $
      fail "precedence must be between 0 and 9"
    pure n

-------------------------------------------------------------------------------
-- Helper parsers
-------------------------------------------------------------------------------

identName :: P Name
identName = Name <$> ident

-- Import declaration parser
rawImportDecl :: P RawDeclaration
rawImportDecl = label "import declaration" $ do
  _ <- symbol "import"
  path <- stringLiteral
  _ <- symbol ";"
  pure (RawImportDecl (RawImportModule path))

-- String literal parser  
stringLiteral :: P String
stringLiteral = stringLit