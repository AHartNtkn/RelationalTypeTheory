{-# LANGUAGE OverloadedStrings #-}
module Parser.Raw 
  ( rawTerm
  , rawRType  
  , rawProof
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

-- =====================================================================
-- Helpers: extract the SourcePos carried by the *right‑hand* operand.
-- We put them here (parser layer) to avoid orphan instances elsewhere.
-- =====================================================================

posT :: RawTerm  -> SourcePos
posT (RTVar   _ p)   = p
posT (RTLam   _ _ p) = p
posT (RTApp   _ _ p) = p
posT (RTMacro _ _ p) = p

posR :: RawRType -> SourcePos
posR (RRVar   _ p)   = p
posR (RRArr   _ _ p) = p
posR (RRAll   _ _ p) = p
posR (RRComp  _ _ p) = p
posR (RRConv  _   p) = p
posR (RRMacro _ _ p) = p
posR (RRApp   _ _ p) = p
posR (RRProm  _   p) = p

posP :: RawProof -> SourcePos
posP (RPVar         _ p) = p
posP (RPApp         _ _ p) = p
posP (RPTheorem     _ _ p) = p
posP (RPLamP        _ _ _ p) = p
posP (RPLamT        _ _ p) = p
posP (RPAppT        _ _ p) = p
posP (RPConv        _ _ _ p) = p
posP (RPIota        _ _ p) = p
posP (RPRho         _ _ _ _ _ p) = p
posP (RPPi          _ _ _ _ _ p) = p
posP (RPConvIntro   _ p) = p
posP (RPConvElim    _ p) = p
posP (RPPair        _ _ p) = p
posP (RPMixfix      _ _ p) = p

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

rawTerm :: P RawTerm
rawTerm = termExpr

rawRType :: P RawRType  
rawRType = rtypeExpr

rawProof :: P RawProof
rawProof = proofExpr

rawDeclaration :: P RawDeclaration
rawDeclaration = fixityDecl <|> rawTheorem <|> rawMacro <|> rawImportDecl

rawJudgment :: P RawJudgment
rawJudgment = do
  t1 <- rawTerm
  r <- brackets rawRType
  t2 <- rawTerm  
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
-- Term expressions
-------------------------------------------------------------------------------

termExpr :: P RawTerm
termExpr = do
  atoms <- some termAtom         -- 1 +  atoms
  pure (foldl1' mk atoms)
  where
    mk l r = RTApp l r (posT r)

termAtom :: P RawTerm
termAtom = choice
  [ withPosAfter RTVar (identName <* notFollowedBy (symbol ":")) -- avoid "x :"
  , parens termExpr
  ] <?> "term atom"
-- no termTable needed any more

-------------------------------------------------------------------------------
-- Relational type expressions
-------------------------------------------------------------------------------

-- | A *simple* relational‑type atom – something that **cannot** absorb further
--   space‑separated arguments.  We will use it to delimit macro arguments.
rtypeSimpleAtom :: P RawRType
rtypeSimpleAtom = choice
  [ withPosAfter RRVar identName
  , parens rtypeExpr
  ] <?> "relational type basic atom"

rtypeExpr :: P RawRType
rtypeExpr = do
  atoms <- some rtypeAtom
  pure (foldl1' (\l r -> RRApp l r (posR r)) atoms)

rtypeAtom :: P RawRType
rtypeAtom = rtypeSimpleAtom
-- no rtypeTable needed

-------------------------------------------------------------------------------
-- Proof expressions
-------------------------------------------------------------------------------

proofExpr :: P RawProof
proofExpr = do
  atoms <- some proofAtom
  pure (foldl1' mk atoms)
  where
    mk l r = RPApp l r (posP r)

proofAtom :: P RawProof
proofAtom = choice
  [ withPosAfter RPVar identName
  , parens proofExpr
  ] <?> "proof atom"
-- no proofTable needed

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
  return $ RawMacro name params body

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
      (RawTermBody  <$> try (termExpr  <* lookAhead (symbol ";")))
  <|> (RawRelBody   <$> try (rtypeExpr <* lookAhead (symbol ";")))
  <|> (RawProofBody <$> (proofExpr <* lookAhead (symbol ";")))

rawTheorem :: P RawDeclaration  
rawTheorem = do
  _ <- symbol "⊢" <|> symbol "|-"
  name <- identName
  bindings <- many rawBinding
  _ <- symbol ":"
  judgment <- rawJudgment
  _ <- coloneqq  
  proof <- rawProof
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
