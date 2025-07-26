{-# LANGUAGE OverloadedStrings #-}
module RawParser 
  ( rawTerm
  , rawRType  
  , rawProof
  , rawDeclaration
  , rawJudgment
  , rawBinding
  , parseFile
  , mixfixIdentifier
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Void
import Data.Char (isSpace)
import Control.Monad (void, when)
import           Lexer hiding (isMixfixChar)
import qualified Lexer (isMixfixChar)
import RawAst
import Text.Megaparsec
import Text.Megaparsec.Char (char, spaceChar)
import qualified Control.Monad.Combinators.Expr as E
import qualified Text.Megaparsec.Char.Lexer as L

type P = Parsec Void Text

-- Helper to capture position information
withPos :: (a -> SourcePos -> b) -> P a -> P b
withPos ctor p = ctor <$> p <*> getSourcePos

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
rawDeclaration = fixityDecl <|> rawTheorem <|> rawMacro

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
-- Term expressions (Pratt parsing)
-------------------------------------------------------------------------------

termExpr :: P RawTerm
termExpr = E.makeExprParser termAtom termTable <?> "term"

termAtom :: P RawTerm
termAtom = choice
  [ withPosAfter (\(name,body) -> RTLam name body) $ do
      _    <- lambda
      name <- identName
      _    <- dot
      body <- termExpr
      pure (name,body)
  , withPosAfter RTVar $ do
      name <- identName
      pure name
  , parens termExpr
  ] <?> "term atom"
  where 
    lambda = symbol "λ" <|> symbol "\\"
    dot = symbol "."

termTable :: [[E.Operator P RawTerm]]
termTable = 
  --   ordinary term application  t u
  [ [E.InfixL (do pos <- getSourcePos; return (\l r -> RTApp l r pos))]
  ]

-------------------------------------------------------------------------------
-- Relational type expressions (Pratt parsing)  
-------------------------------------------------------------------------------

-- | A *simple* relational‑type atom – something that **cannot** absorb further
--   space‑separated arguments.  We will use it to delimit macro arguments.
rtypeSimpleAtom :: P RawRType
rtypeSimpleAtom = choice
  [ withPosAfter RRVar identName

  , withPosAfter (\(name,body) -> RRAll name body) $ do
      _    <- forAll
      name <- identName
      _    <- dot
      body <- rtypeExpr
      pure (name,body)


  , parens rtypeExpr
  ] <?> "relational type basic atom"
  where
    forAll    = symbol "∀" <|> symbol "forall"
    dot       = symbol "."

rtypeExpr :: P RawRType
rtypeExpr = E.makeExprParser rtypeAtom rtypeTable <?> "relational type"

-- from now on an atom is *just* an atom
rtypeAtom :: P RawRType
rtypeAtom = rtypeSimpleAtom

rtypeTable :: [[E.Operator P RawRType]]
rtypeTable =
  [ [E.Postfix (do pos <- getSourcePos; _ <- (symbol "˘" <|> symbol "~"); return (\r -> RRConv r pos))]
  -- ***NEW***  ordinary application  R S
  , [E.InfixL (do pos <- getSourcePos
                  return (\l r -> RRApp l r pos))]
  , [E.InfixL (do pos <- getSourcePos
                  _   <- compOp
                  return (\l r -> RRComp l r pos))]
  , [E.InfixR (do pos <- getSourcePos; _ <- (symbol "→" <|> symbol "->"); return (\l r -> RRArr l r pos))]
  ]

-- | Relational‑composition operator.
compOp :: P Text
compOp = symbol "∘"

-------------------------------------------------------------------------------
-- Proof expressions (Pratt parsing)
-------------------------------------------------------------------------------

proofExpr :: P RawProof
proofExpr = E.makeExprParser proofAtom proofTable <?> "proof"

proofAtom :: P RawProof
proofAtom = choice
  [ withPosAfter (\(name,rtype,body) -> RPLamP name rtype body) $ do
      _     <- lambda
      name  <- identName
      _     <- colon
      rtype <- rtypeExpr
      _     <- dot
      body  <- proofExpr
      pure (name,rtype,body)
  , withPosAfter (\(name,body) -> RPLamT name body) $ do
      _    <- typeLambda
      name <- identName
      _    <- dot
      body <- proofExpr
      pure (name,body)
  , withPosAfter (\(t1,t2) -> RPIota t1 t2) $ do
      _       <- iota
      (t1,t2) <- angles (commaSep2 termExpr)
      pure (t1,t2)
  -- (no longer here – handled as prefix ops in table)
  , withPosAfter (\(x,t1,t2,p1,p2) -> RPRho x t1 t2 p1 p2) $ do
      _       <- rho
      (x,t1,t2) <- braces $ do
        x       <- identName
        _       <- dot
        (t1,t2) <- commaSep2 termExpr
        pure (x,t1,t2)
      p1      <- proofExpr
      _       <- symbol "-"
      p2      <- proofExpr
      pure (x,t1,t2,p1,p2)
  , withPosAfter (\(p,x,u,v,q) -> RPPi p x u v q) $ do
      _ <- piSymbol
      parsePiDash
  , withPosAfter (\(p1,p2) -> RPPair p1 p2) . try $ do
      (p1,p2) <- parens (commaSep2 proofExpr)
      pure (p1,p2)
  , withPosAfter RPVar $ do
      name <- identName
      pure name
  , parens proofExpr
  , withPosAfter (\(t1,p,t2) -> RPConv t1 p t2) . try $ do
      t1 <- termExpr
      _  <- convUp
      p  <- proofExpr
      _  <- convDown
      t2 <- termExpr
      pure (t1,p,t2)
  ] <?> "proof atom"
  where
    parsePiDash = do
      p   <- proofExpr          -- no parentheses
      _   <- symbol "-"
      x   <- identName          -- term variable x
      _   <- dot
      u   <- identName          -- proof variable u
      _   <- dot
      v   <- identName          -- proof variable v
      _   <- dot
      q   <- proofExpr
      pure (p,x,u,v,q)

    lambda = symbol "λ" <|> symbol "\\"
    typeLambda = symbol "Λ" <|> symbol "/\\"
    dot = symbol "."
    colon = symbol ":"
    iota = symbol "ι" <|> symbol "iota"  
    rho = symbol "ρ" <|> symbol "rho"
    piSymbol = symbol "π" <|> symbol "pi"
    convUp = symbol "⇃" <|> symbol "conv_up"
    convDown = symbol "⇂" <|> symbol "conv_down"

convIntro, convElim :: P Text
convIntro = symbol "∪ᵢ" <|> symbol "conv_intro"
convElim  = symbol "∪ₑ" <|> symbol "conv_elim"

proofTable :: [[E.Operator P RawProof]]
proofTable =
  -- ∪ᵢ p    ∪ₑ p
  [ [ E.Prefix $ do pos <- getSourcePos
                    _   <- convIntro
                    pure (\p -> RPConvIntro p pos)
    , E.Prefix $ do pos <- getSourcePos
                    _   <- convElim
                    pure (\p -> RPConvElim  p pos) ]
  -- p {T}
  , [E.Postfix $ do
        rty <- braces rtypeExpr
        pos <- getSourcePos
        pure (\p -> RPAppT p rty pos)]
  -- Ordinary proof application  p q
  , [E.InfixL (do pos <- getSourcePos
                  pure (\l r -> RPApp l r pos))]
  ]

-------------------------------------------------------------------------------
-- Declaration parsing
-------------------------------------------------------------------------------

rawMacro :: P RawDeclaration
rawMacro = do
  name <- mixfixIdentifier
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
  -- A term body must be followed immediately by ';'.  If not, we
  -- back‑track and let the relational‑type parser have a go.  This
  -- prevents inputs such as "A → B" from being mis‑classified.
  (RawTermBody <$> try (termExpr <* lookAhead (symbol ";")))
    <|> (RawRelBody <$> rtypeExpr)

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
  name <- mixfixIdentifier
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

mixfixIdentifier :: P Name
mixfixIdentifier = lexeme . try $ do
  txt <- T.pack <$> some (satisfy Lexer.isMixfixChar) <?> "mixfix identifier"
  pure (Name txt)

angles :: P a -> P a
angles = between (symbol "⟨" <|> symbol "<") (symbol "⟩" <|> symbol ">")

-- Parse two comma-separated items of the same type
commaSep2 :: P a -> P (a, a)
commaSep2 p = do
  a <- p
  _ <- symbol ","
  b <- p
  return (a, b)
