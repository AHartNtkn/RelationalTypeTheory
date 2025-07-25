{-# LANGUAGE OverloadedStrings #-}
module RawParser
  ( RawTerm(..)
  , RawRType(..)
  , RawProof(..)
  , RawRelJudgment(..)
  , RawBinding(..)
  , RawMacroBody(..)
  , RawDeclaration(..)
  , RawImportDeclaration(..)
  , RawExportDeclaration(..)
  , RawFixity(..)
  , FixityMap
  , parseTerm, parseRType, parseProof, parseFile
  , parseDeclaration, parseRelJudgment, parseBinding
  , parseImportDeclaration, parseExportDeclaration
  , parseTermWithFixities
  , runParserEmpty, stringLiteral, identifier, operator, mixfixIdentifier
  ) where

import Control.Monad       (void)
import Data.Void
import qualified Data.Map as Map
import qualified Text.Megaparsec as M
import Text.Megaparsec           ((<|>), (<?>), try, many, some, manyTill, optional, oneOf, anySingle, satisfy)
import Text.Megaparsec.Char
import Data.Char (isLetter, isSpace)
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr (Operator(..), makeExprParser)

-- ───────────────────────── 1. Raw AST  ──────────────────────────

type RawName = String

-- | Token types for maximal-munch operator parsing
data Token
  = TIdent String | TOp String
  | TIota | TAngleL | TAngleR | TComma  
  | TLParen | TRParen | TEOF
  deriving (Eq, Show)

-- | Fixity information for operators
data Associativity = LeftAssoc | RightAssoc | NonAssoc deriving (Show, Eq)
type FixityMap = Map.Map String (Associativity, Int)

-- | Convert RawFixity to Associativity and precedence
rawFixityToAssoc :: RawFixity -> (Associativity, Int)
rawFixityToAssoc (RawInfixl n) = (LeftAssoc, n)
rawFixityToAssoc (RawInfixr n) = (RightAssoc, n)
rawFixityToAssoc (RawInfixN n) = (NonAssoc, n)
rawFixityToAssoc (RawPrefix n) = (LeftAssoc, n)  -- Treat as left-assoc for now
rawFixityToAssoc (RawPostfix n) = (LeftAssoc, n) -- Treat as left-assoc for now

data RawTerm
  = RTVar RawName
  | RTLam RawName RawTerm
  | RTApp RawTerm RawTerm
  | RTMacro RawName [RawTerm]  -- still raw; resolved later
  | RawOp String                -- operator tokens for mixfix desugaring
  deriving (Show,Eq)

data RawRType
  = RRVar RawName
  | RRArr RawRType RawRType
  | RRAll RawName RawRType
  | RRComp RawRType RawRType
  | RRConv RawRType
  | RRProm RawTerm
  | RRMacro RawName [RawRType]
  deriving (Show,Eq)

data RawProof
  = RPVar RawName                 -- may be proof‑var or theorem, resolved later
  | RPLam RawName RawRType RawProof
  | RPTyLam RawName RawProof
  | RPApp RawProof RawProof
  | RPTyApp RawProof RawRType
  deriving (Show,Eq)

data RawRelJudgment = RawRelJudgment RawTerm RawRType RawTerm
  deriving (Show,Eq)

data RawBinding
  = RawTermBinding RawName
  | RawRelBinding RawName  
  | RawProofBinding RawName RawRelJudgment
  deriving (Show,Eq)

data RawMacroBody = RawMacroBodySrc String
  deriving (Show,Eq)

data RawDeclaration
  = RawMacroDef RawName [RawName] RawMacroBody
  | RawTheoremDef RawName [RawBinding] RawRelJudgment RawProof
  | RawImportDecl RawImportDeclaration
  | RawExportDecl RawExportDeclaration
  | RawFixityDecl RawFixity RawName
  deriving (Show,Eq)

data RawImportDeclaration
  = RawImportModule String
  | RawImportModuleAs String String
  | RawImportOnly String [String]
  deriving (Show,Eq)

data RawExportDeclaration
  = RawExportSymbols [String]
  deriving (Show,Eq)

data RawFixity
  = RawInfixl Int
  | RawInfixr Int
  | RawInfixN Int
  | RawPrefix Int
  | RawPostfix Int
  deriving (Show,Eq)

-- ───────────────────────── 2. Parser setup ──────────────────────

type Parser = M.Parsec Void String

-- | Space consumer that requires at least one space (for operators/keywords)
sc1 :: Parser ()
sc1 = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

-- | Space consumer that allows zero spaces (for delimiters at EOF)
sc0 :: Parser ()
sc0 = L.space (void spaceChar) (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

-- | Legacy alias for compatibility
sc :: Parser ()
sc = sc1

scn :: Parser ()
scn = L.space (void spaceChar) (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc1

lexeme0 :: Parser a -> Parser a
lexeme0 = L.lexeme sc0

symbol :: String -> Parser String
symbol = L.symbol sc1

symbol0 :: String -> Parser String
symbol0 = L.symbol sc0

-- | Parse specific token (simplified version)
token :: Token -> Parser ()
token TAngleL = void (symbol0 "⟨" <|> symbol0 "<")
token TAngleR = void (symbol0 "⟩" <|> symbol0 ">")
token TComma = void (symbol0 ",")
token TLParen = void (symbol0 "(")
token TRParen = void (symbol0 ")")
token TIota = void (symbol0 "ι⟨" <|> symbol0 "ι<" <|> symbol0 "iota<")
token _ = fail "unsupported token"

-- | Reusable angle bracket combinator  
angles :: Parser a -> Parser a
angles = M.between (token TAngleL <?> "⟨ or <")
                   (token TAngleR <?> "⟩ or >")

parens :: Parser a -> Parser a
parens = M.between (symbol0 "(") (symbol0 ")")

identifierRaw :: Parser RawName
identifierRaw = do
  c <- letterChar
  if c `elem` ['Λ','λ','∀','∃','ρ','ι','∪']
    then fail "reserved character"
    else do
      rest <- many (alphaNumChar <|> char '_' <|> char '\'')
      pure (c:rest)

identifier :: Parser RawName
identifier = lexeme . try $ 
  -- Try atomic tokens first
  (symbol0 "ι⟨" >> return "ι⟨") <|>
  (symbol0 "ι<" >> return "ι<") <|>  
  (symbol0 "iota<" >> return "iota<") <|>
  (symbol0 "ρ{" >> return "ρ{") <|>
  (symbol "∪ᵢ" >> return "∪ᵢ") <|>                 -- Unicode conversion intro (requires whitespace)
  (symbol "∪ₑ" >> return "∪ₑ") <|>                 -- Unicode conversion elim (requires whitespace)
  (symbol "convIntro" >> return "convIntro") <|>   -- ASCII alternative (requires whitespace)
  (symbol "convElim" >> return "convElim") <|>     -- ASCII alternative (requires whitespace)
  (symbol "π" >> return "π") <|>                   -- Pi token (requires whitespace)
  (symbol "pi" >> return "pi") <|>                 -- ASCII pi alternative (requires whitespace)
  (symbol "-" >> return "-") <|>                   -- Dash for pi syntax (requires whitespace)
  (symbol0 "." >> return ".") <|>                  -- Dot as atomic token (banned from user expressions)
  (symbol0 "," >> return ",") <|>                  -- Add comma as a token
  (symbol0 "⟩" >> return "⟩") <|>  -- Add closing angle bracket as a token
  (symbol0 ">" >> return ">") <|>  -- Add closing angle bracket as a token
  -- Then try regular identifiers
  (do _ <- M.lookAhead (satisfy (\ch -> isLetter ch && ch `notElem` reserved))
      first <- letterChar
      rest <- many (alphaNumChar <|> char '_' <|> char '\'')
      pure (first:rest))
  where
    reserved = ['Λ','λ','∀','∃']  -- Remove ρ, ι, ∪ since they're handled as atomic tokens

-- Parser for mixfix identifiers (allows underscores at beginning and end)
mixfixIdentifier :: Parser RawName
mixfixIdentifier = lexeme $ do
  parts <- some (underscorePart <|> namePart <|> operatorPart)
  return (concat parts)
  where
    underscorePart = string "_"
    namePart = some (alphaNumChar <|> oneOf ("'!?" :: String))
    operatorPart = some operatorChar

-- | Check if character can be part of an operator
isOpChar :: Char -> Bool
isOpChar c = not (isSpace c) && c `notElem` (";,.(){}[]\"'" :: String)

-- | Parse operator or bracket with maximal-munch
opOrBracket :: Parser Token
opOrBracket = lexeme0 $ do
  s <- some (satisfy isOpChar)
  pure $ case s of
    "<"  -> TAngleL
    ">"  -> TAngleR  
    "⟨"  -> TAngleL
    "⟩"  -> TAngleR
    _    -> TOp s

-- Parser for operator tokens (for mixfix support)
operatorChar :: Parser Char
operatorChar = satisfy isOpChar

operator :: Parser String
operator = lexeme $ some operatorChar

-- Helpers for postfix parsing
binaryL :: String -> (a -> a -> a) -> Parser (a -> a -> a)
binaryL op f = f <$ symbol op


-- ─────────────────────── 3. Fixity collection (Pass 0) ─────────

-- | Collect all fixity declarations from input (simplified approach)
collectFixities :: Parser FixityMap
collectFixities = Map.fromList <$> many (try parseFixityDecl)
  where
    parseFixityDecl = do
      -- Skip to the next fixity declaration
      _ <- manyTill anySingle (M.lookAhead (symbol "infixl" <|> symbol "infixr" <|> symbol "infix" <|> symbol "prefix" <|> symbol "postfix"))
      fixity <- parseRawFixity
      name <- mixfixIdentifier
      _ <- symbol ";"
      return (name, rawFixityToAssoc fixity)

parseRawFixity :: Parser RawFixity
parseRawFixity = 
      RawInfixl <$> (symbol "infixl" *> L.decimal)
  <|> RawInfixr <$> (symbol "infixr" *> L.decimal)  
  <|> RawInfixN <$> (symbol "infix" *> L.decimal)
  <|> RawPrefix <$> (symbol "prefix" *> L.decimal)
  <|> RawPostfix <$> (symbol "postfix" *> L.decimal)


-- ─────────────────────── 4. Dynamic term grammar (Pass 1) ──────

-- | Build operator table from fixity map
buildTermTable :: FixityMap -> [[Operator Parser RawTerm]]
buildTermTable fixities = 
  let operators = Map.toList fixities
      grouped = groupByPrecedence operators
  in map (map buildOperator) grouped ++ [[ InfixL (RTApp <$ sc) ]] -- Application at lowest precedence
  where
    groupByPrecedence :: [(String, (Associativity, Int))] -> [[(String, (Associativity, Int))]]
    groupByPrecedence ops = 
      let precs = map (snd . snd) ops
          maxPrec = if null precs then 0 else maximum precs
      in [[(name, assocPrec) | (name, assocPrec@(_, prec)) <- ops, prec == p] | p <- [maxPrec, maxPrec-1..1]]
    
    buildOperator :: (String, (Associativity, Int)) -> Operator Parser RawTerm
    buildOperator (name, (LeftAssoc, _)) = InfixL (binaryL name (\l r -> RTApp (RTApp (RTVar name) l) r))
    buildOperator (name, (RightAssoc, _)) = InfixR (binaryL name (\l r -> RTApp (RTApp (RTVar name) l) r))  
    buildOperator (name, (NonAssoc, _)) = InfixN (binaryL name (\l r -> RTApp (RTApp (RTVar name) l) r))

-- | Parse terms with given fixity map
parseTermWithFixities :: FixityMap -> Parser RawTerm
parseTermWithFixities fixities = sc *> makeExprParser (termAtomWithFixities fixities) (buildTermTable fixities) <?> "term"

-- | Default parseTerm uses empty fixity map
parseTerm :: Parser RawTerm
parseTerm = parseTermWithFixities Map.empty

-- | Parse term atoms with fixity context
termAtomWithFixities :: FixityMap -> Parser RawTerm
termAtomWithFixities fixities =
      parens (parseTermWithFixities fixities)
  <|> parseLambdaWithFixities fixities
  <|> try (RawOp <$> operator)  -- Try operator first before identifier
  <|> RTVar <$> identifier
  <?> "term atom"


parseLambdaWithFixities :: FixityMap -> Parser RawTerm
parseLambdaWithFixities fixities = do
  _ <- symbol "\\" <|> symbol "λ"
  x <- identifier
  _ <- symbol "."
  body <- parseTermWithFixities fixities
  return (RTLam x body)


-- ───────────────────── 4. Relation‑type grammar ─────────────────

rTypeTable :: [[Operator Parser RawRType]]
rTypeTable =
  [ [ Postfix (RRConv <$ (symbol "˘" <|> symbol "^")) ]
  , [ InfixL (binaryL "∘" RRComp) ]
  , [ InfixR (binaryL "->" RRArr)
    , InfixR (binaryL "→"  RRArr) ]
  ]

parseRType :: Parser RawRType
parseRType = parseRTypeWithFixities Map.empty

parseRTypeWithFixities :: FixityMap -> Parser RawRType
parseRTypeWithFixities fixities = sc *> makeExprParser (rTypeAppWithFixities fixities) rTypeTable <?> "type"

-- Parse relational type applications (like "List A" or "Pair A B")
rTypeAppWithFixities :: FixityMap -> Parser RawRType
rTypeAppWithFixities fixities = do
  atoms <- some (rTypeAtomWithFixities fixities)
  case atoms of
    [single] -> return single
    (RRVar name : args) -> return (RRMacro name args)
    _ -> fail "invalid type application"

rTypeAtomWithFixities :: FixityMap -> Parser RawRType
rTypeAtomWithFixities fixities =
      parseForallWithFixities fixities
  <|> RRProm <$> (symbol "prom" *> parseTermWithFixities fixities)
  <|> RRVar <$> identifier
  <|> parens (try (parseRTypeWithFixities fixities) <|> (RRProm <$> parseTermWithFixities fixities))
  <?> "type atom"

parseForallWithFixities :: FixityMap -> Parser RawRType
parseForallWithFixities fixities = do
  _ <- symbol "forall" <|> symbol "∀"
  x <- identifier
  _ <- symbol "."
  body <- parseRTypeWithFixities fixities
  return (RRAll x body)

-- ───────────────────── 5. Proof grammar  ────────────────────────

proofTable :: [[Operator Parser RawProof]]
proofTable =
  [ [ Postfix tyApp ]
  , [ InfixL (RPApp <$ sc) ]      -- application by space
  ]

tyApp :: Parser (RawProof -> RawProof)
tyApp = do
  _ <- symbol0 "{"
  ty <- parseRType
  _ <- symbol0 "}"
  return (`RPTyApp` ty)

parseProof :: Parser RawProof
parseProof = parseProofWithFixities Map.empty

-- ───────────────────── 6. Declarations ──────────────────────────

parseRelJudgment :: Parser RawRelJudgment
parseRelJudgment = parseRelJudgmentWithFixities Map.empty

parseRelJudgmentWithFixities :: FixityMap -> Parser RawRelJudgment
parseRelJudgmentWithFixities fixities = do
  t1 <- parseTermWithFixities fixities
  _ <- symbol0 "["
  rel <- parseRTypeWithFixities fixities
  _ <- symbol0 "]"
  t2 <- parseTermWithFixities fixities
  return (RawRelJudgment t1 rel t2)

parseBinding :: Parser RawBinding
parseBinding = parseBindingWithFixities Map.empty

parseBindingWithFixities :: FixityMap -> Parser RawBinding
parseBindingWithFixities fixities = try parseTermBinding <|> try parseRelBinding <|> parseProofBinding
  where
    parseTermBinding = do
      _ <- symbol0 "("
      x <- identifier
      _ <- symbol ":"
      _ <- symbol "Term"
      _ <- symbol0 ")"
      return (RawTermBinding x)
    
    parseRelBinding = do
      _ <- symbol0 "("
      x <- identifier
      _ <- symbol ":"
      _ <- symbol "Rel"
      _ <- symbol0 ")"
      return (RawRelBinding x)
    
    parseProofBinding = do
      _ <- symbol0 "("
      x <- identifier
      _ <- symbol ":"
      relJudg <- parseRelJudgmentWithFixities fixities
      _ <- symbol0 ")"
      return (RawProofBinding x relJudg)

parseDeclaration :: Parser RawDeclaration
parseDeclaration = parseDeclarationWithFixities Map.empty

parseImportDeclaration :: Parser RawImportDeclaration
parseImportDeclaration = do
  _ <- symbol "import"
  path <- stringLiteral
  suffix <- optional importSuffix
  _ <- symbol0 ";"
  case suffix of
    Nothing -> return (RawImportModule path)
    Just (Left alias) -> return (RawImportModuleAs path alias)
    Just (Right names) -> return (RawImportOnly path names)
  where
    importSuffix = asClause <|> onlyClause
    asClause = Left <$> (symbol "as" >> identifier)
    onlyClause = Right <$> (symbol0 "(" >> sepBy identifier (symbol0 ",") <* symbol0 ")")

parseExportDeclaration :: Parser RawExportDeclaration
parseExportDeclaration = do
  _ <- symbol "export"
  names <- sepBy identifier (symbol0 ",")
  _ <- symbol0 ";"
  return (RawExportSymbols names)

stringLiteral :: Parser String
stringLiteral = lexeme (char '"' >> manyTill L.charLiteral (char '"'))

sepBy :: Parser a -> Parser sep -> Parser [a]
sepBy p sep = sepBy1 p sep <|> return []

sepBy1 :: Parser a -> Parser sep -> Parser [a]
sepBy1 p sep = (:) <$> p <*> many (sep >> p)


-- ───────────────────── 7. Whole file  ───────────────────────────

-- | Two-phase parsing: collect fixities, then parse with dynamic operator table
parseFile :: Parser [RawDeclaration]
parseFile = do
  input <- M.getInput
  fixities <- collectFixities
  M.setInput input  -- Reset to beginning
  parseWithFixities fixities

-- | Parse declarations with given fixity map
parseWithFixities :: FixityMap -> Parser [RawDeclaration]
parseWithFixities fixities = sc *> many (parseDeclarationWithFixities fixities) <* M.eof

-- | Parse a single declaration with fixity context
parseDeclarationWithFixities :: FixityMap -> Parser RawDeclaration
parseDeclarationWithFixities fixities = 
      parseImportDef 
  <|> parseExportDef 
  <|> parseFixityDef
  <|> parseTheoremDef 
  <|> parseMacroDef
  where
    parseImportDef = RawImportDecl <$> parseImportDeclaration
    parseExportDef = RawExportDecl <$> parseExportDeclaration
    parseFixityDef = do
      fixity <- parseRawFixity
      name <- identifier
      _ <- symbol ";"
      return (RawFixityDecl fixity name)
    parseTheoremDef = do
      _ <- symbol "⊢" <|> symbol "theorem"
      name <- identifier
      bindings <- many parseBinding
      _ <- symbol ":"
      judgment <- parseRelJudgment
      _ <- symbol "≔" <|> symbol ":="
      proof <- parseProofWithFixities fixities
      _ <- symbol ";"
      return (RawTheoremDef name bindings judgment proof)
    parseMacroDef = do
      name <- mixfixIdentifier
      params <- many identifier
      _ <- symbol "≔" <|> symbol ":="
      body <- parseMacroBodyWithFixities fixities
      _ <- symbol ";"
      return (RawMacroDef name params body)

-- | Parse macro body with fixity context
parseMacroBodyWithFixities :: FixityMap -> Parser RawMacroBody  
parseMacroBodyWithFixities _ = RawMacroBodySrc <$> (sc *> manyTill anySingle (M.lookAhead (symbol ";")))

-- | Parse proof with fixity context  
parseProofWithFixities :: FixityMap -> Parser RawProof
parseProofWithFixities fixities = sc *> makeExprParser (proofAtomWithFixities fixities) proofTable <?> "proof"

-- | Parse proof atoms that may contain terms with fixities
proofAtomWithFixities :: FixityMap -> Parser RawProof
proofAtomWithFixities fixities =
      parens (parseProofWithFixities fixities)
  <|> try (lamExprWithFixities fixities)  
  <|> try (tyLamExprWithFixities fixities)
  <|> RPVar <$> identifier
  <?> "proof atom"

-- Helper functions for proof expressions with fixity context
lamExprWithFixities :: FixityMap -> Parser RawProof
lamExprWithFixities fixities =
  RPLam <$>
    ((symbol "\\" <|> symbol "λ") *> identifier) <*>
    (symbol ":" *> parseRType) <*>
    (symbol "." *> parseProofWithFixities fixities)

tyLamExprWithFixities :: FixityMap -> Parser RawProof
tyLamExprWithFixities fixities = do
  _ <- string "Λ" <|> string "TyLam"
  scn
  x <- identifierRaw
  _ <- char '.'
  body <- parseProofWithFixities fixities
  pure (RPTyLam x body)

-- Helper to run parser without context (for compatibility)
runParserEmpty :: Parser a -> String -> Either (M.ParseErrorBundle String Void) a
runParserEmpty p input = M.runParser p "" input