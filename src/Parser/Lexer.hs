module Parser.Lexer 
  ( sc
  , symbol
  , ident
  , lexeme
  , pKeyword
  , parens
  , brackets
  , braces
  , coloneqq
  , isValidIdentChar
  , stringLit
  ) where

import Data.Char (generalCategory, GeneralCategory(..))
import Text.Megaparsec
import Text.Megaparsec.Char (spaceChar, char)
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void
import Control.Monad (void)

type P = Parsec Void String

-- | Standard space consumer
--
-- `space1` insisted on at least one white‑space character after every
-- token.  When we had        … R S] …,
-- the closing ']' came immediately after `S`, no space in‑between, so
-- the lexeme for `S` failed and the parser back‑tracked, silently
-- dropping the final macro argument.  Allowing *zero or more* spaces
-- fixes the problem everywhere (identifiers, symbols, brackets, …).
sc :: P ()
sc = L.space (void spaceChar)                       -- zero‑or‑more spaces
               (L.skipLineComment "--")
               (L.skipBlockComment "{-" "-}")

lexeme :: P a -> P a
lexeme = L.lexeme sc

symbol :: String -> P String
symbol = L.symbol sc

-- | Keywords that may appear in concrete syntax but are *not* legal
-- identifiers.  Putting them here guarantees we fail fast in the
-- *parser* phase – the elaborator will never see them.
reservedWords :: [String]
reservedWords =
  [ "Term","term","Rel","rel"                               -- sorts & binders
  ]

operatorCats :: [GeneralCategory]
operatorCats =
  [ OtherPunctuation
  , DashPunctuation
  , InitialQuote
  , FinalQuote
  , OpenPunctuation
  , ClosePunctuation
  ]

isIdentChar :: Char -> Bool
isIdentChar c = case generalCategory c of
  UppercaseLetter     -> True
  LowercaseLetter     -> True
  TitlecaseLetter     -> True
  OtherLetter         -> True
  ModifierLetter      -> True
  DecimalNumber       -> True
  LetterNumber        -> True
  OtherNumber         -> True
  MathSymbol          -> True
  CurrencySymbol      -> True
  ModifierSymbol      -> True
  OtherSymbol         -> True
  ConnectorPunctuation -> True
  NonSpacingMark      -> True
  SpacingCombiningMark -> True
  EnclosingMark       -> True
  _ | generalCategory c `elem` operatorCats -> True
  _                   -> c == '_' || c == '\''

-- Reserved delimiter characters that cannot be part of identifiers
isDelimiter :: Char -> Bool
isDelimiter c = c `elem` ['(', ')', ';', '[', ']', '≔']   -- ONLY the truly fatal ones

isValidIdentChar :: Char -> Bool
isValidIdentChar c = isIdentChar c && not (isDelimiter c)

ident :: P String
ident = lexeme . try $ do
  txt <- some (satisfy isValidIdentChar) <?> "identifier"
  if txt `elem` reservedWords
     then fail $ "reserved keyword \"" ++ txt ++ "\""
     else pure txt

pKeyword :: String -> P ()
pKeyword kw = () <$ try (symbol kw)

-- Common symbol combinations
coloneqq :: P String
coloneqq = symbol "≔" <|> symbol "≔"

-- String literal parser
stringLit :: P String
stringLit = lexeme $ do
  _ <- char '"'
  content <- many stringChar
  _ <- char '"'
  return content
  where
    stringChar = satisfy (\c -> c /= '"' && c /= '\n' && c /= '\r')

-- Convenience parsers for common delimiters
parens :: P a -> P a
parens = between (symbol "(") (symbol ")")

brackets :: P a -> P a
brackets = between (symbol "[") (symbol "]")

braces :: P a -> P a
braces = between (symbol "{") (symbol "}")