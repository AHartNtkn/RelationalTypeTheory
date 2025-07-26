{-# LANGUAGE OverloadedStrings #-}
module Lexer 
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
  , isMixfixChar       --  ← NEW
  ) where

import Data.Char (generalCategory, GeneralCategory(..))
import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec
import Text.Megaparsec.Char (spaceChar, char)
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void
import Control.Monad (void)

type P = Parsec Void Text

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

symbol :: Text -> P Text
symbol = L.symbol sc

-- | Keywords that may appear in concrete syntax but are *not* legal
-- identifiers.  Putting them here guarantees we fail fast in the
-- *parser* phase – the elaborator will never see them.
reservedWords :: [Text]
reservedWords =
  [ "Term","term","Rel","rel","forall","Λ","λ","∀"           -- sorts & binders
  , "iota","rho","pi","conv_intro","conv_elim"                  -- proof keywords
  , "conv_up","conv_down","proof"                               -- misc.
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
  && c `notElem` ['λ', '→', '∘', '˘', '∀', 'ι', 'ρ', 'π', '⇃', '⇂', 'Λ']

-- Reserved delimiter characters that cannot be part of identifiers
isDelimiter :: Char -> Bool
isDelimiter c = c `elem` ['(', ')', '[', ']', '{', '}', ';', ',', ':', '.', '⟨', '⟩', '<', '>', '-']

isValidIdentChar :: Char -> Bool
isValidIdentChar c = isIdentChar c && not (isDelimiter c)

-- | Character class for **mixfix operator names**.
--   We allow the regular identifier alphabet **plus**
--   the three ASCII glyphs that we still want to treat as
--   delimiters for *ordinary* identifiers.
--
--   * keeps the iota/rho fixes intact because the global
--     delimiter table is left untouched;
--   * does **not** include '⟨' or '⟩', so the old "y⟩"
--     problem does not re‑appear.
isMixfixChar :: Char -> Bool
isMixfixChar c =
     (isIdentChar c && not (isDelimiter c))  -- normal ident chars
  || c `elem` (['<', '>', '-', '⟨', '⟩', '∣'] :: [Char])   -- extra operator glyphs including brackets
  || c == '_'                                -- hole marker

ident :: P Text
ident = lexeme . try $ do
  txt <- T.pack <$> some (satisfy isValidIdentChar) <?> "identifier"
  if txt `elem` reservedWords
     then fail $ "reserved keyword \"" <> T.unpack txt <> "\""
     else pure txt

pKeyword :: Text -> P ()
pKeyword kw = () <$ try (symbol kw)

-- Common symbol combinations
coloneqq :: P Text
coloneqq = symbol ":=" <|> symbol "≔"

-- Convenience parsers for common delimiters
parens :: P a -> P a
parens = between (symbol "(") (symbol ")")

brackets :: P a -> P a
brackets = between (symbol "[") (symbol "]")

braces :: P a -> P a
braces = between (symbol "{") (symbol "}")