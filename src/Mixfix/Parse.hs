-- | Category-polymorphic Pratt parser with two-level trie dispatch
--
-- This module implements the core parsing engine that can handle any
-- syntactic category implementing MixfixCat. It uses a two-level trie
-- for efficient macro lookup and precedence climbing for conflict resolution.
module Mixfix.Parse
  ( -- * Parser types
    Parser
  , runParser
  , -- * Core parsing functions
    exprP
  , termParser
  , -- * Low-level parsing
    prefixOrAtom
  , infixLit
  , macroCall
  , atom
  ) where

import           Control.Monad (when)
import           Control.Monad.Reader
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Void (Void)
import           Text.Megaparsec hiding (runParser)
import qualified Text.Megaparsec as MP
import           Text.Megaparsec.Char (string, char)
import qualified Data.HashMap.Strict as HM

import           Mixfix.Core
import           Mixfix.Env  
import           Mixfix.Util
import           Mixfix.Fold

-- | Parser monad with environment access
type Parser = ParsecT Void Text (Reader Env)

-- | Run a parser with the given environment and input
runParser :: Parser a -> Env -> Text -> Text -> Either ParseError a
runParser parser env filename input = 
  case MP.runParser (runReaderT parser env) (T.unpack filename) input of
    Left parseErr -> Left $ ParseError 
      (startSpan (errorPos parseErr))
      (T.pack $ errorBundlePretty parseErr)
      []
    Right result -> Right result
  where
    errorPos bundle = 
      case bundleErrors bundle of
        (err:_) -> errorPos' err
        [] -> initialPos (T.unpack filename)
    
    errorPos' (TrivialError pos _ _) = pos
    errorPos' (FancyError pos _) = pos

------------------------------------------------------------
-- Core expression parsing with Pratt precedence climbing
------------------------------------------------------------

-- | Main expression parser for any mixfix category
--
-- This is the primary entry point for parsing expressions. It uses
-- precedence climbing to handle operator precedence and associativity.
exprP :: MixfixCat cat => Int -> Parser (Node cat)
exprP minPrec = do
  lhs <- prefixOrAtom
  prattLoop (nodeSpan lhs) lhs
  where
    prattLoop spL lhs = do
      env <- ask
      let trie = buildTrie (envFingerprint env)
      mc <- optional (try (infixLit trie))
      case mc of
        Nothing -> pure lhs
        Just (macro@(Any m), consume) ->
          if mPrec m < minPrec 
            then pure lhs 
            else do
              _ <- consume  -- commit to this operator
              rhs <- case mAssocInfo m of
                Just (LeftA, _)  -> exprP (mPrec m + 1)
                Just (RightA, _) -> exprP (mPrec m)
                _                -> exprP (mPrec m + 1)
              let sp = mergeSpan spL (nodeSpan rhs)
              let lhs' = mkMacroAny sp macro [lhs, rhs]
              prattLoop sp lhs'

-- | Convenience parser that starts with minimum precedence
termParser :: MixfixCat cat => Parser (Node cat)
termParser = exprP 1

------------------------------------------------------------
-- Prefix and atomic parsing
------------------------------------------------------------

-- | Parse prefix operators or atomic expressions
prefixOrAtom :: MixfixCat cat => Parser (Node cat)
prefixOrAtom = do
  env <- ask
  let trie = buildTrie (envFingerprint env)
  choice
    [ try (macroCall trie isPrefix)
    , atom
    ] <?> "expression"

-- | Parse an atomic expression (identifier, literal, parenthesized expression)
atom :: MixfixCat cat => Parser (Node cat)
atom = choice
  [ mkLeaf <$> leafParser
  , between (symbol "(") (symbol ")") (exprP 1)
  ] <?> "atom"

------------------------------------------------------------
-- Infix operator lookahead
------------------------------------------------------------

-- | Look ahead for infix operators without consuming input
--
-- This returns the macro and a parser action to consume the operator
-- if we decide to use it.
infixLit :: MixfixCat cat => Trie -> Parser (AnyMacro, Parser ())
infixLit trie = do
  pos <- getSourcePos
  tok <- lookAhead anyToken
  let tokText = T.singleton tok
  
  case HM.lookup tokText trie of
    Nothing -> empty
    Just level2 -> do
      -- Try each possibility in the second level
      choice $ map tryMacro (concatMap snd (HM.toList level2))
  where
    tryMacro macro@(Any m) = do
      when (not (isInfix m)) empty
      let consumeAction = void $ macroLiterals (mLitSeq m)
      return (macro, consumeAction)

------------------------------------------------------------
-- Macro application parsing
------------------------------------------------------------

-- | Parse a complete macro application
macroCall :: MixfixCat cat => Trie -> (Macro cat -> Bool) -> Parser (Node cat)
macroCall trie predicate = do
  pos <- getSourcePos
  tok <- lookAhead anyToken
  let tokText = T.singleton tok
  
  case HM.lookup tokText trie of
    Nothing -> empty
    Just level2 -> do
      choice $ map tryMacro (concatMap snd (HM.toList level2))
  where
    tryMacro (Any macro) = do
      when (not (predicate macro)) empty
      args <- parseMacroPattern (mLitSeq macro)
      endPos <- getSourcePos
      let span = (pos, endPos)
      return $ mkMacroAny span (Any macro) args

-- | Parse the literal and hole pattern of a macro
parseMacroPattern :: MixfixCat cat => [LitOrHole] -> Parser [Node cat]
parseMacroPattern = mapM parseElement
  where
    parseElement (L text) = do
      _ <- symbol (T.unpack text)
      return []  -- Literals don't contribute to arguments
    parseElement (H _) = do
      arg <- exprP 1  -- Parse argument with minimum precedence
      return [arg]
    
    -- Flatten the nested lists
    parseElement pattern = concat <$> parseElement pattern

------------------------------------------------------------
-- Utility parsers
------------------------------------------------------------

-- | Parse a sequence of macro literals
macroLiterals :: [LitOrHole] -> Parser ()
macroLiterals = mapM_ parseLit
  where
    parseLit (L text) = void $ symbol (T.unpack text)
    parseLit _ = pure ()  -- Skip holes

-- | Generic leaf parser (to be customized per category)
leafParser :: MixfixCat cat => Parser (Leaf cat)
leafParser = fail "leafParser must be implemented for each category"

-- | Parse a symbol with whitespace handling
symbol :: String -> Parser String
symbol s = lexeme (string s)

-- | Apply lexeme to handle whitespace
lexeme :: Parser a -> Parser a  
lexeme p = p <* skipSpace

-- | Skip whitespace and comments
skipSpace :: Parser ()
skipSpace = space

-- | Parse any single character token
anyToken :: Parser Char
anyToken = anySingle

------------------------------------------------------------
-- Type-safe macro application helpers
------------------------------------------------------------

-- | Apply a macro with existential wrapper (type-safe)
mkMacroAny :: MixfixCat cat 
           => Span 
           -> AnyMacro 
           -> [Node cat] 
           -> Node cat
mkMacroAny span (Any macro) args = mkMacro span macro args

-- | Check if arguments match macro arity
checkArity :: Macro cat -> [Node cat] -> Bool
checkArity macro args = arity macro == length args

-- | Parse macro arguments with proper hole handling
parseMacroArgs :: MixfixCat cat => Macro cat -> Parser [Node cat]
parseMacroArgs macro = do
  args <- sequence $ map parseHole (filter isHole (mLitSeq macro))
  when (not (checkArity macro args)) $
    fail $ "Wrong number of arguments for macro " ++ T.unpack (mName macro)
  return args
  where
    isHole (H _) = True
    isHole _     = False
    
    parseHole (H _) = exprP 1
    parseHole _     = fail "Internal error: parseHole called on literal"

------------------------------------------------------------
-- Error recovery and diagnostics
------------------------------------------------------------

-- | Enhanced error reporting with expected tokens
expectedTokens :: MixfixCat cat => Trie -> SourcePos -> [Text]
expectedTokens trie pos = 
  let available = HM.keys trie
  in take 3 available  -- Limit to most likely candidates

-- | Parse with error recovery
parseWithRecovery :: MixfixCat cat => Parser (Node cat) -> Parser (Node cat)
parseWithRecovery parser = do
  result <- observing parser
  case result of
    Left err -> do
      pos <- getSourcePos
      env <- ask  
      let trie = buildTrie (envFingerprint env)
          expected = expectedTokens trie pos
      fail $ "Parse error at " ++ show pos ++ 
             ", expected one of: " ++ show expected
    Right node -> return node