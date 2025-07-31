-- | Error recovery with configurable recovery tokens
--
-- This module implements multi-level error recovery that allows parsing
-- to continue after encountering errors, providing better diagnostics
-- and IDE support.
module Mixfix.Recover
  ( -- * Recovery frame types
    Frame(..)
  , RecoveryStack
  , RecoveryConfig(..)
  , -- * Recovery operations
    recover
  , recoverWith
  , withRecoveryFrame
  , -- * Recovery configuration
    defaultRecoveryConfig
  , declRecoveryConfig
  , exprRecoveryConfig
  , -- * Error injection
    HoleNode(..)
  , injectErrorHole
  ) where

import           Control.Monad (void, when)
import           Control.Monad.Reader
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.List (find)
import           Text.Megaparsec
import           Text.Megaparsec.Char (char, string)

import           Mixfix.Core
import           Mixfix.Util

-- | Recovery frame types for different parsing contexts
data Frame 
  = Decl      -- ^ Top-level declaration recovery
  | Expr      -- ^ Expression-level recovery  
  | Pattern   -- ^ Pattern-level recovery
  | Block     -- ^ Block/scope recovery
  deriving (Show, Eq, Ord)

-- | Stack of active recovery frames
type RecoveryStack = [Frame]

-- | Configuration for recovery tokens and strategies
data RecoveryConfig = RecoveryConfig
  { -- Recovery tokens for each frame type
    declTokens    :: ![Text]     -- ^ Tokens that end declarations
  , exprTokens    :: ![Text]     -- ^ Tokens that end expressions
  , patternTokens :: ![Text]     -- ^ Tokens that end patterns  
  , blockTokens   :: ![Text]     -- ^ Tokens that end blocks
  
    -- Recovery strategies
  , maxSkipTokens :: !Int        -- ^ Maximum tokens to skip before giving up
  , useIndentation :: !Bool      -- ^ Whether to use indentation for recovery
  , preservePartial :: !Bool     -- ^ Whether to preserve partial parses
  } deriving (Show, Eq)

-- | Error hole node for representing parse failures
data HoleNode cat = HoleNode
  { holeSpan    :: !Span         -- ^ Location of the error
  , holeReason  :: !Text         -- ^ Reason for the error
  , holePartial :: !(Maybe (Node cat))  -- ^ Partial parse if available
  } deriving (Show, Eq)

------------------------------------------------------------
-- Default recovery configurations
------------------------------------------------------------

-- | Default recovery configuration for general parsing
defaultRecoveryConfig :: RecoveryConfig
defaultRecoveryConfig = RecoveryConfig
  { declTokens = [";", "\n\n", "module", "import", "let", "def", "theorem"]
  , exprTokens = [",", ")", "]", "}", ";", "\n", "else", "then"]
  , patternTokens = [",", ")", "=>", "=", "|"]
  , blockTokens = ["}", "end", "\n\n"]
  , maxSkipTokens = 50
  , useIndentation = True
  , preservePartial = True
  }

-- | Recovery configuration optimized for declaration-level parsing
declRecoveryConfig :: RecoveryConfig
declRecoveryConfig = defaultRecoveryConfig
  { declTokens = [";", "\n\n", "module", "import", "macro", "theorem", "⊢"]
  , maxSkipTokens = 100  -- More lenient for top-level
  }

-- | Recovery configuration optimized for expression parsing
exprRecoveryConfig :: RecoveryConfig
exprRecoveryConfig = defaultRecoveryConfig
  { exprTokens = [",", ")", "]", "}", ";", "in", "where", "else", "then"]
  , maxSkipTokens = 20   -- Stricter for expressions
  }

------------------------------------------------------------
-- Core recovery operations
------------------------------------------------------------

-- | Recover from parse error using the current recovery stack
recover :: MixfixCat cat 
        => RecoveryStack 
        -> RecoveryConfig 
        -> Parser (Maybe (Node cat))
recover [] _ = return Nothing  -- No recovery frames
recover (frame:rest) config = do
  pos <- getSourcePos
  result <- recoverAtFrame frame config
  case result of
    Just node -> return (Just node)
    Nothing -> recover rest config  -- Try parent frame

-- | Recover with explicit configuration
recoverWith :: MixfixCat cat
            => RecoveryConfig
            -> Parser (Node cat)
            -> Parser (Node cat)
recoverWith config parser = do
  result <- observing parser
  case result of
    Right node -> return node
    Left err -> do
      maybeRecovered <- recover [Expr] config
      case maybeRecovered of
        Just recovered -> return recovered
        Nothing -> do
          -- Insert error hole and continue
          pos <- getSourcePos
          let span = startSpan pos
          injectErrorHole span "Parse error" Nothing

-- | Execute parser within a recovery frame
withRecoveryFrame :: MixfixCat cat
                  => Frame
                  -> RecoveryConfig  
                  -> Parser (Node cat)
                  -> Parser (Node cat)
withRecoveryFrame frame config parser = do
  -- Add frame to stack (would need ReaderT for real implementation)
  result <- observing parser
  case result of
    Right node -> return node
    Left err -> do
      maybeRecovered <- recover [frame] config
      case maybeRecovered of
        Just recovered -> return recovered
        Nothing -> do
          pos <- getSourcePos
          let span = startSpan pos
          injectErrorHole span ("Parse error in " <> T.pack (show frame)) Nothing

------------------------------------------------------------
-- Frame-specific recovery
------------------------------------------------------------

-- | Recover at a specific frame level
recoverAtFrame :: MixfixCat cat => Frame -> RecoveryConfig -> Parser (Maybe (Node cat))
recoverAtFrame Decl config = recoverDecl config
recoverAtFrame Expr config = recoverExpr config  
recoverAtFrame Pattern config = recoverPattern config
recoverAtFrame Block config = recoverBlock config

-- | Declaration-level recovery
recoverDecl :: MixfixCat cat => RecoveryConfig -> Parser (Maybe (Node cat))
recoverDecl config = do
  pos <- getSourcePos
  skipped <- skipUntilTokens (declTokens config) (maxSkipTokens config)
  if skipped > 0
    then do
      let span = startSpan pos
      hole <- injectErrorHole span "Declaration parse error" Nothing
      return (Just hole)
    else return Nothing

-- | Expression-level recovery  
recoverExpr :: MixfixCat cat => RecoveryConfig -> Parser (Maybe (Node cat))
recoverExpr config = do
  pos <- getSourcePos
  -- Try to preserve partial parse if possible
  partialResult <- optional $ try $ parsePartialExpr
  skipped <- skipUntilTokens (exprTokens config) (maxSkipTokens config)
  if skipped > 0
    then do
      let span = startSpan pos
      hole <- injectErrorHole span "Expression parse error" partialResult
      return (Just hole)
    else return Nothing

-- | Pattern-level recovery
recoverPattern :: MixfixCat cat => RecoveryConfig -> Parser (Maybe (Node cat))
recoverPattern config = do
  pos <- getSourcePos
  skipped <- skipUntilTokens (patternTokens config) (maxSkipTokens config)
  if skipped > 0
    then do
      let span = startSpan pos
      hole <- injectErrorHole span "Pattern parse error" Nothing
      return (Just hole)
    else return Nothing

-- | Block-level recovery
recoverBlock :: MixfixCat cat => RecoveryConfig -> Parser (Maybe (Node cat))
recoverBlock config = do
  pos <- getSourcePos
  -- Use indentation-based recovery if enabled
  recovered <- if useIndentation config
    then recoverByIndentation
    else skipUntilTokens (blockTokens config) (maxSkipTokens config)
  if recovered > 0
    then do
      let span = startSpan pos
      hole <- injectErrorHole span "Block parse error" Nothing
      return (Just hole)
    else return Nothing

------------------------------------------------------------
-- Recovery token matching
------------------------------------------------------------

-- | Skip tokens until finding one of the recovery tokens
skipUntilTokens :: [Text] -> Int -> Parser Int
skipUntilTokens recoveryTokens maxSkip = go 0
  where
    go skipped | skipped >= maxSkip = return skipped
    go skipped = do
      atEnd <- atEnd
      if atEnd then return skipped
      else do
        -- Look ahead to see if we found a recovery token
        found <- optional $ choice $ map (try . string . T.unpack) recoveryTokens
        case found of
          Just _ -> return skipped  -- Found recovery token, stop skipping
          Nothing -> do
            _ <- anySingle  -- Skip one token
            go (skipped + 1)

-- | Check if we're at end of input
atEnd :: Parser Bool
atEnd = do
  result <- observing eof
  case result of
    Right _ -> return True
    Left _ -> return False

-- | Recover using indentation cues
recoverByIndentation :: Parser Int
recoverByIndentation = do
  -- This would need integration with a layout-sensitive lexer
  -- For now, approximate by looking for newlines followed by dedentation
  pos <- getSourcePos
  skipped <- skipToNextLine
  return skipped

-- | Skip to the next line
skipToNextLine :: Parser Int
skipToNextLine = go 0
  where
    go skipped = do
      ch <- optional anySingle
      case ch of
        Nothing -> return skipped
        Just '\n' -> return (skipped + 1)
        Just _ -> go (skipped + 1)

------------------------------------------------------------
-- Error hole injection
------------------------------------------------------------

-- | Inject an error hole node at the current position
injectErrorHole :: MixfixCat cat 
                => Span 
                -> Text 
                -> Maybe (Node cat) 
                -> Parser (Node cat)  
injectErrorHole span reason partial = do
  -- This would need to be implemented per category
  -- For now, create a placeholder
  return $ mkErrorHole span reason partial

-- | Create an error hole node (to be implemented per category)
mkErrorHole :: MixfixCat cat => Span -> Text -> Maybe (Node cat) -> Node cat
mkErrorHole = undefined  -- Implementation depends on category

-- | Parse a partial expression that might be salvageable
parsePartialExpr :: MixfixCat cat => Parser (Node cat)
parsePartialExpr = undefined  -- Implementation depends on category

------------------------------------------------------------
-- Recovery diagnostics and reporting
------------------------------------------------------------

-- | Generate recovery diagnostic message
recoveryDiagnostic :: Frame -> Int -> Text -> Text
recoveryDiagnostic frame tokensSkipped reason =
  "Recovered from " <> reason <> " at " <> T.pack (show frame) <> 
  " level by skipping " <> T.pack (show tokensSkipped) <> " tokens"

-- | Check if recovery was successful
recoverySuccessful :: Maybe (Node cat) -> Bool
recoverySuccessful (Just _) = True
recoverySuccessful Nothing = False

-- | Estimate recovery quality (0.0 = failed, 1.0 = perfect)
recoveryQuality :: Int -> Int -> Double
recoveryQuality tokensSkipped maxTokens =
  max 0.0 (1.0 - fromIntegral tokensSkipped / fromIntegral maxTokens)

------------------------------------------------------------
-- Advanced recovery strategies
------------------------------------------------------------

-- | Try multiple recovery strategies in order of preference
recoverWithStrategies :: MixfixCat cat 
                      => [RecoveryConfig] 
                      -> Parser (Node cat)
                      -> Parser (Node cat)
recoverWithStrategies [] parser = parser  -- No recovery
recoverWithStrategies (cfg:cfgs) parser = do
  result <- observing parser
  case result of
    Right node -> return node
    Left err -> do
      recovered <- recoverWith cfg parser
      -- If recovery failed, try next strategy
      case isErrorHole recovered of
        True -> recoverWithStrategies cfgs parser
        False -> return recovered

-- | Check if a node is an error hole
isErrorHole :: MixfixCat cat => Node cat -> Bool
isErrorHole = undefined  -- Implementation depends on category

-- | Merge multiple partial parses into one
mergePartialParses :: MixfixCat cat => [Node cat] -> Node cat
mergePartialParses = undefined  -- Implementation depends on category

-- | Validate that recovery produced a sensible result
validateRecovery :: MixfixCat cat => Node cat -> Bool
validateRecovery = undefined  -- Implementation depends on category