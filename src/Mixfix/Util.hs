-- | Utility types and functions for the mixfix system
--
-- This module provides common utilities used throughout the mixfix parsing
-- system, including span handling, error types, and helper functions.
module Mixfix.Util
  ( -- * Source spans
    Span
  , startSpan
  , mergeSpan
  , spanToRange
  , -- * Error handling
    ParseError(..)
  , throwParse
  , withSpan
  , -- * Common helpers
    MonadFail
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec (SourcePos, unPos)
import Control.Monad (MonadFail)
import Control.Monad.Except (MonadError, throwError)

-- | Source position span - from start to end position
type Span = (SourcePos, SourcePos)

-- | Create a point span from a single position
startSpan :: SourcePos -> Span
startSpan p = (p, p)

-- | Merge two spans with short-circuit optimization
--
-- This is optimized for the common case where spans are nested or adjacent,
-- providing O(1) merging for most practical cases.
mergeSpan :: Span -> Span -> Span
mergeSpan (a, b) (c, d)
  | a <= c && d <= b = (a, b)  -- left span already encloses right
  | otherwise        = (a, max b d)

-- | Convert a source span to a simple line/column range for display
spanToRange :: Span -> ((Int, Int), (Int, Int))
spanToRange ((SourcePos _ l1 c1), (SourcePos _ l2 c2)) =
  ((unPos l1, unPos c1), (unPos l2, unPos c2))

------------------------------------------------------------
-- Rich semantic errors
------------------------------------------------------------

-- | Structured error type for mixfix parsing failures
--
-- This provides detailed error information including source locations,
-- descriptive messages, and expected tokens for better user experience.
data ParseError = ParseError
  { errorSpan     :: !Span      -- ^ Source location of the error
  , errorMsg      :: !Text      -- ^ Human-readable error message
  , errorExpected :: ![Text]    -- ^ Optional set of expected tokens
  } deriving (Show, Eq)

-- | Throw a parse error with the given span and message
throwParse :: MonadFail m => Span -> Text -> [Text] -> m a
throwParse s m expd = fail (show (ParseError s m expd))

-- | Attach span information to an error result
--
-- This converts simple text errors into structured ParseError values
-- with proper source location information.
withSpan :: Span -> Either Text a -> Either ParseError a
withSpan span (Left msg) = Left (ParseError span msg [])
withSpan _    (Right x)  = Right x

-- Additional utility functions

-- | Check if two spans overlap
spansOverlap :: Span -> Span -> Bool
spansOverlap (a1, a2) (b1, b2) = not (a2 < b1 || b2 < a1)

-- | Check if first span contains the second
spanContains :: Span -> Span -> Bool
spanContains (a1, a2) (b1, b2) = a1 <= b1 && b2 <= a2

-- | Get the length of a span in characters (approximate)
spanLength :: Span -> Int
spanLength (SourcePos _ l1 c1, SourcePos _ l2 c2)
  | l1 == l2  = unPos c2 - unPos c1
  | otherwise = 0  -- Multi-line spans are complex to measure

-- | Create a human-readable description of a span
spanDescription :: Span -> Text
spanDescription span = 
  let ((l1, c1), (l2, c2)) = spanToRange span
  in if l1 == l2
     then T.pack $ "line " ++ show l1 ++ ", columns " ++ show c1 ++ "-" ++ show c2
     else T.pack $ "lines " ++ show l1 ++ "-" ++ show l2