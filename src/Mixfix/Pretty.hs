-- | Generic pretty-printing for mixfix expressions
--
-- This module provides a category-polymorphic pretty-printing system
-- that can reconstruct the original mixfix syntax from parsed ASTs,
-- with proper precedence-based parenthesization.
module Mixfix.Pretty
  ( -- * Pretty-printing typeclass
    MixfixPretty(..)
  , -- * Core pretty-printing functions
    prettyNode
  , prettyWithPrec
  , prettyChain
  , -- * Annotation types
    Ann(..)
  , -- * Pretty-printing configuration
    PrettyConfig(..)
  , defaultPrettyConfig
  , compactPrettyConfig
  , verbosePrettyConfig
  , -- * Utility functions
    parenthesize
  , needsParens
  , renderMixfix
  ) where

import           Data.Text (Text)
import qualified Data.Text as T
import           Prettyprinter
import           Prettyprinter.Render.Text

import           Mixfix.Core
import           Mixfix.Util

-- | Annotation types for styled pretty-printing
data Ann
  = PrecAnn !Int        -- ^ Precedence level annotation
  | MacroAnn !Text      -- ^ Macro name annotation  
  | LeafAnn             -- ^ Leaf node annotation
  | ErrorAnn            -- ^ Error node annotation
  | ParenAnn            -- ^ Parentheses annotation
  deriving (Eq, Ord, Show)

-- | Configuration for pretty-printing behavior
data PrettyConfig = PrettyConfig
  { -- Spacing and layout
    compactSpacing   :: !Bool      -- ^ Minimize whitespace
  , indentWidth      :: !Int       -- ^ Spaces per indent level
  , lineWidth        :: !Int       -- ^ Target line width
  
    -- Parenthesization
  , alwaysParenthesize :: !Bool    -- ^ Force parentheses everywhere
  , minimalParens      :: !Bool    -- ^ Use minimal parentheses
  
    -- Annotation control  
  , showPrecedence     :: !Bool    -- ^ Include precedence annotations
  , showMacroNames     :: !Bool    -- ^ Include macro name annotations
  , colorizeOutput     :: !Bool    -- ^ Use colored output
  
    -- Chain formatting
  , chainNewlines      :: !Bool    -- ^ Put chain elements on new lines
  , alignChains        :: !Bool    -- ^ Align chained operators
  } deriving (Show, Eq)

-- | Extended typeclass for categories that support pretty-printing
class MixfixCat cat => MixfixPretty cat where
  -- | Pretty-print a leaf node
  prettyLeaf :: Leaf cat -> Doc Ann
  
  -- | Get the display name for a macro
  macroName :: Macro cat -> Text
  
  -- | Pretty-print error holes (if supported)
  prettyErrorHole :: Text -> Maybe (Node cat) -> Doc Ann
  prettyErrorHole reason partial = 
    annotate ErrorAnn $ "⟨error:" <+> pretty reason <> "⟩"

------------------------------------------------------------
-- Default configurations
------------------------------------------------------------

-- | Standard pretty-printing configuration
defaultPrettyConfig :: PrettyConfig
defaultPrettyConfig = PrettyConfig
  { compactSpacing = False
  , indentWidth = 2
  , lineWidth = 80
  , alwaysParenthesize = False
  , minimalParens = True
  , showPrecedence = False
  , showMacroNames = False
  , colorizeOutput = False
  , chainNewlines = False
  , alignChains = True
  }

-- | Compact configuration for minimal output
compactPrettyConfig :: PrettyConfig
compactPrettyConfig = defaultPrettyConfig
  { compactSpacing = True
  , lineWidth = 120
  , chainNewlines = False
  , alignChains = False
  }

-- | Verbose configuration for debugging
verbosePrettyConfig :: PrettyConfig
verbosePrettyConfig = defaultPrettyConfig
  { showPrecedence = True
  , showMacroNames = True
  , alwaysParenthesize = True
  , colorizeOutput = True
  }

------------------------------------------------------------
-- Core pretty-printing functions
------------------------------------------------------------

-- | Pretty-print a node with default precedence context
prettyNode :: MixfixPretty cat => PrettyConfig -> Node cat -> Doc Ann
prettyNode config node = prettyWithPrec config 0 node

-- | Pretty-print a node with explicit precedence context
prettyWithPrec :: MixfixPretty cat => PrettyConfig -> Int -> Node cat -> Doc Ann
prettyWithPrec config contextPrec node = 
  case extractMacroInfo node of
    Just (macro, args) -> prettyMacroApp config contextPrec macro args
    Nothing -> prettyLeafNode config node

-- | Pretty-print a macro application with precedence handling
prettyMacroApp :: MixfixPretty cat 
               => PrettyConfig 
               -> Int 
               -> Macro cat 
               -> [Node cat] 
               -> Doc Ann
prettyMacroApp config contextPrec macro args = 
  let macroPrec = mPrec macro
      doc = renderMacroPattern config macro args
      annotatedDoc = if showMacroNames config
                     then annotate (MacroAnn (macroName macro)) doc
                     else doc
      precDoc = if showPrecedence config
                then annotate (PrecAnn macroPrec) annotatedDoc  
                else annotatedDoc
  in if needsParens config contextPrec macroPrec
     then parenthesize precDoc
     else precDoc

-- | Render a macro's literal pattern with arguments
renderMacroPattern :: MixfixPretty cat 
                   => PrettyConfig 
                   -> Macro cat 
                   -> [Node cat] 
                   -> Doc Ann
renderMacroPattern config macro args = 
  let pattern = mLitSeq macro
      argMap = zip [0..] args
  in hsep $ renderElements config pattern argMap

-- | Render individual pattern elements
renderElements :: MixfixPretty cat 
               => PrettyConfig 
               -> [LitOrHole] 
               -> [(Int, Node cat)] 
               -> [Doc Ann]
renderElements config elements argMap = map renderElement elements
  where
    renderElement (L text) = pretty text
    renderElement (H index) = 
      case lookup index argMap of
        Just arg -> prettyWithPrec config (mPrec macro) arg
        Nothing -> annotate ErrorAnn "⟨missing-arg⟩"
    
    -- Get macro from context (would need to be passed down)
    macro = undefined  -- This needs to be available in context

------------------------------------------------------------
-- Chain pretty-printing
------------------------------------------------------------

-- | Pretty-print associative chains with special formatting
prettyChain :: MixfixPretty cat 
            => PrettyConfig 
            -> Macro cat 
            -> [Node cat] 
            -> Doc Ann
prettyChain config macro elements = 
  if chainNewlines config
  then prettyChainVertical config macro elements
  else prettyChainHorizontal config macro elements

-- | Pretty-print chain horizontally
prettyChainHorizontal :: MixfixPretty cat 
                      => PrettyConfig 
                      -> Macro cat 
                      -> [Node cat] 
                      -> Doc Ann
prettyChainHorizontal config macro elements = 
  let opSymbol = extractOperatorSymbol macro
      docs = map (prettyWithPrec config (mPrec macro + 1)) elements
      spacing = if compactSpacing config then mempty else space
  in hsep $ punctuate (spacing <> opSymbol <> spacing) docs

-- | Pretty-print chain vertically  
prettyChainVertical :: MixfixPretty cat 
                    => PrettyConfig 
                    -> Macro cat 
                    -> [Node cat] 
                    -> Doc Ann
prettyChainVertical config macro elements = 
  let opSymbol = extractOperatorSymbol macro
      docs = map (prettyWithPrec config (mPrec macro + 1)) elements
      opDoc = if alignChains config 
              then space <> opSymbol <> space
              else opSymbol <> space
  in align $ vsep $ punctuate opDoc docs

------------------------------------------------------------
-- Parenthesization logic
------------------------------------------------------------

-- | Add parentheses around a document
parenthesize :: Doc Ann -> Doc Ann
parenthesize doc = annotate ParenAnn (lparen <> doc <> rparen)

-- | Determine if parentheses are needed based on precedence
needsParens :: PrettyConfig -> Int -> Int -> Bool
needsParens config contextPrec exprPrec
  | alwaysParenthesize config = True
  | minimalParens config = contextPrec > exprPrec
  | otherwise = contextPrec >= exprPrec

-- | Check if an expression needs parentheses in a given context
needsParensInContext :: MixfixPretty cat 
                     => PrettyConfig 
                     -> Node cat 
                     -> Int 
                     -> Bool
needsParensInContext config node contextPrec =
  case extractMacroInfo node of
    Just (macro, _) -> needsParens config contextPrec (mPrec macro)
    Nothing -> False

------------------------------------------------------------
-- Leaf node pretty-printing
------------------------------------------------------------

-- | Pretty-print a leaf node
prettyLeafNode :: MixfixPretty cat => PrettyConfig -> Node cat -> Doc Ann
prettyLeafNode config node = 
  case extractLeafFromNode node of
    Just leaf -> annotate LeafAnn (prettyLeaf leaf)
    Nothing -> annotate ErrorAnn "⟨unknown-node⟩"

------------------------------------------------------------
-- Rendering and output
------------------------------------------------------------

-- | Render a document to text with the given configuration
renderMixfix :: PrettyConfig -> Doc Ann -> Text
renderMixfix config doc = 
  let layoutOpts = LayoutOptions (AvailablePerLine (lineWidth config) 0.8)
      simpleDoc = layoutPretty layoutOpts doc
  in renderStrict simpleDoc

-- | Render with color support (if enabled)
renderWithColor :: PrettyConfig -> Doc Ann -> Text  
renderWithColor config doc
  | colorizeOutput config = renderWithColorImpl doc
  | otherwise = renderMixfix config doc

-- | Implementation of colored rendering (placeholder)
renderWithColorImpl :: Doc Ann -> Text
renderWithColorImpl = renderStrict . layoutPretty defaultLayoutOptions

------------------------------------------------------------
-- Helper functions (category-specific implementations needed)
------------------------------------------------------------

-- | Extract macro information from a node
extractMacroInfo :: MixfixPretty cat => Node cat -> Maybe (Macro cat, [Node cat])
extractMacroInfo = undefined  -- Implementation depends on Node structure

-- | Extract leaf information from a node
extractLeafFromNode :: MixfixPretty cat => Node cat -> Maybe (Leaf cat)
extractLeafFromNode = undefined  -- Implementation depends on Node structure

-- | Extract the operator symbol from a macro for chain printing
extractOperatorSymbol :: Macro cat -> Doc Ann
extractOperatorSymbol macro = 
  case mLitSeq macro of
    [L op] -> pretty op  -- Simple infix operator
    _ -> pretty (mName macro)  -- Fall back to macro name

------------------------------------------------------------
-- Advanced formatting features
------------------------------------------------------------

-- | Pretty-print with syntax highlighting
prettySyntaxHighlighted :: MixfixPretty cat => Node cat -> Doc Ann
prettySyntaxHighlighted = prettyWithPrec verbosePrettyConfig 0

-- | Pretty-print for IDE display (compact but readable)
prettyForIDE :: MixfixPretty cat => Node cat -> Doc Ann
prettyForIDE = prettyWithPrec defaultPrettyConfig 0

-- | Pretty-print for error messages (minimal but clear)
prettyForError :: MixfixPretty cat => Node cat -> Doc Ann
prettyForError = prettyWithPrec compactPrettyConfig 0

-- | Pretty-print a list of nodes (e.g., arguments)
prettyNodeList :: MixfixPretty cat => PrettyConfig -> [Node cat] -> Doc Ann
prettyNodeList config nodes = 
  let docs = map (prettyWithPrec config 0) nodes
      sep = if compactSpacing config then comma else comma <> space
  in hsep $ punctuate sep docs

-- | Pretty-print with custom separator
prettyNodesWith :: MixfixPretty cat 
                => PrettyConfig 
                -> Doc Ann 
                -> [Node cat] 
                -> Doc Ann
prettyNodesWith config separator nodes =
  let docs = map (prettyWithPrec config 0) nodes
  in hsep $ punctuate separator docs

------------------------------------------------------------
-- Debugging and inspection
------------------------------------------------------------

-- | Pretty-print with full structural information (for debugging)
prettyDebug :: MixfixPretty cat => Node cat -> Doc Ann
prettyDebug node = 
  case extractMacroInfo node of
    Just (macro, args) -> 
      "Macro" <+> pretty (mName macro) <+> 
      parens (pretty (mPrec macro)) <+>
      brackets (prettyNodeList verbosePrettyConfig args)
    Nothing -> 
      case extractLeafFromNode node of
        Just leaf -> "Leaf" <+> parens (prettyLeaf leaf)
        Nothing -> "Unknown"

-- | Show the precedence structure of an expression
prettyPrecedenceTree :: MixfixPretty cat => Node cat -> Doc Ann
prettyPrecedenceTree = prettyWithPrec verbosePrettyConfig 0