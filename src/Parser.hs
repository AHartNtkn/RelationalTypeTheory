module Parser
  ( parseTerm,
    parseRType,
    parseProof,
    parseDeclaration,
    parseFile,
    parseImportsOnly,
    parseRelJudgment,
    parseImportDeclaration,
    parseExportDeclaration,
    Parser,
    runParserEmpty,
    runParserWithMacroEnv,
    runParserWithFilename,
    emptyParseContext,
    runParserT,
    ParseContext (..),
  )
where

import Context (extendMacroEnvironment, extendTheoremEnvironment, lookupTheorem, noMacros, noTheorems)
import Control.Monad.Combinators.Expr
import Control.Monad.Reader
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Void
import Lib
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- Context for tracking variable bindings with de Bruijn indices during parsing
data ParseContext = ParseContext
  { termVars :: Map String Int, -- term variable name -> de Bruijn index
    relVars :: Map String Int, -- relation variable name -> de Bruijn index
    proofVars :: Map String Int, -- proof variable name -> de Bruijn index
    macroEnv :: MacroEnvironment, -- full macro environment
    theoremEnv :: TheoremEnvironment -- full theorem environment
  }
  deriving (Show, Eq)

emptyParseContext :: ParseContext
emptyParseContext = ParseContext Map.empty Map.empty Map.empty noMacros noTheorems

type Parser = ParsecT Void String (Reader ParseContext)

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

identifier :: Parser String
identifier = lexeme ((:) <$> letterChar <*> many (alphaNumChar <|> char '_' <|> char '\''))

stringLiteral :: Parser String
stringLiteral = lexeme (char '"' >> manyTill L.charLiteral (char '"'))

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- Term parsing
parseTerm :: Parser Term
parseTerm = do
  term <- makeExprParser parseTerm' termOps
  validateMacroInstantiation term
  return term

-- Term parsing without macro validation (for use in macro definitions)
parseTermNoValidation :: Parser Term
parseTermNoValidation = makeExprParser parseTerm' termOps

-- Validate that all macros are properly instantiated
validateMacroInstantiation :: Term -> Parser ()
validateMacroInstantiation term = do
  ctx <- ask
  let checkTerm (Var name (-1) _) =
        case Map.lookup name (macroDefinitions (macroEnv ctx)) of
          Just (params, _)
            | not (null params) ->
                fail $ "Macro '" ++ name ++ "' expects " ++ show (length params) ++ " arguments but got 0"
          _ -> return ()
      checkTerm (Lam _ body _) = checkTerm body
      checkTerm (App t1 t2 _) = checkTerm t1 >> checkTerm t2
      checkTerm (TMacro _ args _) = mapM_ checkTerm args
      checkTerm _ = return ()
  checkTerm term

parseTerm' :: Parser Term
parseTerm' =
  parens parseTerm
    <|> parseLam
    <|> parseTermVar

parseTermVar :: Parser Term
parseTermVar = do
  pos <- getSourcePos
  name <- identifier
  ctx <- ask
  case Map.lookup name (termVars ctx) of
    Just index -> return (Var name index pos)
    Nothing ->
      -- Check if it's a macro
      case Map.lookup name (macroDefinitions (macroEnv ctx)) of
        Just ([], _) -> return (TMacro name [] pos) -- 0-arity macro
        Just (_, _) -> return (TMacro name [] pos) -- Start macro accumulation
        Nothing -> fail $ "Unknown identifier: " ++ name

parseLam :: Parser Term
parseLam = do
  pos <- getSourcePos
  _ <- symbol "λ" <|> symbol "\\"
  x <- identifier
  _ <- symbol "."
  t <- local (bindTermVar x) parseTerm
  return (Lam x t pos)
  where
    bindTermVar name ctx =
      let newIndex = 0
          shiftedVars = Map.map (+ 1) (termVars ctx)
       in ctx {termVars = Map.insert name newIndex shiftedVars}

termOps :: [[Operator Parser Term]]
termOps = [[InfixL smartApp]]
  where
    smartApp = do
      ctx <- ask
      return $ \t1 t2 ->
        let pos = termPos t1 -- Use position from left operand
         in case (t1, t2) of
              (TMacro name args _, _) ->
                case Map.lookup name (macroDefinitions (macroEnv ctx)) of
                  Just (params, _) ->
                    -- params = declared parameters
                    let arity = length params
                        newArgs = args ++ [t2] -- argument list *after* adding t2
                     in if length newArgs <= arity
                          then TMacro name newArgs pos -- accumulate while <= arity
                          else App (TMacro name args pos) t2 pos -- switch to App when > arity
                  Nothing -> App t1 t2 pos -- Shouldn't happen, but fallback to App
              _ -> App t1 t2 pos

-- RType parsing
parseRType :: Parser RType
parseRType = makeExprParser parseRType' rtypeOps

parseRType' :: Parser RType
parseRType' =
  parseAll
    <|> try parseProm
    <|> try parseRMacro
    <|> parseRVarOrApp
    <|> parens parseRType

parseRVarOrApp :: Parser RType
parseRVarOrApp = do
  pos <- getSourcePos
  name <- identifier
  ctx <- ask
  case Map.lookup name (relVars ctx) of
    Just index -> return (RVar name index pos)
    Nothing -> do
      -- Check if it's a macro in the macro environment
      case Map.lookup name (macroDefinitions (macroEnv ctx)) of
        Just (_, TermMacro _) ->
          -- Automatically promote term macro to relational context
          return $ Prom (TMacro name [] pos) pos
        Just (_, RelMacro _) ->
          -- Use relational macro directly
          return $ RMacro name [] pos
        Nothing -> do
          -- Check if it's a term variable that should be promoted
          case Map.lookup name (termVars ctx) of
            Just index ->
              -- Automatically promote term variable to relational context
              return $ Prom (Var name index pos) pos
            Nothing ->
              -- Unknown identifier - generate error
              fail $ "Unknown identifier: " ++ name

parseAll :: Parser RType
parseAll = do
  pos <- getSourcePos
  _ <- symbol "∀" <|> symbol "forall"
  x <- identifier
  _ <- symbol "."
  t <- local (bindRelVar x) parseRType
  return (All x t pos)
  where
    bindRelVar name ctx =
      let newIndex = 0
          shiftedVars = Map.map (+ 1) (relVars ctx)
       in ctx {relVars = Map.insert name newIndex shiftedVars}

parseProm :: Parser RType
parseProm = label "promotion" $ do
  pos <- getSourcePos
  term <- promotable
  return (Prom term pos)
  where
    -- Accept **only** (1) any parenthesised term or (2) a bare lambda.
    -- Bare identifiers still need parentheses, preserving the
    -- RVar / Prom disambiguation.
    promotable = try parseLam <|> parens parseTerm

parseRMacro :: Parser RType
parseRMacro = do
  pos <- getSourcePos
  f <- identifier
  args <- some parseRAtom
  return (RMacro f args pos)
  where
    parseRAtom = parens parseRType <|> parseRVarOrApp

rtypeOps :: [[Operator Parser RType]]
rtypeOps =
  [ [ Postfix
        ( do
            pos <- getSourcePos
            _ <- symbol "˘"
            return (\r -> Conv r pos)
        )
    ],
    [InfixL (do pos <- getSourcePos; _ <- symbol "∘"; return (\r1 r2 -> Comp r1 r2 pos))],
    [InfixR (do pos <- getSourcePos; _ <- symbol "->" <|> symbol "→"; return (\r1 r2 -> Arr r1 r2 pos))]
  ]

-- Proof parsing
parseProof :: Parser Proof
parseProof = makeExprParser parseProof' proofOps

parseProof' :: Parser Proof
parseProof' =
  try parsePair
    <|> try parseConvProof -- specific conversion takes priority
    <|> try (parens parseProof) -- add try so we can fall through
    <|> try parseLamP
    <|> try parseTyLam
    <|> try parseIota
    <|> try parseRhoElim
    <|> try parseConvIntro
    <|> try parseConvElim
    <|> try parsePi
    <|> parseProofVar

parseProofVar :: Parser Proof
parseProofVar = do
  pos <- getSourcePos
  name <- identifier
  ctx <- ask
  case Map.lookup name (proofVars ctx) of
    Just index -> return (PVar name index pos)
    Nothing -> do
      -- Check if it's a theorem reference
      case lookupTheorem name (theoremEnv ctx) of
        Right (bindings, _, _) -> do
          -- Try to parse arguments for this theorem
          args <- parseTheoremArgs bindings
          return (PTheoremApp name args pos)
        Left _ -> fail $ "Unknown identifier: " ++ name

-- Parse theorem arguments based on the expected binding types
parseTheoremArgs :: [Binding] -> Parser [TheoremArg]
parseTheoremArgs [] = return []
parseTheoremArgs bindings = do
  -- Try to parse arguments, but allow partial application
  parseArgsUpTo (length bindings) bindings []
  where
    parseArgsUpTo :: Int -> [Binding] -> [TheoremArg] -> Parser [TheoremArg]
    parseArgsUpTo 0 _ acc = return (reverse acc)
    parseArgsUpTo _ [] acc = return (reverse acc)
    parseArgsUpTo remaining (binding:restBindings) acc = do
      maybeArg <- optional (parseTheoremArg binding)
      case maybeArg of
        Nothing -> return (reverse acc) -- No more arguments found
        Just arg -> parseArgsUpTo (remaining - 1) restBindings (arg:acc)

-- Parse a single theorem argument based on its expected binding type
parseTheoremArg :: Binding -> Parser TheoremArg
parseTheoremArg (TermBinding _) = do
  term <- parseTerm
  return (TermArg term)
parseTheoremArg (RelBinding _) = do
  rtype <- parseRType
  return (RelArg rtype)
parseTheoremArg (ProofBinding _ _) = do
  proof <- parseProof
  return (ProofArg proof)

smartProofApp :: Parser (Proof -> Proof -> Proof)
smartProofApp = do
  return $ \p1 p2 -> AppP p1 p2 (proofPos p1)

-- Helper functions to extract terms/relations from proof expressions
extractTermFromProof :: Proof -> Maybe Term
extractTermFromProof (PVar name idx pos) = Just (Var name idx pos)
extractTermFromProof _ = Nothing

extractRelFromProof :: Proof -> Maybe RType  
extractRelFromProof _ = Nothing

proofOps :: [[Operator Parser Proof]]
proofOps =
  [ [ Postfix
        ( do
            pos <- getSourcePos
            _ <- symbol "{"
            ty <- parseRType
            _ <- symbol "}"
            return (\p -> TyApp p ty pos)
        )
    ],
    [InfixL (do pos <- getSourcePos; notFollowedBy (symbol "," <|> symbol ")" <|> symbol "{"); smartProofApp)]
  ]

parseLamP :: Parser Proof
parseLamP = do
  pos <- getSourcePos
  _ <- symbol "λ" <|> symbol "\\"
  x <- identifier
  _ <- symbol ":"
  ty <- parseRType
  _ <- symbol "."
  p <- local (bindProofVar x) parseProof
  return (LamP x ty p pos)
  where
    bindProofVar name ctx =
      let newIndex = 0
          shiftedVars = Map.map (+ 1) (proofVars ctx)
       in ctx {proofVars = Map.insert name newIndex shiftedVars}

parseTyLam :: Parser Proof
parseTyLam = do
  pos <- getSourcePos
  _ <- symbol "Λ" <|> symbol "TyLam"
  x <- identifier
  _ <- symbol "."
  p <- local (bindRelVar x) parseProof
  return (TyLam x p pos)
  where
    bindRelVar name ctx =
      let newIndex = 0
          shiftedVars = Map.map (+ 1) (relVars ctx)
       in ctx {relVars = Map.insert name newIndex shiftedVars}

parseConvProof :: Parser Proof
parseConvProof = do
  pos <- getSourcePos
  t1 <- parseTerm
  _ <- symbol "⇃" <|> symbol "convl"
  p <- parseProof
  _ <- symbol "⇂" <|> symbol "convr"
  t2 <- parseTerm
  return (ConvProof t1 p t2 pos)

parseRhoElim :: Parser Proof
parseRhoElim = do
  pos <- getSourcePos
  _ <- symbol "ρ" <|> symbol "rho"
  _ <- symbol "{"
  x <- identifier
  _ <- symbol "."
  t1 <- local (bindTermVar x) parseTerm
  _ <- symbol ","
  t2 <- local (bindTermVar x) parseTerm
  _ <- symbol "}"
  p1 <- parseProof
  _ <- symbol "-"
  p2 <- parseProof
  return (RhoElim x t1 t2 p1 p2 pos)
  where
    bindTermVar name ctx =
      let newIndex = 0
          shiftedVars = Map.map (+ 1) (termVars ctx)
       in ctx {termVars = Map.insert name newIndex shiftedVars}

parseIota :: Parser Proof
parseIota = do
  pos <- getSourcePos
  _ <- symbol "ι" <|> symbol "iota"
  _ <- symbol "⟨" <|> symbol "<" <|> symbol "{"
  t1 <- parseTerm
  _ <- symbol ","
  t2 <- parseTerm
  _ <- symbol "⟩" <|> symbol ">" <|> symbol "}"
  return (Iota t1 t2 pos)

parseConvIntro :: Parser Proof
parseConvIntro = do
  pos <- getSourcePos
  _ <- symbol "∪ᵢ" <|> symbol "convIntro"
  p <- parseProof
  return (ConvIntro p pos)

parseConvElim :: Parser Proof
parseConvElim = do
  pos <- getSourcePos
  _ <- symbol "∪ₑ" <|> symbol "convElim"
  p <- parseProof
  return (ConvElim p pos)

parsePair :: Parser Proof
parsePair = parens $ do
  pos <- getSourcePos
  p1 <- parseProof
  _ <- symbol ","
  p2 <- parseProof
  return (Pair p1 p2 pos)

parsePi :: Parser Proof
parsePi = do
  pos <- getSourcePos
  _ <- symbol "π" <|> symbol "pi"
  p <- parseProof
  _ <- symbol "-"
  x <- identifier
  _ <- symbol "."
  y <- identifier
  _ <- symbol "."
  z <- identifier
  _ <- symbol "."
  q <- local (bindPiVars x y z) parseProof
  return (Pi p x y z q pos)
  where
    bindPiVars x y z ctx =
      let -- Bind x as a term variable (the intermediate term)
          newTermIndex = 0
          shiftedTermVars = Map.map (+ 1) (termVars ctx)
          ctxWithX = ctx {termVars = Map.insert x newTermIndex shiftedTermVars}

          -- Bind y and z as proof variables (the proof assumptions)
          newProofIndex = 0
          shiftedProofVars = Map.map (+ 1) (proofVars ctxWithX)
          ctxWithY = ctxWithX {proofVars = Map.insert y newProofIndex shiftedProofVars}
          shiftedProofVars2 = Map.map (+ 1) (proofVars ctxWithY)
          ctxWithZ = ctxWithY {proofVars = Map.insert z newProofIndex shiftedProofVars2}
       in ctxWithZ

-- Binding parsing
parseBinding :: Parser Binding
parseBinding = try parseTermBinding <|> try parseRelBinding <|> parseProofBinding

parseTermBinding :: Parser Binding
parseTermBinding = try $ parens $ do
  x <- identifier
  _ <- symbol ":"
  _ <- symbol "Term"
  return (TermBinding x)

parseRelBinding :: Parser Binding
parseRelBinding = try $ parens $ do
  x <- identifier
  _ <- symbol ":"
  _ <- symbol "Rel"
  notFollowedBy alphaNumChar
  return (RelBinding x)

parseProofBinding :: Parser Binding
parseProofBinding = parens $ do
  x <- identifier
  _ <- symbol ":"
  relJudg <- parseRelJudgment
  return (ProofBinding x relJudg)

-- Relational judgment parsing
parseRelJudgment :: Parser RelJudgment
parseRelJudgment = try $ do
  t1 <- parseTerm'
  _ <- symbol "["
  rel <- parseRType
  _ <- symbol "]"
  t2 <- parseTerm'
  return (RelJudgment t1 rel t2)

-- Declaration parsing
parseDeclaration :: Parser Declaration
parseDeclaration = parseImportDef <|> parseExportDef <|> parseTheoremDef <|> parseMacroDef

-- | Macro body = term ▷ ';'  ∨  relational‑type
parseMacroBody :: Parser MacroBody
parseMacroBody = termBranch <|> relBranch
  where
    termBranch = TermMacro <$> try (parseTermNoValidation <* sc <* lookAhead (symbol ";"))
    relBranch = RelMacro <$> parseRType

parseMacroDef :: Parser Declaration
parseMacroDef = do
  name <- identifier
  args <- many identifier
  _ <- symbol "≔" <|> symbol ":="
  let bindArgs ctx =
        let argIndexMap = Map.fromList (zip args (reverse [0 .. length args - 1]))
            newTermVars = Map.union argIndexMap (Map.map (+ length args) (termVars ctx))
            newRelVars = Map.union argIndexMap (Map.map (+ length args) (relVars ctx))
         in ctx {termVars = newTermVars, relVars = newRelVars}
  -- Try parsing as term first, then fall back to relational type
  body <- local bindArgs $ parseMacroBody
  _ <- symbol ";"
  return (MacroDef name args body)

parseTheoremDef :: Parser Declaration
parseTheoremDef = do
  _ <- symbol "⊢" <|> symbol "theorem"
  name <- identifier
  currentCtx <- ask -- Get current context (includes macros from file)
  (bindings, bindingCtx) <- parseBindingsWithContext [] emptyParseContext
  let finalCtx = currentCtx {termVars = termVars bindingCtx, relVars = relVars bindingCtx, proofVars = proofVars bindingCtx}
  _ <- symbol ":"
  relJudg <- local (const finalCtx) parseRelJudgment
  _ <- symbol "≔" <|> symbol ":="
  proof <- local (const finalCtx) parseProof
  _ <- symbol ";"
  return (TheoremDef name bindings relJudg proof)

parseBindingsWithContext :: [Binding] -> ParseContext -> Parser ([Binding], ParseContext)
parseBindingsWithContext acc ctx = do
  currentCtx <- ask -- Get the current context with file-level macros
  let ctxWithMacros = ctx {macroEnv = macroEnv currentCtx} -- Preserve macros in binding context
  maybeBinding <- optional (local (const ctxWithMacros) parseBinding)
  case maybeBinding of
    Nothing -> return (reverse acc, ctx)
    Just binding -> case binding of
      TermBinding termVar ->
        let newIndex = 0
            shiftedVars = Map.map (+ 1) (termVars ctx)
            newCtx = ctx {termVars = Map.insert termVar newIndex shiftedVars}
         in parseBindingsWithContext (binding : acc) newCtx
      RelBinding relVar ->
        let newIndex = 0
            shiftedVars = Map.map (+ 1) (relVars ctx)
            newCtx = ctx {relVars = Map.insert relVar newIndex shiftedVars}
         in parseBindingsWithContext (binding : acc) newCtx
      ProofBinding proofVar _ ->
        let newIndex = 0
            shiftedVars = Map.map (+ 1) (proofVars ctx)
            newCtx = ctx {proofVars = Map.insert proofVar newIndex shiftedVars}
         in parseBindingsWithContext (binding : acc) newCtx

-- Import and Export declaration parsing
parseImportDef :: Parser Declaration
parseImportDef = ImportDecl <$> parseImportDeclaration

parseExportDef :: Parser Declaration
parseExportDef = ExportDecl <$> parseExportDeclaration

parseImportDeclaration :: Parser ImportDeclaration
parseImportDeclaration = do
  _ <- symbol "import"
  path <- stringLiteral
  suffix <- optional importSuffix
  _ <- symbol ";"
  case suffix of
    Nothing -> return (ImportModule path)
    Just (Left alias) -> return (ImportModuleAs path alias)
    Just (Right names) -> return (ImportOnly path names)
  where
    importSuffix = asClause <|> onlyClause
    asClause = Left <$> (symbol "as" >> identifier)
    onlyClause = Right <$> (symbol "(" >> sepBy identifier (symbol ",") <* symbol ")")

parseExportDeclaration :: Parser ExportDeclaration
parseExportDeclaration = do
  _ <- symbol "export"
  names <- sepBy identifier (symbol ",")
  _ <- symbol ";"
  return (ExportSymbols names)

-- File parsing
parseFile :: Parser [Declaration]
parseFile = do
  sc
  decls <- parseDeclarationsWithContext []
  eof
  return decls

-- Parse only import declarations for dependency graph building
parseImportsOnly :: Parser [ImportDeclaration]
parseImportsOnly = do
  sc
  imports <- parseImportsLoop []
  eof
  return (reverse imports)
  where
    parseImportsLoop acc = do
      -- Try to parse an import declaration
      maybeImport <- optional (try parseImportDeclaration)
      case maybeImport of
        Just imp -> parseImportsLoop (imp : acc)
        Nothing -> do
          -- Skip to next potential import or end of file
          maybeChar <- optional anySingle
          case maybeChar of
            Nothing -> return acc -- End of file
            Just _ -> parseImportsLoop acc -- Skip this character and continue

parseDeclarationsWithContext :: [Declaration] -> Parser [Declaration]
parseDeclarationsWithContext acc = do
  maybeDecl <- optional parseDeclaration
  case maybeDecl of
    Nothing -> return (reverse acc)
    Just decl -> case decl of
      MacroDef name args body -> do
        let addMacro ctx = ctx {macroEnv = extendMacroEnvironment name args body (macroEnv ctx)}
        local addMacro $ parseDeclarationsWithContext (decl : acc)
      TheoremDef name bindings judgment proof -> do
        let addTheorem ctx = ctx {theoremEnv = extendTheoremEnvironment name bindings judgment proof (theoremEnv ctx)}
        local addTheorem $ parseDeclarationsWithContext (decl : acc)
      ImportDecl _ -> parseDeclarationsWithContext (decl : acc) -- Import declarations don't affect parsing context
      ExportDecl _ -> parseDeclarationsWithContext (decl : acc) -- Export declarations don't affect parsing context

-- Helper functions to run parsers with macro environment
runParserEmpty :: Parser a -> String -> Either (ParseErrorBundle String Void) a
runParserEmpty p input = runReader (runParserT p "" input) emptyParseContext

runParserWithMacroEnv :: MacroEnvironment -> Parser a -> String -> Either (ParseErrorBundle String Void) a
runParserWithMacroEnv env p input =
  let ctx = emptyParseContext {macroEnv = env}
   in runReader (runParserT p "" input) ctx

runParserWithFilename :: String -> Parser a -> String -> Either (ParseErrorBundle String Void) a
runParserWithFilename filename p input = runReader (runParserT p filename input) emptyParseContext
