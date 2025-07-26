module Parser.Legacy
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
    mixfixIdentifier,
    symbol,
    parseDeclarationsWithContext,
    parseTermAtom,
    termSpec,
    buildMixfixOps,
    parseIota,
    parseTermVar,
    identifier,
    parseBindingsWithContext,
    parseBinding,
    sc,
    parseMacroDef,
    parseTheoremDef,
  )
where

import Context (extendMacroEnvironment, extendTheoremEnvironment, lookupTheorem, noMacros, noTheorems)
import Control.Monad.Combinators.Expr
import qualified Control.Monad.Combinators.Expr as Expr
import Control.Monad.Reader
import Data.Char (isAlphaNum, isPunctuation, isSymbol)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Void
import Lib
import Parser.Mixfix
import Text.Megaparsec
import qualified Text.Megaparsec as MP (getSourcePos)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- Context for tracking variable bindings with de Bruijn indices during parsing
data ParseContext = ParseContext
  { termVars :: Map String Int, -- term variable name -> de Bruijn index
    relVars :: Map String Int, -- relation variable name -> de Bruijn index
    proofVars :: Map String Int, -- proof variable name -> de Bruijn index
    macroEnv :: MacroEnvironment, -- full macro environment
    theoremEnv :: TheoremEnvironment, -- full theorem environment
    kwdSet :: Set.Set String, -- mixfix keywords (literal segments)
    allowMixfix :: Bool -- flag to prevent left-recursion in generalMixfix
  }
  deriving (Show, Eq)

instance HasMacroEnv ParseContext where
  getMacroEnv = macroEnv
  getAllowMixfix = allowMixfix
  setAllowMixfix b ctx = ctx { allowMixfix = b }

emptyParseContext :: ParseContext
emptyParseContext = ParseContext Map.empty Map.empty Map.empty noMacros noTheorems (mixfixKeywords noMacros) True

type Parser = ParsecT Void String (Reader ParseContext)

-- Smart application for terms - handles accumulating arguments for macro application
smartApp :: Parser (Term -> Term -> Term)
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

-- Mixfix specifications for terms and relations
termSpec :: MixfixSpec Parser Term
termSpec =
  MixfixSpec
    { holeParser = parseTerm,
      mkMacroNode = \n as pos -> TMacro n as pos,
      isRightBody = \x -> case x of TermMacro _ -> True; _ -> False,
      extraOps = [], -- nothing beyond smartApp
      smartAppOp = Just [Expr.InfixL smartApp], -- re‑use existing one
      symbolParser = symbol,
      posParser = MP.getSourcePos
    }

relSpec :: MixfixSpec Parser RType
relSpec =
  MixfixSpec
    { holeParser = parseRType,
      mkMacroNode = \n as pos -> RMacro n as pos,
      isRightBody = \x -> case x of RelMacro _ -> True; _ -> False,
      extraOps =
        [ [Expr.Postfix (do pos <- MP.getSourcePos; _ <- symbol "˘"; pure (\r -> Conv r pos))],
          [Expr.InfixL (do pos <- MP.getSourcePos; _ <- symbol "∘"; pure (\r1 r2 -> Comp r1 r2 pos))],
          [ Expr.InfixR
              ( do
                  pos <- MP.getSourcePos
                  _ <- symbol "->" <|> symbol "→"
                  pure (\r1 r2 -> Arr r1 r2 pos)
              )
          ]
        ],
      smartAppOp = Nothing,
      symbolParser = symbol,
      posParser = MP.getSourcePos
    }

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

identifier :: Parser String
identifier = lexeme . try $ do
  s <- (:) <$> letterChar <*> many (alphaNumChar <|> char '_' <|> char '\'')
  ctx <- ask
  let kws = kwdSet ctx
  when (s `Set.member` kws) $
    fail $
      "'" ++ s ++ "' is a reserved mixfix keyword"
  pure s

-- | Mixfix / operator identifier.
--   First character may be '_' or any symbol.  We stop on whitespace,
--   ';' or one of the reserved delimiters to keep the grammar unambiguous.
mixfixIdentifier :: Parser String
mixfixIdentifier = lexeme (some opChar <?> "operator identifier")
  where
    opChar = satisfy isOpChar
    -- Liberal set including unicode symbols, but excluding reserved syntax characters
    isOpChar c =
      (isAlphaNum c || isSymbol c || isPunctuation c || c `elem` ("_+-*/=<>:&|!~^?%$#@." :: String))
        && c `notElem` (";(){}[]," :: String)

stringLiteral :: Parser String
stringLiteral = lexeme (char '"' >> manyTill L.charLiteral (char '"'))

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- Term parsing
parseTerm :: Parser Term
parseTerm = do
  ctx <- ask
  let ops = buildMixfixOps termSpec (macroEnv ctx)
  term <- makeExprParser parseTermAtom ops
  validateMacroInstantiation term
  return term

-- Term parsing without macro validation (for use in macro definitions)
parseTermNoValidation :: Parser Term
parseTermNoValidation = do
  ctx <- ask
  let ops = buildMixfixOps termSpec (macroEnv ctx)
  makeExprParser parseTermAtom ops

parseTermAtom :: Parser Term
parseTermAtom =
  parens parseTerm
    <|> parseLam
    <|> generalMixfix termSpec     -- try first
    <|> parseTermVar               -- fallback

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
      checkTerm (TMacro name args _) = do
        -- Check macro arity
        case Map.lookup name (macroDefinitions (macroEnv ctx)) of
          Just (params, _) -> do
            let expectedArity = length params
                actualArity = length args
            if actualArity < expectedArity
              then fail $ "Macro '" ++ name ++ "' expects " ++ show expectedArity ++ " arguments but got " ++ show actualArity
              else mapM_ checkTerm args
          Nothing -> mapM_ checkTerm args
      checkTerm _ = return ()
  checkTerm term

-- Validate that all relational macros are properly instantiated
validateRMacroInstantiation :: RType -> Parser ()
validateRMacroInstantiation rtype = do
  ctx <- ask
  let checkRType (RVar name (-1) _) =
        case Map.lookup name (macroDefinitions (macroEnv ctx)) of
          Just (params, _)
            | not (null params) ->
                fail $ "Macro '" ++ name ++ "' expects " ++ show (length params) ++ " arguments but got 0"
          _ -> return ()
      checkRType (All _ body _) = checkRType body
      checkRType (Arr t1 t2 _) = checkRType t1 >> checkRType t2
      checkRType (Comp t1 t2 _) = checkRType t1 >> checkRType t2
      checkRType (Conv t _) = checkRType t
      checkRType (RMacro name args _) = do
        -- Check macro arity
        case Map.lookup name (macroDefinitions (macroEnv ctx)) of
          Just (params, _) -> do
            let expectedArity = length params
                actualArity = length args
            if actualArity < expectedArity
              then fail $ "Macro '" ++ name ++ "' expects " ++ show expectedArity ++ " arguments but got " ++ show actualArity
              else if actualArity > expectedArity
                then fail $ "Macro '" ++ name ++ "' expects " ++ show expectedArity ++ " arguments but got " ++ show actualArity
                else mapM_ checkRType args
          Nothing -> mapM_ checkRType args
      checkRType (Prom term _) = validateMacroInstantiation term
      checkRType _ = return ()
  checkRType rtype

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
        Nothing -> fail $ "Unknown term: " ++ name

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

-- RType parsing
parseRType :: Parser RType
parseRType = do
  ctx <- ask
  let ops = buildMixfixOps relSpec (macroEnv ctx)
  rtype <- makeExprParser parseRTypeAtom ops
  validateRMacroInstantiation rtype
  return rtype

parseRTypeAtom :: Parser RType
parseRTypeAtom =
  parseAll
    <|> try parseProm
    <|> try parseRMacro
    <|> generalMixfix relSpec     -- try first
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
              fail $ "Unknown relation: " ++ name

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
  ctx <- ask
  -- Validate that f is actually a known relational macro
  case Map.lookup f (macroDefinitions (macroEnv ctx)) of
    Just (_, RelMacro _) -> do
      args <- some parseRAtom
      return (RMacro f args pos)
    _ -> fail $ "Unknown relational macro: " ++ f
  where
    parseRAtom = parens parseRType <|> parseRVarOrApp

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
        Left _ -> fail $ "Unknown proof: " ++ name

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
    parseArgsUpTo remaining (binding : restBindings) acc = do
      maybeArg <- optional (parseTheoremArg binding)
      case maybeArg of
        Nothing -> return (reverse acc) -- No more arguments found
        Just arg -> parseArgsUpTo (remaining - 1) restBindings (arg : acc)

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

proofOps :: [[Operator Parser Proof]]
proofOps =
  [ [ Control.Monad.Combinators.Expr.Postfix
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
  t1 <- parseTermAtom
  _ <- symbol "["
  rel <- parseRType
  _ <- symbol "]"
  t2 <- parseTermAtom
  return (RelJudgment t1 rel t2)

-- Declaration parsing
parseDeclaration :: Parser Declaration
parseDeclaration = parseImportDef <|> parseExportDef <|> parseFixityDecl <|> parseTheoremDef <|> parseMacroDef

-- | Parse fixity declarations like "infixl 6 _+_;"
parseFixityDecl :: Parser Declaration
parseFixityDecl = do
  fixityConstructor <-
    (symbol "infixl" >> return Lib.Infixl)
      <|> (symbol "infixr" >> return Lib.Infixr)
      <|> (symbol "infix" >> return Lib.InfixN)
      <|> (symbol "prefix" >> return Lib.Prefix)
      <|> (symbol "postfix" >> return Lib.Postfix)
  level <- L.decimal :: Parser Int
  when (level > 9) $ fail "Precedence level must be 0-9"
  sc
  name <- mixfixIdentifier
  -- Validate that fixity matches the pattern
  let pattern = parseMixfixPattern name
  case fixityConstructor level of
    Lib.Infixl _ -> case pattern of
      [Hole, Literal _, Hole] -> return ()
      _ -> fail $ "infixl requires pattern _literal_ but got: " ++ name
    Lib.Infixr _ -> case pattern of
      [Hole, Literal _, Hole] -> return ()
      _ -> fail $ "infixr requires pattern _literal_ but got: " ++ name
    Lib.InfixN _ -> case pattern of
      [Hole, Literal _, Hole] -> return ()
      _ -> fail $ "infix requires pattern _literal_ but got: " ++ name
    Lib.Prefix _ -> case pattern of
      Literal _ : Hole : _ -> return ()
      _ -> fail $ "prefix requires pattern starting with literal followed by hole(s), but got: " ++ name
    Lib.Postfix _ -> case reverse pattern of
      Literal _ : Hole : _ -> return ()
      _ -> fail $ "postfix requires pattern ending with hole followed by literal, but got: " ++ name
  void $ symbol ";"
  return (FixityDecl (fixityConstructor level) name)

-- | Macro body = term ▷ ';'  ∨  relational‑type
parseMacroBody :: Parser MacroBody
parseMacroBody = termBranch <|> relBranch
  where
    termBranch = TermMacro <$> try (parseTermNoValidation <* sc <* lookAhead (symbol ";"))
    relBranch = RelMacro <$> parseRType

parseMacroDef :: Parser Declaration
parseMacroDef = do
  name <- mixfixIdentifier
  -- Generate auto-parameters if none provided (for mixfix macros)
  let autoParams = ["p" ++ show i | i <- [1 .. holes name]]
  explicitParams <- many identifier
  let params = if null explicitParams then autoParams else explicitParams
  _ <- symbol "≔" <|> symbol ":="
  let bindArgs ctx =
        let argIndexMap = Map.fromList (zip params (reverse [0 .. length params - 1]))
            newTermVars = Map.union argIndexMap (Map.map (+ length params) (termVars ctx))
            newRelVars = Map.union argIndexMap (Map.map (+ length params) (relVars ctx))
         in ctx {termVars = newTermVars, relVars = newRelVars}
  -- Try parsing as term first, then fall back to relational type
  body <- local bindArgs $ parseMacroBody
  void $ symbol ";"
  -- For now, just use defaultFixity - inline fixity will be added later
  return (MacroDef name params body)

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
        let addMacro ctx =
              if '_' `elem` name
                then -- Mixfix macro: use declared fixity or default

                  let currentEnv = macroEnv ctx
                      fixity = case Map.lookup name (macroFixities currentEnv) of
                        Just declaredFixity -> declaredFixity -- Use declared fixity
                        Nothing -> case holes name of -- Use default fixity
                          2 -> Lib.Infixl 6 -- default infix for binary operators
                          _ -> Lib.Prefix 9 -- default prefix for other mixfix
                      newEnv = extendMacroEnvironment name args body fixity currentEnv
                   in ctx {macroEnv = newEnv, kwdSet = mixfixKeywords newEnv}
                else -- Regular macro: add without fixity (use dummy fixity that won't be used)

                  let newEnv = extendMacroEnvironment name args body (defaultFixity name) (macroEnv ctx)
                   in ctx {macroEnv = newEnv, kwdSet = mixfixKeywords newEnv}
        local addMacro $ parseDeclarationsWithContext (decl : acc)
      TheoremDef name bindings judgment proof -> do
        let addTheorem ctx = ctx {theoremEnv = extendTheoremEnvironment name bindings judgment proof (theoremEnv ctx)}
        local addTheorem $ parseDeclarationsWithContext (decl : acc)
      FixityDecl fixity name -> do
        let addFixity ctx =
              let currentEnv = macroEnv ctx
                  -- Always add fixity - it will be used when the macro is defined
                  newEnv = currentEnv {macroFixities = Map.insert name fixity (macroFixities currentEnv)}
               in ctx {macroEnv = newEnv, kwdSet = mixfixKeywords newEnv}
        local addFixity $ parseDeclarationsWithContext (decl : acc)
      ImportDecl _ -> parseDeclarationsWithContext (decl : acc) -- Import declarations don't affect parsing context
      ExportDecl _ -> parseDeclarationsWithContext (decl : acc) -- Export declarations don't affect parsing context

-- Helper functions to run parsers with macro environment
runParserEmpty :: Parser a -> String -> Either (ParseErrorBundle String Void) a
runParserEmpty p input = runReader (runParserT p "" input) emptyParseContext

runParserWithMacroEnv :: MacroEnvironment -> Parser a -> String -> Either (ParseErrorBundle String Void) a
runParserWithMacroEnv env p input =
  let ctx = emptyParseContext {macroEnv = env, kwdSet = mixfixKeywords env}
   in runReader (runParserT p "" input) ctx

runParserWithFilename :: String -> Parser a -> String -> Either (ParseErrorBundle String Void) a
runParserWithFilename filename p input = runReader (runParserT p filename input) emptyParseContext
