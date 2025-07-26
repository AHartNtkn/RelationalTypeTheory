{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module Elaborate
  ( elaborate
  , elaborateDeclaration
  , elaborateTerm
  , elaborateRType
  , elaborateProof
  , FrontEndError(..)
  , ElaborateError(..)
  , ElaborateContext(..)
  , emptyElaborateContext
  , ElaborateM
  , isPostfixOperator
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as Map
import           Data.List       (find)
import           Data.Foldable   (asum)
import qualified Data.IntMap as IntMap
import qualified Data.Set as S
import qualified Data.Text as T
import           Data.List  (intercalate)     -- NEW
import Text.Megaparsec (SourcePos, initialPos, ParseErrorBundle)
import Data.Text (Text)
import Data.Void
import Data.Bifunctor (first)
import Data.Maybe (fromMaybe)

import Lib hiding (splitMixfix, mixfixKeywords)
import qualified RawAst as Raw
import RawAst (nameString)
import Mixfix (splitMixfix, mixfixKeywords)

data FrontEndError
  = ParseError (ParseErrorBundle Text Void)
  | ElabError  ElaborateError
  deriving (Show, Eq)

-- Errors that can occur during elaboration
data ElaborateError
  = UnknownVariable String SourcePos
  | UnknownMacro String SourcePos
  | UnknownTheorem String SourcePos
  | MacroArityMismatch String Int Int SourcePos  -- name, expected, actual, pos
  | TheoremArityMismatch String Int Int SourcePos
  | InvalidMixfixPattern String SourcePos
  | CircularMacroReference String SourcePos
  deriving (Show, Eq)

-- Context for elaboration - contains macro and theorem environments
data ElaborateContext = ElaborateContext
  { macroEnv :: Lib.MacroEnvironment
  , theoremEnv :: Lib.TheoremEnvironment
  , termDepth :: Int  -- current lambda depth for terms
  , relDepth :: Int   -- current forall depth for relations
  , proofDepth :: Int -- current lambda depth for proofs
  , boundVars :: Map.Map String Int  -- variable name -> de Bruijn index (distance from binding site)
  , boundRelVars :: Map.Map String Int  -- relational variable name -> de Bruijn index
  , boundProofVars :: Map.Map String (Int, RelJudgment)  -- proof var -> (index, judgment)
  } deriving (Show, Eq)

shiftIntMap :: Map.Map k Int -> Map.Map k Int
shiftIntMap = Map.map (+1)

shiftProofMap :: Map.Map String (Int,RelJudgment)
              -> Map.Map String (Int,RelJudgment)
shiftProofMap = Map.map (\(i,j) -> (i+1,j))

bindTermVar :: String -> ElaborateContext -> ElaborateContext
bindTermVar x ctx =
  ctx { boundVars = Map.insert x 0 (shiftIntMap (boundVars ctx))
      , termDepth = termDepth ctx + 1 }

bindRelVar :: String -> ElaborateContext -> ElaborateContext
bindRelVar r ctx =
  ctx { boundRelVars = Map.insert r 0 (shiftIntMap (boundRelVars ctx))
      , relDepth  = relDepth  ctx + 1 }

bindProofVar :: String -> RelJudgment -> ElaborateContext -> ElaborateContext
bindProofVar p j ctx =
  ctx { boundProofVars = Map.insert p (0,j) (shiftProofMap (boundProofVars ctx))
      , proofDepth = proofDepth ctx + 1 }

emptyElaborateContext :: ElaborateContext
emptyElaborateContext = ElaborateContext
  { macroEnv = Lib.MacroEnvironment Map.empty Map.empty
  , theoremEnv = Lib.TheoremEnvironment Map.empty
  , termDepth = 0
  , relDepth = 0
  , proofDepth = 0
  , boundVars = Map.empty
  , boundRelVars = Map.empty
  , boundProofVars = Map.empty
  }

type ElaborateM = ReaderT ElaborateContext (Except ElaborateError)

----------------------------------------------------------------------
-- Mixfix re-parsing after the grammar parser
----------------------------------------------------------------------

data Tok a = TV a                        -- operand
           | TOP Text SourcePos          -- operator literal token
  deriving Show

data Assoc = ALeft | ARight | ANon deriving Eq

toTokT :: S.Set T.Text -> Raw.RawTerm -> Tok Raw.RawTerm
toTokT ops t@(Raw.RTVar (Raw.Name nm) pos)
  | nm `S.member` ops             = TOP nm pos
  | otherwise                     = TV  t
toTokT _   t                      = TV  t

toTokR :: S.Set T.Text -> Raw.RawRType -> Tok Raw.RawRType
toTokR ops r@(Raw.RRVar (Raw.Name nm) pos)
  | nm `S.member` ops             = TOP nm pos
  | otherwise                     = TV  r
toTokR _   r                      = TV  r

-- Build one precedence table   Int -> [(literal, assoc)]
type PrecTable = IntMap.IntMap [(Text, Assoc)]

-- Check if an operator is postfix in the macro environment
isPostfixOperator :: Text -> MacroEnvironment -> Bool
isPostfixOperator op env = 
  let opStr = T.unpack op
  in any (\(macroName, fixity) -> 
    case fixity of
      Postfix _ -> opStr `elem` splitMixfix macroName
      _ -> False
  ) (Map.toList (macroFixities env))

precTable :: MacroEnvironment -> PrecTable
precTable env = IntMap.fromListWith (++)
  [ (p, [(T.pack keyword, assoc)])
  | (macroName, fix) <- Map.toList (macroFixities env)
  , keyword <- splitMixfix macroName
  , let (assoc, p) = case fix of
          Infixl  n -> (ALeft , n)
          Infixr  n -> (ARight, n)
          InfixN  n -> (ANon  , n)
          Prefix  n -> (ARight, n)
          Postfix n -> (ALeft , n)
  ]

-- Flatten a left-nested application
flattenAppsT :: Raw.RawTerm -> [Raw.RawTerm]
flattenAppsT = go []
  where
    go acc (Raw.RTApp f x _) = go (x:acc) f
    go acc t = t:acc

flattenAppsR :: Raw.RawRType -> [Raw.RawRType]
flattenAppsR = go []
  where
    -- NEW: collapse R S T …   (left‑nested)
    go acc (Raw.RRApp f x _)  = go (x:acc) f
    -- keep the old composition flattening – harmless and still useful
    go acc (Raw.RRComp f x _) = go (x:acc) f
    go acc r                  = r:acc


-- Simple shunting-yard for binary infix operators
reduceLevelT :: Int -> [Tok Raw.RawTerm] -> ElaborateM [Tok Raw.RawTerm]
reduceLevelT k toks = do
  ctx <- ask
  let lits = fromMaybe [] (IntMap.lookup k (precTable (macroEnv ctx)))
  go ctx lits toks
  where
    -- Handle postfix operators: TV a : TOP op : rest
    go ctx lits (TV a : TOP op pos : rest)
      | Just ALeft <- lookup op lits, isPostfixOperator op (macroEnv ctx) = do
          let macroName = "_" <> T.unpack op
              rawNode = Raw.RTMacro (Raw.Name (T.pack macroName)) [a] pos
          go ctx lits (TV rawNode : rest)
    -- gather as many  (TOP op TV arg)  pairs as we can to build one n‑ary node
    go ctx lits (TV a : TOP op pos : TV b : rest)
      | Just assoc <- lookup op lits = do
          let (args, rest') = collect op [a, b] rest
              macroName     = "_" <> intercalate "_" (replicate (length args - 1) (T.unpack op)) <> "_"
          case Map.lookup macroName (macroDefinitions (macroEnv ctx)) of
            Just (params, _) | length params == length args -> do
              let rawNode = Raw.RTMacro (Raw.Name (T.pack macroName)) args pos
              go ctx lits (TV rawNode : rest')
            _ -> do -- fallback to binary   _op_
              let rawNode = Raw.RTMacro (Raw.Name ("_" <> op <> "_")) [a, b] pos
              go ctx lits (TV rawNode : rest)
      | otherwise = (TV a :) <$> go ctx lits (TOP op pos : TV b : rest)
    go ctx lits (x:xs) = (x:) <$> go ctx lits xs
    go _ _ [] = return []

    -- keep swallowing   TOP op TV arg
    collect op acc (TOP op' _ : TV c : rest) | op' == op =
      collect op (acc ++ [c]) rest
    collect _  acc rest = (acc, rest)

-- **exact copy** for relational types ----------------------------------------
reduceLevelR :: Int -> [Tok Raw.RawRType] -> ElaborateM [Tok Raw.RawRType]
reduceLevelR k toks = do
  ctx <- ask
  let lits = fromMaybe [] (IntMap.lookup k (precTable (macroEnv ctx)))
  go ctx lits toks
  where
    -- Handle postfix operators: TV a : TOP op : rest
    go ctx lits (TV a : TOP op pos : rest)
      | Just ALeft <- lookup op lits, isPostfixOperator op (macroEnv ctx) = do
          let macroName = "_" <> T.unpack op
              rawNode = Raw.RRMacro (Raw.Name (T.pack macroName)) [a] pos
          go ctx lits (TV rawNode : rest)
    go ctx lits (TV a : TOP op pos : TV b : rest)
      | Just assoc <- lookup op lits = do
          let (args, rest') = collect op [a, b] rest
              macroName     = "_" <> intercalate "_" (replicate (length args - 1) (T.unpack op)) <> "_"
          case Map.lookup macroName (macroDefinitions (macroEnv ctx)) of
            Just (params, _) | length params == length args -> do
              let rawNode = Raw.RRMacro (Raw.Name (T.pack macroName)) args pos
              go ctx lits (TV rawNode : rest')
            _ -> do -- binary fallback
              let rawNode = Raw.RRMacro (Raw.Name ("_" <> op <> "_")) [a, b] pos
              go ctx lits (TV rawNode : rest)
      | otherwise = (TV a :) <$> go ctx lits (TOP op pos : TV b : rest)
    go ctx lits (x:xs) = (x:) <$> go ctx lits xs
    go _ _ [] = return []

    collect op acc (TOP op' _ : TV c : rest) | op' == op =
      collect op (acc ++ [c]) rest
    collect _  acc rest = (acc, rest)

runLevelsT :: [Int] -> [Tok Raw.RawTerm] -> ElaborateM [Tok Raw.RawTerm]
-- We now run *two* passes per precedence level:
--   1. reducePrefixT  – handles n‑ary **prefix** patterns such as
--      "if _ then _ else _"
--   2. reduceLevelT   – existing binary infix handling
runLevelsT ks toks = foldM (\acc k -> reducePrefixT k acc >>= reduceLevelT k) toks ks

runLevelsR :: [Int] -> [Tok Raw.RawRType] -> ElaborateM [Tok Raw.RawRType]
runLevelsR ks toks = foldM (\acc k -> reducePrefixR k acc >>= reduceLevelR k) toks ks

----------------------------------------------------------------------
-- NEW CODE:  generic *prefix*‑mixfix reduction (any arity ≥ 1)
----------------------------------------------------------------------

-- | Collect (macro‑name , literal pieces) for every *prefix* operator
--   that lives on precedence @k@.
prefixMacros
  :: Int
  -> MacroEnvironment
  -> [(String,[T.Text])]   -- (canonicalName , ["if","then","else"])
prefixMacros k env =
  [ (m , map T.pack (splitMixfix m))
  | (m,Prefix p) <- Map.toList (macroFixities env)
  , p == k
  ]

-- | Try to match a single prefix pattern at the head of the token stream.
--   Return @(macroName , args , rest)@ on success.
matchPrefix
  :: (String,[T.Text])
  -> [Tok a]
  -> Maybe (String,[a],[Tok a], SourcePos)
matchPrefix (mName,lits) toks = go lits toks [] Nothing
  where
    -- usual "lit • arg" steps
    go :: [T.Text] -> [Tok a] -> [a] -> Maybe SourcePos
       -> Maybe (String,[a],[Tok a], SourcePos)
    go (l:ls) (TOP lit pos : TV arg : rest) acc start
      | lit == l  = go ls rest (acc ++ [arg]) (Just (maybe pos id start))
    -- ***NEW*** – final *closing literal* after the last argument
    go [l] (TOP lit pos : rest) acc start
      | lit == l  = Just (mName,acc,rest, maybe pos id start)
    go [] rest acc (Just startPos) =
          Just (mName,acc,rest,startPos)
    go _ _ _ _    = Nothing

-- | Reduce *prefix* mixfix operators of precedence @k@ inside a
--   token stream (terms).
reducePrefixT :: Int -> [Tok Raw.RawTerm] -> ElaborateM [Tok Raw.RawTerm]
reducePrefixT k toks = do
  env <- asks macroEnv
  let pms = prefixMacros k env
  pure (loop toks pms)
  where
    loop [] _ = []
    loop ts@(TOP lit _ : _) pms =
      case asum (map (`matchPrefix` ts) pms) of
        Just (mName,args,rest,startPos) ->
          let node = Raw.RTMacro (Raw.Name (T.pack mName)) args startPos
          in TV node : loop rest pms
        Nothing -> case ts of
                     x:xs -> x : loop xs pms
                     []   -> []
    loop (x:xs) pms = x : loop xs pms

-- | Same, but for relational‑types.
reducePrefixR :: Int -> [Tok Raw.RawRType] -> ElaborateM [Tok Raw.RawRType]
reducePrefixR k toks = do
  env <- asks macroEnv
  let pms = prefixMacros k env
  pure (loop toks pms)
  where
    loop [] _ = []
    loop ts@(TOP lit _ : _) pms =
      case asum (map (`matchPrefix` ts) pms) of
        Just (mName,args,rest,startPos) ->
          let node = Raw.RRMacro (Raw.Name (T.pack mName)) args startPos
          in TV node : loop rest pms
        Nothing -> case ts of
                     x:xs -> x : loop xs pms
                     []   -> []
    loop (x:xs) pms = x : loop xs pms

reparseTerms :: SourcePos -> [Raw.RawTerm] -> ElaborateM Term
reparseTerms pos rawList = do
  ctx <- ask
  let ops = S.map T.pack (mixfixKeywords (macroEnv ctx))
      toks0 = map (toTokT ops) rawList
      precs = reverse (IntMap.keys (precTable (macroEnv ctx)))
  toks1 <- runLevelsT precs toks0
  case toks1 of
    [TV raw] -> elaborateTerm raw
    _ -> throwError $ InvalidMixfixPattern "cannot resolve operators" pos

reparseRTypes :: SourcePos -> [Raw.RawRType] -> ElaborateM RType
reparseRTypes pos rawList = do
  ctx <- ask
  let ops = S.map T.pack (mixfixKeywords (macroEnv ctx))
      toks0 = map (toTokR ops) rawList
      precs = reverse (IntMap.keys (precTable (macroEnv ctx)))
  toks1 <- runLevelsR precs toks0
  case toks1 of
    [TV raw] -> elaborateRType raw
    _ -> throwError $ InvalidMixfixPattern "cannot resolve operators" pos


-- Check if there are any operator tokens in the list
hasOperatorT :: [Tok Raw.RawTerm] -> Bool
hasOperatorT = any isOp
  where
    isOp (TOP _ _) = True
    isOp _ = False

hasOperatorR :: [Tok Raw.RawRType] -> Bool
hasOperatorR = any isOp
  where
    isOp (TOP _ _) = True
    isOp _ = False

-- Main elaboration function
elaborate :: ElaborateContext -> Raw.RawDeclaration
          -> Either FrontEndError        Declaration
elaborate ctx rawDecl =
  first ElabError $ runExcept (runReaderT (elaborateDeclaration rawDecl) ctx)

elaborateDeclaration :: Raw.RawDeclaration -> ElaborateM Declaration
elaborateDeclaration (Raw.RawMacro name params body) = do
  ctx <- ask
  let pNames = map nameString params

      -- Using the centralized binder functions

      ctxTerm = foldl (flip bindTermVar) ctx pNames   -- last parameter = index 0
      ctxRel  = foldl (flip bindRelVar ) ctx pNames
  -------------------------------------------------------------------------
  elaboratedBody <- case body of
    Raw.RawTermBody _ -> local (const ctxTerm) (elaborateMacroBody body)
    Raw.RawRelBody  _ -> local (const ctxRel ) (elaborateMacroBody body)

  let declared = Map.lookup (nameString name) (macroFixities (macroEnv ctx))
      fx       = maybe (defaultFixity (nameString name)) id declared
  pure $ MacroDef (nameString name) pNames elaboratedBody
  
elaborateDeclaration (Raw.RawTheorem name bindings judgment proof) = do
  -- Elaborate bindings and extend context
  (elaboratedBindings, newCtx) <- elaborateBindings bindings
  -- Elaborate judgment and proof in extended context
  elaboratedJudgment <- local (const newCtx) (elaborateJudgment judgment)
  elaboratedProof <- local (const newCtx) (elaborateProof proof)
  return $ TheoremDef (nameString name) elaboratedBindings elaboratedJudgment elaboratedProof

elaborateDeclaration (Raw.RawFixityDecl fix name) = do
  ctx <- ask
  let env0 = macroEnv ctx
      env1 = env0 { macroFixities = Map.insert (nameString name) fix
                                         (macroFixities env0) }
  local (\c -> c { macroEnv = env1 })
        (pure (FixityDecl fix (nameString name)))

elaborateMacroBody :: Raw.RawMacroBody -> ElaborateM Lib.MacroBody
elaborateMacroBody (Raw.RawTermBody rawTerm) = do
  elaboratedTerm <- elaborateTerm rawTerm
  return $ Lib.TermMacro elaboratedTerm
elaborateMacroBody (Raw.RawRelBody rawRType) = do
  elaboratedRType <- elaborateRType rawRType
  return $ Lib.RelMacro elaboratedRType

elaborateBindings :: [Raw.RawBinding] -> ElaborateM ([Binding], ElaborateContext)
elaborateBindings bindings = do
  ctx <- ask
  foldM elaborateBinding ([], ctx) bindings
  where
    elaborateBinding (acc, ctx) (Raw.RawTermBinding name) = do
      let binding = TermBinding (nameString name)
      let newCtx = bindTermVar (nameString name) ctx
      return (acc ++ [binding], newCtx)
    
    elaborateBinding (acc, ctx) (Raw.RawRelBinding name) = do
      let binding = RelBinding (nameString name)
      let newCtx = bindRelVar  (nameString name) ctx
      return (acc ++ [binding], newCtx)
    
    elaborateBinding (acc, ctx) (Raw.RawProofBinding name rawJudgment) = do
      elaboratedJudgment <- local (const ctx) (elaborateJudgment rawJudgment)
      let binding = ProofBinding (nameString name) elaboratedJudgment
      let newCtx = bindProofVar (nameString name) elaboratedJudgment ctx
      return (acc ++ [binding], newCtx)

elaborateJudgment :: Raw.RawJudgment -> ElaborateM RelJudgment
elaborateJudgment (Raw.RawJudgment rawTerm1 rawRType rawTerm2) = do
  term1 <- elaborateTerm rawTerm1
  rtype <- elaborateRType rawRType
  term2 <- elaborateTerm rawTerm2
  return $ RelJudgment term1 rtype term2


elaborateTerm :: Raw.RawTerm -> ElaborateM Term
elaborateTerm (Raw.RTVar name pos) = do
  ctx <- ask
  case Map.lookup (nameString name) (boundVars ctx) of
    Just bindingDepth ->
      return $ Var (nameString name) bindingDepth pos
    Nothing -> 
      -- Try looking up as a macro with zero arguments
      case Map.lookup (nameString name) (Lib.macroDefinitions (macroEnv ctx)) of
        Just ([], macroBody) -> 
          -- Macro with zero arguments - create TMacro node
          case macroBody of
            Lib.TermMacro _ -> return $ TMacro (nameString name) [] pos
            Lib.RelMacro _ -> throwError $ UnknownVariable ("Relational macro " ++ nameString name ++ " used in term context") pos
        Just (params, _) -> 
          -- Macro exists but requires arguments
          throwError $ MacroArityMismatch (nameString name) (length params) 0 pos
        Nothing -> throwError $ UnknownVariable (nameString name) pos

elaborateTerm (Raw.RTLam name rawBody pos) = do
  ctx <- ask
  let varName = nameString name
  let newCtx = bindTermVar varName ctx
  body <- local (const newCtx) (elaborateTerm rawBody)
  return $ Lam varName body pos

elaborateTerm raw@(Raw.RTApp _ _ pos) = do
  ctx <- ask
  let flattened = flattenAppsT raw
      ops = S.map T.pack (mixfixKeywords (macroEnv ctx))
      toks = map (toTokT ops) flattened
  -- Check if this contains mixfix operators
  if hasOperatorT toks
    then -- Contains mixfix operators - use mixfix parsing
      reparseTerms pos flattened
    else -- No mixfix operators - check for simple macro application
      case flattened of
        (Raw.RTVar name _ : args) -> do
          let macroName = nameString name
          -- First check if this name is bound as a variable - bound variables take precedence
          case Map.lookup macroName (boundVars ctx) of
            Just _ -> elaborateAppLeft raw  -- Bound variable - regular function application
            Nothing -> 
              case Map.lookup macroName (Lib.macroDefinitions (macroEnv ctx)) of
                Nothing -> elaborateAppLeft raw  -- Not a macro - regular function application
                Just (params, _) -> smartAppT macroName params args pos  -- Macro application
        _ -> elaborateAppLeft raw  -- Not a simple application - regular function application
  where
    elaborateAppLeft (Raw.RTApp rawFunc rawArg _) = do
      func <- elaborateTerm rawFunc
      arg <- elaborateTerm rawArg
      return $ App func arg pos
    elaborateAppLeft other = elaborateTerm other
    
    smartAppT macroName params args pos = do
      -- Terms allow over-application (unlike relations)
      if length args < length params
        then throwError $ MacroArityMismatch macroName (length params) (length args) pos
        else do
          let (macroArgs, extraArgs) = splitAt (length params) args
          elaboratedMacroArgs <- mapM elaborateTerm macroArgs
          let macroApp = TMacro macroName elaboratedMacroArgs pos
          -- Apply any extra arguments
          foldM (\acc arg -> do
            elaboratedArg <- elaborateTerm arg
            return $ App acc elaboratedArg pos) macroApp extraArgs

elaborateTerm (Raw.RTMacro name rawArgs pos) = do
  ctx <- ask
  let macroName = nameString name
  case Map.lookup macroName (Lib.macroDefinitions (macroEnv ctx)) of
    Nothing -> throwError $ UnknownMacro macroName pos
    Just (params, _) -> do
      when (length params /= length rawArgs) $
        throwError $ MacroArityMismatch macroName (length params) (length rawArgs) pos
      args <- mapM elaborateTerm rawArgs
      return $ TMacro macroName args pos

elaborateRType :: Raw.RawRType -> ElaborateM RType
elaborateRType (Raw.RRVar name pos) = do
  ctx <- ask
  case Map.lookup (nameString name) (boundRelVars ctx) of
    Just bindingDepth -> 
      return $ RVar (nameString name) bindingDepth pos
    Nothing -> 
      -- Try looking up as a term variable (which can be promoted to relation)
      case Map.lookup (nameString name) (boundVars ctx) of
        Just bindingDepth ->
          return $ Prom (Var (nameString name) bindingDepth pos) pos
        Nothing -> 
          -- Try looking up as a macro with zero arguments
          case Map.lookup (nameString name) (Lib.macroDefinitions (macroEnv ctx)) of
            Just ([], macroBody) -> 
              -- Macro with zero arguments - create RMacro node or promote TMacro
              case macroBody of
                Lib.TermMacro _ -> return $ Prom (TMacro (nameString name) [] pos) pos
                Lib.RelMacro _ -> return $ RMacro (nameString name) [] pos
            Just (params, _) -> 
              -- Macro exists but requires arguments
              throwError $ MacroArityMismatch (nameString name) (length params) 0 pos
            Nothing -> throwError $ UnknownVariable (nameString name) pos

elaborateRType (Raw.RRArr rawLeft rawRight pos) = do
  left <- elaborateRType rawLeft
  right <- elaborateRType rawRight
  return $ Arr left right pos

elaborateRType (Raw.RRAll name rawBody pos) = do
  ctx <- ask
  let varName = nameString name
  let newCtx = bindRelVar varName ctx
  body <- local (const newCtx) (elaborateRType rawBody)
  return $ All varName body pos

-- | Juxtaposition in relational types is *only* allowed to form a
--   (prefix or infix) macro application.  Anything left over after
--   re‑parsing is therefore an error.
elaborateRType raw@(Raw.RRApp _ _ pos) = do
  ctx  <- ask
  let flattened = flattenAppsR raw
      ops = S.map T.pack (mixfixKeywords (macroEnv ctx))
      toks = map (toTokR ops) flattened
  -- Check if this contains mixfix operators
  if hasOperatorR toks
    then -- Contains mixfix operators - use mixfix parsing
      reparseRTypes pos flattened
    else -- No mixfix operators - check for simple macro application
      case flattened of
        (Raw.RRVar name _ : args) -> do
          let macroName = nameString name
          case Map.lookup macroName (Lib.macroDefinitions (macroEnv ctx)) of
            Nothing -> throwError $ InvalidMixfixPattern "bare application is illegal for Rel" pos
            Just (params, _) -> smartAppR macroName params args pos
        _ -> throwError $ InvalidMixfixPattern "bare application is illegal for Rel" pos
  where
    smartAppR macroName params args pos = do
      when (length params /= length args) $
        throwError $ MacroArityMismatch macroName (length params) (length args) pos
      elaboratedArgs <- mapM elaborateRType args
      return $ RMacro macroName elaboratedArgs pos

elaborateRType raw@(Raw.RRComp _ _ pos) = do
  ctx <- ask
  let ops = S.map T.pack (mixfixKeywords (macroEnv ctx))
      toks = map (toTokR ops) (flattenAppsR raw)
  case hasOperatorR toks of
    False -> elaborateCompLeft raw
    True  -> reparseRTypes pos (flattenAppsR raw)
  where
    elaborateCompLeft (Raw.RRComp rawLeft rawRight _) = do
      left <- elaborateRType rawLeft
      right <- elaborateRType rawRight
      return $ Comp left right pos
    elaborateCompLeft other = elaborateRType other

elaborateRType (Raw.RRConv rawRType pos) = do
  rtype <- elaborateRType rawRType
  return $ Conv rtype pos

elaborateRType (Raw.RRMacro name rawArgs pos) = do
  ctx <- ask
  let macroName = nameString name
  case Map.lookup macroName (Lib.macroDefinitions (macroEnv ctx)) of
    Nothing -> throwError $ UnknownMacro macroName pos
    Just (params, _) -> do
      when (length params /= length rawArgs) $
        throwError $ MacroArityMismatch macroName (length params) (length rawArgs) pos
      args <- mapM elaborateRType rawArgs
      return $ RMacro macroName args pos

elaborateRType (Raw.RRProm rawTerm pos) = do
  term <- elaborateTerm rawTerm
  return $ Prom term pos

elaborateProof :: Raw.RawProof -> ElaborateM Proof
elaborateProof (Raw.RPVar name pos) = do
  ctx <- ask
  case Map.lookup (nameString name) (boundProofVars ctx) of
    Just (bindingDepth, _) ->
      return $ PVar (nameString name) bindingDepth pos
    Nothing -> throwError $ UnknownVariable (nameString name) pos

elaborateProof (Raw.RPApp rawFunc rawArg pos) = do
  func <- elaborateProof rawFunc
  arg <- elaborateProof rawArg
  return $ AppP func arg pos

elaborateProof (Raw.RPTheorem name rawArgs pos) = do
  ctx <- ask
  let theoremName = nameString name
  case Map.lookup theoremName (Lib.theoremDefinitions (theoremEnv ctx)) of
    Nothing -> throwError $ UnknownTheorem theoremName pos
    Just (bindings, _, _) -> do
      when (length bindings /= length rawArgs) $
        throwError $ TheoremArityMismatch theoremName (length bindings) (length rawArgs) pos
      args <- mapM elaborateArg rawArgs
      return $ PTheoremApp theoremName args pos

elaborateProof (Raw.RPLamP name rawRType rawBody pos) = do
  ctx <- ask
  elaboratedRType <- elaborateRType rawRType
  let varName = nameString name
  -- Create a dummy judgment for the proof variable
  let judgment = RelJudgment (Var "dummy" 0 pos) elaboratedRType (Var "dummy" 0 pos)
  let newCtx = bindProofVar varName judgment ctx
  body <- local (const newCtx) (elaborateProof rawBody)
  return $ LamP varName elaboratedRType body pos

elaborateProof (Raw.RPLamT name rawBody pos) = do
  ctx <- ask
  let varName = nameString name
  let newCtx = bindRelVar varName ctx
  body <- local (const newCtx) (elaborateProof rawBody)
  return $ TyLam varName body pos

elaborateProof (Raw.RPAppT rawProof rawRType pos) = do
  proof <- elaborateProof rawProof
  rtype <- elaborateRType rawRType
  return $ TyApp proof rtype pos

elaborateProof (Raw.RPConv rawTerm1 rawProof rawTerm2 pos) = do
  term1 <- elaborateTerm rawTerm1
  proof <- elaborateProof rawProof
  term2 <- elaborateTerm rawTerm2
  return $ ConvProof term1 proof term2 pos

elaborateProof (Raw.RPIota rawTerm1 rawTerm2 pos) = do
  term1 <- elaborateTerm rawTerm1
  term2 <- elaborateTerm rawTerm2
  return $ Iota term1 term2 pos

elaborateProof (Raw.RPRho x rawT1 rawT2 rawP1 rawP2 pos) = do
  ctx <- ask
  let ctxWithX = bindTermVar (nameString x) ctx
  t1 <- local (const ctxWithX) (elaborateTerm rawT1)
  t2 <- local (const ctxWithX) (elaborateTerm rawT2)
  p1 <- elaborateProof rawP1     --  x NOT in scope here
  p2 <- elaborateProof rawP2
  return $ RhoElim (nameString x) t1 t2 p1 p2 pos

elaborateProof (Raw.RPPi rawProof x u v rawQ pos) = do
  p <- elaborateProof rawProof
  ctx <- ask
  -- Bind x as a term variable
  let xName = nameString x
      uName = nameString u
      vName = nameString v
      dummyJudgment = RelJudgment (Var "dummy" 0 pos) (RVar "dummy" 0 pos) (Var "dummy" 0 pos)
      ctxWithX  = bindTermVar  xName ctx
      ctxWithU  = bindProofVar uName dummyJudgment ctxWithX
      ctxWithUV = bindProofVar vName dummyJudgment ctxWithU
  -- Elaborate q in the extended context
  q <- local (const ctxWithUV) (elaborateProof rawQ)
  return $ Pi p xName uName vName q pos

elaborateProof (Raw.RPConvIntro rawProof pos) = do
  proof <- elaborateProof rawProof
  return $ ConvIntro proof pos

elaborateProof (Raw.RPConvElim rawProof pos) = do
  proof <- elaborateProof rawProof
  return $ ConvElim proof pos

elaborateProof (Raw.RPPair rawProof1 rawProof2 pos) = do
  proof1 <- elaborateProof rawProof1
  proof2 <- elaborateProof rawProof2
  return $ Pair proof1 proof2 pos

elaborateProof (Raw.RPMixfix name rawArgs pos) = do
  args <- mapM elaborateProof rawArgs
  -- For now, treat mixfix as regular function application
  return $ PTheoremApp (nameString name) (map ProofArg args) pos

elaborateArg :: Raw.RawArg -> ElaborateM TheoremArg
elaborateArg (Raw.TermArg rawTerm) = do
  term <- elaborateTerm rawTerm
  return $ TermArg term
elaborateArg (Raw.RelArg rawRType) = do
  rtype <- elaborateRType rawRType
  return $ RelArg rtype
elaborateArg (Raw.ProofArg rawProof) = do
  proof <- elaborateProof rawProof
  return $ ProofArg proof