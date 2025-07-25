{-# LANGUAGE OverloadedStrings #-}
module Elaborate
  ( ElaborateError(..)
  , elaborateTerm
  , elaborateRType  
  , elaborateProof
  , elaborateRelJudgment
  , elaborateBinding
  , elaborateDeclaration
  , ElaborateContext(..)
  , emptyElaborateContext
  , desugarMixfix
  ) where

import qualified Data.Map as Map
import Data.List (intercalate)
import Control.Monad (foldM)
import RawParser (FixityMap, parseTermWithFixities, parseRType, RawTerm(..), RawRType(..), RawProof(..), RawRelJudgment(..), RawBinding(..), RawMacroBody(..), RawDeclaration(..), RawImportDeclaration(..), RawExportDeclaration(..), RawFixity(..))
import Lib
import Context (lookupTheorem)
import Text.Megaparsec (SourcePos, initialPos)
import qualified Text.Megaparsec as M (runParser)

-- | Errors that can occur during elaboration
data ElaborateError
  = UnknownTerm String
  | UnknownRelation String  
  | UnknownProof String
  | UnknownTheorem String
  | MacroArityMismatch String Int Int  -- name, expected, got
  | TheoremArityMismatch String Int Int -- name, expected, got
  deriving (Show, Eq)

-- | Context for elaboration with environments and de Bruijn tracking
data ElaborateContext = ElaborateContext
  { termVars :: Map.Map String Int
  , relVars :: Map.Map String Int
  , proofVars :: Map.Map String Int
  , macroEnv :: MacroEnvironment
  , theoremEnv :: TheoremEnvironment
  , fixities :: FixityMap
  , currentPos :: SourcePos
  } deriving (Show, Eq)

-- | Generate a more specific position for different constructs
makePos :: String -> SourcePos
makePos name = initialPos ("elaboration:" ++ name)


emptyElaborateContext :: FixityMap -> MacroEnvironment -> TheoremEnvironment -> ElaborateContext
emptyElaborateContext fx mEnv tEnv = ElaborateContext
  { termVars = Map.empty
  , relVars = Map.empty  
  , proofVars = Map.empty
  , macroEnv = mEnv
  , theoremEnv = tEnv
  , fixities = fx
  , currentPos = initialPos "elaboration"
  }


-- | Elaborate a raw term into a concrete term
elaborateTerm :: ElaborateContext -> RawTerm -> Either ElaborateError Term
elaborateTerm ctx rawTerm = do
  let desugared = desugarMixfix (macroEnv ctx) rawTerm
  case desugared of
    ------------------------------------------------------------------
    -- λ-abstraction
    RTLam v body -> do
      let pos      = makePos ("lambda:" ++ v)
          newIndex = 0
          shifted  = Map.map (+1) (termVars ctx)
          ctx'     = ctx { termVars = Map.insert v newIndex shifted }
      body' <- elaborateTerm ctx' body
      Right (Lam v body' pos)

    ------------------------------------------------------------------
    -- Application chain – *here* we decide if head is Var or Macro
    RTApp _ _ | Just ts <- flattenApp desugared -> elabAppChain ctx ts
    ------------------------------------------------------------------
    -- Should be unreachable after mix-fix pass, but keep for safety
    RTApp _ _ -> Left (UnknownTerm "internal-RTApp-not-flattened")
    RTMacro name args -> do
      let pos = makePos ("macro:" ++ name)
      case Map.lookup name (macroDefinitions (macroEnv ctx)) of
        Just (params, TermMacro _) -> do
          let expectedArity = length params
              gotArity = length args
          if expectedArity == gotArity
            then do
              args' <- mapM (elaborateTerm ctx) args
              Right (TMacro name args' pos)
            else Left (MacroArityMismatch name expectedArity gotArity)
        Just (_, RelMacro _) -> Left (UnknownTerm name)
        Nothing -> Left (UnknownTerm name)
    RawOp op    -> Left (UnknownTerm op)
    RTVar v     -> resolveHead ctx v []           -- bare identifier
  where
    ----------------------------------------------------------------
    -- flatten left-associative RTApp into (head : args)
    flattenApp :: RawTerm -> Maybe [RawTerm]
    flattenApp t = case go t of
                     (_:_:_) -> Just (reverse (go t)) -- two or more elements => application
                     _       -> Nothing
      where
        go (RTApp f x) = x : go f
        go other       = [other]

    ----------------------------------------------------------------
    -- elaborate an application list
    elabAppChain :: ElaborateContext -> [RawTerm] -> Either ElaborateError Term
    elabAppChain c (RTVar hd : args) = do
      -- First resolve the head with *current* environment.
      headTerm <- resolveHead c hd args
      -- If resolveHead already built a macro with exactly arity,
      --   maybe there are leftover arguments (over-application).
      -- headTerm is either Var… or TMacro… possibly partially applied.
      foldM (\f a -> do
               arg' <- elaborateTerm c a
               return (App f arg' (makePos "application")))
            headTerm
            (drop (numConsumed headTerm) args)
      where
        numConsumed (TMacro _ as _) = length as
        numConsumed _               = 0
    elabAppChain c (hd : args) = do
      -- Handle non-identifier heads (like lambdas, other expressions)
      headTerm <- elaborateTerm c hd
      foldM (\f a -> do
               arg' <- elaborateTerm c a
               return (App f arg' (makePos "application")))
            headTerm
            args
    elabAppChain _ []    = error "impossible: empty application list"

    ----------------------------------------------------------------
    -- Decide Var vs. Macro (arity checked) vs. Unknown
    resolveHead :: ElaborateContext -> String -> [RawTerm] -> Either ElaborateError Term
    resolveHead c name argRaw =
      case Map.lookup name (termVars c) of
        Just idx -> pure (Var name idx (makePos ("var:" ++ name)))  -- shadowed ⇒ variable
        Nothing  ->
          case Map.lookup name (macroDefinitions (macroEnv c)) of
            Just (params, TermMacro _) ->
              let need = length params
                  have = length argRaw
              in if have >= need
                 then do
                   argsElab <- traverse (elaborateTerm c) (take need argRaw)
                   pure (TMacro name argsElab (makePos ("macro:" ++ name)))
                 else Left (MacroArityMismatch name need have)
            _ -> Left (UnknownTerm name)

-- | Elaborate a raw relation type into a concrete relation type  
elaborateRType :: ElaborateContext -> RawRType -> Either ElaborateError RType
elaborateRType ctx (RRVar name) = do
  let pos = makePos ("rvar:" ++ name)
  case Map.lookup name (relVars ctx) of
    Just index -> Right (RVar name index pos)
    Nothing ->
      -- Check if it's a macro
      case Map.lookup name (macroDefinitions (macroEnv ctx)) of
        Just ([], RelMacro body) -> Right (RMacro name [] pos) -- 0-arity macro
        Just (params, RelMacro _) -> Left (MacroArityMismatch name (length params) 0)
        Just (_, TermMacro _) -> Left (UnknownRelation name) -- Can't use term macro as rel
        Nothing -> Left (UnknownRelation name)

elaborateRType ctx (RRArr left right) = do
  let pos = makePos "arrow"
  left' <- elaborateRType ctx left
  right' <- elaborateRType ctx right
  Right (Arr left' right' pos)

elaborateRType ctx (RRAll var body) = do
  let pos = currentPos ctx
      newIndex = 0
      shiftedVars = Map.map (+ 1) (relVars ctx)
      newCtx = ctx { relVars = Map.insert var newIndex shiftedVars }
  body' <- elaborateRType newCtx body
  Right (All var body' pos)

elaborateRType ctx (RRComp left right) = do
  let pos = makePos "comp"
  left' <- elaborateRType ctx left
  right' <- elaborateRType ctx right
  Right (Comp left' right' pos)

elaborateRType ctx (RRConv rtype) = do
  let pos = makePos "conv"
  rtype' <- elaborateRType ctx rtype
  Right (Conv rtype' pos)

elaborateRType ctx (RRProm term) = do
  let pos = currentPos ctx
  term' <- elaborateTerm ctx term
  Right (Prom term' pos)

elaborateRType ctx (RRMacro name args) = do
  let pos = currentPos ctx
  case Map.lookup name (macroDefinitions (macroEnv ctx)) of
    Just (params, RelMacro _) -> do
      let expectedArity = length params
          gotArity = length args
      if expectedArity == gotArity
        then do
          args' <- mapM (elaborateRType ctx) args
          Right (RMacro name args' pos)
        else Left (MacroArityMismatch name expectedArity gotArity)
    Just (_, TermMacro _) -> Left (UnknownRelation name)
    Nothing -> Left (UnknownRelation name)

-- | Elaborate a raw relational judgment
elaborateRelJudgment :: ElaborateContext -> RawRelJudgment -> Either ElaborateError RelJudgment
elaborateRelJudgment ctx (RawRelJudgment t1 r t2) = do
  t1' <- elaborateTerm ctx t1
  r' <- elaborateRType ctx r
  t2' <- elaborateTerm ctx t2
  Right (RelJudgment t1' r' t2')

-- | Elaborate a raw binding
elaborateBinding :: ElaborateContext -> RawBinding -> Either ElaborateError Binding
elaborateBinding _ (RawTermBinding name) = Right (TermBinding name)
elaborateBinding _ (RawRelBinding name) = Right (RelBinding name)
elaborateBinding ctx (RawProofBinding name judgment) = do
  judgment' <- elaborateRelJudgment ctx judgment
  Right (ProofBinding name judgment')

-- | Disambiguate macro body by trying both term and relational type interpretations
disambiguateMacroBody :: ElaborateContext -> String -> [String] -> Either ElaborateError MacroBody
disambiguateMacroBody ctx src params =
  let n = length params
      paramMap = Map.fromList (zip params (reverse [0..n-1]))
      
      -- contexts for the two attempts
      termCtx = ctx { termVars = paramMap, relVars = Map.empty }
      relCtx = ctx { termVars = Map.empty, relVars = paramMap }
      
      -- helpers
      run p fx = M.runParser (p fx) "<macro-body>" src
      
      tryRel =
        case M.runParser parseRType "<macro-body>" src of
          Right rawTy ->
            case elaborateRType relCtx rawTy of
              Right ty -> Right (RelMacro ty)
              Left _ -> Left (UnknownTerm "cannot parse macro body as term or relational type")
          Left _ -> Left (UnknownTerm "cannot parse macro body as term or relational type")
  in
  -- 1. try as term
  case run parseTermWithFixities (fixities ctx) of
    Right rawTerm ->
      case elaborateTerm termCtx rawTerm of
        Right t -> Right (TermMacro t)
        Left _ -> tryRel
    Left _ -> tryRel

-- | Elaborate a raw declaration
elaborateDeclaration :: ElaborateContext -> RawDeclaration -> Either ElaborateError Declaration
elaborateDeclaration ctx (RawMacroDef name params (RawMacroBodySrc src)) = do
  body' <- disambiguateMacroBody ctx src params
  Right (MacroDef name params body')
elaborateDeclaration ctx (RawTheoremDef name bindings judgment proof) = do
  bindings' <- mapM (elaborateBinding ctx) bindings
  judgment' <- elaborateRelJudgment ctx judgment
  proof' <- elaborateProof ctx proof
  Right (TheoremDef name bindings' judgment' proof')
elaborateDeclaration _ (RawImportDecl (RawImportModule path)) = 
  Right (ImportDecl (ImportModule path))
elaborateDeclaration _ (RawImportDecl (RawImportModuleAs path alias)) = 
  Right (ImportDecl (ImportModuleAs path alias))
elaborateDeclaration _ (RawImportDecl (RawImportOnly path names)) = 
  Right (ImportDecl (ImportOnly path names))
elaborateDeclaration _ (RawExportDecl (RawExportSymbols names)) = 
  Right (ExportDecl (ExportSymbols names))
elaborateDeclaration _ (RawFixityDecl rawFixity name) = do
  let fixity = case rawFixity of
        RawInfixl n -> Infixl n
        RawInfixr n -> Infixr n
        RawInfixN n -> InfixN n
        RawPrefix n -> Prefix n
        RawPostfix n -> Postfix n
  Right (FixityDecl fixity name)

-- | Elaborate a raw proof into a concrete proof
elaborateProof :: ElaborateContext -> RawProof -> Either ElaborateError Proof
elaborateProof ctx (RPVar name) = do
  let pos = currentPos ctx
  case Map.lookup name (proofVars ctx) of
    Just index -> Right (PVar name index pos)
    Nothing ->
      -- Check if it's a theorem
      case lookupTheorem name (theoremEnv ctx) of
        Right (bindings, _, _) -> 
          if null bindings
            then Right (PTheoremApp name [] pos) -- 0-arity theorem is valid
            else Left (TheoremArityMismatch name (length bindings) 0)
        Left _ -> Left (UnknownTheorem name)

elaborateProof ctx (RPLam var rtype body) = do
  let pos = currentPos ctx
      newIndex = 0
      shiftedVars = Map.map (+ 1) (proofVars ctx)
      newCtx = ctx { proofVars = Map.insert var newIndex shiftedVars }
  rtype' <- elaborateRType ctx rtype
  body' <- elaborateProof newCtx body
  Right (LamP var rtype' body' pos)

elaborateProof ctx (RPTyLam var body) = do
  let pos = currentPos ctx
      newIndex = 0
      shiftedVars = Map.map (+ 1) (relVars ctx)
      newCtx = ctx { relVars = Map.insert var newIndex shiftedVars }
  body' <- elaborateProof newCtx body
  Right (TyLam var body' pos)

-- Pattern recognition for atomic tokens that were parsed as applications
-- ι⟨x, y⟩ pattern: ι⟨ x , y ⟩ (parsed as nested left-associative applications)
elaborateProof ctx (RPApp (RPApp (RPApp (RPApp (RPVar "ι⟨") t1) (RPVar ",")) t2) (RPVar "⟩")) = 
  elaborateIotaArgs ctx "ι⟨" t1 t2

elaborateProof ctx (RPApp (RPApp (RPApp (RPApp (RPVar "ι<") t1) (RPVar ",")) t2) (RPVar ">")) = 
  elaborateIotaArgs ctx "ι<" t1 t2

elaborateProof ctx (RPApp (RPApp (RPApp (RPApp (RPVar "iota<") t1) (RPVar ",")) t2) (RPVar ">")) = 
  elaborateIotaArgs ctx "iota<" t1 t2

-- Add other patterns for atomic tokens
elaborateProof ctx (RPApp (RPVar "∪ᵢ") proof) = do
  let pos = currentPos ctx
  proof' <- elaborateProof ctx proof
  Right (ConvIntro proof' pos)

elaborateProof ctx (RPApp (RPVar "convIntro") proof) = do
  let pos = currentPos ctx
  proof' <- elaborateProof ctx proof
  Right (ConvIntro proof' pos)

elaborateProof ctx (RPApp (RPVar "∪ₑ") proof) = do
  let pos = currentPos ctx
  proof' <- elaborateProof ctx proof
  Right (ConvElim proof' pos)

elaborateProof ctx (RPApp (RPVar "convElim") proof) = do
  let pos = currentPos ctx
  proof' <- elaborateProof ctx proof
  Right (ConvElim proof' pos)

elaborateProof ctx (RPApp func arg) = do
  let pos = currentPos ctx
  func' <- elaborateProof ctx func
  arg' <- elaborateProof ctx arg
  Right (AppP func' arg' pos)

elaborateProof ctx (RPTyApp proof rtype) = do
  let pos = currentPos ctx
  proof' <- elaborateProof ctx proof
  rtype' <- elaborateRType ctx rtype
  Right (TyApp proof' rtype' pos)

-- Add other patterns as needed for ρ{, π, etc.

-- | Helper function to elaborate iota patterns from atomic tokens with specific arguments
elaborateIotaArgs :: ElaborateContext -> String -> RawProof -> RawProof -> Either ElaborateError Proof
elaborateIotaArgs ctx _tokenName t1 t2 = do
  let pos = currentPos ctx
  -- Convert proof variables to terms
  case (convertProofToTerm t1, convertProofToTerm t2) of
    (Just term1, Just term2) -> do
      t1' <- elaborateTerm ctx term1
      t2' <- elaborateTerm ctx term2
      Right (Iota t1' t2' pos)
    _ -> Left (UnknownProof "malformed iota pattern arguments")
  where
    -- Convert RawProof to RawTerm for simple variable cases
    convertProofToTerm :: RawProof -> Maybe RawTerm
    convertProofToTerm (RPVar name) = Just (RTVar name)
    convertProofToTerm _ = Nothing


-- | Desugar only syntactic mix-fix notation.
--   It *never* introduces RTMacro nodes – that is postponed to elaboration.
desugarMixfix :: MacroEnvironment -> RawTerm -> RawTerm
desugarMixfix env = go
  where
    hole = "_"

    go t = case t of
      RTApp a b       -> reassemble (flatten t)
      RTLam n b       -> RTLam n (go b)
      RTMacro n as    -> RTMacro n (map go as)   -- should appear only inside existing macros
      RawOp op        -> RTVar op               -- a naked operator token becomes a variable name
      _               -> t

    ----------------------------------------------------------------
    -- flatten a left-nested application into [t₀,t₁,…,tₙ]
    flatten (RTApp x y) = flatten x ++ [y]
    flatten term        = [term]

    ----------------------------------------------------------------
    -- Attempt to merge operator tokens into a single head.
    -- Never decides macro-ness; produces ordinary applications.
    reassemble terms =
      case splitOnOps terms of
        Nothing           -> foldl1 RTApp (map go terms)
        Just (atoms,lits) ->
          let opName = intercalate hole (hole : lits) ++ hole
              headApp = foldl RTApp (RTVar opName) (map go atoms)
          in headApp                             -- ← still plain Var as head

    ----------------------------------------------------------------
    -- Detect pattern  a RawOp b RawOp c ...
    splitOnOps (a:RawOp l:rest) =
      collect [a] [l] rest
      where
        collect accA accL (t:RawOp l2:ts) | not (isRawOp t) =
            collect (accA ++ [t]) (accL ++ [l2]) ts
        collect accA accL [t] | not (isRawOp t) =
            Just (accA ++ [t], accL)
        collect _ _ _ = Nothing
    splitOnOps _ = Nothing

    isRawOp (RawOp _) = True
    isRawOp _         = False
