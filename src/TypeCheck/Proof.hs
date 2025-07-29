module TypeCheck.Proof
  ( checkProof,
    inferProofType,
    ProofCheckResult (..),
    relJudgmentEqual,
    checkTheoremArgs,
    instantiateTheoremJudgment,
  )
where

import Core.Context
import qualified Data.Set as Set
import qualified Data.Map as Map
import Core.Errors
import Core.Syntax
import Operations.Generic.FreeVars (freeVars)
import Operations.Generic.Expansion (expandFully, ExpansionResult(..))
import Operations.Generic.BetaEta (betaEtaEquality)
import Operations.Generic.Equality (alphaEquality)
import Operations.Generic.Shift (shift, shiftWithBoundsCheck, shiftTermsInRType, shiftTermsInRTypeWithBoundsCheck, shiftTermExcept, shiftRTypeExcept, shiftFreeRelVars)
import Operations.Generic.Substitution (SubstAst(..), applyTheoremSubsToJudgment)
import Operations.Generic.Macro (elabMacroAppG)
import Operations.Generic.Expansion (expandWHNF)

-- | Result of proof checking
data ProofCheckResult = ProofCheckResult
  { resultJudgment :: RelJudgment,
    resultContext :: TypingContext
  }
  deriving (Show, Eq)

-- | Check if a proof has a given relational judgment in a context
checkProof :: TypingContext -> MacroEnvironment -> TheoremEnvironment -> Proof -> RelJudgment -> Either RelTTError ProofCheckResult
checkProof ctx macroEnv theoremEnv proof expectedJudgment = do
  result <- inferProofType ctx macroEnv theoremEnv proof
  let actualJudgment = resultJudgment result

  -- Check if the inferred judgment matches the expected one
  judgmentEqual <- relJudgmentEqual macroEnv actualJudgment expectedJudgment
  if judgmentEqual
    then return result
    else do
      -- Try to normalize both judgments for better error reporting
      normalizedForms <- case (normalizeJudgment macroEnv expectedJudgment, normalizeJudgment macroEnv actualJudgment) of
        (Right normExpected, Right normActual) ->
          if normExpected == expectedJudgment && normActual == actualJudgment
            then return Nothing -- No difference from original forms
            else return $ Just (normExpected, normActual)
        _ -> return Nothing -- Normalization failed, don't show normalized forms
      Left $ ProofTypingError proof expectedJudgment actualJudgment normalizedForms (ErrorContext (proofPos proof) "proof checking")

-- | Infer the relational judgment that a proof establishes
inferProofType :: TypingContext -> MacroEnvironment -> TheoremEnvironment -> Proof -> Either RelTTError ProofCheckResult
inferProofType ctx macroEnv theoremEnv proof = case proof of
  -- Variable rule: Γ ⊢ u : t[R]t' if u : t[R]t' ∈ Γ
  PVar name idx pos -> do
    -- Regular proof variable lookup
    (contextIdx, judgment) <- lookupProof name ctx
    if contextIdx == idx
      then return $ ProofCheckResult judgment ctx
      else Left $ InvalidDeBruijnIndex idx (ErrorContext pos "proof variable lookup")

  -- Theorem application rule: Γ ⊢ theorem_name args : instantiated_judgment
  PTheoremApp name args pos -> do
    -- Look up theorem in environment
    (bindings, judgment, _) <- lookupTheorem name theoremEnv

    -- Check that argument count doesn't exceed binding count
    let bindingCount = length bindings
        argCount = length args
    if argCount > bindingCount
      then Left $ InternalError ("Too many arguments for theorem " ++ name ++ ": expected " ++ show bindingCount ++ ", got " ++ show argCount) (ErrorContext pos "theorem application")
      else do
        -- Type check each argument against its expected binding type
        validatedArgs <- checkTheoremArgs bindings args ctx macroEnv theoremEnv pos

        -- Apply substitutions to get the instantiated judgment
        instantiatedJudgment <- instantiateTheoremJudgment bindings validatedArgs judgment

        return $ ProofCheckResult instantiatedJudgment ctx

  -- \| Λ-introduction for proofs
  LamP proofVar rtype body pos -> do
    ---------------------------------------------------------
    -- 1. generate two fresh witness names
    let (x, x', ctx1) = freshVarPair "x" "x'" ctx

        witnessLeft = Var x 0 pos -- index 0 now, becomes 1 after λ-wrap
        witnessRight = Var x' 0 pos -- index 0 on right side

        -- proof binding q : x [R] x'
        proofJudg = RelJudgment witnessLeft rtype witnessRight

        -- 2. extend context with that single proof entry
        ctx2 = extendProofContext proofVar proofJudg ctx1
    ---------------------------------------------------------
    -- 3. infer body under Γ, q
    ProofCheckResult {resultJudgment = RelJudgment t1 r' t2} <-
      inferProofType ctx2 macroEnv theoremEnv body

    -- 4. lift every *other* free variable by 1; the two freshly created
    --    witnesses (x, x') themselves must stay where they are.
    let prot = Set.fromList [x, x']
        t1Shift = shiftTermExcept prot 1 t1
        t2Shift = shiftTermExcept prot 1 t2
        r'Shift = shiftRTypeExcept prot 1 r'

        -- 5. wrap each side with its witness-λ
        termLeft = Lam x t1Shift pos
        termRight = Lam x' t2Shift pos
        resultTy = Arr rtype r'Shift pos
        finalJudg = RelJudgment termLeft resultTy termRight

    return $ ProofCheckResult finalJudg ctx1

  -- Application: Γ ⊢ p₁ p₂ : t₁ t₂[R']t₁' t₂'
  AppP proof1 proof2 pos -> do
    result1 <- inferProofType ctx macroEnv theoremEnv proof1
    result2 <- inferProofType ctx macroEnv theoremEnv proof2

    let RelJudgment term1 rtype1 term1' = resultJudgment result1
        RelJudgment term2 rtype2 term2' = resultJudgment result2

    case rtype1 of
      Arr argType resultType _ -> do
        -- Check that argument type matches
        let typesEqual = alphaEquality macroEnv argType rtype2
        if typesEqual
          then do
            let resultTerm1 = App term1 term2 pos
                resultTerm2 = App term1' term2' pos
                finalJudgment = RelJudgment resultTerm1 resultType resultTerm2
            return $ ProofCheckResult finalJudgment ctx
          else Left $ TypeMismatch argType rtype2 (ErrorContext pos "proof application")
      _ -> Left $ InvalidTypeApplication rtype1 (ErrorContext pos "proof application")

  -- Type application: Γ ⊢ p { R } : t[[R/X]R']t'
  TyApp proof1 rtype pos -> do
    result1 <- inferProofType ctx macroEnv theoremEnv proof1
    let RelJudgment term1 rtype1 term1' = resultJudgment result1

    -- Expand macros in the type before checking if it's universally quantified
    expandResult <- expandWHNF macroEnv rtype1
    let expandedRType = expandedValue expandResult

    case expandedRType of
      All varName bodyType _ -> do
        let substitutedType = substIndex 0 rtype bodyType
            finalJudgment = RelJudgment term1 substitutedType term1'
        return $ ProofCheckResult finalJudgment ctx
      _ -> Left $ InvalidTypeApplication rtype1 (ErrorContext pos "type application")

  -- Type lambda: Γ ⊢ Λx .p : t[∀x . R]t'
  TyLam varName body pos -> do
    -- Check freshness condition
    if isFreshInContext varName ctx
      then do
        -- Extend context with relation variable
        let extendedCtx = extendRelContext varName ctx
        result <- inferProofType extendedCtx macroEnv theoremEnv body
        let RelJudgment term1 rtype term2 = resultJudgment result
            -- Shift free relation variables by +1, except the bound variable
            shiftedRType = shiftFreeRelVars varName 1 rtype
            quantifiedType = All varName shiftedRType pos
            finalJudgment = RelJudgment term1 quantifiedType term2
        return $ ProofCheckResult finalJudgment ctx
      else Left $ DuplicateBinding varName (ErrorContext pos "type lambda")

  -- Conversion: Γ ⊢ t₁' ⇃ p ⇂ t₂' : t₁'[R]t₂'
  ConvProof term1' proof1 term2' pos -> do
    result <- inferProofType ctx macroEnv theoremEnv proof1
    let RelJudgment term1 rtype term2 = resultJudgment result

    -- Check β-η equivalence with macro expansion
    equiv1 <- betaEtaEquality macroEnv term1 term1'
    equiv2 <- betaEtaEquality macroEnv term2 term2'

    case (equiv1, equiv2) of
      (True, True) -> do
        let finalJudgment = RelJudgment term1' rtype term2'
        return $ ProofCheckResult finalJudgment ctx
      (False, _) -> Left $ LeftConversionError term1 term1' (ErrorContext pos "left conversion")
      (_, False) -> Left $ RightConversionError term2 term2' (ErrorContext pos "right conversion")

  -- Converse introduction: Γ ⊢ ∪ᵢ p : t'[R^∪]t
  ConvIntro proof1 pos -> do
    result <- inferProofType ctx macroEnv theoremEnv proof1
    let RelJudgment term1 rtype term2 = resultJudgment result
        converseType = Conv rtype pos
        finalJudgment = RelJudgment term2 converseType term1
    return $ ProofCheckResult finalJudgment ctx

  -- Converse elimination: Γ ⊢ ∪ₑ p : t'[R]t
  ConvElim proof1 pos -> do
    result <- inferProofType ctx macroEnv theoremEnv proof1
    let RelJudgment term1 rtype term2 = resultJudgment result

    case rtype of
      Conv innerType _ -> do
        let finalJudgment = RelJudgment term2 innerType term1
        return $ ProofCheckResult finalJudgment ctx
      _ -> Left $ ConverseError proof1 (RelJudgment term1 rtype term2) (ErrorContext pos "converse elimination")

  -- Iota (term promotion introduction): Γ ⊢ ι{t,t'} : t[t'](t' t)
  Iota term1 term2 pos -> do
    let promotedType = Prom term2 pos
        resultTerm2 = App term2 term1 pos
        finalJudgment = RelJudgment term1 promotedType resultTerm2
    return $ ProofCheckResult finalJudgment ctx

  -- Rho elimination: ρ{ x .t₁,t₂} p - p' : [t'/x]t₁[R][t'/x]t₂
  -- Paper rule: Γ ⊢ p : t[t'']t', Γ ⊢ p' : [t'' t/x]t₁[R][t'' t/x]t₂
  --             ⊢ ρ{ x .t₁,t₂} p - p' : [t'/x]t₁[R][t'/x]t₂
  RhoElim varName term1 term2 proof1 proof2 pos -> do
    -- Check first proof: p : t[t'']t'
    result1 <- inferProofType ctx macroEnv theoremEnv proof1
    let RelJudgment proofTerm1 proofType proofTerm2 = resultJudgment result1

    case proofType of
      Prom promotedTerm _ -> do
        -- From the first proof, we have: t[t'']t' where t'' = promotedTerm, t = proofTerm1, t' = proofTerm2
        -- We need to check that proof2 has type: [t'' t/x]t₁[R][t'' t/x]t₂
        let substitutedApp = App promotedTerm proofTerm1 pos -- t'' t
            expectedSubstTerm1 = substIndex 0 substitutedApp term1 -- [t'' t/0]t₁
            expectedSubstTerm2 = substIndex 0 substitutedApp term2 -- [t'' t/0]t₂

        -- Check second proof
        result2 <- inferProofType ctx macroEnv theoremEnv proof2
        let RelJudgment actualTerm1 actualRType actualTerm2 = resultJudgment result2

        -- Verify the second proof has the expected type (use syntactic equality)
        let termEq1 = alphaEquality macroEnv actualTerm1 expectedSubstTerm1
            termEq2 = alphaEquality macroEnv actualTerm2 expectedSubstTerm2
        case (termEq1, termEq2) of
          (True, True) -> do
            -- Return the final judgment: [t'/0]t₁[R][t'/0]t₂
            let resultSubstTerm1 = substIndex 0 proofTerm2 term1 -- [t'/0]t₁
                resultSubstTerm2 = substIndex 0 proofTerm2 term2 -- [t'/0]t₂
                finalJudgment = RelJudgment resultSubstTerm1 actualRType resultSubstTerm2
            return $ ProofCheckResult finalJudgment ctx
          _ ->
            let expectedJudgment = RelJudgment expectedSubstTerm1 actualRType expectedSubstTerm2
                actualJudgment = RelJudgment actualTerm1 actualRType actualTerm2
             in Left $ RhoEliminationTypeMismatchError proof2 expectedJudgment actualJudgment (ErrorContext pos "rho elimination: second proof type mismatch")
      _ -> Left $ RhoEliminationNonPromotedError proof1 (RelJudgment proofTerm1 proofType proofTerm2) (ErrorContext pos "rho elimination: first proof must have promoted type")

  -- Composition introduction: Γ ⊢ (p,p') : t[R∘R']t'
  Pair proof1 proof2 pos -> do
    result1 <- inferProofType ctx macroEnv theoremEnv proof1
    result2 <- inferProofType ctx macroEnv theoremEnv proof2

    let RelJudgment term1 rtype1 termMiddle = resultJudgment result1
        RelJudgment termMiddle' rtype2 term2 = resultJudgment result2

    -- Check that the middle terms are equal (use syntactic equality)
    let termsEqual = alphaEquality macroEnv termMiddle termMiddle'
    if termsEqual
      then do
        let compositionType = Comp rtype1 rtype2 pos
            finalJudgment = RelJudgment term1 compositionType term2
        return $ ProofCheckResult finalJudgment ctx
      else Left $ CompositionError proof1 proof2 termMiddle termMiddle' (ErrorContext pos "composition introduction")

  -- Pi elimination: Γ ⊢ π p - x . u . v .p' : t₁[R'']t₂
  -- Paper rule: Γ ⊢ p : t[R∘R']t', Γ, u : t[R]x, v : x[R']t' ⊢ p' : t₁[R'']t₂
  --             ⊢ π p - x . u . v .p' : t₁[R'']t₂
  Pi proof1 varX varU varV proof2 pos -> do
    result1 <- inferProofType ctx macroEnv theoremEnv proof1
    let RelJudgment term1 rtype term2 = resultJudgment result1

    case rtype of
      Comp rtype1 rtype2 _ -> do
        -- Side condition (**): x ∉ FV(Γ, t₁, t₂, t, t', R, R', R'')
        let contextFreeVars = boundVarsInContext ctx
            term1FreeVars = freeVars macroEnv term1
            term2FreeVars = freeVars macroEnv term2
            rtype1FreeVars = freeVars macroEnv rtype1
            rtype2FreeVars = freeVars macroEnv rtype2
            allFreeVars = Set.unions [contextFreeVars, term1FreeVars, term2FreeVars, rtype1FreeVars, rtype2FreeVars]

        if Set.member varX allFreeVars
          then
            Left $
              InvalidContext
                ("Pi elimination variable " ++ varX ++ " violates side condition (**): appears in free variables of context, terms, or types")
                (ErrorContext pos "pi elimination side condition")
          else do
            -- Create fresh witness term for x
            -- x should be a fresh term variable - we'll use index 0 and extend contexts appropriately
            let witnessTerm = Var varX 0 pos -- Fresh variable x
            -- Shift existing terms and types up by 1 for the new term variable
                term1Shifted = shift 1 term1
                term2Shifted = shift 1 term2
                rtype1Shifted = shiftTermsInRType 1 rtype1
                rtype2Shifted = shiftTermsInRType 1 rtype2
                -- Extend context with term binding for x first
                ctxWithX = extendTermContext varX (RMacro "Witness" [] pos) ctx
                -- Create witness judgments: u : t[R]x, v : x[R']t'
                witnessJudgment1 = RelJudgment term1Shifted rtype1Shifted witnessTerm
                witnessJudgment2 = RelJudgment witnessTerm rtype2Shifted term2Shifted
                -- Extend context with proof bindings u and v
                ctx1 = extendProofContext varU witnessJudgment1 ctxWithX
                ctx2 = extendProofContext varV witnessJudgment2 ctx1

            -- Check proof2 in extended context
            result2 <- inferProofType ctx2 macroEnv theoremEnv proof2
            -- The lookup already handles shifting, so bounds check the result as-is
            let RelJudgment resultTerm1 resultRType resultTerm2 = resultJudgment result2
            case ( shiftWithBoundsCheck (-1) resultTerm1,
                   shiftWithBoundsCheck (-1) resultTerm2,
                   shiftTermsInRTypeWithBoundsCheck (-1) resultRType
                 ) of
              (Just shiftedTerm1, Just shiftedTerm2, Just shiftedRType) -> do
                let finalJudgment = RelJudgment shiftedTerm1 shiftedRType shiftedTerm2
                return $ ProofCheckResult finalJudgment ctx
              _ ->
                Left $
                  InvalidContext
                    "Pi elimination result references bound variables (x, u, or v)"
                    (ErrorContext pos "pi elimination bounds check")
      _ -> Left $ CompositionError proof1 proof1 term1 term2 (ErrorContext pos "pi elimination: first proof must have composition type")

  -- PMacro case - expand and recurse
  PMacro name args pos -> do
    case Map.lookup name (macroDefinitions macroEnv) of
      Nothing -> Left $ UnknownMacro name (ErrorContext pos "proof macro lookup")
      Just (sig, ProofMacro body) -> 
        case elabMacroAppG macroEnv name sig body [p | MProof p <- args] of
          Right expandedProof -> inferProofType ctx macroEnv theoremEnv expandedProof
          Left err -> Left $ InternalError ("Proof macro expansion failed: " ++ show err) (ErrorContext pos "proof macro expansion")
      Just (_, TermMacro _) -> Left $ InvalidMixfixPattern ("Term macro " ++ name ++ " used in proof context") (ErrorContext pos "proof macro application")
      Just (_, RelMacro _) -> Left $ InvalidMixfixPattern ("Relational macro " ++ name ++ " used in proof context") (ErrorContext pos "proof macro application")

-- Helper functions

-- | Normalize a judgment by expanding macros in terms and types (NO BETA-ETA)
normalizeJudgment :: MacroEnvironment -> RelJudgment -> Either RelTTError RelJudgment
normalizeJudgment macroEnv (RelJudgment t1 rtype t2) = do
  -- Only expand macros, do NOT do beta-eta normalization
  termResult1 <- expandFully macroEnv t1
  termResult2 <- expandFully macroEnv t2
  expandResult <- expandWHNF macroEnv rtype
  return $ RelJudgment (expandedValue termResult1) (expandedValue expandResult) (expandedValue termResult2)

-- | Check equality of relational judgments
-- NOTE: Relational judgments must be syntactically equal, not β-η equivalent
-- This is crucial for type safety - x [R] y and (λ z . z) x [R] y are different judgments
relJudgmentEqual :: MacroEnvironment -> RelJudgment -> RelJudgment -> Either RelTTError Bool
relJudgmentEqual macroEnv (RelJudgment t1 r1 t1') (RelJudgment t2 r2 t2') = do
  -- Use syntactic equality (alpha equivalence) for terms, not β-η equivalence
  let termEq1 = alphaEquality macroEnv t1 t2
      termEq2 = alphaEquality macroEnv t1' t2'
  let typeEq = alphaEquality macroEnv r1 r2
  return $ termEq1 && termEq2 && typeEq

-- | Sequentially check theorem arguments, carrying the substitution that has
--   already been established by earlier (term/rel/proof) arguments.
checkTheoremArgs :: [Binding] -> [TheoremArg] -> TypingContext -> MacroEnvironment -> TheoremEnvironment -> SourcePos -> Either RelTTError [TheoremArg]
checkTheoremArgs bindings args ctx macroEnv theoremEnv pos =
  go [] [] (zip bindings args)
  where
    -- accSubs : substitutions established so far (left‑to‑right)
    -- accArgs : validated args in the same order as given
    go accSubs accArgs [] = return (reverse accArgs)
    go accSubs accArgs ((bind, arg) : rest) = case (bind, arg) of
      (TermBinding _, TermArg _) ->
        go (accSubs ++ [(bind, arg)]) (arg : accArgs) rest
      (RelBinding _, RelArg _) ->
        go (accSubs ++ [(bind, arg)]) (arg : accArgs) rest
      (ProofBinding _ templJudg, ProofArg p) -> do
        -- instantiate the template with what we already know
        instTempl <- applyTheoremSubsToJudgment accSubs templJudg

        -- infer and compare
        ProofCheckResult {resultJudgment = actualJudg} <-
          inferProofType ctx macroEnv theoremEnv p
        equal <- relJudgmentEqual macroEnv instTempl actualJudg
        if equal
          then go (accSubs ++ [(bind, arg)]) (arg : accArgs) rest
          else
            Left $
              ProofTypingError
                p
                instTempl
                actualJudg
                Nothing
                (ErrorContext pos "theorem argument proof type mismatch")
      _ ->
        Left $
          InternalError
            "Theorem argument type mismatch"
            (ErrorContext pos "theorem argument validation")

-- | Instantiate a theorem judgment by applying argument substitutions
instantiateTheoremJudgment :: [Binding] -> [TheoremArg] -> RelJudgment -> Either RelTTError RelJudgment
instantiateTheoremJudgment bindings args judgment = do
  let substitutions = zip bindings args
  applyTheoremSubsToJudgment substitutions judgment

