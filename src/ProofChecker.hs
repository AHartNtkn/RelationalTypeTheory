module ProofChecker
  ( checkProof,
    inferProofType,
    ProofCheckResult (..),
    relJudgmentEqual,
    substituteTermVar,
  )
where

import Context
import qualified Data.Set as Set
import Errors
import Lib
import Normalize (shiftTerm, shiftTermWithBoundsCheck, termEquality, termEqualityAlpha)
import TypeOps (shiftTermsInRType, shiftTermsInRTypeWithBoundsCheck, substituteTypeVar, typeEquality)

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
    else Left $ ProofTypingError proof expectedJudgment actualJudgment (ErrorContext (proofPos proof) "proof checking")

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

  -- Theorem reference rule: Γ ⊢ theorem_name : theorem_judgment
  PTheorem name _ -> do
    -- Theorem reference - look up in theorem environment
    (_, judgment, _) <- lookupTheorem name theoremEnv
    -- For now, return the theorem's judgment directly
    -- TODO: Handle theorem instantiation with bindings
    return $ ProofCheckResult judgment ctx

  -- Lambda introduction: Γ ⊢ λu:T.p : λx.t[R→R']λx'.t'
  LamP proofVar rtype body pos -> do
    -- Lambda rule: Γ, q : x [R] x' ⊢ p : t [R'] t'  (*)
    --              =====================================
    --              Γ ⊢ λq:R.p : λx.t [R → R'] λx'.t'

    -- Create fresh lambda variable names (not related to proof parameter name)
    let varName = "x"
        varName' = "x'"
        -- Create judgment using fresh variable names: x [R] x'
        proofJudgment = RelJudgment (Var varName 0 pos) rtype (Var varName' 0 pos)
        -- Extend context with proof variable q
        extendedCtx = extendProofContext proofVar proofJudgment ctx

    -- Check the body p in the extended context
    bodyResult <- inferProofType extendedCtx macroEnv theoremEnv body
    let RelJudgment bodyTerm1 bodyRType bodyTerm2 = resultJudgment bodyResult

    -- Shift the body terms by +1 for the lambda abstraction
    let shiftedBodyTerm1 = shiftTerm 1 bodyTerm1
        shiftedBodyTerm2 = shiftTerm 1 bodyTerm2

    -- Form the result: λx.t [R → R'] λx'.t'
    let resultRType = Arr rtype bodyRType pos
        resultTerm1 = Lam varName shiftedBodyTerm1 pos
        resultTerm2 = Lam varName' shiftedBodyTerm2 pos
        finalJudgment = RelJudgment resultTerm1 resultRType resultTerm2

    return $ ProofCheckResult finalJudgment ctx

  -- Application: Γ ⊢ p₁ p₂ : t₁ t₂[R']t₁' t₂'
  AppP proof1 proof2 pos -> do
    result1 <- inferProofType ctx macroEnv theoremEnv proof1
    result2 <- inferProofType ctx macroEnv theoremEnv proof2

    let RelJudgment term1 rtype1 term1' = resultJudgment result1
        RelJudgment term2 rtype2 term2' = resultJudgment result2

    case rtype1 of
      Arr argType resultType _ -> do
        -- Check that argument type matches
        typesEqual <- typeEquality macroEnv argType rtype2
        if typesEqual
          then do
            let resultTerm1 = App term1 term2 pos
                resultTerm2 = App term1' term2' pos
                finalJudgment = RelJudgment resultTerm1 resultType resultTerm2
            return $ ProofCheckResult finalJudgment ctx
          else Left $ TypeMismatch argType rtype2 (ErrorContext pos "proof application")
      _ -> Left $ InvalidTypeApplication rtype1 (ErrorContext pos "proof application")

  -- Type application: Γ ⊢ p{R} : t[[R/X]R']t'
  TyApp proof1 rtype pos -> do
    result1 <- inferProofType ctx macroEnv theoremEnv proof1
    let RelJudgment term1 rtype1 term1' = resultJudgment result1

    case rtype1 of
      All varName bodyType _ -> do
        let substitutedType = substituteTypeVar varName rtype bodyType
            finalJudgment = RelJudgment term1 substitutedType term1'
        return $ ProofCheckResult finalJudgment ctx
      _ -> Left $ InvalidTypeApplication rtype1 (ErrorContext pos "type application")

  -- Type lambda: Γ ⊢ Λx.p : t[∀x.R]t'
  TyLam varName body pos -> do
    -- Check freshness condition
    if isFreshInContext varName ctx
      then do
        -- Extend context with relation variable
        let extendedCtx = extendRelContext varName ctx
        result <- inferProofType extendedCtx macroEnv theoremEnv body
        let RelJudgment term1 rtype term2 = resultJudgment result
            quantifiedType = All varName rtype pos
            finalJudgment = RelJudgment term1 quantifiedType term2
        return $ ProofCheckResult finalJudgment ctx
      else Left $ DuplicateBinding varName (ErrorContext pos "type lambda")

  -- Conversion: Γ ⊢ t₁' ⇃ p ⇂ t₂' : t₁'[R]t₂'
  ConvProof term1' proof1 term2' pos -> do
    result <- inferProofType ctx macroEnv theoremEnv proof1
    let RelJudgment term1 rtype term2 = resultJudgment result

    -- Check β-η equivalence with macro expansion
    equiv1 <- termEquality macroEnv term1 term1'
    equiv2 <- termEquality macroEnv term2 term2'

    if equiv1 && equiv2
      then do
        let finalJudgment = RelJudgment term1' rtype term2'
        return $ ProofCheckResult finalJudgment ctx
      else Left $ TermConversionError term1 term1' term2 term2' (ErrorContext pos "conversion")

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

  -- Rho elimination: ρ{x.t₁,t₂} p - p' : [t'/x]t₁[R][t'/x]t₂
  -- Paper rule: Γ ⊢ p : t[t'']t', Γ ⊢ p' : [t'' t/x]t₁[R][t'' t/x]t₂
  --             ⊢ ρ{x.t₁,t₂} p - p' : [t'/x]t₁[R][t'/x]t₂
  RhoElim varName term1 term2 proof1 proof2 pos -> do
    -- Check first proof: p : t[t'']t'
    result1 <- inferProofType ctx macroEnv theoremEnv proof1
    let RelJudgment proofTerm1 proofType proofTerm2 = resultJudgment result1

    case proofType of
      Prom promotedTerm _ -> do
        -- From the first proof, we have: t[t'']t' where t'' = promotedTerm, t = proofTerm1, t' = proofTerm2
        -- We need to check that proof2 has type: [t'' t/x]t₁[R][t'' t/x]t₂
        let substitutedApp = App promotedTerm proofTerm1 pos -- t'' t
            expectedSubstTerm1 = substituteTermVar varName substitutedApp term1 -- [t'' t/x]t₁
            expectedSubstTerm2 = substituteTermVar varName substitutedApp term2 -- [t'' t/x]t₂

        -- Check second proof
        result2 <- inferProofType ctx macroEnv theoremEnv proof2
        let RelJudgment actualTerm1 actualRType actualTerm2 = resultJudgment result2

        -- Verify the second proof has the expected type (use syntactic equality)
        case (termEqualityAlpha actualTerm1 expectedSubstTerm1, termEqualityAlpha actualTerm2 expectedSubstTerm2) of
          (True, True) -> do
            -- Return the final judgment: [t'/x]t₁[R][t'/x]t₂
            let resultSubstTerm1 = substituteTermVar varName proofTerm2 term1 -- [t'/x]t₁
                resultSubstTerm2 = substituteTermVar varName proofTerm2 term2 -- [t'/x]t₂
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
    let termsEqual = termEqualityAlpha termMiddle termMiddle'
    if termsEqual
      then do
        let compositionType = Comp rtype1 rtype2 pos
            finalJudgment = RelJudgment term1 compositionType term2
        return $ ProofCheckResult finalJudgment ctx
      else Left $ CompositionError proof1 proof2 termMiddle termMiddle' (ErrorContext pos "composition introduction")

  -- Pi elimination: Γ ⊢ π p - x.u.v.p' : t₁[R'']t₂
  -- Paper rule: Γ ⊢ p : t[R∘R']t', Γ, u : t[R]x, v : x[R']t' ⊢ p' : t₁[R'']t₂
  --             ⊢ π p - x.u.v.p' : t₁[R'']t₂
  Pi proof1 varX varU varV proof2 pos -> do
    result1 <- inferProofType ctx macroEnv theoremEnv proof1
    let RelJudgment term1 rtype term2 = resultJudgment result1

    case rtype of
      Comp rtype1 rtype2 _ -> do
        -- Side condition (**): x ∉ FV(Γ, t₁, t₂, t, t', R, R', R'')
        let contextFreeVars = freeVarsInContext ctx
            term1FreeVars = freeVarsInTerm term1
            term2FreeVars = freeVarsInTerm term2
            rtype1FreeVars = freeVarsInRType rtype1
            rtype2FreeVars = freeVarsInRType rtype2
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
                term1Shifted = shiftTerm 1 term1
                term2Shifted = shiftTerm 1 term2
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
            case ( shiftTermWithBoundsCheck (-1) resultTerm1,
                   shiftTermWithBoundsCheck (-1) resultTerm2,
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

-- Helper functions

-- | Check equality of relational judgments
-- NOTE: Relational judgments must be syntactically equal, not β-η equivalent
-- This is crucial for type safety - x [R] y and (λz.z) x [R] y are different judgments
relJudgmentEqual :: MacroEnvironment -> RelJudgment -> RelJudgment -> Either RelTTError Bool
relJudgmentEqual macroEnv (RelJudgment t1 r1 t1') (RelJudgment t2 r2 t2') = do
  -- Use syntactic equality (alpha equivalence) for terms, not β-η equivalence
  let termEq1 = termEqualityAlpha t1 t2
      termEq2 = termEqualityAlpha t1' t2'
  typeEq <- typeEquality macroEnv r1 r2
  return $ termEq1 && termEq2 && typeEq

-- | Substitute a term for a variable in another term
substituteTermVar :: String -> Term -> Term -> Term
substituteTermVar var replacement term = case term of
  Var name _ _ | name == var -> replacement
  Var _ _ _ -> term
  Lam name _ _ | name == var -> term -- Variable is shadowed
  Lam name body pos -> Lam name (substituteTermVar var replacement body) pos
  App t1 t2 pos -> App (substituteTermVar var replacement t1) (substituteTermVar var replacement t2) pos
  TMacro name args pos -> TMacro name (map (substituteTermVar var replacement) args) pos
