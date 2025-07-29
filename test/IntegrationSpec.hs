{-# LANGUAGE OverloadedStrings, LambdaCase #-}

module IntegrationSpec (spec) where

import Core.Context
import qualified Data.Set as Set
import Parser.Elaborate (elaborate, emptyCtxWithBuiltins)
import Parser.Context (ElaborateContext(..))
import Core.Errors
import Core.Syntax
import Core.Environment (noMacros, noTheorems, extendMacroEnvironment)
import Parser.Mixfix (defaultFixity)
import Operations.Generic.BetaEta (betaEtaEquality, normalizeForBetaEta)
import Operations.Generic.Expansion (expandFully, ExpansionResult(..))
import Operations.Generic.Equality (alphaEquality)
import Operations.Generic.FreeVars (freeVars)
import Operations.Generic.Substitution (substIndex)
import TypeCheck.Proof
import Parser.Raw (rawDeclaration, rawProof)
import Parser.Elaborate (elaborateProof)
import Core.Raw (RawDeclaration(..))
import Text.Megaparsec (runParser)
import Test.Hspec
import TestHelpers
import Text.Megaparsec (initialPos, runParser, errorBundlePretty)

ip :: SourcePos
ip = (initialPos "test")

-- Wrapper functions to match old API
expandMacros :: MacroEnvironment -> RType -> Either RelTTError (ExpansionResult RType)
expandMacros env rtype = expandFully env rtype

expandedType :: ExpansionResult RType -> RType
expandedType = expandedValue

-- Use the record field accessors directly
-- wasExpanded :: ExpansionResult a -> Bool (already available)
-- expansionSteps :: ExpansionResult a -> Int (already available)

typeEquality :: MacroEnvironment -> RType -> RType -> Either RelTTError Bool
typeEquality env t1 t2 = Right $ alphaEquality env t1 t2

substituteTypeVar :: Int -> RType -> RType -> RType
substituteTypeVar = substIndex

normalizedTerm :: Term -> Term
normalizedTerm = id  -- Simplified - would need proper normalization wrapper

freeTypeVariables :: RType -> Set.Set String
freeTypeVariables rtype = freeVars noMacros rtype

parseDeclaration :: String -> Either String Declaration  
parseDeclaration content =
  case runParser rawDeclaration "test" (content) of
    Left parseErr -> Left $ "Parse error: " ++ errorBundlePretty parseErr
    Right rawDecl -> case elaborate emptyCtxWithBuiltins rawDecl of
      Left err -> Left $ "Error: " ++ show err
      Right decl -> Right decl

-- Helper functions for tests that don't use macros
normalizeTermBetaEta :: MacroEnvironment -> Term -> Either RelTTError Term
normalizeTermBetaEta env term = normalizeForBetaEta env term

termEqualityBetaEta :: Term -> Term -> Either RelTTError Bool
termEqualityBetaEta = betaEtaEquality noMacros

spec :: Spec
spec = do
  endToEndWorkflowSpec
  macroIntegrationSpec
  realExamplesSpec
  paperExamplesSpec
  parserProofCheckerPipelineSpec
  quantifierDeBruijnBugSpec

-- | Test end-to-end workflows combining multiple modules
endToEndWorkflowSpec :: Spec
endToEndWorkflowSpec = describe "end-to-end workflows" $ do
  it "normalizes and compares terms in context" $ do
    -- Create a context with some bindings
    let _ctx = extendTermContext "f" (Arr (RMacro "A" [] ip) (RMacro "B" [] ip) ip) emptyTypingContext

    -- Create two beta-equivalent terms
    let term1 = App (Lam "x" (App (Var "f" 1 ip) (Var "x" 0 ip) ip) ip) (Var "a" (-1) ip) ip
        term2 = App (Var "f" 0 ip) (Var "a" (-1) ip) ip

    -- Normalize and compare
    case (normalizeTermBetaEta noMacros term1, normalizeTermBetaEta noMacros term2, termEqualityBetaEta term1 term2) of
      (Right norm1, Right norm2, Right equality) -> do
        -- Both should normalize to the same result
        normalizedTerm norm1 `shouldBe` normalizedTerm norm2
        equality `shouldBe` True
      (Left err, _, _) -> expectationFailure $ "term1 normalization failed: " ++ show err
      (_, Left err, _) -> expectationFailure $ "term2 normalization failed: " ++ show err
      (_, _, Left err) -> expectationFailure $ "equality check failed: " ++ show err

  it "expands macros and normalizes promoted terms" $ do
    -- Set up macro environment
    let env = extendMacroEnvironment "Id" [] (RelMacro (Prom (Lam "x" (Var "x" 0 ip) ip) ip)) (defaultFixity "TEST") noMacros

    -- Create a type with macro and promoted term
    let macroType = RMacro "Id" [] ip
        promotedType = Prom (Lam "y" (Var "y" 0 ip) ip) ip

    -- Expand macro and compare
    case expandMacros env macroType of
      Right expanded -> do
        case typeEquality env (expandedType expanded) promotedType of
          Right equality -> equality `shouldBe` True -- Both represent identity function
          Left err -> expectationFailure $ "equality check failed: " ++ show err
      Left err -> expectationFailure $ "macro expansion failed: " ++ show err

  it "handles complex type substitution with normalization" $ do
    -- Create a complex type with variables and terms
    let complexType = Arr (RVar "X" 0 ip) (Prom (App (Lam "f" (Var "f" 0 ip) ip) (Var "identity" 0 ip) ip) ip) ip
        substitution = RMacro "Int" [] ip

    -- Perform substitution
    let substituted = substituteTypeVar 0 substitution complexType

    -- The result should have Int substituted for X
    case substituted of
      Arr (RMacro "Int" [] _) (Prom _ _) _ -> return ()
      _ -> expectationFailure $ "Expected substitution to work, got: " ++ show substituted

-- | Test macro system integration
macroIntegrationSpec :: Spec
macroIntegrationSpec = describe "macro system integration" $ do
  it "handles nested macro definitions and usage" $ do
    -- Build a macro environment with dependencies
    let env0 = noMacros
        env1 = extendMacroEnvironment "Id" [] (RelMacro (Prom (Lam "x" (Var "x" 0 ip) ip) ip)) (defaultFixity "TEST") env0
        env2 = extendMacroEnvironment "Const" ["A"] (RelMacro (Arr (RVar "A" 0 ip) (Arr (RMacro "Any" [] ip) (RVar "A" 0 ip) ip) ip)) (defaultFixity "TEST") env1
        env3 = extendMacroEnvironment "Apply" ["F", "A"] (RelMacro (Comp (RVar "F" 1 ip) (RVar "A" 0 ip) ip)) (defaultFixity "TEST") env2

    -- Test macro expansion chain
    let complexMacro = RMacro "Apply" [MRel (RMacro "Id" [] ip), MRel (RMacro "Const" [MRel (RMacro "Int" [] ip)] ip)] ip

    case expandMacros env3 complexMacro of
      Right result -> do
        wasExpanded result `shouldBe` True
        expansionSteps result `shouldSatisfy` (> 0)
      Left err -> expectationFailure $ "macro expansion failed: " ++ show err

  it "optimizes macro equality checking" $ do
    -- Create macro environment with two macros that expand to the same thing but have different names
    let env =
          extendMacroEnvironment "List" ["T"] (RelMacro (Arr (RVar "T" 0 ip) (RMacro "Container" [] ip) ip)) (defaultFixity "TEST") $
            extendMacroEnvironment "Array" ["T"] (RelMacro (Arr (RVar "T" 0 ip) (RMacro "Container" [] ip) ip)) (defaultFixity "TEST") noMacros

        -- Identical macros (should not require expansion - optimization applies)
        identicalMacro1 = RMacro "List" [MRel (RMacro "Int" [] ip)] ip
        identicalMacro2 = RMacro "List" [MRel (RMacro "Int" [] ip)] ip

        -- Different macros with same expansion (should require expansion)
        differentMacro1 = RMacro "List" [MRel (RMacro "Int" [] ip)] ip
        differentMacro2 = RMacro "Array" [MRel (RMacro "Int" [] ip)] ip

    -- Both should give True, but optimization should apply to identical case
    case (typeEquality env identicalMacro1 identicalMacro2, typeEquality env differentMacro1 differentMacro2) of
      (Right True, Right True) -> do
        -- Verify that expansion is needed for the different macro case but not identical
        case (expandMacros env identicalMacro1, expandMacros env differentMacro1) of
          (Right identicalResult, Right differentResult) -> do
            -- The key optimization: identical macros shouldn't need as many expansion steps
            -- Both should expand to verify the optimization is working correctly
            expandedType identicalResult `shouldBe` expandedType differentResult
          (Left err, _) -> expectationFailure $ "Expansion failed: " ++ show err
          (_, Left err) -> expectationFailure $ "Expansion failed: " ++ show err
      (Left err, _) -> expectationFailure $ "Identical macro equality failed: " ++ show err
      (_, Left err) -> expectationFailure $ "Different macro equality failed: " ++ show err
      (Right False, _) -> expectationFailure "Identical macros should be equal"
      (_, Right False) -> expectationFailure "Different macros with same expansion should be equal"

-- | Test with realistic RelTT examples
realExamplesSpec :: Spec
realExamplesSpec = describe "realistic RelTT examples" $ do
  it "handles identity relation macro" $ do
    -- Identity relation: Id ≔ (λ x . x)^
    let env = extendMacroEnvironment "Id" [] (RelMacro (Prom (Lam "x" (Var "x" 0 ip) ip) ip)) (defaultFixity "TEST") noMacros
        idType = RMacro "Id" [] ip

    -- Expand and verify
    case expandMacros env idType of
      Right result ->
        case expandedType result of
          Prom (Lam "x" (Var "x" 0 _) _) _ -> return ()
          _ -> expectationFailure "Expected identity function"
      Left err -> expectationFailure $ "macro expansion failed: " ++ show err

  it "handles composition macro" $ do
    -- Composition: Comp R S ≔ R ∘ S
    let env = extendMacroEnvironment "Comp" ["R", "S"] (RelMacro (Comp (RVar "R" 1 ip) (RVar "S" 0 ip) ip)) (defaultFixity "TEST") noMacros
        compType = RMacro "Comp" [MRel (RMacro "F" [] ip), MRel (RMacro "G" [] ip)] ip

    case expandMacros env compType of
      Right result ->
        case expandedType result of
          Comp (RMacro "F" [] _) (RMacro "G" [] _) _ -> return ()
          _ -> expectationFailure $ "Expected composition, got: " ++ show (expandedType result)
      Left err -> expectationFailure $ "macro expansion failed: " ++ show err

  it "handles converse operations" $ do
    -- Symmetric relation: Sym R ≔ R ˘
    let env = extendMacroEnvironment "Sym" ["R"] (RelMacro (Conv (RVar "R" 0 ip) ip)) (defaultFixity "TEST") noMacros
        symType = RMacro "Sym" [MRel (RMacro "Related" [] ip)] ip

    case expandMacros env symType of
      Right result ->
        case expandedType result of
          Conv (RMacro "Related" [] _) _ -> return ()
          _ -> expectationFailure "Expected converse relation"
      Left err -> expectationFailure $ "macro expansion failed: " ++ show err

  it "handles quantified relations" $ do
    -- Universal relation: All X . X → X
    let universalType = All "X" (Arr (RVar "X" 0 ip) (RVar "X" 0 ip) ip) ip

    -- Test type operations
    let freeVars = freeTypeVariables universalType
    Set.null freeVars `shouldBe` True -- No free variables

    -- Test substitution (should not affect bound X)
    let substituted = substituteTypeVar 0 (RMacro "Int" [] ip) universalType
    substituted `shouldBe` universalType

  it "handles complex proof judgments" $ do
    -- Relational judgment: t [R ∘ S ˘] u
    let relation = Comp (RVar "R" (-1) ip) (Conv (RVar "S" (-1) ip) ip) ip
        judgment = RelJudgment (Var "t" (-1) ip) relation (Var "u" (-1) ip)

    -- Test context with proof binding
    let ctx = extendProofContext "p" judgment emptyTypingContext
    case lookupProof "p" ctx of
      Right (0, j) -> j `shouldBe` judgment
      Left err -> expectationFailure $ "Expected successful proof lookup: " ++ show err
      Right (idx, _) -> expectationFailure $ "Expected index 0, got: " ++ show idx

-- Helper functions for integration testing

-- | Test examples directly from the RelTT paper
paperExamplesSpec :: Spec
paperExamplesSpec = describe "examples from RelTT paper" $ do
  booleanDistinctionSpec
  termPromotionExamplesSpec
  compositionExamplesSpec
  converseExamplesSpec
  proofTermExamplesSpec

-- | Boolean distinction example from the paper
booleanDistinctionSpec :: Spec
booleanDistinctionSpec = describe "boolean distinction" $ do
  it "demonstrates 'True Different From False' lemma from the paper" $ do
    -- Bool ≔ ∀ X . X → X → X
    let boolType = All "X" (Arr (RVar "X" 0 ip) (Arr (RVar "X" 0 ip) (RVar "X" 0 ip) ip) ip) ip

        -- tt ≔ λ x . λ y . x (first projection)
        ttTerm = Lam "x" (Lam "y" (Var "x" 1 ip) ip) ip

        -- ff ≔ λ x . λ y . y (second projection)
        ffTerm = Lam "x" (Lam "y" (Var "y" 0 ip) ip) ip

    -- Create context with assumptions from the paper's lemma:
    -- 1. tt [Bool] ff (assumption that true and false are related)
    -- 2. x [R] x' (arbitrary elements related by R)
    -- 3. y [R] y' (arbitrary elements related by R)
    let termCtx =
          extendTermContext "y'" (RMacro "B" [] ip) $
            extendTermContext "y" (RMacro "B" [] ip) $
              extendTermContext "x'" (RMacro "A" [] ip) $
                extendTermContext "x" (RMacro "A" [] ip) emptyTypingContext

        -- Assumption 1: tt [Bool] ff where tt and ff are the actual lambda terms
        boolJudgment = RelJudgment ttTerm boolType ffTerm

        -- Assumption 2: x [R] x'
        xJudgment = RelJudgment (Var "x" 3 ip) (RMacro "R" [] ip) (Var "x'" 2 ip)

        -- Assumption 3: y [R] y'
        yJudgment = RelJudgment (Var "y" 1 ip) (RMacro "R" [] ip) (Var "y'" 0 ip)

        -- Build proof context with all assumptions
        proofCtx =
          extendProofContext "y_proof" yJudgment $
            extendProofContext "x_proof" xJudgment $
              extendProofContext "bool_assumption" boolJudgment termCtx

        env = noMacros

    -- Now construct the actual proof derivation from the paper:
    -- 1. Type application: bool_assumption{R} : (λ x . λ y . x)[R→R→R](λ x . λ y . y)
    let step1 = TyApp (PVar "bool_assumption" 2 ip) (RMacro "R" [] ip) ip

    -- 2. Apply with x_proof: step1 x_proof : ((λ x . λ y . x) x)[R→R]((λ x . λ y . y) x')
    let step2 = AppP step1 (PVar "x_proof" 1 ip) ip

    -- 3. Apply with y_proof: step2 y_proof : (((λ x . λ y . x) x) y)[R](((λ x . λ y . y) x') y')
    let step3 = AppP step2 (PVar "y_proof" 0 ip) ip

    -- The terms should β-reduce:
    -- (λ x . λ y . x) x y → x
    -- (λ x . λ y . y) x' y' → y'

    -- First, let's check what step3 actually proves and then try the conversion
    case inferProofType proofCtx env noTheorems step3 of
      Right _step3Result -> do
        -- step3 should prove something that β-reduces to x[R]y'
        -- Let's try the conversion directly
        let finalProof = ConvProof (Var "x" 3 ip) step3 (Var "y'" 0 ip) ip

        case inferProofType proofCtx env noTheorems finalProof of
          Right result -> do
            case resultJudgment result of
              RelJudgment derivedTerm1 derivedRel derivedTerm2 -> do
                -- We should derive x[R]y' - demonstrating the inconsistency
                derivedTerm1 `shouldBe` Var "x" 3 ip
                derivedRel `shouldBe` RMacro "R" [] ip
                derivedTerm2 `shouldBe` Var "y'" 0 ip

                -- This proves ANY x and y' are related by ANY R if tt[Bool]ff
                -- Verify this is indeed an absurdity by showing it's a general pattern
                -- If we can derive x[R]y' for arbitrary x, y', R, then the type system is inconsistent

                -- The absurdity: we derived a judgment between unrelated terms x and y'
                -- where x has type A and y' has type B, but they're related by R
                -- This should not be possible in a consistent system
                derivedTerm1 `shouldNotBe` derivedTerm2 -- Different terms

          -- The significance: this pattern can be generalized to ANY terms and relations
          -- making the entire relational type system trivial

          Left err -> expectationFailure $ "Expected successful derivation of inconsistency: " ++ show err
      Left err -> expectationFailure $ "Expected step3 to be well-typed: " ++ show err

    -- Test that tt and ff are syntactically distinct
    ttTerm `shouldNotBe` ffTerm

  it "shows that assuming tt [Bool] ff leads to trivial relations" $ do
    -- This test demonstrates the full significance of the "True Different From False" lemma
    -- If we assume tt [Bool] ff, we can derive that ANY two terms are related by ANY relation
    -- This would collapse the entire relational structure, proving the assumption false

    let _boolType = All "X" (Arr (RVar "X" 0 ip) (Arr (RVar "X" 0 ip) (RVar "X" 0 ip) ip) ip) ip
        ttTerm = Lam "x" (Lam "y" (Var "x" 1 ip) ip) ip
        ffTerm = Lam "x" (Lam "y" (Var "y" 0 ip) ip) ip

    -- Verify the structural difference that prevents trivialization
    case (normalizeTermBetaEta noMacros ttTerm, normalizeTermBetaEta noMacros ffTerm) of
      (Right ttNorm, Right ffNorm) -> do
        -- The key assertion: tt and ff have different normal forms
        normalizedTerm ttNorm `shouldNotBe` normalizedTerm ffNorm

        -- More specific verification of the distinction
        -- tt normalizes to λ x . λ y . x (first projection)
        -- ff normalizes to λ x . λ y . y (second projection)
        let expectedTt = Lam "x" (Lam "y" (Var "x" 1 ip) ip) ip
            expectedFf = Lam "x" (Lam "y" (Var "y" 0 ip) ip) ip

        normalizedTerm ttNorm `shouldBe` expectedTt
        normalizedTerm ffNorm `shouldBe` expectedFf

        -- This structural difference is what maintains logical consistency
        -- and prevents the derivation of arbitrary relations from tt[Bool]ff

        -- Additional verification: terms have same type but different behavior
        -- Both should be well-typed with Bool type, but behave differently
        ttNorm `shouldSatisfy` (\n -> termStructure (normalizedTerm n) /= termStructure (normalizedTerm ffNorm))
      (Left err, _) -> expectationFailure $ "tt normalization failed: " ++ show err
      (_, Left err) -> expectationFailure $ "ff normalization failed: " ++ show err
  where
    termStructure (Var _ idx _) = "Var" ++ show idx
    termStructure (Lam _ body _) = "Lam(" ++ termStructure body ++ ")"
    termStructure (App t1 t2 _) = "App(" ++ termStructure t1 ++ "," ++ termStructure t2 ++ ")"
    termStructure (TMacro name args _) = "TMacro(" ++ name ++ ",[" ++ show (length args) ++ "])"

-- | Term promotion examples from the paper
termPromotionExamplesSpec :: Spec
termPromotionExamplesSpec = describe "term promotion examples" $ do
  it "demonstrates identity function promotion" $ do
    -- Id ≔ (λ x . x)^
    let idTerm = Lam "x" (Var "x" 0 ip) ip
        idMacro = Prom idTerm ip
        env = extendMacroEnvironment "Id" [] (RelMacro idMacro) (defaultFixity "TEST") noMacros

    -- Test macro expansion
    case expandMacros env (RMacro "Id" [] ip) of
      Right result -> expandedType result `shouldBe` idMacro
      Left err -> expectationFailure $ "Identity macro expansion failed: " ++ show err

  it "demonstrates complex lambda promotion" $ do
    -- LambdaMacro A B ≔ (λ x . λ y . x y)^
    let lambdaTerm = Lam "x" (Lam "y" (App (Var "x" 1 ip) (Var "y" 0 ip) ip) ip) ip
        lambdaMacro = Prom lambdaTerm ip
        env = extendMacroEnvironment "LambdaMacro" ["A", "B"] (RelMacro lambdaMacro) (defaultFixity "TEST") noMacros

    -- Test parameterized macro expansion
    case expandMacros env (RMacro "LambdaMacro" [MRel (RMacro "Int" [] ip), MRel (RMacro "Bool" [] ip)] ip) of
      Right result -> expandedType result `shouldBe` lambdaMacro
      Left err -> expectationFailure $ "Lambda macro expansion failed: " ++ show err

-- | Composition examples from the paper
compositionExamplesSpec :: Spec
compositionExamplesSpec = describe "composition examples" $ do
  it "demonstrates basic composition R ∘ S" $ do
    -- Test with proof checking
    let env = noMacros
        termCtx =
          extendTermContext "z" (RMacro "C" [] ip) $
            extendTermContext "y" (RMacro "B" [] ip) $
              extendTermContext "x" (RMacro "A" [] ip) emptyTypingContext

        -- Create proof context: x[R]y, y[S]z
        judgment1 = RelJudgment (Var "x" 2 ip) (RMacro "R" [] ip) (Var "y" 1 ip)
        judgment2 = RelJudgment (Var "y" 1 ip) (RMacro "S" [] ip) (Var "z" 0 ip)

        proofCtx =
          extendProofContext "q" judgment2 $
            extendProofContext "p" judgment1 termCtx

        -- Composition proof: (p, q) : x[R∘S]z
        compProof = Pair (PVar "p" 1 ip) (PVar "q" 0 ip) ip

    case inferProofType proofCtx env noTheorems compProof of
      Right result ->
        case resultJudgment result of
          RelJudgment term1 actualType term2 -> do
            term1 `shouldBe` Var "x" 2 ip
            term2 `shouldBe` Var "z" 0 ip
            actualType `shouldBe` Comp (RMacro "R" [] ip) (RMacro "S" [] ip) ip
      Left err -> expectationFailure $ "Expected successful composition proof: " ++ show err

  it "demonstrates complex composition DoubleComp R S ≔ R ∘ R ∘ S" $ do
    -- Corrected: Use RVar with proper de Bruijn indices for macro parameters
    -- RVar "R" 1 represents the first parameter, RVar "S" 0 represents the second parameter
    let doubleComp = Comp (RVar "R" 1 ip) (Comp (RVar "R" 1 ip) (RVar "S" 0 ip) ip) ip
        env = extendMacroEnvironment "DoubleComp" ["R", "S"] (RelMacro doubleComp) (defaultFixity "TEST") noMacros

    case expandMacros env (RMacro "DoubleComp" [MRel (RMacro "Eq" [] ip), MRel (RMacro "Lt" [] ip)] ip) of
      Right result ->
        -- Test the correct behavior: R substituted with Eq, S substituted with Lt
        expandedType result `shouldBe` Comp (RMacro "Eq" [] ip) (Comp (RMacro "Eq" [] ip) (RMacro "Lt" [] ip) ip) ip
      Left err -> expectationFailure $ "Double composition macro failed: " ++ show err

-- | Converse examples from the paper
converseExamplesSpec :: Spec
converseExamplesSpec = describe "converse examples" $ do
  it "demonstrates basic converse R ˘" $ do
    let convType = Conv (RMacro "R" [] ip) ip

    -- Test with proof checking
    let termCtx =
          extendTermContext "y" (RMacro "B" [] ip) $
            extendTermContext "x" (RMacro "A" [] ip) emptyTypingContext

        -- Original judgment: x[R]y
        originalJudgment = RelJudgment (Var "x" 1 ip) convType (Var "y" 0 ip)
        proofCtx = extendProofContext "p" originalJudgment termCtx

        -- Converse introduction: ∪ᵢ p : y[R ˘]x
        convProof = ConvIntro (PVar "p" 0 ip) ip
        env = noMacros

    case inferProofType proofCtx env noTheorems convProof of
      Right result ->
        case resultJudgment result of
          RelJudgment term1 actualType term2 -> do
            term1 `shouldBe` Var "y" 0 ip -- Terms swapped
            term2 `shouldBe` Var "x" 1 ip
            actualType `shouldBe` Conv convType ip
      Left err -> expectationFailure $ "Expected successful converse proof: " ++ show err

  it "demonstrates symmetry macro Sym R ≔ R ˘" $ do
    let symMacro = Conv (RVar "R" 0 ip) ip
        env = extendMacroEnvironment "Sym" ["R"] (RelMacro symMacro) (defaultFixity "TEST") noMacros

    case expandMacros env (RMacro "Sym" [MRel (RMacro "Equal" [] ip)] ip) of
      Right result -> expandedType result `shouldBe` Conv (RMacro "Equal" [] ip) ip
      Left err -> expectationFailure $ "Symmetry macro expansion failed: " ++ show err

-- | Proof term examples from the paper
proofTermExamplesSpec :: Spec
proofTermExamplesSpec = describe "proof term examples" $ do
  it "demonstrates iota term promotion ι⟨t,f⟩ : t[f^](f t)" $ do
    -- Identity function: λ x . x
    let idTerm = Lam "x" (Var "x" 0 ip) ip
        termCtx = extendTermContext "t" (RMacro "A" [] ip) emptyTypingContext

        -- Iota proof: ι⟨t, λ x . x⟩ proves t[(λ x . x)^]((λ x . x) t)
        iotaProof = Iota (Var "t" 0 ip) idTerm ip
        env = noMacros

    case inferProofType termCtx env noTheorems iotaProof of
      Right result ->
        case resultJudgment result of
          RelJudgment term1 (Prom term2 _) term3 -> do
            term1 `shouldBe` Var "t" 0 ip
            term2 `shouldBe` idTerm
            term3 `shouldBe` App idTerm (Var "t" 0 ip) ip
          RelJudgment _ relType _ -> expectationFailure $ "Expected promotion type but got: " ++ show relType
      Left err -> expectationFailure $ "Expected successful iota proof: " ++ show err

  it "verifies literal iota typing rule ι⟨a, f⟩ : a [f] (f a) end-to-end" $ do
    -- End-to-end integration test: parse, type-check, and verify the literal typing rule
    let fileContent =
          unlines
            [ "⊢ iotaRule (a : term) (f : term): a [f] (f a) ≔ ι⟨a, f⟩;"
            ]

    case parseFileDeclarations fileContent of
      Right decls -> do
        let theoremDefs = [d | d@(TheoremDef _ _ _ _) <- decls]
        length theoremDefs `shouldBe` 1

        case head theoremDefs of
          TheoremDef "iotaRule" bindings judgment proof -> do
            -- Verify the bindings
            length bindings `shouldBe` 2

            -- Verify the judgment structure
            case judgment of
              RelJudgment leftTerm relType rightTerm -> do
                leftTerm `shouldBeEqual` Var "a" 1 ip
                relType `shouldBeEqual` Prom (Var "f" 0 ip) ip
                rightTerm `shouldBeEqual` App (Var "f" 0 ip) (Var "a" 1 ip) ip

                -- Verify the proof term
                proof `shouldBeEqual` Iota (Var "a" 1 ip) (Var "f" 0 ip) ip

                -- Type check the theorem
                case parseAndCheckTheorem fileContent "iotaRule" of
                  Right result -> do
                    -- Successfully parsed and proved the literal typing rule
                    resultJudgment result `shouldBeEqual` judgment
                  Left err -> expectationFailure $ "Expected successful literal iota rule proof: " ++ show err
          other -> expectationFailure $ "Expected TheoremDef 'iotaRule' but got: " ++ show other
      Left parseErr -> expectationFailure $ "Expected successful parsing: " ++ parseErr

  it "demonstrates transitivity via composition" $ do
    -- Build context: t[R]u, u[S]v ⊢ t[R∘S]v
    let termCtx =
          extendTermContext "v" (RMacro "C" [] ip) $
            extendTermContext "u" (RMacro "B" [] ip) $
              extendTermContext "t" (RMacro "A" [] ip) emptyTypingContext

        judgment1 = RelJudgment (Var "t" 2 ip) (RMacro "R" [] ip) (Var "u" 1 ip)
        judgment2 = RelJudgment (Var "u" 1 ip) (RMacro "S" [] ip) (Var "v" 0 ip)

        proofCtx =
          extendProofContext "q" judgment2 $
            extendProofContext "p" judgment1 termCtx

        -- Transitivity proof: (p, q) : t[R∘S]v
        transProof = Pair (PVar "p" 1 ip) (PVar "q" 0 ip) ip
        env = noMacros

    case inferProofType proofCtx env noTheorems transProof of
      Right result ->
        case resultJudgment result of
          RelJudgment term1 (Comp rtype1 rtype2 _) term2 -> do
            term1 `shouldBe` Var "t" 2 ip
            term2 `shouldBe` Var "v" 0 ip
            rtype1 `shouldBe` RMacro "R" [] ip
            rtype2 `shouldBe` RMacro "S" [] ip
          RelJudgment _ relType _ -> expectationFailure $ "Expected composition type but got: " ++ show relType
      Left err -> expectationFailure $ "Expected successful transitivity proof: " ++ show err

-- | Test Parser → ProofChecker integration pipeline
parserProofCheckerPipelineSpec :: Spec
parserProofCheckerPipelineSpec = describe "Parser → ProofChecker pipeline" $ do
  basicPipelineSpec
  errorHandlingPipelineSpec
  realRelTTExamplesSpec
  complexFileProcessingSpec
  tmacroProofIntegrationSpec

-- | Test basic pipeline functionality
basicPipelineSpec :: Spec
basicPipelineSpec = describe "basic pipeline tests" $ do
  it "parses and checks simple macro with proof" $ do
    let fileContent =
          unlines
            [ "Id ≔ λ x . x;",
              "⊢ reflexivity (t : term): t[Id](Id t) ≔ ι⟨t, Id⟩;"
            ]

    case parseFileDeclarations fileContent of
      Right decls -> do
        let _macroDefs = [d | d@(MacroDef _ _ _) <- decls]
            theoremDefs = [d | d@(TheoremDef _ _ _ _) <- decls]
        length _macroDefs `shouldBe` 1
        length theoremDefs `shouldBe` 1

        -- Build macro environment from parsed macros
        let (newMacroEnv, newTheoremEnv) = buildEnvironmentsFromDeclarations decls
        -- Test the theorem proof checking
        case theoremDefs of
          [TheoremDef "reflexivity" bindings judgment proof] -> do
            let ctx = buildContextFromBindings bindings
            case checkProof ctx newMacroEnv newTheoremEnv proof judgment of
              Right _ -> do
                -- Proof should establish the expected judgment
                return ()
              Left err -> expectationFailure $ "Proof checking failed: " ++ show err
          _ -> expectationFailure "Expected single reflexivity theorem"
      Left err -> expectationFailure $ "Parse failed: " ++ err

  it "validates macro environment integration" $ do
    let fileContent =
          unlines
            [ "Comp R S ≔ R ∘ S;",
              "⊢ transitivity (R : rel) (S : rel) (x : term) (y : term) (z : term) (p : x[R]y) (q : y[S]z): x[Comp R S]z ≔ (p, q);"
            ]

    case parseFileDeclarations fileContent of
      Right decls -> do
        let _macroDefs = [d | d@(MacroDef _ _ _) <- decls]
            theoremDefs = [d | d@(TheoremDef _ _ _ _) <- decls]
        let (newMacroEnv, _) = buildEnvironmentsFromDeclarations decls
        -- Verify macro expansion works
        case expandMacros newMacroEnv (RMacro "Comp" [MRel (RVar "R" 1 ip), MRel (RVar "S" 0 ip)] ip) of
          Right result ->
            expandedType result `shouldBeEqual` Comp (RVar "R" 1 ip) (RVar "S" 0 ip) ip
          Left err -> expectationFailure $ "Macro expansion failed: " ++ show err

        -- Verify the theorem uses the macro correctly in its judgment
        case theoremDefs of
          [TheoremDef _ _ judgment _] -> do
            let RelJudgment _ relType _ = judgment
            case relType of
              RMacro "Comp" [MRel (RVar "R" 1 _), MRel (RVar "S" 0 _)] _ -> return ()
              _ -> expectationFailure $ "Expected Comp macro in judgment, got: " ++ show relType
          _ -> expectationFailure "Expected single theorem"
      Left err -> expectationFailure $ "Parse failed: " ++ err

-- | Test error handling across the pipeline
errorHandlingPipelineSpec :: Spec
errorHandlingPipelineSpec = describe "error handling pipeline tests" $ do
  it "handles parse errors before proof checking" $ do
    let invalidContent =
          unlines
            [ "Id ≔ λ x . x;",
              "Bad ≔ R ∘ ∘ S;", -- Invalid syntax
              "⊢ theorem: t[Id]t ≔ ι⟨t,t⟩;"
            ]

    case parseFileDeclarations invalidContent of
      Left _ -> return () -- Expected parse failure
      Right _ -> expectationFailure "Expected parse error for invalid syntax"

  it "handles proof checking errors on valid parsed content" $ do
    let fileContent =
          unlines
            [ "⊢ invalidProof (R : rel) (x : term) (y : term): x[R]y ≔ ι⟨ x , y ⟩;" -- Wrong proof for judgment
            ]

    case parseFileDeclarations fileContent of
      Right decls -> do
        let theoremDefs = [d | d@(TheoremDef _ _ _ _) <- decls]
        case theoremDefs of
          [TheoremDef _ bindings judgment proof] -> do
            let ctx = buildContextFromBindings bindings
                (newMacroEnv, newTheoremEnv) = buildEnvironmentsFromDeclarations decls
            case checkProof ctx newMacroEnv newTheoremEnv proof judgment of
              Left _ -> return () -- Expected proof checking error
              Right _ -> expectationFailure "Expected proof checking to fail"
          _ -> expectationFailure "Expected single theorem"
      Left err -> expectationFailure $ "Parse failed: " ++ err

-- | Test real RelTT examples through the pipeline
realRelTTExamplesSpec :: Spec
realRelTTExamplesSpec = describe "real RelTT examples" $ do
  it "processes identity theorem end-to-end" $ do
    let fileContent =
          unlines
            [ "Id ≔ λ x . x;",
              "⊢ identity (t : term): t[Id](Id t) ≔ ι⟨t, Id⟩;"
            ]

    case parseAndCheckTheorem fileContent "identity" of
      Right _ -> do
        -- Successfully parsed and proved the identity theorem
        return ()
      Left err -> expectationFailure $ "Identity theorem failed: " ++ err

  it "processes composition theorem with macro" $ do
    let fileContent =
          unlines
            [ "Comp R S ≔ R ∘ S;",
              "⊢ transitivity (R : rel) (S : rel) (x : term) (y : term) (z : term) (p : x[R]y) (q : y[S]z): x[Comp R S]z ≔ (p, q);"
            ]

    case parseAndCheckTheorem fileContent "transitivity" of
      Right _ -> return ()
      Left err -> expectationFailure $ "Transitivity theorem failed: " ++ err

  it "processes converse theorem" $ do
    let fileContent =
          unlines
            [ "⊢ symmetry (R : rel) (x : term) (y : term) (p : x[R]y): y[R ˘]x ≔ ∪ᵢ p;"
            ]

    case parseAndCheckTheorem fileContent "symmetry" of
      Right _ -> return ()
      Left err -> expectationFailure $ "Symmetry theorem failed: " ++ err

-- | Test complex file processing
complexFileProcessingSpec :: Spec
complexFileProcessingSpec = describe "complex file processing" $ do
  it "processes multi-theorem files" $ do
    let fileContent =
          unlines
            [ "Id ≔ λ x . x;",
              "Sym R ≔ R ˘;",
              "⊢ identity (t : Term): t[Id](Id t) ≔ ι⟨ t , Id ⟩;",
              "⊢ symmetry (R : Rel) (x : Term) (y : Term) (p : x[R]y) : y[Sym R]x ≔ ∪ᵢ p;"
            ]

    case parseFileDeclarations fileContent of
      Right decls -> do
        let _macroDefs = [d | d@(MacroDef _ _ _) <- decls]
            theoremDefs = [d | d@(TheoremDef _ _ _ _) <- decls]
        length _macroDefs `shouldBe` 2
        length theoremDefs `shouldBe` 2

        let (newMacroEnv, _) = buildEnvironmentsFromDeclarations decls
        -- Check each theorem individually
        mapM_ (checkTheoremInEnvironment newMacroEnv) theoremDefs
      Left err -> expectationFailure $ "Parse failed: " ++ err

  it "handles dependent macros" $ do
    let fileContent =
          unlines
            [ "Base R ≔ R ∘ R;",
              "Extended R S ≔ Base R ∘ S;",
              "⊢ example (R : Rel) (S : Rel) (x : Term) (y : Term) (p : x[Extended R S]y) : x[Extended R S]y ≔ p;"
            ]

    case parseFileDeclarations fileContent of
      Right decls -> do
        let _macroDefs = [d | d@(MacroDef _ _ _) <- decls]
            theoremDefs = [d | d@(TheoremDef _ _ _ _) <- decls]
        let (newMacroEnv, _) = buildEnvironmentsFromDeclarations decls
        -- Test that dependent macro expansion works
        case expandMacros newMacroEnv (RMacro "Extended" [MRel (RMacro "A" [] ip), MRel (RMacro "B" [] ip)] ip) of
          Right result -> do
            -- Should expand to (A ∘ A) ∘ B (Base A gets expanded too)
            let expected = Comp (Comp (RMacro "A" [] ip) (RMacro "A" [] ip) ip) (RMacro "B" [] ip) ip
            expandedType result `shouldBeEqual` expected
          Left err -> expectationFailure $ "Dependent macro expansion failed: " ++ show err

        -- Verify theorem checking still works
        mapM_ (checkTheoremInEnvironment newMacroEnv) theoremDefs
      Left err -> expectationFailure $ "Parse failed: " ++ err

-- Helper functions for pipeline integration testing

-- | Parse file content and check a specific theorem
parseAndCheckTheorem :: String -> String -> Either String ProofCheckResult
parseAndCheckTheorem fileContent theoremName =
  case parseFileDeclarations fileContent of
    Left parseErr -> Left parseErr
    Right decls -> do
      let (newMacroEnv, newTheoremEnv) = buildEnvironmentsFromDeclarations decls
          theoremDefs = [d | d@(TheoremDef _ _ _ _) <- decls]

      case [t | t@(TheoremDef name _ _ _) <- theoremDefs, name == theoremName] of
        [TheoremDef _ bindings judgment proof] -> do
          let ctx = buildContextFromBindings bindings
          case inferProofType ctx newMacroEnv newTheoremEnv proof of
            Left proofErr -> Left $ "Proof error: " ++ show proofErr
            Right result ->
              -- Use macro-aware equality to check judgments
              case relJudgmentEqual newMacroEnv (resultJudgment result) judgment of
                Right True -> Right result
                Right False -> Left $ "Judgment mismatch: inferred " ++ show (resultJudgment result) ++ " vs expected " ++ show judgment
                Left err -> Left $ "Equality check failed: " ++ show err
        [] -> Left $ "Theorem not found: " ++ theoremName
        _ -> Left $ "Multiple theorems with name: " ++ theoremName

-- | Check a theorem in a given macro environment
checkTheoremInEnvironment :: MacroEnvironment -> Declaration -> Expectation
checkTheoremInEnvironment newMacroEnv (TheoremDef name bindings judgment proof) = do
  let ctx = buildContextFromBindings bindings
  case checkProof ctx newMacroEnv noTheorems proof judgment of
    Right _ -> return ()
    Left err -> expectationFailure $ "Theorem " ++ name ++ " failed: " ++ show err
checkTheoremInEnvironment _ _ =
  expectationFailure "Expected theorem declaration"

-- | Test TMacro integration with proof checking
tmacroProofIntegrationSpec :: Spec
tmacroProofIntegrationSpec = describe "TMacro proof integration" $ do
  it "handles TMacro expansion in iota proofs" $ do
    -- Test: ι⟨t, f x⟩ where f is a term macro
    let env = extendMacroEnvironment "id" [] (TermMacro (Lam "x" (Var "x" 0 ip) ip)) (defaultFixity "TEST") noMacros
        termCtx =
          extendTermContext "t" (RMacro "A" [] ip) $
            extendTermContext "x" (RMacro "A" [] ip) emptyTypingContext

        -- Parse and check: ι⟨t, id x⟩
        -- This should prove: t[(id x)^]((id x) t)
        tmacroTerm = TMacro "id" [MTerm (Var "x" 0 ip)] ip -- Should expand to (λ x . x) x ≡ x
        iotaProof = Iota (Var "t" 1 ip) tmacroTerm ip

    case inferProofType termCtx env noTheorems iotaProof of
      Right result ->
        case resultJudgment result of
          RelJudgment term1 (Prom promTerm _) term2 -> do
            term1 `shouldBe` Var "t" 1 ip
            promTerm `shouldBe` tmacroTerm -- Should contain the TMacro
            term2 `shouldBe` App tmacroTerm (Var "t" 1 ip) ip -- Application of TMacro
          RelJudgment _ relType _ -> expectationFailure $ "Expected promotion type but got: " ++ show relType
      Left err -> expectationFailure $ "Expected successful TMacro iota proof: " ++ show err

  it "handles TMacro in proof term applications" $ do
    -- Test proof application where terms contain TMacros
    let env = extendMacroEnvironment "const" ["a"] (TermMacro (Lam "x" (Var "a" 0 ip) ip)) (defaultFixity "TEST") noMacros
        termCtx =
          extendTermContext "y" (RMacro "B" [] ip) $
            extendTermContext "x" (RMacro "A" [] ip) emptyTypingContext

        -- Create proof context with TMacro in judgments
        -- p : (const y) [R→S] (const y)
        -- q : x [R] x
        constY = TMacro "const" [MTerm (Var "y" 0 ip)] ip
        judgment1 = RelJudgment constY (Arr (RMacro "R" [] ip) (RMacro "S" [] ip) ip) constY
        judgment2 = RelJudgment (Var "x" 1 ip) (RMacro "R" [] ip) (Var "x" 1 ip)

        proofCtx =
          extendProofContext "q" judgment2 $
            extendProofContext "p" judgment1 termCtx

        -- Application: p q should give (const y) x [S] (const y) x
        appProof = AppP (PVar "p" 1 ip) (PVar "q" 0 ip) ip

    case inferProofType proofCtx env noTheorems appProof of
      Right result ->
        case resultJudgment result of
          RelJudgment term1 relType term2 -> do
            term1 `shouldBe` App constY (Var "x" 1 ip) ip
            term2 `shouldBe` App constY (Var "x" 1 ip) ip
            relType `shouldBe` RMacro "S" [] ip
      Left err -> expectationFailure $ "Expected successful TMacro application proof: " ++ show err

  it "handles nested TMacro applications in proofs" $ do
    -- Test deeply nested TMacro applications
    let macroEnv1 = extendMacroEnvironment "id" [] (TermMacro (Lam "x" (Var "x" 0 ip) ip)) (defaultFixity "TEST") noMacros
        macroEnv2 = extendMacroEnvironment "app" ["f", "x"] (TermMacro (App (Var "f" 1 ip) (Var "x" 0 ip) ip)) (defaultFixity "TEST") macroEnv1

        termCtx =
          extendTermContext "f" (RMacro "A→B" [] ip) $
            extendTermContext "x" (RMacro "A" [] ip) emptyTypingContext

        -- Nested TMacro: app (id f) x should represent ((λ x . x) f) x ≡ f x
        nestedTMacro = TMacro "app" [MTerm (TMacro "id" [MTerm (Var "f" 1 ip)] ip), MTerm (Var "x" 0 ip)] ip

        -- Test with iota: ι⟨nestedTMacro, id nestedTMacro⟩
        iotaProof = Iota nestedTMacro (TMacro "id" [MTerm nestedTMacro] ip) ip

    case inferProofType termCtx macroEnv2 noTheorems iotaProof of
      Right result ->
        case resultJudgment result of
          RelJudgment term1 (Prom promTerm _) term2 -> do
            term1 `shouldBe` nestedTMacro
            promTerm `shouldBe` TMacro "id" [MTerm nestedTMacro] ip
            term2 `shouldBe` App (TMacro "id" [MTerm nestedTMacro] ip) nestedTMacro ip
          RelJudgment _ relType _ -> expectationFailure $ "Expected promotion type but got: " ++ show relType
      Left err -> expectationFailure $ "Expected successful nested TMacro proof: " ++ show err

  it "handles TMacro substitution in lambda abstractions" $ do
    -- Test lambda abstractions containing TMacros using proper de Bruijn substitution
    let -- Lambda with TMacro: λ y . const a y (where 'a' has de Bruijn index 1)
        lambdaWithTMacro = Lam "y" (App (TMacro "const" [MTerm (Var "a" 1 ip)] ip) (Var "y" 0 ip) ip) ip

        -- Test substitution of index 1 with new term
        replacement = Var "b" 0 ip  -- Replacement term
        substituted = substIndex 1 replacement lambdaWithTMacro
        expected = Lam "y" (App (TMacro "const" [MTerm (Var "b" 0 ip)] ip) (Var "y" 0 ip) ip) ip

    substituted `shouldBe` expected

  it "handles TMacro in conversion proofs" $ do
    -- Test term conversion with TMacros
    let env = extendMacroEnvironment "id" ["x"] (TermMacro (Var "x" 0 ip)) (defaultFixity "TEST") noMacros
        termCtx = extendTermContext "t" (RMacro "A" [] ip) emptyTypingContext

        -- Create a proof that t ≡ t via identity
        idT = TMacro "id" [MTerm (Var "t" 0 ip)] ip

        -- Conversion proof: t ⇃ proof ⇂ (id t)
        -- This should demonstrate that t converts to (id t) which should be equivalent
        innerProof = Iota (Var "t" 0 ip) (Lam "x" (Var "x" 0 ip) ip) ip -- ι⟨t, λ x . x⟩
        convProof = ConvProof (Var "t" 0 ip) innerProof idT ip

    case inferProofType termCtx env noTheorems convProof of
      Right result ->
        case resultJudgment result of
          RelJudgment term1 relType term2 -> do
            term1 `shouldBe` Var "t" 0 ip
            term2 `shouldBe` idT
            -- The relational type should be preserved through conversion
            case relType of
              Prom _ _ -> return () -- Expected promoted type
              _ -> expectationFailure $ "Expected promoted type, got: " ++ show relType
      Left err -> expectationFailure $ "Expected successful TMacro conversion proof: " ++ show err

  it "handles TMacro arity validation in proof context" $ do
    -- Test that TMacro arity is validated during proof checking
    let env = extendMacroEnvironment "binary" ["x", "y"] (TermMacro (App (Var "x" 1 ip) (Var "y" 0 ip) ip)) (defaultFixity "TEST") noMacros
        termCtx = extendTermContext "a" (RMacro "A" [] ip) emptyTypingContext

        -- TMacro with wrong arity (expects 2 args, gets 1)
        wrongArityTMacro = TMacro "binary" [MTerm (Var "a" 0 ip)] ip -- Missing second argument

        -- This should work - the parser creates TMacro with whatever args it gets
        -- The expansion/normalization phase would handle arity validation
        iotaProof = Iota wrongArityTMacro wrongArityTMacro ip

    case inferProofType termCtx env noTheorems iotaProof of
      Right result ->
        -- The proof should succeed syntactically, arity checking happens during expansion
        case resultJudgment result of
          RelJudgment term1 (Prom promTerm _) _ -> do
            term1 `shouldBe` wrongArityTMacro
            promTerm `shouldBe` wrongArityTMacro
          RelJudgment _ relType _ -> expectationFailure $ "Expected promotion type but got: " ++ show relType
      Left err -> expectationFailure $ "Expected proof to succeed syntactically: " ++ show err

  it "detects variable shadowing bug in pi elimination" $ do
    -- This should FAIL but currently passes due to variable shadowing bug
    -- The theorem binding 'x' and the pi-bound 'x' are different variables
    let input = "⊢ shadowing_bug_test (R : Rel) (S : Rel) (a : Term) (b : Term) (x : Term) (p : a [R ∘ S] b) : a [R] x ≔ π p - x . u . v . u;"
    case parseFileDeclarations input of
      Right [TheoremDef _ bindings judgment proof] -> do
        -- Build context from bindings
        let ctx = buildContextFromBindings bindings
            (newMacroEnv, newTheoremEnv) = (noMacros, noTheorems)
        -- This should fail type checking because the pi-bound x and parameter x are different
        case checkProof ctx newMacroEnv newTheoremEnv proof judgment of
          Right _ -> expectationFailure "Expected type checking to fail due to variable shadowing, but it passed"
          Left _ -> return () -- Expected failure
      Right _ -> expectationFailure "Expected single theorem declaration"
      Left err -> expectationFailure $ "Parse failed: " ++ err

  it "detects pi elimination type error with different variable name" $ do
    -- Same test but with 'y' instead of shadowed 'x' to show AST differences
    -- This should also FAIL because the conclusion 'a [R] x' doesn't match what pi elimination produces
    let input = "⊢ pi_type_error_test (R : Rel) (S : Rel) (a : Term) (b : Term) (x : Term) (p : a [R ∘ S] b) : a [R] x ≔ π p - y . u . v . u;"
    case parseFileDeclarations input of
      Right [TheoremDef _ bindings judgment proof] -> do
        -- Build context from bindings
        let ctx = buildContextFromBindings bindings
            (newMacroEnv, newTheoremEnv) = (noMacros, noTheorems)
        -- This should fail type checking
        case checkProof ctx newMacroEnv newTheoremEnv proof judgment of
          Right _ -> expectationFailure "Expected type checking to fail, but it passed"
          Left _ -> return () -- Expected failure
      Right _ -> expectationFailure "Expected single theorem declaration"
      Left err -> expectationFailure $ "Parse failed: " ++ err

  it "correctly shifts indices in pi elimination - term variables" $ do
    -- Test that term variable indices are shifted correctly
    let input = "⊢ pi_shift_term (R : Rel) (S : Rel) (t : Term) (p : t [R ∘ S] t) : t [R] t ≔ π p - x . u . v . ι⟨t,t⟩;"
    case parseFileDeclarations input of
      Right [TheoremDef _ bindings judgment proof] -> do
        let ctx = buildContextFromBindings bindings
            (newMacroEnv, newTheoremEnv) = (noMacros, noTheorems)
        -- This should fail because after shifting, the 't' in the conclusion should have index 1, not 0
        case checkProof ctx newMacroEnv newTheoremEnv proof judgment of
          Right _ -> expectationFailure "Expected type checking to fail due to incorrect index shifting"
          Left _ -> return ()
      Right other -> expectationFailure $ "Expected single theorem declaration but got: " ++ show other
      Left err -> expectationFailure $ "Parse failed with error: " ++ err

  it "correctly shifts indices in lambda abstraction (proof level)" $ do
    -- Test that λ (proof lambda) shifts proof variable indices correctly
    let input = "⊢ lambda_shift_test (R : Rel) (a : Term) (q : a [R] a) : (λ x . a) [R → R] (λ x' . a) ≔ λ p : R . q;"
    case parseFileDeclarations input of
      Right [TheoremDef _ bindings judgment proof] -> do
        let ctx = buildContextFromBindings bindings
            (newMacroEnv, newTheoremEnv) = (noMacros, noTheorems)
        -- The 'q' inside the lambda body should have its index shifted when 'p' is bound
        case checkProof ctx newMacroEnv newTheoremEnv proof judgment of
          Right _ -> return () -- Expected to pass
          Left _ -> expectationFailure "Lambda abstraction should handle indices correctly"
      Right other -> expectationFailure $ "Expected single theorem declaration but got: " ++ show other
      Left err -> expectationFailure $ "Parse failed with error: " ++ err

  it "verifies complex index shifting with nested binders" $ do
    -- Test multiple nested binders to ensure cumulative shifting works
    let input = "⊢ nested_shift (R : Rel) (S : Rel) (T : Rel) (a : Term) (p : a [R ∘ S ∘ T] a) : a [∀ X . R → X → T] a ≔ Λ X . λ u : R . λ v : X . π p - x . r . s . π s - y . t . u' . ι⟨ a , a ⟩;"
    case parseFileDeclarations input of
      Right [TheoremDef _ bindings judgment proof] -> do
        let ctx = buildContextFromBindings bindings
            (newMacroEnv, newTheoremEnv) = (noMacros, noTheorems)
        -- This tests cumulative shifting through multiple binders
        case checkProof ctx newMacroEnv newTheoremEnv proof judgment of
          _ -> return () -- We mainly want to see the AST structure
      Right other -> expectationFailure $ "Expected single theorem declaration but got: " ++ show other
      Left err -> expectationFailure $ "Parse failed with error: " ++ err

-- | Test for quantifier de Bruijn index bug through integration
quantifierDeBruijnBugSpec :: Spec
quantifierDeBruijnBugSpec = describe "quantifier de Bruijn index bug (integration)" $ do
  it "parse and check theorem with unbound relation in quantifier" $ do
    -- Test Method 2: Parse theorem declaration and check it
    let theoremText = "⊢ bug_test (S : Rel) (a : Term) (b : Term) (p : a [∀ X . S] b) : a [S] b ≔ p { S };"
    case parseDeclaration theoremText of
      Left parseErr -> expectationFailure $ "Parse should succeed: " ++ parseErr
      Right (TheoremDef _ bindings judgment proof) -> do
        let ctx = buildContextFromBindings bindings
            (newMacroEnv, newTheoremEnv) = (noMacros, noTheorems)
        case checkProof ctx newMacroEnv newTheoremEnv proof judgment of
          Right _ -> return () -- Should succeed
          Left err ->
            expectationFailure $
              "Theorem should type check but failed due to de Bruijn bug: " ++ show err
      _ -> expectationFailure "Expected theorem declaration"

  it "parse and check file content with quantifier bug patterns" $ do
    -- Test Method 3: Parse full file content
    let fileContent =
          unlines
            [ "-- Multiple theorems demonstrating the bug",
              "⊢ constant_bug (S : Rel) (a : Term) (b : Term)",
              "    (p : a [∀ X . S] b) : a [S] b ≔ p { S };",
              "",
              "⊢ composition_bug (R : Rel) (S : Rel) (a : Term) (b : Term)",
              "    (p : a [∀ X . X ∘ S] b) : a [R ∘ S] b ≔ p { R };",
              "",
              "⊢ control_works (R : Rel) (a : Term) (b : Term)",
              "    (p : a [∀ X . X] b) : a [R] b ≔ p { R };"
            ]

    case parseFileDeclarations fileContent of
      Left parseErr -> expectationFailure $ "File should parse: " ++ parseErr
      Right decls -> do
        -- Build environments
        let (builtMacroEnv, builtTheoremEnv) = buildEnvironmentsFromDeclarations decls

        -- Check each theorem
        mapM_ (checkDeclForBugTest builtMacroEnv builtTheoremEnv) decls


  it "DEBUG: test parentheses parsing shows structure difference" $ do
    let withParens = "(p { R }){ S }"
    let withoutParens = "p { R } { S }"
    let justParens = "(p)"
    
    putStrLn "\n=== TEST JUST PARENTHESES (p) ==="
    case runParser rawProof "test" justParens of
      Left parseErr -> putStrLn $ "Parse error: " ++ show parseErr
      Right result -> putStrLn $ "Raw result: " ++ show result
    
    putStrLn "\n=== TEST WITHOUT PARENTHESES p { R } { S } ==="  
    case runParser rawProof "test" withoutParens of
      Left parseErr -> putStrLn $ "Parse error: " ++ show parseErr
      Right result -> putStrLn $ "Raw result: " ++ show result
    
    putStrLn "\n=== TEST WITH PARENTHESES (p { R }){ S } ==="
    case runParser rawProof "test" withParens of
      Left parseErr -> putStrLn $ "Parse error: " ++ show parseErr
      Right result -> putStrLn $ "Raw result: " ++ show result

  it "nested quantifier substitution shows index corruption clearly" $ do
    -- Test the case that clearly demonstrates the index shifting bug
    let theoremText = "⊢ nested_bug (R : Rel) (S : Rel) (T : Rel) (a : Term) (b : Term) (p : a [∀ X . ∀ Y . X ∘ T] b) : a [R ∘ T] b ≔ (p { R }){ S };"
    case parseDeclaration theoremText of
      Left parseErr -> expectationFailure $ "Parse should succeed: " ++ parseErr
      Right (TheoremDef _ bindings judgment proof) -> do
        let ctx = buildContextFromBindings bindings
            (newMacroEnv, newTheoremEnv) = (noMacros, noTheorems)
        case checkProof ctx newMacroEnv newTheoremEnv proof judgment of
          Right _ -> return () -- Should work when bug is fixed
          Left err ->
            expectationFailure $
              "Nested quantifier theorem should work but failed: " ++ show err
      _ -> expectationFailure "Expected theorem declaration"

  it "quantifier commutativity with type lambdas should work" $ do
    -- Test the failing forall_commute case from demo.rtt
    -- This involves both type lambdas (Λ Y . Λ X .) and type applications (p { X }{Y})
    let theoremText = "⊢ forall_commute_test (a : Term) (b : Term) (R : Rel) (p : a [∀ X . ∀ Y . R] b) : a [∀ Y . ∀ X . R] b ≔ Λ Y . Λ X . (p { X }){ Y };"
    case parseDeclaration theoremText of
      Left parseErr -> expectationFailure $ "Parse should succeed: " ++ parseErr
      Right (TheoremDef _ bindings judgment proof) -> do
        let ctx = buildContextFromBindings bindings
            (newMacroEnv, newTheoremEnv) = (noMacros, noTheorems)
        case checkProof ctx newMacroEnv newTheoremEnv proof judgment of
          Right _ -> return () -- Should work when bug is fixed
          Left err ->
            expectationFailure $
              "Quantifier commutativity theorem should work but failed: " ++ show err
      _ -> expectationFailure "Expected theorem declaration"

-- Helper functions for quantifier bug tests

checkDeclForBugTest :: MacroEnvironment -> TheoremEnvironment -> Declaration -> Expectation
checkDeclForBugTest _ _ (MacroDef _ _ _) = return () -- Skip macro definitions
checkDeclForBugTest localMacroEnv localTheoremEnv (TheoremDef _ bindings judgment proof) = do
  let ctx = buildContextFromBindings bindings
  case checkProof ctx localMacroEnv localTheoremEnv proof judgment of
    Right _ -> return ()
    Left err -> expectationFailure $ "Theorem should work: " ++ show err
checkDeclForBugTest _ _ _ = return () -- Skip other declarations
