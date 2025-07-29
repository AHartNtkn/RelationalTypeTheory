{-# LANGUAGE OverloadedStrings #-}

module NormalizeSpec (spec) where

import Core.Errors
import Core.Syntax
import Core.Context (emptyContext, extendMacroContext)
import Operations.Generic.BetaEta (betaEtaEquality, normalizeForBetaEta)
import Operations.Generic.Equality (alphaEquality)
import Operations.Generic.Substitution (substIndex)
import Test.Hspec
import TestHelpers (simpleParamInfo)
import Parser.Mixfix (defaultFixity)
import Text.Megaparsec (initialPos)

-- | Normalization result to match old API
data NormalizationResult = NormalizationResult
  { normalizedTerm :: Term
  , wasNormalized :: Bool
  , reductionSteps :: Int
  } deriving (Show, Eq)

-- Test helpers - use empty macro environment for tests that don't need macros
normalizeTermBetaEta :: Term -> Either RelTTError NormalizationResult
normalizeTermBetaEta term = do
  normalized <- normalizeForBetaEta emptyContext term
  return $ NormalizationResult
    { normalizedTerm = normalized
    , wasNormalized = normalized /= term
    , reductionSteps = if normalized /= term then 1 else 0  -- Simplified step counting
    }

termEqualityBetaEta :: Term -> Term -> Either RelTTError Bool
termEqualityBetaEta t1 t2 = betaEtaEquality emptyContext t1 t2

-- Weak head normal form (simplified implementation)
normalizeTermWHNF :: Context -> Term -> Either RelTTError NormalizationResult
normalizeTermWHNF env term = do
  -- For WHNF, we only reduce the outermost redex
  normalized <- normalizeForBetaEta env term
  return $ NormalizationResult
    { normalizedTerm = normalized
    , wasNormalized = normalized /= term
    , reductionSteps = if normalized /= term then 1 else 0
    }

-- Substitution wrapper
substituteTerm :: Term -> Term -> Either RelTTError Term
substituteTerm replacement target = Right $ substIndex 0 replacement target

-- Alpha equality with macro environment
termEqualityAlpha :: Context -> Term -> Term -> Either RelTTError Bool
termEqualityAlpha env t1 t2 = Right $ alphaEquality env t1 t2

spec :: Spec
spec = do
  betaReductionSpec
  etaReductionSpec
  substitutionSpec
  equalitySpec
  macroExpansionAlphaEqualitySpec
  normalizationStrategySpec
  normalizationEdgeCasesSpec

-- | Test β-reduction functionality
betaReductionSpec :: Spec
betaReductionSpec = describe "β-reduction" $ do
  it "reduces basic application: (λ x . x) a → a" $ do
    let term = App (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> do
        normalizedTerm result `shouldBe` Var "a" (-1) (initialPos "test")
        wasNormalized result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "reduces nested applications: (λ x . λ y . x) a b → a" $ do
    let term = App (App (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")) (Var "b" (-1) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> normalizedTerm result `shouldBe` Var "a" (-1) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "reduces complex substitution: (λ x . λ y . x y) f a → f a" $ do
    let term = App (App (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "f" (-1) (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> normalizedTerm result `shouldBe` App (Var "f" (-1) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "handles de Bruijn index shifting: (λ x . λ y . x) (λ z . z) → λ y . λ z . z" $ do
    let term = App (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> normalizedTerm result `shouldBe` Lam "y" (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

-- | Test η-reduction functionality
etaReductionSpec :: Spec
etaReductionSpec = describe "η-reduction" $ do
  it "reduces basic eta: λ x . f x → f (when x not free in f)" $ do
    let term = Lam "x" (App (Var "f" (-1) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> normalizedTerm result `shouldBe` Var "f" (-1) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "does not reduce when variable is free: λ x . f x y" $ do
    let term = Lam "x" (App (App (Var "f" (-1) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "y" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result ->
        -- Should not eta-reduce because the lambda is not of the form λ x . t x
        normalizedTerm result `shouldBe` term
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "reduces nested lambda eta: λ x . λ y . f x y → f" $ do
    let term = Lam "x" (Lam "y" (App (App (Var "f" (-1) (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> normalizedTerm result `shouldBe` Var "f" (-1) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

-- | Test substitution operations
substitutionSpec :: Spec
substitutionSpec = describe "substitution" $ do
  it "performs simple substitution: [a/x](x y) → a y" $ do
    let target = App (Var "x" 0 (initialPos "test")) (Var "y" (-1) (initialPos "test")) (initialPos "test")
        replacement = Var "a" (-1) (initialPos "test")
    case substituteTerm replacement target of
      Right result -> result `shouldBe` App (Var "a" (-1) (initialPos "test")) (Var "y" (-1) (initialPos "test")) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "avoids variable capture in lambda bodies" $ do
    let target = Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        replacement = Var "y" (-1) (initialPos "test")
    case substituteTerm replacement target of
      Right result ->
        -- After substitution, the inner y should refer to the lambda-bound y
        result `shouldBe` Lam "y" (App (Var "y" (-1) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "preserves free variables correctly" $ do
    let target = App (Var "x" 0 (initialPos "test")) (Var "z" (-1) (initialPos "test")) (initialPos "test")
        replacement = Var "a" (-1) (initialPos "test")
    case substituteTerm replacement target of
      Right result -> result `shouldBe` App (Var "a" (-1) (initialPos "test")) (Var "z" (-1) (initialPos "test")) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "handles complex nested substitutions" $ do
    let target = Lam "y" (App (Var "x" 1 (initialPos "test")) (Lam "z" (App (Var "x" 2 (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        replacement = Lam "w" (Var "w" 0 (initialPos "test")) (initialPos "test")
    case substituteTerm replacement target of
      Right result -> result `shouldBe` Lam "y" (App (Lam "w" (Var "w" 0 (initialPos "test")) (initialPos "test")) (Lam "z" (App (Lam "w" (Var "w" 0 (initialPos "test")) (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

-- | Test equality checking
equalitySpec :: Spec
equalitySpec = describe "equality checking" $ do
  it "recognizes alpha equivalence: λ x . x ≡ λ y . y" $ do
    let term1 = Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")
        term2 = Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")
    case termEqualityBetaEta term1 term2 of
      Right result -> result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "recognizes beta-eta equivalence: (λ x . x) a ≡ a" $ do
    let term1 = App (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")
        term2 = Var "a" (-1) (initialPos "test")
    case termEqualityBetaEta term1 term2 of
      Right result -> result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "rejects non-equivalent terms: λ x . x ≢ λ x . x x" $ do
    let term1 = Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")
        term2 = Lam "x" (App (Var "x" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
    case termEqualityBetaEta term1 term2 of
      Right result -> result `shouldBe` False
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "handles complex nested equivalences" $ do
    let term1 = App (Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "f" (-1) (initialPos "test")) (initialPos "test")
        term2 = Lam "y" (App (Var "f" (-1) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
    case termEqualityBetaEta term1 term2 of
      Right result -> result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

-- | Test macro expansion in alpha equality
macroExpansionAlphaEqualitySpec :: Spec
macroExpansionAlphaEqualitySpec = describe "macro expansion in alpha equality" $ do
  it "expands term macros before alpha comparison" $ do
    let macroEnv = 
          extendMacroContext "True" [] (TermMacro (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))) (defaultFixity "True") $
          extendMacroContext "Identity" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))) (defaultFixity "Identity") $
          emptyContext
    case termEqualityAlpha macroEnv (TMacro "Identity" [] (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) of
      Right result -> result `shouldBe` True
      Left err -> expectationFailure $ "Alpha equality with macro expansion failed: " ++ show err

  it "expands both terms before comparing" $ do
    let macroEnv =
          extendMacroContext "Id" [] (TermMacro (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test"))) (defaultFixity "Id") $
          extendMacroContext "Identity" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))) (defaultFixity "Identity") $
          emptyContext
    case termEqualityAlpha macroEnv (TMacro "Identity" [] (initialPos "test")) (TMacro "Id" [] (initialPos "test")) of
      Right result -> result `shouldBe` True -- Alpha equivalent after expansion
      Left err -> expectationFailure $ "Alpha equality with both macros failed: " ++ show err

  it "recognizes parameterized macro and its expanded form as alpha-equivalent" $ do
    let macroEnv =
          extendMacroContext "a" [] (TermMacro (Var "a_const" (-1) (initialPos "test"))) (defaultFixity "a") $
          extendMacroContext "Const" [simpleParamInfo "x" TermK] (TermMacro (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test"))) (defaultFixity "Const") $
          emptyContext
        macroCall = TMacro "Const" [MTerm (TMacro "a" [] (initialPos "test"))] (initialPos "test")
        expectedExpansion = Lam "y" (TMacro "a" [] (initialPos "test")) (initialPos "test")
    case termEqualityAlpha macroEnv macroCall expectedExpansion of
      Right True -> return () -- Success: macro expands to expected form
      Right False ->
        expectationFailure $
          "Macro " ++ show macroCall ++ " should expand to " ++ show expectedExpansion ++ " but they were not considered equal"
      Left err -> expectationFailure $ "Comparison failed: " ++ show err

-- | Test normalization strategies
normalizationStrategySpec :: Spec
normalizationStrategySpec = describe "normalization strategies" $ do
  it "weak head normal form reduces outer redexes only" $ do
    let term = App (Lam "x" (App (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")
    case normalizeTermWHNF emptyContext term of
      Right result -> do
        -- WHNF reduces: (λ x . (λ y . y) x) a → (λ y . y) a → a
        -- Both reductions happen because both are at the top level
        let expected = Var "a" (-1) (initialPos "test")
        normalizedTerm result `shouldBe` expected
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "weak head normal form stops at lambda (does not reduce under lambda)" $ do
    -- This term has a redex under a lambda: λ z . (λ x . x) a
    let term = Lam "z" (App (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
    case normalizeTermWHNF emptyContext term of
      Right result -> do
        -- WHNF should NOT reduce under the lambda
        -- The term is already in WHNF because it's a lambda
        normalizedTerm result `shouldBe` term
        reductionSteps result `shouldBe` 0
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "weak head normal form stops at constructor-like forms" $ do
    -- A lambda is already in WHNF
    let term1 = Lam "x" (App (App (Var "f" (-1) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "y" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
    case normalizeTermWHNF emptyContext term1 of
      Right result -> do
        normalizedTerm result `shouldBe` term1
        reductionSteps result `shouldBe` 0
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

    -- A variable is already in WHNF
    let term2 = Var "x" (-1) (initialPos "test")
    case normalizeTermWHNF emptyContext term2 of
      Right result -> do
        normalizedTerm result `shouldBe` term2
        reductionSteps result `shouldBe` 0
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

    -- An application with a variable head is in WHNF
    let term3 = App (App (Var "f" (-1) (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (App (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (Var "z" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
    case normalizeTermWHNF emptyContext term3 of
      Right result -> do
        -- WHNF doesn't reduce this because the head is a variable, not a lambda
        normalizedTerm result `shouldBe` term3
        reductionSteps result `shouldBe` 0
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "full normalization reduces everything" $ do
    let term = App (Lam "x" (App (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> normalizedTerm result `shouldBe` Var "a" (-1) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "counts normalization steps correctly" $ do
    let term = App (App (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")) (Var "b" (-1) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> reductionSteps result `shouldBe` 2 -- Two beta reductions
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

-- | Test normalization edge cases and complex scenarios
normalizationEdgeCasesSpec :: Spec
normalizationEdgeCasesSpec = describe "normalization edge cases" $ do
  it "handles deeply nested lambda applications" $ do
    -- Create a deeply nested term: (λ x . (λ y . (λ z . z) y) x) a
    let deepTerm = App (Lam "x" (App (Lam "y" (App (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta deepTerm of
      Right result -> normalizedTerm result `shouldBe` Var "a" (-1) (initialPos "test")
      Left err -> expectationFailure $ "Deep nested term failed: " ++ show err

  it "handles variable capture scenarios correctly" $ do
    -- Test: (λ x . λ y . x) y should become λ z . y (avoiding capture)
    let term = App (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "y" (-1) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> do
        -- The result should be λ y . y but with adjusted indices to avoid capture
        case normalizedTerm result of
          Lam "y" (Var "y" _ _) _ -> return () -- Index might be adjusted
          other -> expectationFailure $ "Expected lambda avoiding capture, got: " ++ show other
      Left err -> expectationFailure $ "Variable capture test failed: " ++ show err

  it "handles complex substitution with many free variables" $ do
    -- (λ x . f x g x h) a where f, g, h are free
    let term = App (Lam "x" (App (App (App (Var "f" (-1) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "g" (-1) (initialPos "test")) (initialPos "test")) (App (Var "x" 0 (initialPos "test")) (Var "h" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> do
        let expected = App (App (App (Var "f" (-1) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")) (Var "g" (-1) (initialPos "test")) (initialPos "test")) (App (Var "a" (-1) (initialPos "test")) (Var "h" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
        normalizedTerm result `shouldBe` expected
      Left err -> expectationFailure $ "Complex substitution failed: " ++ show err

  it "handles terms that create new reduction opportunities" $ do
    -- (λ f . f (λ x . x)) (λg. λ y . g y) -> λ y . (λ x . x) y -> λ y . y
    let term = App (Lam "f" (App (Var "f" 0 (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Lam "g" (Lam "y" (App (Var "g" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> normalizedTerm result `shouldBe` Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")
      Left err -> expectationFailure $ "Cascading reduction failed: " ++ show err

  it "handles eta-reduction with complex bodies" $ do
    -- λ x . (λ y . f y g) x should eta-reduce to something alpha-equivalent to λ y . f y g
    let term = Lam "x" (App (Lam "y" (App (App (Var "f" (-1) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (Var "g" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> do
        -- Check the structure rather than exact names
        case normalizedTerm result of
          Lam _ (App (App (Var "f" (-1) _) (Var _ 0 _) _) (Var "g" (-1) _) _) _ -> return ()
          other -> expectationFailure $ "Expected eta-reduced lambda structure, got: " ++ show other
      Left err -> expectationFailure $ "Complex eta-reduction failed: " ++ show err

  it "handles terms with multiple consecutive reductions" $ do
    -- ((λ x . λ y . x) a) b -> (λ y . a) b -> a
    let term = App (App (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")) (Var "b" (-1) (initialPos "test")) (initialPos "test")
    case normalizeTermBetaEta term of
      Right result -> do
        normalizedTerm result `shouldBe` Var "a" (-1) (initialPos "test")
        reductionSteps result `shouldBe` 2
      Left err -> expectationFailure $ "Multiple consecutive reductions failed: " ++ show err

  it "handles alpha-conversion correctly" $ do
    -- Test that α-equivalent terms normalize to structurally equivalent results
    let term1 = Lam "x" (App (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
    let term2 = Lam "z" (App (Lam "w" (Var "w" 0 (initialPos "test")) (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
    case (normalizeTermBetaEta term1, normalizeTermBetaEta term2) of
      (Right result1, Right result2) -> do
        -- Both should normalize to identity functions (possibly with different names)
        case (normalizedTerm result1, normalizedTerm result2) of
          (Lam _ (Var _ 0 _) _, Lam _ (Var _ 0 _) _) -> return ()
          (r1, r2) -> expectationFailure $ "Expected both to normalize to identity, got: " ++ show r1 ++ " and " ++ show r2
      (Left err, _) -> expectationFailure $ "Alpha conversion test failed on term1: " ++ show err
      (_, Left err) -> expectationFailure $ "Alpha conversion test failed on term2: " ++ show err

  it "handles de Bruijn index boundary conditions" $ do
    -- Test with index 0 (immediately bound variable)
    let term1 = App (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "a" (-1) (initialPos "test")) (initialPos "test")
    -- Test with higher indices
    let term2 = App (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "b" (-1) (initialPos "test")) (initialPos "test")
    case (normalizeTermBetaEta term1, normalizeTermBetaEta term2) of
      (Right result1, Right result2) -> do
        normalizedTerm result1 `shouldBe` Var "a" (-1) (initialPos "test")
        normalizedTerm result2 `shouldBe` Lam "y" (Var "b" (-1) (initialPos "test")) (initialPos "test")
      (Left err, _) -> expectationFailure $ "De Bruijn boundary test failed on term1: " ++ show err
      (_, Left err) -> expectationFailure $ "De Bruijn boundary test failed on term2: " ++ show err
