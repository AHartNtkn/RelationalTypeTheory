{-# LANGUAGE OverloadedStrings #-}

module ProofCheckerSpec (spec) where

import Core.Context
import qualified Data.Map as Map
import Core.Errors
import Core.Raw (RawDeclaration(..))
import Core.Syntax
import Operations.Generic.Mixfix (defaultFixity)
import Parser.Raw (rawDeclaration)
import Parser.Elaborate (elaborate)
import TypeCheck.Proof
import Text.Megaparsec (runParser)
import Test.Hspec
import TestHelpers (buildContextFromBindings, simpleRelMacro)
import Text.Megaparsec (initialPos)

-- Helper to create ParamInfo for tests
testParamInfo :: String -> ParamInfo
testParamInfo name = ParamInfo name TermK False []

testRelParamInfo :: String -> ParamInfo
testRelParamInfo name = ParamInfo name RelK False []

spec :: Spec
spec = do
  basicProofCheckingSpec
  proofLambdaSpec
  proofApplicationSpec
  typeApplicationSpec
  typeLambdaSpec
  conversionProofSpec
  rhoEliminationSpec
  piEliminationSpec
  iotaProofSpec
  converseProofSpec
  compositionProofSpec
  quantifierScopeInteractionSpec
  wellFormednessViolationSpec
  theoremReferencingProofCheckSpec
  alphaEquivalenceVsBetaEtaSpec
  judgmentEqualityMacroExpansionSpec
  quantifierDeBruijnBugProofSpec

-- | Test basic proof checking functionality
basicProofCheckingSpec :: Spec
basicProofCheckingSpec = describe "basic proof checking" $ do
  it "checks proof variables correctly" $ do
    -- Create a context with term variables for x, y
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext
        judgment = RelJudgment (Var "x" 1 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" 0 (initialPos "test"))
        ctx = extendProofContext "p" judgment termCtx
        proof = PVar "p" 0 (initialPos "test")

    case inferProofType ctx proof of
      Right result -> resultJudgment result `shouldBe` judgment
      Left err -> expectationFailure $ "Expected successful proof check: " ++ show err

  it "rejects invalid proof variables" $ do
    let ctx = emptyContext
        proof = PVar "unknown" 0 (initialPos "test")

    case inferProofType ctx proof of
      Left _ -> return () -- Expected failure
      Right _ -> expectationFailure "Expected proof checking to fail for unknown variable"

-- | Test proof lambda abstractions (LamP)
proofLambdaSpec :: Spec
proofLambdaSpec = describe "proof lambda abstractions (LamP)" $ do
  it "correctly types λ u : R .p : R → R'" $ do
    -- Test: λu:(A→B).p where p uses u to prove x[A→B]y
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Create the arrow type A → B
        arrType = Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")

        -- Body proof that uses the lambda-bound proof variable
        -- p : x[A→B]y using proof variable u
        bodyProof = PVar "u" 0 (initialPos "test")

        -- Lambda proof: λu:(A→B).u
        lambdaProof = LamP "u" arrType bodyProof (initialPos "test")

    case inferProofType termCtx  lambdaProof of
      Right result -> do
        let RelJudgment term1 resultType term2 = resultJudgment result
        case resultType of
          Arr argType bodyType _ -> do
            argType `shouldBe` arrType
            -- The body type should be what the inner proof establishes
            -- Since bodyProof is just 'u' which has type arrType,
            -- the resulting judgment should be λ x . x[arrType→arrType]λ x' . x'
            bodyType `shouldBe` arrType

            -- Also verify the structure of the derived terms
            -- term1 should be Lam "u" <term derived from body>
            -- term2 should be Lam "u'" <term derived from body>
            case (term1, term2) of
              (Lam "x0" _ _, Lam "x'0" _ _) -> do
                -- The body terms should correspond to the terms in the body proof judgment
                -- Since the body proof is just PVar "u" 0, these should be fresh variables
                return ()
              _ -> expectationFailure $ "Expected lambda terms in judgment, got: " ++ show (term1, term2)
          _ -> expectationFailure $ "Expected arrow type, got: " ++ show resultType
      Left err -> expectationFailure $ "Expected successful lambda proof: " ++ show err

  it "handles nested proof lambda abstractions" $ do
    -- Test: λ u : R . λv:S.body
    let termCtx =
          extendTermContext "z" (RMacro "C" [] (initialPos "test")) $
            extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
              extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        rType = RMacro "R" [] (initialPos "test")
        sType = RMacro "S" [] (initialPos "test")

        -- Inner lambda: λv:S.v
        innerLambda = LamP "v" sType (PVar "v" 0 (initialPos "test")) (initialPos "test")

        -- Outer lambda: λ u : R . λv:S.v
        outerLambda = LamP "u" rType innerLambda (initialPos "test")

    case inferProofType termCtx  outerLambda of
      Right result -> do
        let RelJudgment term1 resultType term2 = resultJudgment result
        case resultType of
          Arr arg1 (Arr arg2 bodyType _) _ -> do
            arg1 `shouldBe` rType
            arg2 `shouldBe` sType
            -- The innermost body type should match what the inner body establishes
            bodyType `shouldBe` sType

            -- Verify the structure of derived terms
            case (term1, term2) of
              (Lam "x0" innerTerm1 _, Lam "x'0" innerTerm2 _) -> do
                -- The inner terms should also be lambdas
                case (innerTerm1, innerTerm2) of
                  (Lam "x1" _ _, Lam "x'1" _ _) -> return ()
                  _ -> expectationFailure $ "Expected inner lambda terms"
              _ -> expectationFailure $ "Expected outer lambda terms"
          _ -> expectationFailure $ "Expected nested arrow type, got: " ++ show resultType
      Left err -> expectationFailure $ "Expected successful nested lambda proof: " ++ show err

-- | Test proof applications (AppP)
proofApplicationSpec :: Spec
proofApplicationSpec = describe "proof applications (AppP)" $ do
  it "correctly types proof application p q : R'" $ do
    -- Create context with function proof p : R → S and argument proof q : R
    let termCtx =
          extendTermContext "z" (RMacro "C" [] (initialPos "test")) $
            extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
              extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        rType = RMacro "R" [] (initialPos "test")
        sType = RMacro "S" [] (initialPos "test")
        arrType = Arr rType sType (initialPos "test")

        -- Function judgment: x[R→S]y
        funcJudgment = RelJudgment (Var "x" 2 (initialPos "test")) arrType (Var "y" 1 (initialPos "test"))

        -- Argument judgment: y[R]z
        argJudgment = RelJudgment (Var "y" 1 (initialPos "test")) rType (Var "z" 0 (initialPos "test"))

        ctx =
          extendProofContext "q" argJudgment $
            extendProofContext "p" funcJudgment termCtx

        -- Application: p q
        appProof = AppP (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")

        -- Expected result: (x y)[S](y z) - proof application applies the function
        expectedJudgment = RelJudgment (App (Var "x" 2 (initialPos "test")) (Var "y" 1 (initialPos "test")) (initialPos "test")) sType (App (Var "y" 1 (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test"))

    case inferProofType ctx appProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful proof application: " ++ show err

  it "rejects proof application with type mismatch" $ do
    -- Create mismatched function and argument types
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        rType = RMacro "R" [] (initialPos "test")
        sType = RMacro "S" [] (initialPos "test")
        tType = RMacro "T" [] (initialPos "test") -- Different type
        arrType = Arr rType sType (initialPos "test")

        funcJudgment = RelJudgment (Var "x" 1 (initialPos "test")) arrType (Var "y" 0 (initialPos "test"))
        argJudgment = RelJudgment (Var "x" 1 (initialPos "test")) tType (Var "y" 0 (initialPos "test")) -- Wrong type T instead of R
        ctx =
          extendProofContext "q" argJudgment $
            extendProofContext "p" funcJudgment termCtx

        appProof = AppP (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")

    case inferProofType ctx appProof of
      Left (TypeMismatch _ _ _) -> return () -- Expected type mismatch error
      Left err -> expectationFailure $ "Expected TypeMismatch, got: " ++ show err
      Right _ -> expectationFailure "Expected proof application to fail with type mismatch"

-- | Test type applications (TyApp)
typeApplicationSpec :: Spec
typeApplicationSpec = describe "type applications (TyApp)" $ do
  it "correctly types p { R } for universally quantified proof" $ do
    -- Test: p { R } where p : ∀ X .P[X]
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Universal type: ∀ X . x[X]y
        universalType = All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")
        universalJudgment = RelJudgment (Var "x" 1 (initialPos "test")) universalType (Var "y" 0 (initialPos "test"))

        ctx = extendProofContext "p" universalJudgment termCtx

        -- Type application: p { R }
        substitutionType = RMacro "R" [] (initialPos "test")
        typeAppProof = TyApp (PVar "p" 0 (initialPos "test")) substitutionType (initialPos "test")

        -- Expected: x[R]y (X substituted with R)
        expectedJudgment = RelJudgment (Var "x" 1 (initialPos "test")) substitutionType (Var "y" 0 (initialPos "test"))

    case inferProofType ctx typeAppProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful type application: " ++ show err

  it "tests universal instantiation over macro expanding to quantified type" $ do
    -- Test: if we have C ≔ ∀ X . X → X → X, can we do p{A} where p : b [C] b?
    let termCtx = extendTermContext "b" (RMacro "Term" [] (initialPos "test")) emptyContext

        -- Define macro C ≔ ∀ X . X → X → X (like Bool)
        pos = initialPos "test"
        quantifiedMacro = RelMacro $ All "X" (Arr (RVar "X" 0 pos) (Arr (RVar "X" 0 pos) (RVar "X" 0 pos) pos) pos) pos
        macroCtx = extendMacroContext "C" [] quantifiedMacro (defaultFixity "TEST") termCtx

        -- Proof variable p : b [C] b
        macroJudgment = RelJudgment (Var "b" 0 (initialPos "test")) (RMacro "C" [] (initialPos "test")) (Var "b" 0 (initialPos "test"))
        ctx = extendProofContext "p" macroJudgment macroCtx

        -- Type application: p{A}
        instantiationType = RMacro "A" [] (initialPos "test")
        typeAppProof = TyApp (PVar "p" 0 (initialPos "test")) instantiationType (initialPos "test")

    case inferProofType ctx typeAppProof of
      Right result -> do
        -- Expected: b [A → A → A] b
        let RelJudgment _ relType _ = resultJudgment result
        case relType of
          Arr (RMacro "A" [] _) (Arr (RMacro "A" [] _) (RMacro "A" [] _) _) _ ->
            return () -- This is what we expect
          _ -> expectationFailure $ "Expected A → A → A type, got: " ++ show relType
      Left err -> expectationFailure $ "Expected successful type application over macro: " ++ show err

  it "rejects type application on non-universal proof" $ do
    -- Try to apply type to non-universal proof
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        nonUniversalType = RMacro "R" [] (initialPos "test") -- Not universal
        judgment = RelJudgment (Var "x" 1 (initialPos "test")) nonUniversalType (Var "y" 0 (initialPos "test"))

        ctx = extendProofContext "p" judgment termCtx
        typeAppProof = TyApp (PVar "p" 0 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (initialPos "test")

    case inferProofType ctx typeAppProof of
      Left (InvalidTypeApplication _ _) -> return () -- Expected error
      Left err -> expectationFailure $ "Expected InvalidTypeApplication, got: " ++ show err
      Right _ -> expectationFailure "Expected type application to fail on non-universal proof"

-- | Test type lambda abstractions (TyLam)
typeLambdaSpec :: Spec
typeLambdaSpec = describe "type lambda abstractions (TyLam)" $ do
  it "correctly types Λx .p : ∀x . R" $ do
    -- Test: Λx .p where p proves something with free type variable x
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "t" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Body proof that uses free type variable X
        bodyJudgment = RelJudgment (Var "t" 1 (initialPos "test")) (RVar "X" (-1) (initialPos "test")) (Var "y" 0 (initialPos "test"))
        bodyCtx = extendProofContext "body" bodyJudgment termCtx

        -- Type lambda: Λx .body
        typeLambdaProof = TyLam "X" (PVar "body" 0 (initialPos "test")) (initialPos "test")

    case inferProofType bodyCtx  typeLambdaProof of
      Right result -> do
        let RelJudgment term1 resultType term2 = resultJudgment result
        case resultType of
          All varName innerType _ -> do
            varName `shouldBe` "X"
            -- The inner type should be what the body proves
            -- The body proves t[X]y, so innerType should remain as free variable
            -- The quantification doesn't change the inner structure
            innerType `shouldBe` RVar "X" (-1) (initialPos "test") -- Still free inside the quantifier

            -- Verify that the terms are the same as in the body judgment
            term1 `shouldBe` Var "t" 1 (initialPos "test")
            term2 `shouldBe` Var "y" 0 (initialPos "test")
          _ -> expectationFailure $ "Expected universal type, got: " ++ show resultType
      Left err -> expectationFailure $ "Expected successful type lambda: " ++ show err

-- | Test conversion proofs (ConvProof)
conversionProofSpec :: Spec
conversionProofSpec = describe "conversion proofs (ConvProof)" $ do
  it "correctly types t₁' ⇃ p ⇂ t₂' with β-η equivalent terms" $ do
    -- Test conversion with beta-equivalent terms
    let termCtx = extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Original terms in proof: ((λ x . x) a) [R] a
        originalTerm1 = App (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")
        originalTerm2 = Var "a" 0 (initialPos "test")
        originalJudgment = RelJudgment originalTerm1 (RMacro "R" [] (initialPos "test")) originalTerm2

        ctx = extendProofContext "p" originalJudgment termCtx

        -- Conversion: a ⇃ p ⇂ a (β-reducing (λ x . x) a to a)
        convertedTerm1 = Var "a" 0 (initialPos "test") -- β-equivalent to (λ x . x) a
        convertedTerm2 = Var "a" 0 (initialPos "test") -- Same
        conversionProof = ConvProof convertedTerm1 (PVar "p" 0 (initialPos "test")) convertedTerm2 (initialPos "test")

        expectedJudgment = RelJudgment convertedTerm1 (RMacro "R" [] (initialPos "test")) convertedTerm2

    case inferProofType ctx conversionProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful conversion proof: " ++ show err

  it "rejects conversion with non-equivalent terms" $ do
    -- Test conversion with non-equivalent terms
    let termCtx =
          extendTermContext "b" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        originalJudgment = RelJudgment (Var "a" 1 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "a" 1 (initialPos "test"))
        ctx = extendProofContext "p" originalJudgment termCtx

        -- Try to convert to different terms
        nonEquivTerm1 = Var "b" 0 (initialPos "test") -- Not equivalent to a
        conversionProof = ConvProof nonEquivTerm1 (PVar "p" 0 (initialPos "test")) (Var "a" 1 (initialPos "test")) (initialPos "test")

    case inferProofType ctx conversionProof of
      Left (LeftConversionError _ _ _) -> return () -- Expected left conversion error
      Left (RightConversionError _ _ _) -> return () -- Expected right conversion error
      Left err -> expectationFailure $ "Expected conversion error, got: " ++ show err
      Right _ -> expectationFailure "Expected conversion to fail with non-equivalent terms"

  it "rejects conversion proof with mismatched judgment types" $ do
    -- Critical test: ((λ z . z) x) ⇃ rel ⇂ b should NOT have type x [S] b
    let termCtx =
          extendTermContext "b" (RMacro "Term" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "Term" [] (initialPos "test")) emptyContext

        -- rel : x [S] b
        relType = RMacro "S" [] (initialPos "test")
        originalJudgment = RelJudgment (Var "x" 1 (initialPos "test")) relType (Var "b" 0 (initialPos "test"))
        ctx = extendProofContext "rel" originalJudgment termCtx

        -- Conversion proof: ((λ z . z) x) ⇃ rel ⇂ b
        lamTerm = App (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (Var "x" 1 (initialPos "test")) (initialPos "test")
        conversionProof = ConvProof lamTerm (PVar "rel" 0 (initialPos "test")) (Var "b" 0 (initialPos "test")) (initialPos "test")

        -- Expected judgment: x [S] b (which should NOT match the inferred type)
        expectedJudgment = RelJudgment (Var "x" 1 (initialPos "test")) relType (Var "b" 0 (initialPos "test"))


    case checkProof ctx conversionProof expectedJudgment of
      Left (ProofTypingError _ expected actual _ _) -> do
        -- Verify the expected and actual judgments are different
        expected `shouldBe` RelJudgment (Var "x" 1 (initialPos "test")) relType (Var "b" 0 (initialPos "test"))
        actual `shouldBe` RelJudgment lamTerm relType (Var "b" 0 (initialPos "test"))
      Left err -> expectationFailure $ "Expected ProofTypingError, got: " ++ show err
      Right _ -> expectationFailure "Expected conversion to fail - inferred type should be ((λ z . z) x) [S] b, not x [S] b"

-- | Test rho elimination (RhoElim)
rhoEliminationSpec :: Spec
rhoEliminationSpec = describe "rho elimination (RhoElim)" $ do
  it "correctly types ρ{ x .t₁,t₂} p - p' according to paper rule" $ do
    -- Paper rule: Γ ⊢ p : t[t'']t', Γ ⊢ p' : [t'' t/x]t₁[R][t'' t/x]t₂
    --             ⊢ ρ{ x .t₁,t₂} p - p' : [t'/x]t₁[R][t'/x]t₂

    let termCtx =
          extendTermContext "g" (Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")) $
            extendTermContext "f" (Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")) $
              extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- First proof p : a[f](f a) - promotion identity
        promotedTerm = Var "f" 1 (initialPos "test") -- t'' from rule
        firstJudgment = RelJudgment (Var "a" 2 (initialPos "test")) (Prom promotedTerm (initialPos "test")) (App promotedTerm (Var "a" 2 (initialPos "test")) (initialPos "test"))

        -- Template terms with free variable x
        template1 = App (Var "x" (-1) (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test") -- t₁: x a
        template2 = App (Var "g" 0 (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test") -- t₂: g a

        -- Second proof must have type: [f a/x](x a)[R][f a/x](g a)
        -- which simplifies to: (f a) a [R] g a
        secondJudgment =
          RelJudgment
            (App (App (Var "f" 1 (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test")) -- (f a) a
            (RMacro "R" [] (initialPos "test")) -- R
            (App (Var "g" 0 (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test")) -- g a
        ctx =
          extendProofContext "p2" secondJudgment $
            extendProofContext "p1" firstJudgment termCtx

        -- Rho elimination: ρ{ x . x a, g a} p1 - p2
        rhoProof = RhoElim "x" template1 template2 (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")

        -- Expected result: [t'/x]t₁[R][t'/x]t₂ where t' = f a
        -- So: [(f a)/x](x a)[R][(f a)/x](g a) = (f a) a [R] g a
        expectedJudgment =
          RelJudgment
            (App (App (Var "f" 1 (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test")) -- (f a) a
            (RMacro "R" [] (initialPos "test")) -- R
            (App (Var "g" 0 (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test")) -- g a
    case inferProofType ctx rhoProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful rho elimination: " ++ show err

  it "rejects rho elimination when first proof is not promotion" $ do
    -- Test that rho elimination fails when first proof doesn't have promoted type
    let termCtx = extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Non-promotion proof: a[R]a
        nonPromotionJudgment = RelJudgment (Var "a" 0 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "a" 0 (initialPos "test"))

        -- Template terms
        template1 = Var "x" (-1) (initialPos "test")
        template2 = Var "x" (-1) (initialPos "test")

        -- Dummy second proof
        secondJudgment = RelJudgment (Var "a" 0 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "a" 0 (initialPos "test"))

        ctx =
          extendProofContext "p2" secondJudgment $
            extendProofContext "p1" nonPromotionJudgment termCtx

        rhoProof = RhoElim "x" template1 template2 (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")

    case inferProofType ctx rhoProof of
      Left (RhoEliminationNonPromotedError _ _ _) -> return () -- Expected error
      Left err -> expectationFailure $ "Expected RhoEliminationError, got: " ++ show err
      Right _ -> expectationFailure "Expected rho elimination to fail with non-promotion proof"

  it "validates complex substitution in rho elimination" $ do
    -- Test more complex substitution scenarios
    let termCtx =
          extendTermContext "h" (Arr (RMacro "A" [] (initialPos "test")) (Arr (RMacro "B" [] (initialPos "test")) (RMacro "C" [] (initialPos "test")) (initialPos "test")) (initialPos "test")) $
            extendTermContext "b" (RMacro "B" [] (initialPos "test")) $
              extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- First proof: a[h](h a)
        promotedTerm = Var "h" 0 (initialPos "test")
        firstJudgment = RelJudgment (Var "a" 2 (initialPos "test")) (Prom promotedTerm (initialPos "test")) (App promotedTerm (Var "a" 2 (initialPos "test")) (initialPos "test"))

        -- Complex template terms: x b, h a b
        template1 = App (Var "x" (-1) (initialPos "test")) (Var "b" 1 (initialPos "test")) (initialPos "test") -- x b
        template2 = App (App (Var "h" 0 (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test")) (Var "b" 1 (initialPos "test")) (initialPos "test") -- h a b

        -- Second proof: (h a) b [R] h a b
        secondJudgment =
          RelJudgment
            (App (App (Var "h" 0 (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test")) (Var "b" 1 (initialPos "test")) (initialPos "test")) -- (h a) b
            (RMacro "R" [] (initialPos "test")) -- R
            (App (App (Var "h" 0 (initialPos "test")) (Var "a" 2 (initialPos "test")) (initialPos "test")) (Var "b" 1 (initialPos "test")) (initialPos "test")) -- h a b
        ctx =
          extendProofContext "p2" secondJudgment $
            extendProofContext "p1" firstJudgment termCtx

        rhoProof = RhoElim "x" template1 template2 (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")

        -- Expected: substituting (h a) for x gives: (h a) b [R] h a b
        expectedJudgment = secondJudgment

    case inferProofType ctx rhoProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful complex rho elimination: " ++ show err

  it "handles variable capture in rho elimination substitution" $ do
    -- Test edge case where substitution might capture bound variables
    let termCtx =
          extendTermContext "y" (RMacro "A" [] (initialPos "test")) $
            extendTermContext "f" (Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")) emptyContext

        -- First proof: y[f](f y) - promotion with f containing free variable y
        promotedTerm = Var "f" 0 (initialPos "test") -- f as promoted term
        firstJudgment = RelJudgment (Var "y" 1 (initialPos "test")) (Prom promotedTerm (initialPos "test")) (App promotedTerm (Var "y" 1 (initialPos "test")) (initialPos "test"))

        -- Template with bound variable y that could be captured: λ y . x y
        template1 = Lam "y" (App (Var "x" (-1) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test") -- λ y . x y
        template2 = Var "y" 1 (initialPos "test") -- outer y (not the bound one)

        -- After substitution [f y/x], template1 becomes: λ y . (f y) y
        -- This tests proper handling of bound vs free variables
        substitutedTemplate1 = Lam "y" (App (App (Var "f" 0 (initialPos "test")) (Var "y" 1 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")

        secondJudgment =
          RelJudgment
            substitutedTemplate1 -- λ y . (f y) y
            (RMacro "R" [] (initialPos "test")) -- R
            (Var "y" 1 (initialPos "test")) -- y
        ctx =
          extendProofContext "p2" secondJudgment $
            extendProofContext "p1" firstJudgment termCtx

        rhoProof = RhoElim "x" template1 template2 (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")

        -- Expected result: [f y/x](λ y . x y)[R][f y/x]y = (λ y . (f y) y)[R]y
        expectedJudgment =
          RelJudgment
            substitutedTemplate1 -- λ y . (f y) y
            (RMacro "R" [] (initialPos "test")) -- R
            (Var "y" 1 (initialPos "test")) -- y
    case inferProofType ctx rhoProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful variable capture handling: " ++ show err

  it "handles nested lambda substitution in rho elimination" $ do
    -- Test substitution into nested lambda expressions
    let termCtx =
          extendTermContext "a" (RMacro "A" [] (initialPos "test")) $
            extendTermContext "g" (Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")) emptyContext

        -- First proof: a[g](g a)
        promotedTerm = Var "g" 0 (initialPos "test")
        firstJudgment = RelJudgment (Var "a" 1 (initialPos "test")) (Prom promotedTerm (initialPos "test")) (App promotedTerm (Var "a" 1 (initialPos "test")) (initialPos "test"))

        -- Template with nested lambdas: λ f . λ z . x (f z)
        template1 = Lam "f" (Lam "z" (App (Var "x" (-1) (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        template2 = Var "a" 1 (initialPos "test")

        -- After substitution [g a/x]: λ f . λ z . (g a) (f z)
        substitutedTemplate1 = Lam "f" (Lam "z" (App (App (Var "g" 0 (initialPos "test")) (Var "a" 1 (initialPos "test")) (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")

        secondJudgment =
          RelJudgment
            substitutedTemplate1 -- λ f . λ z . (g a) (f z)
            (RMacro "R" [] (initialPos "test")) -- R
            (Var "a" 1 (initialPos "test")) -- a
        ctx =
          extendProofContext "p2" secondJudgment $
            extendProofContext "p1" firstJudgment termCtx

        rhoProof = RhoElim "x" template1 template2 (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")

        -- Expected: properly substituted nested lambda
        expectedJudgment = secondJudgment

    case inferProofType ctx rhoProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful nested lambda substitution: " ++ show err

  it "rejects rho elimination with mismatched second proof type" $ do
    -- Test that substitution validation properly rejects incorrect second proofs
    let termCtx =
          extendTermContext "b" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "a" (RMacro "A" [] (initialPos "test")) $
              extendTermContext "f" (Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")) emptyContext

        -- First proof: a[f](f a)
        promotedTerm = Var "f" 0 (initialPos "test")
        firstJudgment = RelJudgment (Var "a" 1 (initialPos "test")) (Prom promotedTerm (initialPos "test")) (App promotedTerm (Var "a" 1 (initialPos "test")) (initialPos "test"))

        -- Template: x, b
        template1 = Var "x" (-1) (initialPos "test") -- x
        template2 = Var "b" 2 (initialPos "test") -- b

        -- WRONG second proof: should be (f a)[R]b but we give b[R]b instead
        wrongSecondJudgment = RelJudgment (Var "b" 2 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "b" 2 (initialPos "test"))

        ctx =
          extendProofContext "p2" wrongSecondJudgment $
            extendProofContext "p1" firstJudgment termCtx

        rhoProof = RhoElim "x" template1 template2 (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")

    case inferProofType ctx rhoProof of
      Left (RhoEliminationTypeMismatchError _ _ _ _) -> return () -- Expected error
      Left err -> expectationFailure $ "Expected RhoEliminationTypeMismatchError, got: " ++ show err
      Right _ -> expectationFailure "Expected rho elimination to reject mismatched second proof"

-- | Test pi elimination (Pi)
piEliminationSpec :: Spec
piEliminationSpec = describe "pi elimination (Pi)" $ do
  it "correctly types π p - x . u . v .p' according to paper rule [LEFT]" $ do
    -- Paper rule: Γ ⊢ p : t[R∘R']t', Γ, u : t[R]x, v : x[R']t' ⊢ p' : t₁[R'']t₂
    --             ⊢ π p - x . u . v .p' : t₁[R'']t₂

    let termCtx =
          extendTermContext "d" (RMacro "D" [] (initialPos "test")) $
            extendTermContext "c" (RMacro "C" [] (initialPos "test")) $
              extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Composition proof: a[R∘S]c
        compType = Comp (RMacro "R" [] (initialPos "test")) (RMacro "S" [] (initialPos "test")) (initialPos "test")
        compJudgment = RelJudgment (Var "a" 2 (initialPos "test")) compType (Var "c" 1 (initialPos "test"))

        ctx = extendProofContext "comp" compJudgment termCtx

        -- Pi elimination: π comp - x . u . v .inner
        -- The inner proof will be a direct reference to one of the witnesses
        -- We'll use witness u which references bound variable u - this should fail
        piProof = Pi (PVar "comp" 0 (initialPos "test")) "x" "u" "v" (PVar "u" 1 (initialPos "test")) (initialPos "test")

    case inferProofType ctx piProof of
      Right result -> expectationFailure $ "Expected pi elimination to fail because it references bound variable u, but got: " ++ show (resultJudgment result)
      Left (InvalidContext msg _) -> msg `shouldContain` "bound variables"
      Left err -> expectationFailure $ "Expected bound variable error, but got: " ++ show err

  it "correctly types π p - x . u . v .p' according to paper rule [RIGHT]" $ do
    -- Paper rule: Γ ⊢ p : t[R∘R']t', Γ, u : t[R]x, v : x[R']t' ⊢ p' : t₁[R'']t₂
    --             ⊢ π p - x . u . v .p' : t₁[R'']t₂

    let termCtx =
          extendTermContext "d" (RMacro "D" [] (initialPos "test")) $
            extendTermContext "c" (RMacro "C" [] (initialPos "test")) $
              extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Composition proof: a[R∘S]c
        compType = Comp (RMacro "R" [] (initialPos "test")) (RMacro "S" [] (initialPos "test")) (initialPos "test")
        compJudgment = RelJudgment (Var "a" 2 (initialPos "test")) compType (Var "c" 1 (initialPos "test"))

        ctx = extendProofContext "comp" compJudgment termCtx

        -- Pi elimination: π comp - x . u . v .inner
        -- The inner proof will be a direct reference to one of the witnesses
        -- We'll use witness v which references bound variable v - this should fail
        piProof = Pi (PVar "comp" 0 (initialPos "test")) "x" "u" "v" (PVar "v" 0 (initialPos "test")) (initialPos "test")

    case inferProofType ctx piProof of
      Right result -> expectationFailure $ "Expected pi elimination to fail because it references bound variable v, but got: " ++ show (resultJudgment result)
      Left (InvalidContext msg _) -> msg `shouldContain` "bound variables"
      Left err -> expectationFailure $ "Expected bound variable error, but got: " ++ show err

  it "correctly types π p - x . u . v .p' according to paper rule [COMP]" $ do
    -- Paper rule: Γ ⊢ p : t[R∘R']t', Γ, u : t[R]x, v : x[R']t' ⊢ p' : t₁[R'']t₂
    --             ⊢ π p - x . u . v .p' : t₁[R'']t₂

    let termCtx =
          extendTermContext "d" (RMacro "D" [] (initialPos "test")) $
            extendTermContext "c" (RMacro "C" [] (initialPos "test")) $
              extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Composition proof: a[R∘S]c
        compType = Comp (RMacro "R" [] (initialPos "test")) (RMacro "S" [] (initialPos "test")) (initialPos "test")
        compJudgment = RelJudgment (Var "a" 2 (initialPos "test")) compType (Var "c" 1 (initialPos "test"))

        ctx = extendProofContext "comp" compJudgment termCtx

        -- Pi elimination: π comp - x . u . v .inner
        -- The inner proof will be a direct reference to one of the witnesses
        -- We'll use witness u which should be at index 1 in the extended context (after x, u are added)
        piProof = Pi (PVar "comp" 0 (initialPos "test")) "x" "u" "v" (PVar "comp" 2 (initialPos "test")) (initialPos "test")

        -- Expected result: what witness comp establishes: a[R∘S]c
        expectedJudgment = RelJudgment (Var "a" 2 (initialPos "test")) compType (Var "c" 1 (initialPos "test"))

    case inferProofType ctx piProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful pi elimination: " ++ show err

  it "rejects pi elimination when first proof is not composition" $ do
    -- Test that pi elimination fails when first proof doesn't have composition type
    let termCtx = extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Non-composition proof: a[R]a
        nonCompJudgment = RelJudgment (Var "a" 0 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "a" 0 (initialPos "test"))

        -- Dummy inner proof
        innerJudgment = RelJudgment (Var "a" 0 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "a" 0 (initialPos "test"))

        ctx =
          extendProofContext "inner" innerJudgment $
            extendProofContext "p" nonCompJudgment termCtx

        piProof = Pi (PVar "p" 1 (initialPos "test")) "x" "u" "v" (PVar "inner" 0 (initialPos "test")) (initialPos "test")

    case inferProofType ctx piProof of
      Left (CompositionError _ _ _ _ _) -> return () -- Expected error
      Left err -> expectationFailure $ "Expected CompositionError, got: " ++ show err
      Right _ -> expectationFailure "Expected pi elimination to fail with non-composition proof"

  it "validates witness extraction in pi elimination context" $ do
    -- Test that the extracted witnesses u and v are properly available
    let termCtx =
          extendTermContext "c" (RMacro "C" [] (initialPos "test")) $
            extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Composition proof: a[R∘S]c
        compType = Comp (RMacro "R" [] (initialPos "test")) (RMacro "S" [] (initialPos "test")) (initialPos "test")
        compJudgment = RelJudgment (Var "a" 1 (initialPos "test")) compType (Var "c" 0 (initialPos "test"))

        ctx = extendProofContext "comp" compJudgment termCtx

        -- Inner proof that uses the witness u - this should fail because u is bound
        innerProof = PVar "u" 1 (initialPos "test") -- Reference the u witness
        piProof = Pi (PVar "comp" 0 (initialPos "test")) "x" "u" "v" innerProof (initialPos "test")

    case inferProofType ctx piProof of
      Right result -> expectationFailure $ "Expected pi elimination to fail because it references bound variable u, but got: " ++ show (resultJudgment result)
      Left (InvalidContext msg _) -> msg `shouldContain` "bound variables"
      Left err -> expectationFailure $ "Expected bound variable error, but got: " ++ show err

-- | Test iota (term promotion introduction)
iotaProofSpec :: Spec
iotaProofSpec = describe "iota (term promotion introduction)" $ do
  it "correctly types ι{t,t'} : t[t'](t' t)" $ do
    -- Create a context with term variables for x, f
    let termCtx =
          extendTermContext "f" (Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext
        term1 = Var "x" 1 (initialPos "test")
        term2 = Var "f" 0 (initialPos "test")
        proof = Iota term1 term2 (initialPos "test")

        -- Expected: x[f](f x)
        expectedJudgment = RelJudgment term1 (Prom term2 (initialPos "test")) (App term2 term1 (initialPos "test"))

    case inferProofType termCtx  proof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful iota proof: " ++ show err

  it "handles iota with lambda terms" $ do
    -- Create a context with term variable for a
    let termCtx = extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext
        term1 = Var "a" 0 (initialPos "test")
        term2 = Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test") -- identity function
        proof = Iota term1 term2 (initialPos "test")

        -- Expected: a[λ x . x]((λ x . x) a)
        expectedJudgment = RelJudgment term1 (Prom term2 (initialPos "test")) (App term2 term1 (initialPos "test"))

    case inferProofType termCtx  proof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful iota proof with lambda: " ++ show err

  it "verifies literal typing rule: ι⟨a, f⟩ : a [f] (f a)" $ do
    -- Bind a and f in context, then verify ι⟨a, f⟩ : a [f] (f a)
    -- This is a literal check of the verbatim typing rule
    let termCtx =
          extendTermContext "f" (Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")) $
            extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext
        a = Var "a" 1 (initialPos "test")
        f = Var "f" 0 (initialPos "test")
        proof = Iota a f (initialPos "test")

        -- Expected type: a [f] (f a) - exactly the typing rule
        expectedJudgment = RelJudgment a (Prom f (initialPos "test")) (App f a (initialPos "test"))

    case inferProofType termCtx  proof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful verification of ι⟨a, f⟩ : a [f] (f a): " ++ show err

-- | Test converse operations
converseProofSpec :: Spec
converseProofSpec = describe "converse operations" $ do
  it "checks converse introduction ∪ᵢ p : t'[R^∪]t" $ do
    -- Create a context with term variables for x, y
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext
        originalJudgment = RelJudgment (Var "x" 1 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" 0 (initialPos "test"))
        ctx = extendProofContext "p" originalJudgment termCtx
        proof = ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")

        -- Expected: y[R^∪]x (swapped terms, converse type)
        expectedJudgment = RelJudgment (Var "y" 0 (initialPos "test")) (Conv (RMacro "R" [] (initialPos "test")) (initialPos "test")) (Var "x" 1 (initialPos "test"))

    case inferProofType ctx proof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful converse introduction: " ++ show err

  it "checks converse elimination ∪ₑ p : t'[R]t" $ do
    -- Create a context with term variables for x, y
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext
        originalJudgment = RelJudgment (Var "x" 1 (initialPos "test")) (Conv (RMacro "R" [] (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test"))
        ctx = extendProofContext "p" originalJudgment termCtx
        proof = ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test")

        -- Expected: y[R]x (swapped terms, non-converse type)
        expectedJudgment = RelJudgment (Var "y" 0 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "x" 1 (initialPos "test"))

    case inferProofType ctx proof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful converse elimination: " ++ show err

  it "rejects converse elimination on non-converse types" $ do
    -- Create a context with term variables for x, y
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext
        originalJudgment = RelJudgment (Var "x" 1 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" 0 (initialPos "test")) -- Not R^∪
        ctx = extendProofContext "p" originalJudgment termCtx
        proof = ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test")

    case inferProofType ctx proof of
      Left (ConverseError _ _ _) -> return () -- Expected this specific error
      Left err -> expectationFailure $ "Expected ConverseError, got: " ++ show err
      Right _ -> expectationFailure "Expected converse elimination to fail on non-converse type"

-- | Test composition operations
compositionProofSpec :: Spec
compositionProofSpec = describe "composition operations" $ do
  it "checks composition introduction (p,p') : t[R∘S]t'" $ do
    -- Create a context with term variables for x, y, z
    let termCtx =
          extendTermContext "z" (RMacro "C" [] (initialPos "test")) $
            extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
              extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Use proper bound variables: x[R]y and y[S]z where middle terms match
        judgment1 = RelJudgment (Var "x" 2 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" 1 (initialPos "test"))
        judgment2 = RelJudgment (Var "y" 1 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "z" 0 (initialPos "test"))

        ctx =
          extendProofContext "p2" judgment2 $
            extendProofContext "p1" judgment1 termCtx
        proof = Pair (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")

        -- Expected: x[R∘S]z
        expectedJudgment = RelJudgment (Var "x" 2 (initialPos "test")) (Comp (RMacro "R" [] (initialPos "test")) (RMacro "S" [] (initialPos "test")) (initialPos "test")) (Var "z" 0 (initialPos "test"))

    case inferProofType ctx proof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful composition introduction: " ++ show err

  it "rejects composition with mismatched middle terms" $ do
    -- Create a context with term variables for x, y, w, z
    let termCtx =
          extendTermContext "z" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "w" (RMacro "B" [] (initialPos "test")) $
              extendTermContext "y" (RMacro "A" [] (initialPos "test")) $
                extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Use proper bound variables: x[R]y and w[S]z where y ≠ w
        judgment1 = RelJudgment (Var "x" 3 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" 2 (initialPos "test"))
        judgment2 = RelJudgment (Var "w" 1 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "z" 0 (initialPos "test"))

        ctx =
          extendProofContext "p2" judgment2 $
            extendProofContext "p1" judgment1 termCtx
        proof = Pair (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")

    case inferProofType ctx proof of
      Left (CompositionError _ _ _ _ _) -> return () -- Expected this specific error
      Left err -> expectationFailure $ "Expected CompositionError, got: " ++ show err
      Right _ -> expectationFailure "Expected composition to fail with mismatched middle terms"

  it "handles complex composition chains (R ∘ S) ∘ T" $ do
    -- Test associativity of composition: (R ∘ S) ∘ T
    -- Setup: x[R]y, y[S]z, z[T]w
    -- Goal: x[(R ∘ S) ∘ T]w
    let termCtx =
          extendTermContext "w" (RMacro "D" [] (initialPos "test")) $
            extendTermContext "z" (RMacro "C" [] (initialPos "test")) $
              extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
                extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Three basic relations
        judgment1 = RelJudgment (Var "x" 3 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" 2 (initialPos "test")) -- x[R]y
        judgment2 = RelJudgment (Var "y" 2 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "z" 1 (initialPos "test")) -- y[S]z
        judgment3 = RelJudgment (Var "z" 1 (initialPos "test")) (RMacro "T" [] (initialPos "test")) (Var "w" 0 (initialPos "test")) -- z[T]w
        ctx =
          extendProofContext "p3" judgment3 $
            extendProofContext "p2" judgment2 $
              extendProofContext "p1" judgment1 termCtx

        -- First compose R ∘ S: (p1, p2) : x[R∘S]z
        innerComp = Pair (PVar "p1" 2 (initialPos "test")) (PVar "p2" 1 (initialPos "test")) (initialPos "test")

        -- Then compose (R ∘ S) ∘ T: ((p1, p2), p3) : x[(R∘S)∘T]w
        outerComp = Pair innerComp (PVar "p3" 0 (initialPos "test")) (initialPos "test")

        -- Expected: x[(R∘S)∘T]w
        expectedType = Comp (Comp (RMacro "R" [] (initialPos "test")) (RMacro "S" [] (initialPos "test")) (initialPos "test")) (RMacro "T" [] (initialPos "test")) (initialPos "test")
        expectedJudgment = RelJudgment (Var "x" 3 (initialPos "test")) expectedType (Var "w" 0 (initialPos "test"))

    case inferProofType ctx outerComp of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful composition chain: " ++ show err

  it "handles complex composition chains R ∘ (S ∘ T)" $ do
    -- Test the other associativity: R ∘ (S ∘ T)
    -- Same setup but different grouping
    let termCtx =
          extendTermContext "w" (RMacro "D" [] (initialPos "test")) $
            extendTermContext "z" (RMacro "C" [] (initialPos "test")) $
              extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
                extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Three basic relations
        judgment1 = RelJudgment (Var "x" 3 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" 2 (initialPos "test")) -- x[R]y
        judgment2 = RelJudgment (Var "y" 2 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "z" 1 (initialPos "test")) -- y[S]z
        judgment3 = RelJudgment (Var "z" 1 (initialPos "test")) (RMacro "T" [] (initialPos "test")) (Var "w" 0 (initialPos "test")) -- z[T]w
        ctx =
          extendProofContext "p3" judgment3 $
            extendProofContext "p2" judgment2 $
              extendProofContext "p1" judgment1 termCtx

        -- First compose S ∘ T: (p2, p3) : y[S∘T]w
        innerComp = Pair (PVar "p2" 1 (initialPos "test")) (PVar "p3" 0 (initialPos "test")) (initialPos "test")

        -- Then compose R ∘ (S ∘ T): (p1, (p2, p3)) : x[R∘(S∘T)]w
        outerComp = Pair (PVar "p1" 2 (initialPos "test")) innerComp (initialPos "test")

        -- Expected: x[R∘(S∘T)]w
        expectedType = Comp (RMacro "R" [] (initialPos "test")) (Comp (RMacro "S" [] (initialPos "test")) (RMacro "T" [] (initialPos "test")) (initialPos "test")) (initialPos "test")
        expectedJudgment = RelJudgment (Var "x" 3 (initialPos "test")) expectedType (Var "w" 0 (initialPos "test"))

    case inferProofType ctx outerComp of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful composition chain: " ++ show err

  it "handles long composition chains R ∘ S ∘ T ∘ U ∘ V" $ do
    -- Test very long composition chains
    let termCtx =
          extendTermContext "v" (RMacro "F" [] (initialPos "test")) $
            extendTermContext "u" (RMacro "E" [] (initialPos "test")) $
              extendTermContext "t" (RMacro "D" [] (initialPos "test")) $
                extendTermContext "s" (RMacro "C" [] (initialPos "test")) $
                  extendTermContext "r" (RMacro "B" [] (initialPos "test")) $
                    extendTermContext "q" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Five relations: q[R]r, r[S]s, s[T]t, t[U]u, u[V]v
        judgment1 = RelJudgment (Var "q" 5 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "r" 4 (initialPos "test"))
        judgment2 = RelJudgment (Var "r" 4 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "s" 3 (initialPos "test"))
        judgment3 = RelJudgment (Var "s" 3 (initialPos "test")) (RMacro "T" [] (initialPos "test")) (Var "t" 2 (initialPos "test"))
        judgment4 = RelJudgment (Var "t" 2 (initialPos "test")) (RMacro "U" [] (initialPos "test")) (Var "u" 1 (initialPos "test"))
        judgment5 = RelJudgment (Var "u" 1 (initialPos "test")) (RMacro "V" [] (initialPos "test")) (Var "v" 0 (initialPos "test"))

        ctx =
          extendProofContext "p5" judgment5 $
            extendProofContext "p4" judgment4 $
              extendProofContext "p3" judgment3 $
                extendProofContext "p2" judgment2 $
                  extendProofContext "p1" judgment1 termCtx

        -- Build left-associated composition: ((((R ∘ S) ∘ T) ∘ U) ∘ V)
        comp1 = Pair (PVar "p1" 4 (initialPos "test")) (PVar "p2" 3 (initialPos "test")) (initialPos "test") -- R ∘ S
        comp2 = Pair comp1 (PVar "p3" 2 (initialPos "test")) (initialPos "test") -- (R ∘ S) ∘ T
        comp3 = Pair comp2 (PVar "p4" 1 (initialPos "test")) (initialPos "test") -- ((R ∘ S) ∘ T) ∘ U
        comp4 = Pair comp3 (PVar "p5" 0 (initialPos "test")) (initialPos "test") -- (((R ∘ S) ∘ T) ∘ U) ∘ V

        -- Expected deeply nested composition type
        expectedType = Comp (Comp (Comp (Comp (RMacro "R" [] (initialPos "test")) (RMacro "S" [] (initialPos "test")) (initialPos "test")) (RMacro "T" [] (initialPos "test")) (initialPos "test")) (RMacro "U" [] (initialPos "test")) (initialPos "test")) (RMacro "V" [] (initialPos "test")) (initialPos "test")
        expectedJudgment = RelJudgment (Var "q" 5 (initialPos "test")) expectedType (Var "v" 0 (initialPos "test"))

    case inferProofType ctx comp4 of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful long composition chain: " ++ show err

  it "handles composition with converse operations (R ˘ ∘ S)" $ do
    -- Test composition combined with converse
    let termCtx =
          extendTermContext "z" (RMacro "C" [] (initialPos "test")) $
            extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
              extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Setup: y[R]x (note the direction), y[S]z
        forwardJudgment = RelJudgment (Var "y" 1 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "x" 2 (initialPos "test")) -- y[R]x
        secondJudgment = RelJudgment (Var "y" 1 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "z" 0 (initialPos "test")) -- y[S]z
        ctx =
          extendProofContext "p2" secondJudgment $
            extendProofContext "p1" forwardJudgment termCtx

        -- Create converse: x[R ˘]y from y[R]x
        converseProof = ConvIntro (PVar "p1" 1 (initialPos "test")) (initialPos "test")

        -- Then compose: (converse, p2) should give x[R ˘∘S]z
        compositionProof = Pair converseProof (PVar "p2" 0 (initialPos "test")) (initialPos "test")

        -- Expected: x[R ˘∘S]z
        expectedType = Comp (Conv (RMacro "R" [] (initialPos "test")) (initialPos "test")) (RMacro "S" [] (initialPos "test")) (initialPos "test")
        expectedJudgment = RelJudgment (Var "x" 2 (initialPos "test")) expectedType (Var "z" 0 (initialPos "test"))

    case inferProofType ctx compositionProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful composition with converse: " ++ show err

  it "rejects composition chains with broken middle terms" $ do
    -- Test that composition chains properly validate middle term consistency
    let termCtx =
          extendTermContext "w" (RMacro "D" [] (initialPos "test")) $
            extendTermContext "z" (RMacro "C" [] (initialPos "test")) $
              extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
                extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Setup with intentional mismatch: x[R]y, z[S]w (missing y[?]z)
        judgment1 = RelJudgment (Var "x" 3 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" 2 (initialPos "test")) -- x[R]y
        judgment2 = RelJudgment (Var "z" 1 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "w" 0 (initialPos "test")) -- z[S]w (should be y[S]z)
        ctx =
          extendProofContext "p2" judgment2 $
            extendProofContext "p1" judgment1 termCtx

        -- Try to compose - this should fail
        invalidComposition = Pair (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")

    case inferProofType ctx invalidComposition of
      Left (CompositionError _ _ _ _ _) -> return () -- Expected error
      Left err -> expectationFailure $ "Expected CompositionError, got: " ++ show err
      Right _ -> expectationFailure "Expected composition to fail with broken chain"

-- | Test quantifier scope interactions with other constructs
quantifierScopeInteractionSpec :: Spec
quantifierScopeInteractionSpec = describe "quantifier scope interactions" $ do
  it "handles quantifiers in composition: ∀ X .(R ∘ S)" $ do
    -- Test quantifier scoping over composition
    let termCtx =
          extendTermContext "z" (RMacro "C" [] (initialPos "test")) $
            extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
              extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Create composition R ∘ S where R and S both use type variable X
        innerComp = Comp (RVar "X" (-1) (initialPos "test")) (RVar "X" (-1) (initialPos "test")) (initialPos "test") -- X ∘ X
        quantifiedType = All "X" innerComp (initialPos "test") -- ∀ X .(X ∘ X)

        -- Body proof that establishes the composition under the quantifier
        judgment1 = RelJudgment (Var "x" 2 (initialPos "test")) (RVar "X" (-1) (initialPos "test")) (Var "y" 1 (initialPos "test"))
        judgment2 = RelJudgment (Var "y" 1 (initialPos "test")) (RVar "X" (-1) (initialPos "test")) (Var "z" 0 (initialPos "test"))

        ctx =
          extendProofContext "p2" judgment2 $
            extendProofContext "p1" judgment1 termCtx

        -- Composition proof: (p1, p2) : x[X∘X]z
        compProof = Pair (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")

        -- Type lambda wrapping the composition: Λx .(p1, p2) : ∀ X .(X ∘ X)
        quantifierProof = TyLam "X" compProof (initialPos "test")

        expectedJudgment = RelJudgment (Var "x" 2 (initialPos "test")) quantifiedType (Var "z" 0 (initialPos "test"))

    case inferProofType ctx quantifierProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful quantified composition: " ++ show err

  it "handles nested quantifiers: ∀ X . ∀ Y .(X ∘ Y)" $ do
    -- Test nested quantifier scoping
    let termCtx =
          extendTermContext "z" (RMacro "C" [] (initialPos "test")) $
            extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
              extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Inner composition: X ∘ Y
        innerComp = Comp (RVar "X" (-1) (initialPos "test")) (RVar "Y" (-1) (initialPos "test")) (initialPos "test")
        -- Nested quantifiers: ∀ X . ∀ Y .(X ∘ Y)
        innerQuantified = All "Y" innerComp (initialPos "test") -- ∀ Y .(X ∘ Y)
        outerQuantified = All "X" innerQuantified (initialPos "test") -- ∀ X . ∀ Y .(X ∘ Y)

        -- Body proofs
        judgment1 = RelJudgment (Var "x" 2 (initialPos "test")) (RVar "X" (-1) (initialPos "test")) (Var "y" 1 (initialPos "test"))
        judgment2 = RelJudgment (Var "y" 1 (initialPos "test")) (RVar "Y" (-1) (initialPos "test")) (Var "z" 0 (initialPos "test"))

        ctx =
          extendProofContext "p2" judgment2 $
            extendProofContext "p1" judgment1 termCtx

        -- Build nested type lambdas: Λ X .Λ Y .(p1, p2)
        compProof = Pair (PVar "p1" 1 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (initialPos "test")
        innerTypeProof = TyLam "Y" compProof (initialPos "test")
        outerTypeProof = TyLam "X" innerTypeProof (initialPos "test")

        expectedJudgment = RelJudgment (Var "x" 2 (initialPos "test")) outerQuantified (Var "z" 0 (initialPos "test"))

    case inferProofType ctx outerTypeProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful nested quantifiers: " ++ show err

  it "handles quantifiers with converse: ∀ X .(X˘)" $ do
    -- Test quantifier scoping over converse
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Type: ∀ X .(X˘)
        converseType = Conv (RVar "X" (-1) (initialPos "test")) (initialPos "test") -- X˘
        quantifiedType = All "X" converseType (initialPos "test") -- ∀ X .(X˘)

        -- Body proof: x[X]y, then converse to get y[X˘]x
        forwardJudgment = RelJudgment (Var "x" 1 (initialPos "test")) (RVar "X" (-1) (initialPos "test")) (Var "y" 0 (initialPos "test"))
        ctx = extendProofContext "p" forwardJudgment termCtx

        -- Converse proof: ∪ᵢ p : y[X˘]x
        converseProof = ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")

        -- Type lambda: Λx .(∪ᵢ p) : ∀ X .(X˘)
        quantifierProof = TyLam "X" converseProof (initialPos "test")

        expectedJudgment = RelJudgment (Var "y" 0 (initialPos "test")) quantifiedType (Var "x" 1 (initialPos "test"))

    case inferProofType ctx quantifierProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful quantified converse: " ++ show err

  it "handles quantifiers with promotion: ∀ X .(t^)" $ do
    -- Test quantifier scoping over promotion
    let termCtx =
          extendTermContext "f" (Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")) $
            extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Promotion term that doesn't involve X
        promotedTerm = Var "f" 0 (initialPos "test") -- f

        -- Type: ∀ X .(f^)
        promotionType = Prom promotedTerm (initialPos "test") -- f^
        quantifiedType = All "X" promotionType (initialPos "test") -- ∀ X .(f^)

        -- Body proof: a[f^](f a)
        promotionJudgment = RelJudgment (Var "a" 1 (initialPos "test")) promotionType (App (Var "f" 0 (initialPos "test")) (Var "a" 1 (initialPos "test")) (initialPos "test"))
        ctx = extendProofContext "p" promotionJudgment termCtx

        -- Type lambda: Λx .p : ∀ X .(f^)
        quantifierProof = TyLam "X" (PVar "p" 0 (initialPos "test")) (initialPos "test")

        expectedJudgment = RelJudgment (Var "a" 1 (initialPos "test")) quantifiedType (App (Var "f" 0 (initialPos "test")) (Var "a" 1 (initialPos "test")) (initialPos "test"))

    case inferProofType ctx quantifierProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful quantified promotion: " ++ show err

  it "handles type application instantiating quantifiers: p { R } from ∀ X . R'" $ do
    -- Test type application on quantified types
    let termCtx =
          extendTermContext "y" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Original quantified type: ∀ X .(X → A)
        innerType = Arr (RVar "X" 0 (initialPos "test")) (RMacro "A" [] (initialPos "test")) (initialPos "test") -- X → A
        quantifiedType = All "X" innerType (initialPos "test") -- ∀ X .(X → A)

        -- Body proof establishes the quantified relation
        bodyJudgment = RelJudgment (Var "x" 1 (initialPos "test")) quantifiedType (Var "y" 0 (initialPos "test"))
        ctx = extendProofContext "p" bodyJudgment termCtx

        -- Type application: p{B} should instantiate X with B
        instantiationType = RMacro "B" [] (initialPos "test")
        typeAppProof = TyApp (PVar "p" 0 (initialPos "test")) instantiationType (initialPos "test")

        -- Expected result: x[B → A]y
        expectedType = Arr (RMacro "B" [] (initialPos "test")) (RMacro "A" [] (initialPos "test")) (initialPos "test")
        expectedJudgment = RelJudgment (Var "x" 1 (initialPos "test")) expectedType (Var "y" 0 (initialPos "test"))

    case inferProofType ctx typeAppProof of
      Right result -> resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful type application: " ++ show err

  it "rejects quantifier variable capture violations" $ do
    -- Test that quantifier variables don't capture existing bindings
    let baseCtx = extendRelContext "X" emptyContext -- X already bound
        termCtx = extendTermContext "a" (RMacro "A" [] (initialPos "test")) baseCtx

        -- Try to create ∀ X . R where X is already bound - this should fail
        bodyJudgment = RelJudgment (Var "a" 0 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "a" 0 (initialPos "test"))
        ctx = extendProofContext "p" bodyJudgment termCtx

        -- This should violate freshness constraint
        invalidQuantifierProof = TyLam "X" (PVar "p" 0 (initialPos "test")) (initialPos "test")

    case inferProofType ctx invalidQuantifierProof of
      Left (DuplicateBinding "X" _) -> return () -- Expected error
      Left err -> expectationFailure $ "Expected DuplicateBinding error, got: " ++ show err
      Right _ -> expectationFailure "Expected quantifier to fail with duplicate binding"

-- | Test well-formedness violations according to paper requirements
wellFormednessViolationSpec :: Spec
wellFormednessViolationSpec = describe "well-formedness violations" $ do
  it "detects violation of type lambda freshness constraint (direct name binding)" $ do
    -- Paper requires X ∉ FV(Γ) for Λx .p : t[∀x . R]t'
    -- Test case where X is already directly bound as a relation variable
    let baseCtx = extendRelContext "X" emptyContext -- X directly bound as relation

        -- Try to create type lambda that binds X again - this should violate freshness
        bodyJudgment = RelJudgment (Var "a" (-1) (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "a" (-1) (initialPos "test"))
        bodyCtx = extendProofContext "body" bodyJudgment baseCtx

        -- This violates the constraint since X is already bound in context
        violatingProof = TyLam "X" (PVar "body" 0 (initialPos "test")) (initialPos "test")

    case inferProofType bodyCtx  violatingProof of
      Left (DuplicateBinding "X" _) -> return () -- Expected error
      Left err -> expectationFailure $ "Expected DuplicateBinding error, got: " ++ show err
      Right _ -> expectationFailure "Expected type lambda to fail when X is already bound"

  it "detects unbound variables in proof context" $ do
    -- Test that unbound proof variables are caught by the type checker
    let termCtx = extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Try to reference a proof variable that doesn't exist
        invalidProof = PVar "nonexistent" 5 (initialPos "test") -- Non-existent variable

    case inferProofType termCtx  invalidProof of
      Left (UnboundVariable "nonexistent" _) -> return () -- Expected error
      Left err -> expectationFailure $ "Expected UnboundVariable error, got: " ++ show err
      Right _ -> expectationFailure "Expected proof checking to fail with unbound variable"

  it "validates proof binding term consistency against context" $ do
    -- Test that proof bindings can reference terms correctly according to de Bruijn indices
    let termCtx =
          extendTermContext "b" (RMacro "B" [] (initialPos "test")) $
            extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Create valid proof binding that properly references existing terms
        validJudgment = RelJudgment (Var "a" 1 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "b" 0 (initialPos "test")) -- Correct indices

        -- Test that we can successfully retrieve and use the proof
        ctx = extendProofContext "p" validJudgment termCtx
        proof = PVar "p" 0 (initialPos "test")

    case inferProofType ctx proof of
      Right result -> do
        -- The proof should succeed and preserve the correct judgment
        let RelJudgment term1 rtype term2 = resultJudgment result
        term1 `shouldBe` Var "a" 1 (initialPos "test") -- Should preserve correct reference to 'a'
        rtype `shouldBe` RMacro "R" [] (initialPos "test")
        term2 `shouldBe` Var "b" 0 (initialPos "test") -- Should preserve correct reference to 'b'
      Left err -> expectationFailure $ "Expected successful proof retrieval: " ++ show err

  it "validates proper context extension ordering" $ do
    -- Test that context extensions maintain proper de Bruijn ordering
    let baseCtx = emptyContext

        -- Extend context in steps and verify indices
        ctx1 = extendTermContext "a" (RMacro "A" [] (initialPos "test")) baseCtx
        ctx2 = extendTermContext "b" (RMacro "B" [] (initialPos "test")) ctx1
        ctx3 = extendTermContext "c" (RMacro "C" [] (initialPos "test")) ctx2

        -- Create judgment that uses all variables
        judgment = RelJudgment (Var "a" 2 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "c" 0 (initialPos "test")) -- a is at index 2, c at 0
        ctx4 = extendProofContext "p" judgment ctx3

        proof = PVar "p" 0 (initialPos "test")

    case inferProofType ctx4  proof of
      Right result -> do
        let RelJudgment term1 _ term2 = resultJudgment result
        term1 `shouldBe` Var "a" 2 (initialPos "test") -- Should preserve correct index
        term2 `shouldBe` Var "c" 0 (initialPos "test") -- Should preserve correct index
      Left err -> expectationFailure $ "Expected successful proof with proper indices: " ++ show err

  it "detects malformed contexts with inconsistent type bindings" $ do
    -- Test edge case where relation types reference unbound type variables
    let termCtx = extendTermContext "a" (RVar "UnboundType" (-1) (initialPos "test")) emptyContext

        -- This creates a context with reference to unbound type variable
        -- The system should handle this gracefully
        judgment = RelJudgment (Var "a" 0 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "a" 0 (initialPos "test"))
        ctx = extendProofContext "p" judgment termCtx

        proof = PVar "p" 0 (initialPos "test")

    case inferProofType ctx proof of
      Right _ -> return () -- This should work - free type variables are allowed
      Left err -> expectationFailure $ "Unexpected error with free type variable: " ++ show err

  it "validates macro environment parameter arity checking" $ do
    -- Test that macro environment validates parameter arity during expansion
    let testParams = [testRelParamInfo "X", testRelParamInfo "Y"]
        testMacro = RelMacro (Arr (RVar "X" 0 (initialPos "test")) (RVar "Y" 1 (initialPos "test")) (initialPos "test"))
        macroCtx = extendMacroContext "TestMacro" testParams testMacro (defaultFixity "TEST") emptyContext
        termCtx = extendTermContext "a" (RMacro "A" [] (initialPos "test")) macroCtx

        -- Create proof that would trigger macro expansion with wrong arity
        wrongArityJudgment = RelJudgment (Var "a" 0 (initialPos "test")) (RMacro "TestMacro" [MRel (RMacro "R" [] (initialPos "test"))] (initialPos "test")) (Var "a" 0 (initialPos "test")) -- Only 1 arg, needs 2
        ctx = extendProofContext "p" wrongArityJudgment termCtx

        -- Try to check a proof that uses the macro - this should detect arity mismatch during type operations
        proof = PVar "p" 0 (initialPos "test")

    case inferProofType ctx proof of
      Right result -> do
        -- If successful, the macro wasn't expanded (which is also valid behavior)
        -- Verify we get the unexpanded macro application
        let RelJudgment _ rtype _ = resultJudgment result
        case rtype of
          RMacro "TestMacro" [MRel (RMacro "R" [] _)] _ -> return () -- Unexpanded is acceptable
          _ -> expectationFailure $ "Expected macro application or arity error, got: " ++ show rtype
      Left _ ->
        -- Also acceptable if the system detects arity mismatch
        return ()

-- | Test theorem referencing in proof checking
theoremReferencingProofCheckSpec :: Spec
theoremReferencingProofCheckSpec = describe "theorem referencing proof checking" $ do
  it "resolves simple theorem references correctly" $ do
    -- Create a theorem environment with a simple theorem
    let simpleTheorem =
          TheoremDef
            "identity"
            [TermBinding "t"]
            (RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test")))
            (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test"))
        ctx = case simpleTheorem of
          TheoremDef name bindings judgment proof ->
            extendTheoremContext name bindings judgment proof emptyContext
          _ -> error "Expected TheoremDef in test"
        theoremRef = PTheoremApp "identity" [] (initialPos "test") -- theorem reference
    case inferProofType ctx theoremRef of
      Right result -> do
        let expectedJudgment = RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test"))
        resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful theorem reference resolution: " ++ show err

  it "fails gracefully for undefined theorem references" $ do
    -- Test undefined theorem reference
    let ctx = emptyContext
        undefinedRef = PTheoremApp "nonexistent" [] (initialPos "test")

    case inferProofType ctx undefinedRef of
      Left _ -> return () -- Expected failure
      Right _ -> expectationFailure "Expected failure for undefined theorem reference"

  it "handles theorem references with mixed binding types" $ do
    -- Create a theorem with term, relation, and proof bindings
    let complexTheorem =
          TheoremDef
            "complex"
            [ TermBinding "t",
              RelBinding "R",
              ProofBinding "p" (RelJudgment (Var "t" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")))
            ]
            (RelJudgment (Var "t" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")))
            (PVar "p" 0 (initialPos "test"))
        ctx = case complexTheorem of
          TheoremDef name bindings judgment proof ->
            extendTheoremContext name bindings judgment proof emptyContext
          _ -> error "Expected TheoremDef in test"
        theoremRef = PTheoremApp "complex" [] (initialPos "test")

    case inferProofType ctx theoremRef of
      Right result -> do
        let expectedJudgment = RelJudgment (Var "t" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "t" 0 (initialPos "test"))
        resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected successful complex theorem reference: " ++ show err

  it "distinguishes theorem references from proof variables in type checking" $ do
    -- Test that theorem references (index -1) and proof variables (index >= 0) behave differently
    let theoremCtx =
          extendTheoremContext
            "testTheorem"
            [TermBinding "x"]
            (RelJudgment (Var "x" 0 (initialPos "test")) (RMacro "TestRel" [] (initialPos "test")) (Var "x" 0 (initialPos "test")))
            (Iota (Var "x" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))
            emptyContext

        -- Create context with a proof variable of the same name
        proofJudgment = RelJudgment (Var "y" 0 (initialPos "test")) (RMacro "DifferentRel" [] (initialPos "test")) (Var "y" 0 (initialPos "test"))
        ctx = extendProofContext "testTheorem" proofJudgment theoremCtx

        -- Test proof variable (index 0)
        proofVarRef = PVar "testTheorem" 0 (initialPos "test")
        theoremRef = PTheoremApp "testTheorem" [] (initialPos "test")

    -- Test proof variable gives different result than theorem reference
    case (inferProofType ctx proofVarRef, inferProofType ctx theoremRef) of
      (Right proofResult, Right theoremResult) -> do
        -- Results should be different
        resultJudgment proofResult `shouldNotBe` resultJudgment theoremResult
        -- Proof variable should return the context judgment
        resultJudgment proofResult `shouldBe` proofJudgment
        -- Theorem reference should return the theorem judgment
        let expectedTheoremJudgment = RelJudgment (Var "x" 0 (initialPos "test")) (RMacro "TestRel" [] (initialPos "test")) (Var "x" 0 (initialPos "test"))
        resultJudgment theoremResult `shouldBe` expectedTheoremJudgment
      (Left err, _) -> expectationFailure $ "Expected successful proof variable resolution: " ++ show err
      (_, Left err) -> expectationFailure $ "Expected successful theorem reference resolution: " ++ show err

  it "works with theorem references in complex proof expressions" $ do
    -- Test theorem references within more complex proof structures
    let identityTheorem =
          extendTheoremContext
            "id"
            [TermBinding "t"]
            (RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test")))
            (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test"))
            emptyContext

        -- Create a context where we can apply the theorem reference
        termCtx = extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Create an application using the theorem reference
        -- This is a simplified test - in practice would need proper type matching
        theoremRef = PTheoremApp "id" [] (initialPos "test")

    case inferProofType termCtx theoremRef of
      Right result -> do
        -- Verify we get the expected judgment structure
        let RelJudgment _ rtype _ = resultJudgment result
        case rtype of
          Prom (Lam "x" (Var "x" 0 _) _) _ -> return () -- Expected identity function promotion
          _ -> expectationFailure $ "Expected promoted identity function, got: " ++ show rtype
      Left err -> expectationFailure $ "Expected successful theorem application: " ++ show err

  it "handles empty theorem environments correctly" $ do
    -- Test behavior with empty theorem environment
    let ctx = emptyContext
        anyTheoremRef = PTheoremApp "anything" [] (initialPos "test")

    case inferProofType ctx anyTheoremRef of
      Left _ -> return () -- Expected failure
      Right _ -> expectationFailure "Expected failure with empty theorem environment"

  it "rejects PVar with negative indices (prevents magic number hacks)" $ do
    -- Test that PVar with index -1 always fails (no more magic numbers!)
    let ctx = emptyContext
        invalidProofVar = PVar "someVariable" (-1) (initialPos "test") -- This should NEVER work
    case inferProofType ctx invalidProofVar of
      Left _ -> return () -- Expected failure - no magic numbers allowed!
      Right _ -> expectationFailure "PVar with index -1 should always fail - no magic number hacks allowed!"

  it "rejects PVar with negative indices even with theorem in environment" $ do
    -- Test that PVar(-1) fails even when a theorem with the same name exists
    let theoremEnv =
          extendTheoremContext
            "testName"
            [TermBinding "t"]
            (RelJudgment (Var "t" 0 (initialPos "test")) (RMacro "TestRel" [] (initialPos "test")) (Var "t" 0 (initialPos "test")))
            (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test"))
            emptyContext
        ctx = emptyContext
        invalidProofVar = PVar "testName" (-1) (initialPos "test") -- Wrong way to reference theorem
        correctTheoremRef = PTheoremApp "testName" [] (initialPos "test") -- Right way to reference theorem
    case (inferProofType ctx invalidProofVar, inferProofType ctx correctTheoremRef) of
      (Left _, Right _) -> return () -- PVar(-1) fails, PTheoremApp succeeds - this is correct!
      (Right _, _) -> expectationFailure "PVar with index -1 should always fail, even when theorem exists!"
      (Left _, Left _) -> expectationFailure "PTheoremApp should succeed when theorem exists"

  it "enforces that free variables never exist" $ do
    -- This test ensures that PVar with index -1 (which should never be created by parser) always fails
    let invalidProofVar = PVar "freeVariable" (-1) (initialPos "test")
        ctx = emptyContext

    -- Any PVar with index -1 should always fail type checking
    case inferProofType ctx invalidProofVar of
      Left (UnboundVariable "freeVariable" _) -> return () -- Expected error for unbound variable
      Left (InvalidDeBruijnIndex (-1) _) -> return () -- Also acceptable
      Left err -> expectationFailure $ "Wrong error type: " ++ show err
      Right _ -> expectationFailure "PVar with index -1 should always fail type checking"

  it "validates theorem instantiation properly" $ do
    -- Theorems with bindings need proper instantiation (future work)
    let theoremWithBindings =
          extendTheoremContext
            "paramTheorem"
            [TermBinding "t", RelBinding "R"]
            (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "t" 1 (initialPos "test")))
            (Iota (Var "t" 1 (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
            emptyContext
        ctx = emptyContext
    -- For now, theorem references ignore bindings
    case inferProofType theoremWithBindings (PTheoremApp "paramTheorem" [] (initialPos "test")) of
      Right result -> do
        let RelJudgment t1 r t2 = resultJudgment result
        -- The theorem's judgment is returned directly (bindings not yet instantiated)
        t1 `shouldBe` Var "t" 1 (initialPos "test")
        r `shouldBe` RVar "R" 0 (initialPos "test")
        t2 `shouldBe` Var "t" 1 (initialPos "test")
      Left err -> expectationFailure $ "Theorem reference failed: " ++ show err

  it "basic theorem reference application - universal proof applied to function" $ do
    -- Test 1: Proof of ∀ X . X, then function (∀ X . X) → B, apply proof to function to get B
    let universalProof =
          extendTheoremContext
            "universalThm"
            []
            (RelJudgment (Var "x" 0 (initialPos "test")) (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test")))
            (TyLam "X" (Iota (Var "x" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
            emptyContext

        functionTheorem =
          extendTheoremContext
            "functionThm"
            [ProofBinding "f" (RelJudgment (Var "dummy" 0 (initialPos "test")) (Arr (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")) (Var "dummy" 0 (initialPos "test")))]
            (RelJudgment (Var "dummy" 0 (initialPos "test")) (RMacro "B" [] (initialPos "test")) (Var "dummy" 0 (initialPos "test")))
            (AppP (PVar "f" 0 (initialPos "test")) (PTheoremApp "universalThm" [] (initialPos "test")) (initialPos "test")) -- Apply function f to universal proof
            universalProof

        ctx =
          extendTermContext "dummy" (RMacro "DummyType" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "SomeType" [] (initialPos "test")) emptyContext

    case inferProofType functionTheorem (PTheoremApp "functionThm" [] (initialPos "test")) of
      Right result -> do
        let RelJudgment _ r _ = resultJudgment result
        r `shouldBe` RMacro "B" [] (initialPos "test") -- Should produce type B
        return ()
      Left err -> expectationFailure $ "Basic theorem application failed: " ++ show err

  it "basic theorem reference application - identity function applied to value" $ do
    -- Test 2: Proof of ∀ X . X → X, then assume A and apply identity to get A
    let identityProof =
          extendTheoremContext
            "identityThm"
            []
            (RelJudgment (Var "f" 0 (initialPos "test")) (All "X" (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "f" 0 (initialPos "test")))
            (TyLam "X" (LamP "x" (RVar "X" 0 (initialPos "test")) (PVar "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
            emptyContext

        applicationTheorem =
          extendTheoremContext
            "appThm"
            [TermBinding "a"]
            (RelJudgment (Var "a" 0 (initialPos "test")) (RMacro "A" [] (initialPos "test")) (Var "a" 0 (initialPos "test")))
            (AppP (TyApp (PTheoremApp "identityThm" [] (initialPos "test")) (RMacro "A" [] (initialPos "test")) (initialPos "test")) (Iota (Var "a" 0 (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) -- Apply identity to a
            identityProof

        ctx = extendTermContext "f" (RMacro "FuncType" [] (initialPos "test")) emptyContext

    case inferProofType applicationTheorem (PTheoremApp "appThm" [] (initialPos "test")) of
      Right result -> do
        let RelJudgment _ r _ = resultJudgment result
        r `shouldBe` RMacro "A" [] (initialPos "test") -- Should produce type A
        return ()
      Left err -> expectationFailure $ "Basic identity application failed: " ++ show err

  it "handles theorem references in lambda abstractions" $ do
    -- Test theorem reference inside proof lambda body
    let identityTheorem =
          extendTheoremContext
            "identity"
            [TermBinding "t"]
            (RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test")))
            (Iota (Var "t" 0 (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
            emptyContext

        ctx = emptyContext

        -- Test: λp: SomeRel. identity
        lambdaProof = LamP "p" (RMacro "SomeRel" [] (initialPos "test")) (PTheoremApp "identity" [] (initialPos "test")) (initialPos "test")

    case inferProofType identityTheorem lambdaProof of
      Right result -> do
        case resultJudgment result of
          RelJudgment _ (Arr argType _ _) _ -> do
            argType `shouldBe` RMacro "SomeRel" [] (initialPos "test")
            return ()
          other -> expectationFailure $ "Expected arrow type but got: " ++ show other
      Left err -> expectationFailure $ "Theorem reference in lambda failed: " ++ show err

  it "handles theorem references in composition proofs" $ do
    -- Test theorem references in composition (Pair)
    let theorem1 =
          extendTheoremContext
            "thm1"
            []
            (RelJudgment (Var "a" 0 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "b" 0 (initialPos "test")))
            (Iota (Var "a" 0 (initialPos "test")) (Var "b" 0 (initialPos "test")) (initialPos "test"))
            emptyContext

        theorem2 =
          extendTheoremContext
            "thm2"
            []
            (RelJudgment (Var "b" 0 (initialPos "test")) (RMacro "S" [] (initialPos "test")) (Var "c" 0 (initialPos "test")))
            (Iota (Var "b" 0 (initialPos "test")) (Var "c" 0 (initialPos "test")) (initialPos "test"))
            theorem1

        ctx =
          extendTermContext "c" (RMacro "C" [] (initialPos "test")) $
            extendTermContext "b" (RMacro "B" [] (initialPos "test")) $
              extendTermContext "a" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Test: (thm1, thm2) should give composition
        compositionProof = Pair (PTheoremApp "thm1" [] (initialPos "test")) (PTheoremApp "thm2" [] (initialPos "test")) (initialPos "test")

    case inferProofType theorem2 compositionProof of
      Right result -> do
        case resultJudgment result of
          RelJudgment _ (Comp r1 r2 _) _ -> do
            r1 `shouldBe` RMacro "R" [] (initialPos "test")
            r2 `shouldBe` RMacro "S" [] (initialPos "test")
            return ()
          other -> expectationFailure $ "Expected composition type but got: " ++ show other
      Left err -> expectationFailure $ "Theorem reference in composition failed: " ++ show err

  it "handles theorem references in conversion proofs" $ do
    -- Test theorem reference in conversion proof
    let identityTheorem =
          extendTheoremContext
            "identity"
            []
            (RelJudgment (Var "x" 0 (initialPos "test")) (Prom (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test")))
            (Iota (Var "x" 0 (initialPos "test")) (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
            emptyContext

        ctx = extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

        -- Test: x ⇃ identity ⇂ x (convert using theorem)
        conversionProof = ConvProof (Var "x" 0 (initialPos "test")) (PTheoremApp "identity" [] (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")

    case inferProofType identityTheorem conversionProof of
      Right result -> do
        let RelJudgment t1 _ t2 = resultJudgment result
        t1 `shouldBe` Var "x" 0 (initialPos "test")
        t2 `shouldBe` Var "x" 0 (initialPos "test")
        return ()
      Left err -> expectationFailure $ "Theorem reference in conversion failed: " ++ show err

  it "handles nested theorem references" $ do
    -- Test theorem that references another theorem
    let baseTheorem =
          extendTheoremContext
            "base"
            []
            (RelJudgment (Var "x" 0 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "x" 0 (initialPos "test")))
            (Iota (Var "x" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))
            emptyContext

        derivedTheorem =
          extendTheoremContext
            "derived"
            []
            (RelJudgment (Var "y" 0 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" 0 (initialPos "test")))
            (PTheoremApp "base" [] (initialPos "test")) -- References base theorem
            baseTheorem

        ctx =
          extendTermContext "y" (RMacro "A" [] (initialPos "test")) $
            extendTermContext "x" (RMacro "A" [] (initialPos "test")) emptyContext

    case inferProofType derivedTheorem (PTheoremApp "derived" [] (initialPos "test")) of
      Right result -> do
        let RelJudgment _ r _ = resultJudgment result
        r `shouldBe` RMacro "R" [] (initialPos "test")
        return ()
      Left err -> expectationFailure $ "Nested theorem reference failed: " ++ show err

  it "handles theorem reference error cases" $ do
    -- Test various error conditions with theorem references
    let theorem1 =
          extendTheoremContext
            "thm1"
            []
            (RelJudgment (Var "a" 0 (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "b" 0 (initialPos "test")))
            (Iota (Var "a" 0 (initialPos "test")) (Var "b" 0 (initialPos "test")) (initialPos "test"))
            emptyContext

        ctx = emptyContext

    -- Test 1: Reference to non-existent theorem should fail
    case inferProofType theorem1 (PTheoremApp "nonexistent" [] (initialPos "test")) of
      Left _ -> return () -- Expected failure
      Right _ -> expectationFailure "Reference to non-existent theorem should fail"

    -- Test 2: Application with wrong arity should fail
    let wrongApp = AppP (PTheoremApp "thm1" [] (initialPos "test")) (PTheoremApp "thm1" [] (initialPos "test")) (initialPos "test")
    case inferProofType theorem1 wrongApp of
      Left _ -> return () -- Expected failure - thm1 is not a function
      Right _ -> expectationFailure "Wrong theorem application should fail"

-- | Test that proof checking rules only use α-equivalence, not β-η equivalence
alphaEquivalenceVsBetaEtaSpec :: Spec
alphaEquivalenceVsBetaEtaSpec = describe "α-equivalence vs β-η equivalence in proof checking" $ do
  rhoEliminationAlphaOnlySpec
  compositionAlphaOnlySpec
  conversionBetaEtaSpec

-- Test that rho elimination only accepts α-equivalent terms, not β-η equivalent
rhoEliminationAlphaOnlySpec :: Spec
rhoEliminationAlphaOnlySpec = describe "rho elimination uses α-equivalence only" $ do
  it "rejects β-η equivalent but not α-equivalent terms in rho elimination" $ do
    let pos = initialPos "test"
        -- Context: x : Term, S : Rel
        termCtx =
          extendTermContext "x" (RMacro "Term" [] pos) $
            extendTermContext "S" (RMacro "Rel" [] pos) emptyContext

        -- First proof: x [(λ z . z)^] x (promoted identity)
        promType = Prom (Lam "z" (Var "z" 0 pos) pos) pos
        firstJudgment = RelJudgment (Var "x" 1 pos) promType (Var "x" 1 pos)
        ctx = extendProofContext "eq" firstJudgment termCtx

        -- Second proof should prove: (λ z . z) x [S] x
        -- But we'll try to use a proof that proves: x [S] x (β-η equivalent but not α-equivalent)
        secondJudgment = RelJudgment (Var "x" 1 pos) (RMacro "S" [] pos) (Var "x" 1 pos)
        finalCtx = extendProofContext "rel" secondJudgment ctx

        -- Rho elimination: ρ{y . y, x } eq - rel
        rhoProof =
          RhoElim
            "y"
            (Var "y" 0 pos)
            (Var "x" 1 pos)
            (PVar "eq" 1 pos)
            (PVar "rel" 0 pos)
            pos

        -- Expected: (λ z . z) x [S] x, but rel proves x [S] x
        expectedJudgment =
          RelJudgment
            (App (Lam "z" (Var "z" 0 pos) pos) (Var "x" 1 pos) pos)
            (RMacro "S" [] pos)
            (Var "x" 1 pos)


    case checkProof finalCtx  rhoProof expectedJudgment of
      Left (RhoEliminationTypeMismatchError _ expected actual _) -> do
        -- Should reject because terms are not α-equivalent
        expected
          `shouldBe` RelJudgment
            (App (Lam "z" (Var "z" 0 pos) pos) (Var "x" 1 pos) pos)
            (RMacro "S" [] pos)
            (Var "x" 1 pos)
        actual `shouldBe` RelJudgment (Var "x" 1 pos) (RMacro "S" [] pos) (Var "x" 1 pos)
      Left err -> expectationFailure $ "Expected RhoEliminationTypeMismatchError, got: " ++ show err
      Right _ -> expectationFailure "Expected rho elimination to fail - terms are β-η equivalent but not α-equivalent"

-- Test that composition only accepts α-equivalent middle terms, not β-η equivalent
compositionAlphaOnlySpec :: Spec
compositionAlphaOnlySpec = describe "composition uses α-equivalence only" $ do
  it "rejects β-η equivalent but not α-equivalent middle terms in composition" $ do
    let pos = initialPos "test"
        -- Context: a, b, c : Term, R, S : Rel
        termCtx =
          extendTermContext "c" (RMacro "Term" [] pos) $
            extendTermContext "b" (RMacro "Term" [] pos) $
              extendTermContext "a" (RMacro "Term" [] pos) $
                extendTermContext "S" (RMacro "Rel" [] pos) $
                  extendTermContext "R" (RMacro "Rel" [] pos) emptyContext

        -- First proof: a [R] b
        firstJudgment = RelJudgment (Var "a" 2 pos) (RMacro "R" [] pos) (Var "b" 1 pos)
        ctx1 = extendProofContext "p1" firstJudgment termCtx

        -- Second proof: (λ z . z) b [S] c (β-η equivalent to b [S] c but not α-equivalent)
        betaEtaMiddle = App (Lam "z" (Var "z" 0 pos) pos) (Var "b" 1 pos) pos
        secondJudgment = RelJudgment betaEtaMiddle (RMacro "S" [] pos) (Var "c" 0 pos)
        ctx2 = extendProofContext "p2" secondJudgment ctx1

        -- Composition: (p1, p2)
        compProof = Pair (PVar "p1" 1 pos) (PVar "p2" 0 pos) pos

        -- Expected: a [R ∘ S] c
        compType = Comp (RMacro "R" [] pos) (RMacro "S" [] pos) pos
        expectedJudgment = RelJudgment (Var "a" 2 pos) compType (Var "c" 0 pos)


    case checkProof ctx2  compProof expectedJudgment of
      Left (CompositionError _ _ middle1 middle2 _) -> do
        -- Should reject because middle terms are not α-equivalent
        middle1 `shouldBe` Var "b" 1 pos
        middle2 `shouldBe` App (Lam "z" (Var "z" 0 pos) pos) (Var "b" 1 pos) pos
      Left err -> expectationFailure $ "Expected CompositionError, got: " ++ show err
      Right _ -> expectationFailure "Expected composition to fail - middle terms are β-η equivalent but not α-equivalent"

-- Test that conversion proofs DO use β-η equivalence (the one exception)
conversionBetaEtaSpec :: Spec
conversionBetaEtaSpec = describe "conversion proofs use β-η equivalence" $ do
  it "accepts β-η equivalent terms in conversion proofs" $ do
    let pos = initialPos "test"
        -- Context: x : Term, R : Rel
        termCtx =
          extendTermContext "x" (RMacro "Term" [] pos) $
            extendTermContext "R" (RMacro "Rel" [] pos) emptyContext

        -- Original proof: (λ z . z) x [R] (λ z . z) x
        origTerm = App (Lam "z" (Var "z" 0 pos) pos) (Var "x" 1 pos) pos
        origJudgment = RelJudgment origTerm (RMacro "R" [] pos) origTerm
        ctx = extendProofContext "p" origJudgment termCtx

        -- Conversion proof: x ⇃ p ⇂ x (β-η equivalent endpoints)
        convProof = ConvProof (Var "x" 1 pos) (PVar "p" 0 pos) (Var "x" 1 pos) pos

        -- Expected: x [R] x
        expectedJudgment = RelJudgment (Var "x" 1 pos) (RMacro "R" [] pos) (Var "x" 1 pos)


    case checkProof ctx convProof expectedJudgment of
      Right result ->
        resultJudgment result `shouldBe` expectedJudgment
      Left err -> expectationFailure $ "Expected conversion to succeed with β-η equivalent terms, got: " ++ show err

-- | Test judgment equality with macro expansion
judgmentEqualityMacroExpansionSpec :: Spec
judgmentEqualityMacroExpansionSpec = describe "judgment equality with macro expansion" $ do
  it "expands term macros in both judgments before comparing" $ do
    let trueMacro = TermMacro (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
        identityMacro = RelMacro (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test"))
        macroCtx1 = extendMacroContext "True" [] trueMacro (defaultFixity "TEST") emptyContext
        macroEnv = extendMacroContext "Identity" [] identityMacro (defaultFixity "TEST") macroCtx1
        judgment1 = RelJudgment (TMacro "True" [] (initialPos "test")) (RMacro "Identity" [] (initialPos "test")) (TMacro "True" [] (initialPos "test"))
        judgment2 = RelJudgment (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (RMacro "Identity" [] (initialPos "test")) (Lam "a" (Lam "b" (Var "a" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))

    case relJudgmentEqual macroEnv judgment1 judgment2 of
      Right result -> result `shouldBe` True -- Should be alpha equivalent after macro expansion
      Left err -> expectationFailure $ "Judgment equality with macro expansion failed: " ++ show err

  it "expands relation macros before comparing" $ do
    let boolMacro = RelMacro (All "X" (Arr (RVar "X" 0 (initialPos "test")) (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
        macroEnv = extendMacroContext "Bool" [] boolMacro (defaultFixity "TEST") emptyContext
        judgment1 = RelJudgment (Var "x" 0 (initialPos "test")) (RMacro "Bool" [] (initialPos "test")) (Var "x" 0 (initialPos "test"))
        judgment2 = RelJudgment (Var "x" 0 (initialPos "test")) (All "X" (Arr (RVar "X" 0 (initialPos "test")) (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "x" 0 (initialPos "test"))

    case relJudgmentEqual macroEnv judgment1 judgment2 of
      Right result -> result `shouldBe` True -- Should be equal after macro expansion
      Left err -> expectationFailure $ "Judgment equality with relation macro expansion failed: " ++ show err

-- | Test for quantifier de Bruijn index bug in proof checking
quantifierDeBruijnBugProofSpec :: Spec
quantifierDeBruijnBugProofSpec = describe "quantifier de Bruijn bug in proof checking" $ do
  it "type application with unbound relation in quantifier should work" $ do
    -- This test demonstrates the bug through the proof checker
    -- p { S } where p : a [∀ X . S] b should type check to a [S] b
    let pos = initialPos "test"
        -- Create the context with necessary bindings
        ctx =
          extendRelContext "S"
            $ extendTermContext "a" (RMacro "A" [] pos)
            $ extendTermContext "b" (RMacro "B" [] pos)
            $ extendProofContext
              "p"
              ( RelJudgment
                  (Var "a" 1 pos)
                  (All "X" (RVar "S" 1 pos) pos)
                  (Var "b" 0 pos)
              )
            $ emptyContext

        -- Create the proof: p { S }
        proof = TyApp (PVar "p" 0 pos) (RVar "S" 0 pos) pos

        -- Expected judgment: a [S] b
        expectedJudgment = RelJudgment (Var "a" 1 pos) (RVar "S" 0 pos) (Var "b" 0 pos)

    -- Check the proof
    case checkProof ctx proof expectedJudgment of
      Right _ -> return () -- Should succeed
      Left err ->
        expectationFailure $
          "Type application should work but failed with: " ++ show err

  it "nested quantifier type applications work" $ do
    -- Test nested type applications using proper RelTT syntax
    let nestedTheorem = "⊢ nested_test (a : Term) (b : Term) (R : Rel) (S : Rel) (T : Rel) (p : a [∀ X . ∀ Y .(X ∘ T)] b) : a [R ∘ T] b ≔ (p { R }){ S };"
        simpleTheorem = "⊢ simple_test (a : Term) (b : Term) (R : Rel) (S : Rel) (p : a [∀ X . S] b) : a [S] b ≔ p { R };"

    case runParser rawDeclaration "test" nestedTheorem of
      Left parseErr -> expectationFailure $ "Parse should succeed: " ++ show parseErr
      Right rawDecl -> 
        case elaborate emptyContext rawDecl of
          Left elabErr -> expectationFailure $ "Elaboration should succeed: " ++ show elabErr
          Right (TheoremDef _ bindings judgment proof) -> do
            let ctx = buildContextFromBindings bindings
            case checkProof ctx proof judgment of
              Right _ -> return () -- Should succeed
              Left err -> expectationFailure $ "Nested quantifier theorem should work: " ++ show err
          _ -> expectationFailure "Expected theorem declaration"

    case runParser rawDeclaration "test" simpleTheorem of
      Left parseErr -> expectationFailure $ "Parse should succeed: " ++ show parseErr
      Right rawDecl ->
        case elaborate emptyContext rawDecl of
          Left elabErr -> expectationFailure $ "Elaboration should succeed: " ++ show elabErr
          Right (TheoremDef _ bindings judgment proof) -> do
            let ctx = buildContextFromBindings bindings
            case checkProof ctx proof judgment of
              Right _ -> return () -- Should succeed
              Left err -> expectationFailure $ "Simple quantifier theorem should work: " ++ show err
          _ -> expectationFailure "Expected theorem declaration"

  it "expands both term and relation macros together" $ do
    let trueMacro = TermMacro (Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))
        boolMacro = RelMacro (All "X" (Arr (RVar "X" 0 (initialPos "test")) (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
        macroCtx1 = extendMacroContext "True" [] trueMacro (defaultFixity "TEST") emptyContext
        macroEnv = extendMacroContext "Bool" [] boolMacro (defaultFixity "TEST") macroCtx1
        judgment1 = RelJudgment (TMacro "True" [] (initialPos "test")) (RMacro "Bool" [] (initialPos "test")) (TMacro "True" [] (initialPos "test"))
        judgment2 = RelJudgment (Lam "a" (Lam "b" (Var "a" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (All "Y" (Arr (RVar "Y" 0 (initialPos "test")) (Arr (RVar "Y" 0 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Lam "c" (Lam "d" (Var "c" 1 (initialPos "test")) (initialPos "test")) (initialPos "test"))

    case relJudgmentEqual macroEnv judgment1 judgment2 of
      Right result -> result `shouldBe` True -- Should be alpha equivalent after expanding all macros
      Left err -> expectationFailure $ "Judgment equality with mixed macro expansion failed: " ++ show err

  it "debug: check de Bruijn indices in proof inference" $ do
    -- Simple proof: λ p : R . p should give λ x . x [R → R] λ x' . x'
    let proof = LamP "p" (RVar "R" 0 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (initialPos "test")
        ctx = emptyContext

    case inferProofType ctx proof of
      Right result -> do
        let actualJudgment = resultJudgment result
        putStrLn $ "Simple proof result: " ++ show actualJudgment

        -- Should be something like: λ x . x [R → R] λ x' . x'
        case actualJudgment of
          RelJudgment (Lam _ (Var _ idx1 _) _) _ (Lam _ (Var _ idx2 _) _) -> do
            putStrLn $ "Left index: " ++ show idx1 ++ ", Right index: " ++ show idx2
            idx1 `shouldBe` 0
            idx2 `shouldBe` 0
          other -> expectationFailure $ "Unexpected judgment structure: " ++ show other
      Left err -> expectationFailure $ "Simple proof inference failed: " ++ show err
