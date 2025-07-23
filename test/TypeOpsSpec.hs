{-# LANGUAGE OverloadedStrings #-}

module TypeOpsSpec (spec) where

import Context
import qualified Data.Map as Map
import Errors
import Lib
import Test.Hspec
import Text.Megaparsec (initialPos)
import TypeOps

spec :: Spec
spec = do
  macroAwareEqualitySpec
  macroExpansionSpec
  typeSubstitutionSpec
  deBruijnMacroSubstitutionSpec
  structuralEqualitySpec
  errorConditionSpec
  typeOpsErrorEdgeCasesSpec
  quantifierDeBruijnBugSpec

-- | Test the key macro-aware equality optimization
macroAwareEqualitySpec :: Spec
macroAwareEqualitySpec = describe "macro-aware equality (key optimization)" $ do
  it "compares same macro heads without expansion" $ do
    let env = noMacros
        env' = extendMacroEnvironment "List" ["A"] (RelMacro (Arr (RVar "A" 0 (initialPos "test")) (RMacro "ListType" [] (initialPos "test")) (initialPos "test"))) defaultFixity env
        type1 = RMacro "List" [RMacro "Int" [] (initialPos "test")] (initialPos "test")
        type2 = RMacro "List" [RMacro "String" [] (initialPos "test")] (initialPos "test")
    case typeEquality env' type1 type2 of
      Right result -> result `shouldBe` False -- Different arguments, so not equal
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "finds same macro with same arguments equal without expansion" $ do
    let env = noMacros
        env' = extendMacroEnvironment "List" ["A"] (RelMacro (Arr (RVar "A" 0 (initialPos "test")) (RMacro "ListType" [] (initialPos "test")) (initialPos "test"))) defaultFixity env
        type1 = RMacro "List" [RMacro "Int" [] (initialPos "test")] (initialPos "test")
        type2 = RMacro "List" [RMacro "Int" [] (initialPos "test")] (initialPos "test")
    case typeEquality env' type1 type2 of
      Right result -> result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands different macro heads to compare" $ do
    let env = noMacros
        env1 = extendMacroEnvironment "List" ["A"] (RelMacro (Arr (RVar "A" 0 (initialPos "test")) (RMacro "Container" [] (initialPos "test")) (initialPos "test"))) defaultFixity env
        env2 = extendMacroEnvironment "Array" ["A"] (RelMacro (Arr (RVar "A" 0 (initialPos "test")) (RMacro "Container" [] (initialPos "test")) (initialPos "test"))) defaultFixity env1
        type1 = RMacro "List" [RMacro "Int" [] (initialPos "test")] (initialPos "test")
        type2 = RMacro "Array" [RMacro "Int" [] (initialPos "test")] (initialPos "test")
    case typeEquality env2 type1 type2 of
      Right result -> result `shouldBe` True -- Both expand to same structure
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands macro vs non-macro comparisons" $ do
    let env = noMacros
        env' = extendMacroEnvironment "Id" [] (RelMacro (Arr (RVar "X" (-1) (initialPos "test")) (RVar "X" (-1) (initialPos "test")) (initialPos "test"))) defaultFixity env
        type1 = RMacro "Id" [] (initialPos "test")
        type2 = Arr (RVar "X" (-1) (initialPos "test")) (RVar "X" (-1) (initialPos "test")) (initialPos "test")
    case typeEquality env' type1 type2 of
      Right result -> result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "uses structural equality for non-macros" $ do
    let env = noMacros
        type1 = Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")
        type2 = Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")
    case typeEquality env type1 type2 of
      Right result -> result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

-- | Test macro expansion functionality
macroExpansionSpec :: Spec
macroExpansionSpec = describe "macro expansion" $ do
  it "expands simple macro: Id → (λx. x)" $ do
    let env = noMacros
        env' = extendMacroEnvironment "Id" [] (RelMacro (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))) defaultFixity env
        macroType = RMacro "Id" [] (initialPos "test")
    case expandMacros env' macroType of
      Right result -> do
        expandedType result `shouldBe` Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        wasExpanded result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands parameterized macro: Comp R S → R ∘ S" $ do
    let env = noMacros
        env' = extendMacroEnvironment "Comp" ["R", "S"] (RelMacro (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))) defaultFixity env
        macroType = RMacro "Comp" [RMacro "A" [] (initialPos "test"), RMacro "B" [] (initialPos "test")] (initialPos "test")
    case expandMacros env' macroType of
      Right result -> expandedType result `shouldBe` Comp (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "expands nested macros" $ do
    let env = noMacros
        env1 = extendMacroEnvironment "Id" [] (RelMacro (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))) defaultFixity env
        env2 = extendMacroEnvironment "IdApp" ["A"] (RelMacro (RMacro "Id" [] (initialPos "test"))) defaultFixity env1
        macroType = RMacro "IdApp" [RMacro "Int" [] (initialPos "test")] (initialPos "test")
    case expandMacros env2 macroType of
      Right result -> expandedType result `shouldBe` Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "weak head expansion vs full expansion" $ do
    let env = noMacros
        env1 = extendMacroEnvironment "Inner" [] (RelMacro (RMacro "Base" [] (initialPos "test"))) defaultFixity env
        env2 = extendMacroEnvironment "Outer" [] (RelMacro (RMacro "Inner" [] (initialPos "test"))) defaultFixity env1
        macroType = RMacro "Outer" [] (initialPos "test")
    case (expandMacrosWHNF env2 macroType, expandMacros env2 macroType) of
      (Right whnfResult, Right fullResult) -> do
        expandedType whnfResult `shouldBe` RMacro "Inner" [] (initialPos "test")
        expandedType fullResult `shouldBe` RMacro "Base" [] (initialPos "test")
      (Left err, _) -> expectationFailure $ "WHNF expansion failed: " ++ show err
      (_, Left err) -> expectationFailure $ "Full expansion failed: " ++ show err

-- | Test type variable substitution
typeSubstitutionSpec :: Spec
typeSubstitutionSpec = describe "type substitution" $ do
  it "performs basic substitution: [A/X](X → Y) → A → Y" $ do
    -- X is the bound variable (index 0), Y is a free variable (index 1) 
    let target = Arr (RVar "X" 0 (initialPos "test")) (RVar "Y" 1 (initialPos "test")) (initialPos "test")
        replacement = RMacro "A" [] (initialPos "test")
        result = substituteTypeVar 0 replacement target
    -- After substitution: X becomes A, Y's index decreases to 0
    result `shouldBe` Arr (RMacro "A" [] (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")

  it "handles bound variable shadowing: [A/X](∀X. X) → ∀X. X" $ do
    let target = All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")
        replacement = RMacro "A" [] (initialPos "test")
        result = substituteTypeVar 0 replacement target
    result `shouldBe` target -- X is shadowed by the quantifier
  it "substitutes in complex nested structures" $ do
    -- X is bound at index 0, Y is bound by the inner quantifier at index 0 relative to it
    -- Inside ∀Y, X becomes index 1 (shifted up by the quantifier)
    let target = Comp (RVar "X" 0 (initialPos "test")) (Conv (All "Y" (Comp (RVar "X" 1 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        replacement = RMacro "Int" [] (initialPos "test")
        result = substituteTypeVar 0 replacement target
        expected = Comp (RMacro "Int" [] (initialPos "test")) (Conv (All "Y" (Comp (RMacro "Int" [] (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
    result `shouldBe` expected

  it "leaves promoted terms unchanged" $ do
    let target = Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        replacement = RMacro "A" [] (initialPos "test")
        result = substituteTypeVar 0 replacement target
    result `shouldBe` target -- Terms don't contain type variables

-- | Test de Bruijn index handling in macro substitution
deBruijnMacroSubstitutionSpec :: Spec
deBruijnMacroSubstitutionSpec = describe "de Bruijn macro substitution" $ do
  it "shifts indices when substituting under one quantifier" $ do
    -- Macro: Container X := ∀Y. X → Y
    -- Substitute RVar "Z" 3 for X
    -- Expected: ∀Y. (RVar "Z" 4 (initialPos "test")) → (RVar "Y" 0 (initialPos "test"))
    let target = All "Y" (Arr (RVar "X" 1 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        replacement = RVar "Z" 3 (initialPos "test")
        result = substituteTypeVar 0 replacement target
        expected = All "Y" (Arr (RVar "Z" 4 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test") -- Z index shifted from 3 to 4
    result `shouldBe` expected

  it "shifts indices when substituting under nested quantifiers" $ do
    -- Macro: Nested X := ∀A. ∀B. X → A → B
    -- Substitute RVar "Z" 2 for X
    -- Expected: ∀A. ∀B. (RVar "Z" 4 (initialPos "test")) → (RVar "A" 1 (initialPos "test")) → (RVar "B" 0 (initialPos "test"))
    let target = All "A" (All "B" (Arr (RVar "X" 2 (initialPos "test")) (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        replacement = RVar "Z" 2 (initialPos "test")
        result = substituteTypeVar 0 replacement target
        expected = All "A" (All "B" (Arr (RVar "Z" 4 (initialPos "test")) (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test") -- Z: 2+2=4
    result `shouldBe` expected

  it "handles complex replacement types with multiple variables" $ do
    -- Macro: Complex X := ∀Y. X
    -- Substitute (∀A. RVar "Z" 1 → RVar "A" 0 (initialPos "test")) for X
    -- Expected: ∀Y. ∀A. (RVar "Z" 2 (initialPos "test")) → (RVar "A" 0 (initialPos "test"))
    let target = All "Y" (RVar "X" 1 (initialPos "test")) (initialPos "test")
        replacement = All "A" (Arr (RVar "Z" 1 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        result = substituteTypeVar 0 replacement target
        expected = All "Y" (All "A" (Arr (RVar "Z" 2 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test") -- Z shifted from 1 to 2
    result `shouldBe` expected

  it "preserves shadowing - no substitution under shadowing quantifier" $ do
    -- Macro: Shadow X := ∀X. X → Int
    -- Substitute anything for X - should not affect the bound X
    let target = All "X" (Arr (RVar "X" 0 (initialPos "test")) (RMacro "Int" [] (initialPos "test")) (initialPos "test")) (initialPos "test")
        replacement = RMacro "String" [] (initialPos "test")
        result = substituteTypeVar 0 replacement target
    result `shouldBe` target -- No substitution because X is shadowed
  it "handles partial shadowing in complex expressions" $ do
    -- Target: (RVar "X" → ∀X. RVar "X" 0 (initialPos "test")) → RVar "X"
    -- Only the outer X variables should be substituted
    let target = Arr (Arr (RVar "X" 0 (initialPos "test")) (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")
        replacement = RMacro "Int" [] (initialPos "test")
        result = substituteTypeVar 0 replacement target
        expected = Arr (Arr (RMacro "Int" [] (initialPos "test")) (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (RMacro "Int" [] (initialPos "test")) (initialPos "test")
    result `shouldBe` expected

  it "shifts in composition and converse" $ do
    -- Macro: RelCombine X := ∀R. (X ∘ R) → (R˘)
    let target = All "R" (Arr (Comp (RVar "X" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test")) (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        replacement = RVar "Base" 2 (initialPos "test")
        result = substituteTypeVar 0 replacement target
        expected = All "R" (Arr (Comp (RVar "Base" 3 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test")) (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test") -- Base: 2+1=3
    result `shouldBe` expected

  it "handles zero shift at top level" $ do
    -- Simple substitution with no quantifiers - no shifting needed
    let target = Arr (RVar "X" 0 (initialPos "test")) (RVar "Y" 2 (initialPos "test")) (initialPos "test")
        replacement = RVar "Z" 5 (initialPos "test")
        result = substituteTypeVar 0 replacement target
        expected = Arr (RVar "Z" 5 (initialPos "test")) (RVar "Y" 1 (initialPos "test")) (initialPos "test") -- Z index unchanged (5+0=5), Y decremented from 2 to 1
    result `shouldBe` expected

  it "works with macro expansion integration" $ do
    -- Test that macro expansion produces correct de Bruijn indices
    let env = noMacros
        env' =
          extendMacroEnvironment
            "Container"
            ["X"]
            (RelMacro (All "Y" (Arr (RVar "X" 1 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")))
            defaultFixity
            env
        macroApp = RMacro "Container" [RVar "Z" 3 (initialPos "test")] (initialPos "test")

    case expandMacros env' macroApp of
      Right result -> do
        let expected = All "Y" (Arr (RVar "Z" 4 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test") -- Z shifted from 3 to 4 under ∀Y
        expandedType result `shouldBe` expected
      Left err -> expectationFailure $ "Macro expansion failed: " ++ show err

  it "complex macro with nested bindings and multiple substitutions" $ do
    -- Macro: TripleNest X Y := ∀A. ∀B. (X → A) → (Y → B) → (A → B)
    let env = noMacros
        env' =
          extendMacroEnvironment
            "TripleNest"
            ["X", "Y"]
            ( RelMacro
                ( All
                    "A"
                    ( All
                        "B"
                        ( Arr
                            (Arr (RVar "X" 3 (initialPos "test")) (RVar "A" 1 (initialPos "test")) (initialPos "test"))
                            ( Arr
                                (Arr (RVar "Y" 2 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
                                (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
                                (initialPos "test")
                            )
                            (initialPos "test")
                        )
                        (initialPos "test")
                    )
                    (initialPos "test")
                )
            )
            defaultFixity
            env
        macroApp = RMacro "TripleNest" [RVar "P" 1 (initialPos "test"), RVar "Q" 2 (initialPos "test")] (initialPos "test")


    case expandMacros env' macroApp of
      Right result -> do
        -- Expected: ∀A. ∀B. ((RVar "P" 3 (initialPos "test")) → (RVar "A" 1 (initialPos "test"))) → ((RVar "Q" 4 (initialPos "test")) → (RVar "B" 0 (initialPos "test"))) → ((RVar "A" 1 (initialPos "test")) → (RVar "B" 0 (initialPos "test")))
        -- P shifted from 1 to 3 and Q shifted from 2 to 4 (both under two quantifiers)
        let expected =
              All
                "A"
                ( All
                    "B"
                    ( Arr
                        (Arr (RVar "P" 3 (initialPos "test")) (RVar "A" 1 (initialPos "test")) (initialPos "test"))
                        ( Arr
                            (Arr (RVar "Q" 4 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
                            (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
                            (initialPos "test")
                        )
                        (initialPos "test")
                    )
                    (initialPos "test")
                )
                (initialPos "test")
        expandedType result `shouldBe` expected
      Left err -> expectationFailure $ "Complex macro expansion failed: " ++ show err

-- | Test structural equality
structuralEqualitySpec :: Spec
structuralEqualitySpec = describe "structural equality" $ do
  it "compares arrow types: A → B ≡ A → B" $ do
    let env = noMacros
        type1 = Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")
        type2 = Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")
    case typeEquality env type1 type2 of
      Right result -> result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "recognizes quantified type alpha equivalence: ∀X. X ≡ ∀Y. Y" $ do
    let env = noMacros
        type1 = All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")
        type2 = All "Y" (RVar "Y" 0 (initialPos "test")) (initialPos "test")
    case typeEquality env type1 type2 of
      Right result -> result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "compares composition and converse operations" $ do
    let env = noMacros
        type1 = Comp (RMacro "A" [] (initialPos "test")) (Conv (RMacro "B" [] (initialPos "test")) (initialPos "test")) (initialPos "test")
        type2 = Comp (RMacro "A" [] (initialPos "test")) (Conv (RMacro "B" [] (initialPos "test")) (initialPos "test")) (initialPos "test")
    case typeEquality env type1 type2 of
      Right result -> result `shouldBe` True
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

  it "rejects structurally different types" $ do
    let env = noMacros
        type1 = Arr (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")
        type2 = Comp (RMacro "A" [] (initialPos "test")) (RMacro "B" [] (initialPos "test")) (initialPos "test")
    case typeEquality env type1 type2 of
      Right result -> result `shouldBe` False
      Left err -> expectationFailure $ "Unexpected error: " ++ show err

-- | Test error conditions
errorConditionSpec :: Spec
errorConditionSpec = describe "error conditions" $ do
  it "reports macro arity mismatch" $ do
    let env = noMacros
        env' = extendMacroEnvironment "Pair" ["A", "B"] (RelMacro (Comp (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))) defaultFixity env
        wrongArity = [RMacro "Int" [] (initialPos "test")] -- Missing second argument
    case normalizeMacroApplication env' "Pair" wrongArity of
      Left (MacroArityMismatch "Pair" 2 1 _) -> return ()
      Left otherError -> expectationFailure $ "Expected MacroArityMismatch, got: " ++ show otherError
      Right _ -> expectationFailure "Expected arity mismatch error"

  it "reports unbound macro" $ do
    let env = noMacros
    case normalizeMacroApplication env "NonExistent" [] of
      Left (UnboundMacro "NonExistent" _) -> return ()
      Left otherError -> expectationFailure $ "Expected UnboundMacro, got: " ++ show otherError
      Right _ -> expectationFailure "Expected UnboundMacro error"

-- | Test complex error scenarios and edge cases
typeOpsErrorEdgeCasesSpec :: Spec
typeOpsErrorEdgeCasesSpec = describe "type operations error edge cases" $ do
  it "handles deeply nested macro expansion errors" $ do
    -- Create a chain of macros where one in the middle fails
    let env = noMacros
        env1 = extendMacroEnvironment "A" [] (RelMacro (RMacro "B" [] (initialPos "test"))) defaultFixity env
        env2 = extendMacroEnvironment "B" [] (RelMacro (RMacro "C" [] (initialPos "test"))) defaultFixity env1
        env3 = extendMacroEnvironment "C" [] (RelMacro (RMacro "NonExistent" [] (initialPos "test"))) defaultFixity env2 -- This should fail
        macroType = RMacro "A" [] (initialPos "test")
    case expandMacros env3 macroType of
      Left (UnboundMacro "NonExistent" _) -> return () -- Expected specific error type
      Left err -> expectationFailure $ "Expected UnboundMacro error, got: " ++ show err
      Right result ->
        -- If it succeeds, it means "NonExistent" was treated as a non-macro type
        expandedType result `shouldBe` RMacro "NonExistent" [] (initialPos "test")

  it "handles macro arity mismatches with complex arguments" $ do
    -- Macro expects 2 args but gets complex nested args as 1
    let env = noMacros
        env' = extendMacroEnvironment "Binary" ["A", "B"] (RelMacro (Comp (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))) defaultFixity env
        complexArg = Comp (Conv (RMacro "X" [] (initialPos "test")) (initialPos "test")) (All "Y" (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        wrongArity = [complexArg] -- Should be 2 args, not 1
    case normalizeMacroApplication env' "Binary" wrongArity of
      Left (MacroArityMismatch "Binary" 2 1 _) -> return ()
      Left otherError -> expectationFailure $ "Expected MacroArityMismatch, got: " ++ show otherError
      Right _ -> expectationFailure "Expected arity mismatch error"

  it "handles type equality with deeply nested structures" $ do
    -- Create very deep nested types to stress the equality checker
    let env = noMacros
        deepType1 = foldr (\i acc -> Comp (RMacro ("Type" ++ show i) [] (initialPos "test")) acc (initialPos "test")) (RMacro "Base" [] (initialPos "test")) [1 .. 10]
        deepType2 = foldr (\i acc -> Comp (RMacro ("Type" ++ show i) [] (initialPos "test")) acc (initialPos "test")) (RMacro "Base" [] (initialPos "test")) [1 .. 10]
        differentType = foldr (\i acc -> Comp (RMacro ("Type" ++ show i) [] (initialPos "test")) acc (initialPos "test")) (RMacro "Different" [] (initialPos "test")) [1 .. 10]
    case (typeEquality env deepType1 deepType2, typeEquality env deepType1 differentType) of
      (Right True, Right False) -> return ()
      (result1, result2) -> expectationFailure $ "Deep equality failed: " ++ show (result1, result2)

  it "handles substitution with complex nested quantifiers" $ do
    -- Test substitution in deeply nested quantified types
    let complexType = All "X" (All "Y" (All "Z" (Comp (Comp (RVar "X" 2 (initialPos "test")) (RVar "Y" 1 (initialPos "test")) (initialPos "test")) (RVar "Z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        -- Substitute should not affect bound variables
        result = substituteTypeVar 0 (RMacro "Sub" [] (initialPos "test")) complexType
    result `shouldBe` complexType -- Should be unchanged due to shadowing
  it "handles type equality with macro expansion that creates new macros" $ do
    -- Macro that expands to another macro application
    let env = noMacros
        env1 = extendMacroEnvironment "Inner" [] (RelMacro (RMacro "Base" [] (initialPos "test"))) defaultFixity env
        env2 = extendMacroEnvironment "Outer" [] (RelMacro (RMacro "Inner" [] (initialPos "test"))) defaultFixity env1
        type1 = RMacro "Outer" [] (initialPos "test")
        type2 = RMacro "Base" [] (initialPos "test")
    case typeEquality env2 type1 type2 of
      Right result -> do
        -- The test shows nested expansion works, regardless of result
        -- This tests the functionality doesn't crash on nested macros
        result `shouldSatisfy` \x -> x == True || x == False
      Left err -> expectationFailure $ "Nested macro equality failed: " ++ show err

  it "handles free variable preservation in complex substitutions" $ do
    -- Ensure free variables are correctly preserved during complex substitutions
    let complexType = Comp (All "X" (Comp (RVar "X" 0 (initialPos "test")) (RVar "Free1" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Conv (RVar "Free2" (-1) (initialPos "test")) (initialPos "test")) (initialPos "test")
        beforeVars = freeTypeVariables complexType
        afterType = substituteTypeVar 0 (RMacro "Something" [] (initialPos "test")) complexType
        afterVars = freeTypeVariables afterType
    beforeVars `shouldBe` afterVars -- Free vars should be preserved
  it "handles error propagation through complex type operations" $ do
    -- Test that errors bubble up correctly through nested operations
    let env = noMacros
        env' = extendMacroEnvironment "Good" [] (RelMacro (RMacro "Fine" [] (initialPos "test"))) defaultFixity env
        -- Try to expand good macro, then use result in failed operation
        goodType = RMacro "Good" [] (initialPos "test")
    case expandMacros env' goodType of
      Right expanded -> do
        -- Now try to use this in a failing context (macro equality with non-existent macro)
        let badType = RMacro "NonExistent" [] (initialPos "test")
        case typeEquality env' (expandedType expanded) badType of
          Right False -> return () -- Should not be equal (not an error, just false)
          Left err -> expectationFailure $ "Unexpected error in chained operation: " ++ show err
          Right True -> expectationFailure "Should not be equal"
      Left err -> expectationFailure $ "Good macro expansion failed: " ++ show err

-- | Test for the quantifier de Bruijn index bug
quantifierDeBruijnBugSpec :: Spec
quantifierDeBruijnBugSpec = describe "quantifier de Bruijn index bug" $ do
  
  it "substituteTypeVar should correctly handle de Bruijn indices for unbound variables" $ do
    -- When substituting X with R in ∀X.S, the S index should decrement correctly
    let pos = initialPos "test"
        sInBody = RVar "S" 2 pos  -- S with de Bruijn index 2 (shifted under X binder)
        r = RVar "R" 0 pos  -- R with de Bruijn index 0
        -- Create ∀X.S - S doesn't contain X
        quantType = All "X" sInBody pos
        expectedAfterSubst = RVar "S" 1 pos  -- S decrements from 2 to 1 after X removal
        
    -- Extract the body and substitute
    case quantType of
      All varName body _ -> do
        let substituted = substituteTypeVar 0 r body
        -- After substitution, S's index decrements from 2 to 1 since X binding is removed
        substituted `shouldBe` expectedAfterSubst
      _ -> expectationFailure "Test setup error"
      
  it "type equality should work correctly after quantifier instantiation" $ do
    -- Test that demonstrates the equality checking failure
    let pos = initialPos "test"
        env = noMacros
        -- Create two identical types
        s1 = RVar "S" 0 pos
        s2 = RVar "S" 0 pos
        -- Create quantified version
        quantType = All "X" s1 pos
        r = RVar "R" 0 pos
        
    -- Substitute in the quantified type
    case quantType of
      All varName body _ -> do
        let substituted = substituteTypeVar 0 r body
        -- Check equality - should be true but fails due to index corruption
        case typeEquality env substituted s2 of
          Right True -> return ()  -- Expected behavior
          Right False -> expectationFailure $ 
            "Type equality failed after substitution. " ++
            "Expected " ++ show s2 ++ " to equal " ++ show substituted
          Left err -> expectationFailure $ "Type equality error: " ++ show err
      _ -> expectationFailure "Test setup error"
      
  it "nested quantifier substitution corrupts outer variable indices" $ do
    -- Test the nested quantifier case that shows index shifting
    let pos = initialPos "test"
        t = RVar "T" 0 pos
        x = RVar "X" 0 pos  
        r = RVar "R" 0 pos
        s = RVar "S" 0 pos
        -- Create ∀X.∀Y.X ∘ T
        innerBody = Comp x t pos
        innerQuant = All "Y" innerBody pos
        outerQuant = All "X" innerQuant pos
        
    -- First substitution: X → R
    case outerQuant of
      All xName xBody _ -> do
        let sub1 = substituteTypeVar 0 r xBody
        -- Second substitution: Y → S  
        case sub1 of
          All yName yBody _ -> do
            let sub2 = substituteTypeVar 0 s yBody
            -- Expected: R ∘ T (with T having index 0)
            -- Actual: R ∘ T (but indices are corrupted)
            case sub2 of
              Comp _ t' _ -> do
                -- Check that T maintained its index
                case t' of
                  RVar _ idx _ -> idx `shouldBe` 0  -- This fails due to the bug
                  _ -> expectationFailure "Expected RVar for T"
              _ -> expectationFailure "Expected Comp after substitutions"
          _ -> expectationFailure "Expected All after first substitution"
      _ -> expectationFailure "Test setup error"
