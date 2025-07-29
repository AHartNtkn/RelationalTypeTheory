{-# LANGUAGE OverloadedStrings #-}

module ContextSpec (spec) where

import qualified Data.Map as Map
import Core.Errors
import Core.Syntax
import Core.Context (emptyContext, extendMacroContext, extendTermContext, extendRelContext, extendProofContext, extendTheoremContext, lookupTerm, lookupRel, lookupProof, lookupTheorem, emptyTypeEnvironment, extendTypeEnvironment, lookupTypeVar, lookupMacro, shiftContext, isFreshInContext, contextSize, validateContext)
import Parser.Mixfix (defaultFixity)
import Test.Hspec
import Text.Megaparsec (initialPos)

spec :: Spec
spec = do
  contextConstructionSpec
  variableLookupSpec
  contextManipulationSpec
  validationSpec
  integrationSpec
  contextStressTestSpec
  theoremEnvironmentSpec

-- | Test context construction and basic operations
contextConstructionSpec :: Spec
contextConstructionSpec = describe "context construction" $ do
  it "creates empty contexts correctly" $ do
    let ctx = emptyContext
    Map.size (termBindings ctx) `shouldBe` 0
    Map.size (relBindings ctx) `shouldBe` 0
    Map.size (proofBindings ctx) `shouldBe` 0
    Map.size (macroDefinitions ctx) `shouldBe` 0

  it "extends context with term binding" $ do
    let ctx = emptyContext
        relType = RMacro "Int" [] (initialPos "test")
        ctx' = extendTermContext "x" relType ctx
    case lookupTerm "x" ctx' of
      Right (0, ty) -> ty `shouldBe` relType
      Left err -> expectationFailure $ "Lookup failed: " ++ show err
      Right (idx, _) -> expectationFailure $ "Expected index 0, got: " ++ show idx

  it "extends context with relation binding" $ do
    let ctx = emptyContext
        ctx' = extendRelContext "R" ctx
    case lookupRel "R" ctx' of
      Right 0 -> return ()
      Left err -> expectationFailure $ "Lookup failed: " ++ show err
      Right idx -> expectationFailure $ "Expected index 0, got: " ++ show idx

  it "extends context with proof binding" $ do
    let ctx = emptyContext
        judgment = RelJudgment (Var "x" (-1) (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "y" (-1) (initialPos "test"))
        ctx' = extendProofContext "p" judgment ctx
    case lookupProof "p" ctx' of
      Right (0, j) -> j `shouldBe` judgment
      Left err -> expectationFailure $ "Lookup failed: " ++ show err
      Right (idx, _) -> expectationFailure $ "Expected index 0, got: " ++ show idx

-- | Test variable lookup operations
variableLookupSpec :: Spec
variableLookupSpec = describe "variable lookup" $ do
  it "successfully looks up bound term variables" $ do
    let ctx = emptyContext
        relType = RMacro "Bool" [] (initialPos "test")
        ctx' = extendTermContext "flag" relType ctx
    case lookupTerm "flag" ctx' of
      Right (0, ty) -> ty `shouldBe` relType
      Left err -> expectationFailure $ "Expected successful lookup, got: " ++ show err
      Right (idx, _) -> expectationFailure $ "Expected index 0, got: " ++ show idx

  it "fails to look up unbound variables" $ do
    let ctx = emptyContext
    case lookupTerm "nonexistent" ctx of
      Left (UnboundVariable "nonexistent" _) -> return ()
      Left otherErr -> expectationFailure $ "Expected UnboundVariable, got: " ++ show otherErr
      Right _ -> expectationFailure "Expected lookup to fail"

  it "handles multiple bindings with correct de Bruijn indices" $ do
    let ctx = emptyContext
        ctx1 = extendTermContext "x" (RMacro "A" [] (initialPos "test")) ctx
        ctx2 = extendTermContext "y" (RMacro "B" [] (initialPos "test")) ctx1
        ctx3 = extendTermContext "z" (RMacro "C" [] (initialPos "test")) ctx2
    case (lookupTerm "x" ctx3, lookupTerm "y" ctx3, lookupTerm "z" ctx3) of
      (Right (2, _), Right (1, _), Right (0, _)) -> return ()
      results -> expectationFailure $ "Expected indices (2,1,0), got: " ++ show results

  it "looks up type variables in environment" $ do
    let env = emptyTypeEnvironment
        env' = extendTypeEnvironment "X" (RMacro "Int" [] (initialPos "test")) env
    case lookupTypeVar "X" env' of
      Right ty -> ty `shouldBe` RMacro "Int" [] (initialPos "test")
      Left err -> expectationFailure $ "Expected successful lookup, got: " ++ show err

  it "looks up macros in environment" $ do
    let params = [ParamInfo "A" RelK False [], ParamInfo "B" RelK False []]
        body = RelMacro (Comp (RVar "A" 0 (initialPos "test")) (RVar "B" 1 (initialPos "test")) (initialPos "test"))
        env' = extendMacroContext "Pair" params body (defaultFixity "TEST") emptyContext
    case lookupMacro "Pair" env' of
      Right (ps, b) -> do
        map pName ps `shouldBe` ["A", "B"]
        b `shouldBe` body
      Left err -> expectationFailure $ "Expected successful lookup, got: " ++ show err

-- | Test context manipulation operations
contextManipulationSpec :: Spec
contextManipulationSpec = describe "context manipulation" $ do
  it "shifts context indices correctly" $ do
    let ctx = emptyContext
        ctx1 = extendTermContext "x" (RMacro "A" [] (initialPos "test")) ctx
        ctx2 = extendRelContext "R" ctx1
        shifted = shiftContext 2 ctx2
    case (lookupTerm "x" shifted, lookupRel "R" shifted) of
      (Right (2, _), Right 2) -> return () -- Both indices shifted by 2
      results -> expectationFailure $ "Expected shifted indices, got: " ++ show results

  it "checks freshness correctly" $ do
    let ctx = emptyContext
        ctx' = extendTermContext "x" (RMacro "A" [] (initialPos "test")) ctx
    isFreshInContext "x" ctx' `shouldBe` False
    isFreshInContext "y" ctx' `shouldBe` True

  it "calculates context size correctly" $ do
    let ctx = emptyContext
        ctx1 = extendTermContext "x" (RMacro "A" [] (initialPos "test")) ctx
        ctx2 = extendRelContext "R" ctx1
        ctx3 = extendProofContext "p" (RelJudgment (Var "a" (-1) (initialPos "test")) (RMacro "R" [] (initialPos "test")) (Var "b" (-1) (initialPos "test"))) ctx2
    contextSize ctx `shouldBe` 0
    contextSize ctx1 `shouldBe` 1
    contextSize ctx2 `shouldBe` 2
    contextSize ctx3 `shouldBe` 3

-- | Test context validation
validationSpec :: Spec
validationSpec = describe "context validation" $ do
  it "validates well-formed contexts" $ do
    let ctx = emptyContext
        ctx1 = extendTermContext "x" (RMacro "A" [] (initialPos "test")) ctx
        ctx2 = extendRelContext "R" ctx1
    case validateContext ctx2 of
      Right () -> return ()
      Left err -> expectationFailure $ "Expected valid context, got: " ++ show err

  it "detects invalid de Bruijn indices" $ do
    -- This test requires manually constructing an invalid context
    -- since the normal extend functions create valid indices
    let invalidCtx = emptyContext
          { termBindings = Map.fromList [("x", (5, Just (RMacro "A" [] (initialPos "test"))))] -- Invalid index 5 in size-1 context
          , termDepth = 1
          }
    case validateContext invalidCtx of
      Left (InvalidDeBruijnIndex 5 _) -> return ()
      Left otherErr -> expectationFailure $ "Expected InvalidDeBruijnIndex, got: " ++ show otherErr
      Right () -> expectationFailure "Expected validation to fail"

  it "handles empty contexts" $ do
    let ctx = emptyContext
    case validateContext ctx of
      Right () -> return ()
      Left err -> expectationFailure $ "Empty context should be valid, got: " ++ show err

-- | Test integration between different context types
integrationSpec :: Spec
integrationSpec = describe "context integration" $ do
  it "combines typing context with environments" $ do
    let typingCtx = extendTermContext "x" (RMacro "Int" [] (initialPos "test")) emptyContext
        typeEnv = extendTypeEnvironment "X" (RMacro "String" [] (initialPos "test")) emptyTypeEnvironment
        macroEnv = extendMacroContext "Id" [] (RelMacro (RMacro "Identity" [] (initialPos "test"))) (defaultFixity "TEST") emptyContext
    -- Test that all three contexts can coexist
    case (lookupTerm "x" typingCtx, lookupTypeVar "X" typeEnv, lookupMacro "Id" macroEnv) of
      (Right _, Right _, Right _) -> return ()
      results -> expectationFailure $ "Expected all lookups to succeed, got: " ++ show results

  it "handles complex nested contexts" $ do
    let ctx = emptyContext
        -- Build a complex context with multiple variable types
        ctx1 = extendTermContext "x" (RMacro "A" [] (initialPos "test")) ctx
        ctx2 = extendRelContext "R" ctx1
        ctx3 = extendProofContext "p" (RelJudgment (Var "x" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "y" (-1) (initialPos "test"))) ctx2
        ctx4 = extendTermContext "y" (RMacro "B" [] (initialPos "test")) ctx3
    -- Verify all bindings have correct indices after multiple extensions
    case (lookupTerm "x" ctx4, lookupRel "R" ctx4, lookupProof "p" ctx4, lookupTerm "y" ctx4) of
      (Right (1, _), Right 0, Right (0, _), Right (0, _)) -> return ()
      results -> expectationFailure $ "Expected correct nested indices, got: " ++ show results

-- | Test context operations under stress conditions
contextStressTestSpec :: Spec
contextStressTestSpec = describe "context operations stress testing" $ do
  it "handles contexts with many bindings (100+ variables)" $ do
    -- Build a context with 150 term bindings
    let buildLargeContext n ctx =
          if n <= 0
            then ctx
            else buildLargeContext (n - 1) (extendTermContext ("var" ++ show n) (RMacro ("Type" ++ show n) [] (initialPos "test")) ctx)
        largeCtx = buildLargeContext 150 emptyContext
    -- Test lookup of variables at different depths
    -- var150 is the most recent (index 0), var1 is the oldest (index 149)
    case (lookupTerm "var1" largeCtx, lookupTerm "var75" largeCtx, lookupTerm "var150" largeCtx) of
      (Right (0, _), Right (74, _), Right (149, _)) -> return ()
      results -> expectationFailure $ "Expected correct indices in large context, got: " ++ show results

  it "handles deeply nested mixed binding patterns" $ do
    -- Create alternating term, rel, and proof bindings
    let buildMixedContext 0 ctx = ctx
        buildMixedContext n ctx =
          let termCtx = extendTermContext ("t" ++ show n) (RMacro "TermType" [] (initialPos "test")) ctx
              relCtx = extendRelContext ("r" ++ show n) termCtx
              proofCtx =
                extendProofContext
                  ("p" ++ show n)
                  (RelJudgment (Var ("t" ++ show n) 1 (initialPos "test")) (RVar ("r" ++ show n) 0 (initialPos "test")) (Var "x" (-1) (initialPos "test")))
                  relCtx
           in buildMixedContext (n - 1) proofCtx
        mixedCtx = buildMixedContext 50 emptyContext
    -- Verify indices are correctly maintained across different binding types
    case (lookupTerm "t25" mixedCtx, lookupRel "r25" mixedCtx, lookupProof "p25" mixedCtx) of
      (Right (_, _), Right _, Right (_, _)) -> return ()
      results -> expectationFailure $ "Mixed binding pattern failed: " ++ show results

  it "handles variable name conflicts and shadowing" $ do
    -- Create multiple variables with same base name but different suffixes
    let ctx = emptyContext
        ctx1 = extendTermContext "x" (RMacro "A" [] (initialPos "test")) ctx
        ctx2 = extendTermContext "x1" (RMacro "B" [] (initialPos "test")) ctx1
        ctx3 = extendTermContext "x_prime" (RMacro "C" [] (initialPos "test")) ctx2
        ctx4 = extendTermContext "x" (RMacro "D" [] (initialPos "test")) ctx3 -- Shadow original x
    case (lookupTerm "x" ctx4, lookupTerm "x1" ctx4, lookupTerm "x_prime" ctx4) of
      (Right (0, RMacro "D" [] _), Right (2, RMacro "B" [] _), Right (1, RMacro "C" [] _)) -> return ()
      results -> expectationFailure $ "Variable shadowing failed: " ++ show results

  it "handles massive context shifting operations" $ do
    -- Build a context and test shifting by large amounts
    let buildContext n ctx =
          if n <= 0
            then ctx
            else buildContext (n - 1) (extendTermContext ("v" ++ show n) (RMacro "Type" [] (initialPos "test")) ctx)
        originalCtx = buildContext 100 emptyContext
        massiveShift = shiftContext 500 originalCtx
    -- v100 is most recent (index 0 + 500 shift = 500), v1 is oldest (index 99 + 500 shift = 599)
    case (lookupTerm "v1" massiveShift, lookupTerm "v50" massiveShift, lookupTerm "v100" massiveShift) of
      (Right (500, _), Right (549, _), Right (599, _)) -> return ()
      results -> expectationFailure $ "Massive context shift failed: " ++ show results

  it "handles complex freshness checking with many variables" $ do
    -- Create context with many similar variable names
    let buildSimilarNames n ctx =
          if n <= 0
            then ctx
            else buildSimilarNames (n - 1) (extendTermContext ("variable_" ++ show n) (RMacro "Type" [] (initialPos "test")) ctx)
        similarCtx = buildSimilarNames 200 emptyContext
    -- Test freshness of various name patterns
    isFreshInContext "variable_1" similarCtx `shouldBe` False
    isFreshInContext "variable_201" similarCtx `shouldBe` True
    isFreshInContext "variable_" similarCtx `shouldBe` True
    isFreshInContext "var" similarCtx `shouldBe` True

  it "handles macro environments with many definitions" $ do
    -- Build macro environment with many macro definitions
    let buildMacroEnv 0 env = env
        buildMacroEnv n env =
          let macroName = "Macro" ++ show n
              params = ["A" ++ show n, "B" ++ show n]
              body = RelMacro (Comp (RVar ("A" ++ show n) 0 (initialPos "test")) (RVar ("B" ++ show n) 1 (initialPos "test")) (initialPos "test"))
           in buildMacroEnv (n - 1) (extendMacroContext macroName (map (\p -> ParamInfo p RelK False []) params) body (defaultFixity "TEST") env)
        largeMacroEnv = buildMacroEnv 100 emptyContext
    -- Test lookup performance and correctness
    case (lookupMacro "Macro1" largeMacroEnv, lookupMacro "Macro50" largeMacroEnv, lookupMacro "Macro100" largeMacroEnv) of
      (Right (ps1, _), Right (ps50, _), Right (ps100, _)) -> do
        map pName ps1 `shouldBe` ["A1", "B1"]
        map pName ps50 `shouldBe` ["A50", "B50"]
        map pName ps100 `shouldBe` ["A100", "B100"]
      results -> expectationFailure $ "Large macro environment failed: " ++ show results

  it "handles type environments with complex type hierarchies" $ do
    -- Build deep type variable environment
    let buildTypeEnv 0 env = env
        buildTypeEnv n env =
          let typeName = "TypeVar" ++ show n
              typeValue =
                if n == 1
                  then RMacro "BaseType" [] (initialPos "test")
                  else RMacro ("TypeVar" ++ show (n - 1)) [] (initialPos "test")
           in buildTypeEnv (n - 1) (extendTypeEnvironment typeName typeValue env)
        deepTypeEnv = buildTypeEnv 75 emptyTypeEnvironment
    -- Test lookup in deep hierarchy
    case (lookupTypeVar "TypeVar1" deepTypeEnv, lookupTypeVar "TypeVar75" deepTypeEnv) of
      (Right (RMacro "BaseType" [] _), Right (RMacro "TypeVar74" [] _)) -> return ()
      results -> expectationFailure $ "Deep type environment failed: " ++ show results

  it "validates contexts with pathological binding patterns" $ do
    -- Create a context that stress-tests validation
    let ctx = emptyContext
        -- Add many bindings of different types in a specific pattern
        addManyBindings 0 c = c
        addManyBindings n c =
          let termCtx = extendTermContext ("term" ++ show n) (RMacro "TermType" [] (initialPos "test")) c
              relCtx = extendRelContext ("rel" ++ show n) termCtx
           in addManyBindings (n - 1) relCtx
        complexCtx = addManyBindings 50 ctx
    -- Validation should succeed even with many bindings
    case validateContext complexCtx of
      Right () -> return ()
      Left err -> expectationFailure $ "Complex context validation failed: " ++ show err

  it "handles rapid context construction and destruction" $ do
    -- Test performance of building up and tearing down contexts
    let buildAndCheck n =
          let buildCtx 0 ctx = ctx
              buildCtx i ctx = buildCtx (i - 1) (extendTermContext ("rapid" ++ show i) (RMacro "Type" [] (initialPos "test")) ctx)
              builtCtx = buildCtx n emptyContext
           in contextSize builtCtx
        size50 = buildAndCheck 50
        size100 = buildAndCheck 100
    size50 `shouldBe` 50
    size100 `shouldBe` 100

  it "handles variable lookup performance with scattered patterns" $ do
    -- Create context where variables are spread throughout
    let buildScatteredContext n ctx =
          if n <= 0
            then ctx
            else
              let termCtx = extendTermContext ("scattered" ++ show n) (RMacro "Type" [] (initialPos "test")) ctx
                  relCtx = extendRelContext ("rel" ++ show n) termCtx
                  proofCtx =
                    extendProofContext
                      ("proof" ++ show n)
                      (RelJudgment (Var "x" (-1) (initialPos "test")) (RVar ("rel" ++ show n) 0 (initialPos "test")) (Var "y" (-1) (initialPos "test")))
                      relCtx
               in buildScatteredContext (n - 1) proofCtx
        scatteredCtx = buildScatteredContext 75 emptyContext
    -- Test lookup at various depths
    case (lookupTerm "scattered1" scatteredCtx, lookupTerm "scattered37" scatteredCtx, lookupTerm "scattered75" scatteredCtx) of
      (Right (_, _), Right (_, _), Right (_, _)) -> return ()
      results -> expectationFailure $ "Scattered pattern lookup failed: " ++ show results

-- | Test theorem environment operations
theoremEnvironmentSpec :: Spec
theoremEnvironmentSpec = describe "theorem environment operations" $ do
  it "creates empty theorem environments correctly" $ do
    let theoremEnv = emptyContext
    Map.size (theoremDefinitions theoremEnv) `shouldBe` 0

  it "extends theorem environment with single theorem" $ do
    let bindings = [TermBinding "t"]
        judgment = RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test"))
        proof = Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test")
        theoremEnv = extendTheoremContext "identity" bindings judgment proof emptyContext
    Map.size (theoremDefinitions theoremEnv) `shouldBe` 1

  it "looks up theorems correctly" $ do
    let bindings = [TermBinding "t"]
        judgment = RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test"))
        proof = Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test")
        theoremEnv = extendTheoremContext "identity" bindings judgment proof emptyContext
    case lookupTheorem "identity" theoremEnv of
      Right (foundBindings, foundJudgment, foundProof) -> do
        foundBindings `shouldBe` bindings
        foundJudgment `shouldBe` judgment
        foundProof `shouldBe` proof
      Left err -> expectationFailure $ "Expected successful theorem lookup: " ++ show err

  it "fails lookup for undefined theorems" $ do
    let theoremEnv = emptyContext
    case lookupTheorem "nonexistent" theoremEnv of
      Left _ -> return () -- Expected failure
      Right _ -> expectationFailure "Expected failure for undefined theorem lookup"

  it "handles multiple theorem definitions" $ do
    -- Create multiple theorems
    let theorem1 =
          extendTheoremContext
            "identity"
            [TermBinding "t"]
            (RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test")))
            (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test"))
            emptyContext
        theorem2 =
          extendTheoremContext
            "composition"
            [TermBinding "x", TermBinding "y", TermBinding "z"]
            (RelJudgment (Var "x" 2 (initialPos "test")) (Comp (RMacro "R" [] (initialPos "test")) (RMacro "S" [] (initialPos "test")) (initialPos "test")) (Var "z" 0 (initialPos "test")))
            (PVar "compProof" 0 (initialPos "test"))
            theorem1

    Map.size (theoremDefinitions theorem2) `shouldBe` 2

    -- Test both lookups work
    case (lookupTheorem "identity" theorem2, lookupTheorem "composition" theorem2) of
      (Right _, Right _) -> return ()
      results -> expectationFailure $ "Expected both theorem lookups to succeed: " ++ show results

  it "handles theorems with complex binding structures" $ do
    -- Test theorem with mixed binding types
    let complexBindings =
          [ TermBinding "t",
            RelBinding "R",
            ProofBinding "p" (RelJudgment (Var "t" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")))
          ]
        complexJudgment = RelJudgment (Var "t" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "t" 0 (initialPos "test"))
        complexProof = PVar "p" 0 (initialPos "test")
        theoremEnv = extendTheoremContext "complex" complexBindings complexJudgment complexProof emptyContext

    case lookupTheorem "complex" theoremEnv of
      Right (foundBindings, foundJudgment, foundProof) -> do
        length foundBindings `shouldBe` 3
        foundJudgment `shouldBe` complexJudgment
        foundProof `shouldBe` complexProof
      Left err -> expectationFailure $ "Expected successful complex theorem lookup: " ++ show err

  it "handles theorem environment extension with duplicates" $ do
    -- Test behavior when extending with same theorem name (should overwrite)
    let theorem1 =
          extendTheoremContext
            "test"
            [TermBinding "x"]
            (RelJudgment (Var "x" 0 (initialPos "test")) (RMacro "R1" [] (initialPos "test")) (Var "x" 0 (initialPos "test")))
            (PVar "proof1" 0 (initialPos "test"))
            emptyContext
        theorem2 =
          extendTheoremContext
            "test" -- Same name
            [TermBinding "y"]
            (RelJudgment (Var "y" 0 (initialPos "test")) (RMacro "R2" [] (initialPos "test")) (Var "y" 0 (initialPos "test")))
            (PVar "proof2" 0 (initialPos "test"))
            theorem1

    Map.size (theoremDefinitions theorem2) `shouldBe` 1 -- Should still be 1 (overwritten)
    case lookupTheorem "test" theorem2 of
      Right (foundBindings, foundJudgment, _) -> do
        -- Should have the second theorem's data
        foundBindings `shouldBe` [TermBinding "y"]
        foundJudgment `shouldBe` RelJudgment (Var "y" 0 (initialPos "test")) (RMacro "R2" [] (initialPos "test")) (Var "y" 0 (initialPos "test"))
      Left err -> expectationFailure $ "Expected successful overwritten theorem lookup: " ++ show err

  it "handles large theorem environments efficiently" $ do
    -- Performance test: create many theorems
    let buildTheoremEnv 0 env = env
        buildTheoremEnv n env =
          let name = "theorem" ++ show n
              bindings = [TermBinding ("t" ++ show n)]
              judgment = RelJudgment (Var ("t" ++ show n) 0 (initialPos "test")) (RMacro ("R" ++ show n) [] (initialPos "test")) (Var ("t" ++ show n) 0 (initialPos "test"))
              proof = Iota (Var ("t" ++ show n) 0 (initialPos "test")) (Var ("t" ++ show n) 0 (initialPos "test")) (initialPos "test")
           in buildTheoremEnv (n - 1) (extendTheoremContext name bindings judgment proof env)
        largeEnv = buildTheoremEnv 100 emptyContext

    Map.size (theoremDefinitions largeEnv) `shouldBe` 100

    -- Test lookups at various positions
    case (lookupTheorem "theorem1" largeEnv, lookupTheorem "theorem50" largeEnv, lookupTheorem "theorem100" largeEnv) of
      (Right _, Right _, Right _) -> return ()
      results -> expectationFailure $ "Expected all large environment lookups to succeed: " ++ show results

  it "validates theorem environment consistency" $ do
    -- Test that theorem environments maintain expected invariants
    let validTheorem =
          extendTheoremContext
            "valid"
            [TermBinding "t"]
            (RelJudgment (Var "t" 0 (initialPos "test")) (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "t" 0 (initialPos "test")))
            (Iota (Var "t" 0 (initialPos "test")) (Var "t" 0 (initialPos "test")) (initialPos "test"))
            emptyContext

    -- Test basic invariants
    Map.size (theoremDefinitions validTheorem) `shouldBe` 1
    Map.member "valid" (theoremDefinitions validTheorem) `shouldBe` True
    Map.member "invalid" (theoremDefinitions validTheorem) `shouldBe` False
