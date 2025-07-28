{-# LANGUAGE OverloadedStrings #-}

module MacroBinderSpec (spec) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Core.Syntax
import Operations.Generic.Macro (renameBinderVarsG, substituteArgsG, inferParamInfosG)
import TestHelpers (simpleTermMacro, simpleRelMacro)
import Test.Hspec
import Text.Megaparsec (initialPos)

spec :: Spec
spec = do
  paramInfoInferenceSpec
  binderAwareSubstitutionSpec
  mixfixBinderOrderSpec
  nestedBinderSpec
  errorHandlingSpec

-- Test automatic parameter inference
paramInfoInferenceSpec :: Spec
paramInfoInferenceSpec = describe "Parameter inference" $ do
  it "detects lambda binders in term macros" $ do
    let params = ["x", "t"]
        body = Lam "x" (Var "t" 0 (initialPos "test")) (initialPos "test")
        inferred = inferParamInfosG params body
    
    -- x should be detected as a binder
    pBinds (inferred !! 0) `shouldBe` True
    pKind (inferred !! 0) `shouldBe` TermK
    
    -- t should depend on x (index 0)
    pDeps (inferred !! 1) `shouldBe` [0]
    pBinds (inferred !! 1) `shouldBe` False

  it "detects forall binders in relational macros" $ do
    let params = ["X", "T"]
        body = All "X" (RVar "T" 0 (initialPos "test")) (initialPos "test")
        inferred = inferParamInfosG params body
    
    -- X should be detected as a binder
    pBinds (inferred !! 0) `shouldBe` True
    pKind (inferred !! 0) `shouldBe` RelK
    
    -- T should depend on X (index 0)
    pDeps (inferred !! 1) `shouldBe` [0]
    pBinds (inferred !! 1) `shouldBe` False

  it "detects no binders in composition macros" $ do
    let params = ["R", "S"]
        body = Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")
        inferred = inferParamInfosG params body
    
    -- Neither R nor S should be binders
    pBinds (inferred !! 0) `shouldBe` False
    pBinds (inferred !! 1) `shouldBe` False
    
    -- No dependencies
    pDeps (inferred !! 0) `shouldBe` []
    pDeps (inferred !! 1) `shouldBe` []

  it "detects proof binders in proof macros" $ do
    let params = ["x", "R", "p"]
        body = LamP "x" (RVar "R" 1 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (initialPos "test")
        inferred = inferParamInfosG params body
    
    -- x should be detected as a proof binder
    pBinds (inferred !! 0) `shouldBe` True
    pKind (inferred !! 0) `shouldBe` ProofK
    
    -- p should depend on x (index 0)
    pDeps (inferred !! 2) `shouldBe` [0]

  it "detects multiple binders in Pi" $ do
    let params = ["p1", "x", "u", "v", "p2"]
        body = Pi (PVar "p1" 4 (initialPos "test")) "x" "u" "v" (PVar "p2" 0 (initialPos "test")) (initialPos "test")
        inferred = inferParamInfosG params body
    
    -- x should be a term binder
    pBinds (inferred !! 1) `shouldBe` True
    pKind (inferred !! 1) `shouldBe` TermK
    
    -- u should be a proof binder
    pBinds (inferred !! 2) `shouldBe` True
    pKind (inferred !! 2) `shouldBe` ProofK
    
    -- v should be a proof binder
    pBinds (inferred !! 3) `shouldBe` True
    pKind (inferred !! 3) `shouldBe` ProofK
    
    -- p2 should depend on x, u, v (indices 1, 2, 3)
    Set.fromList (pDeps (inferred !! 4)) `shouldBe` Set.fromList [1, 2, 3]

-- Test binder-aware substitution
binderAwareSubstitutionSpec :: Spec
binderAwareSubstitutionSpec = describe "Binder-aware substitution" $ do
  it "renames binder variables correctly" $ do
    let sig = [ParamInfo "x" TermK True [], ParamInfo "t" TermK False [0]]
        actuals = [Var "y" 0 (initialPos "test"), Var "body" 0 (initialPos "test")]
        body = Lam "x" (Var "t" 0 (initialPos "test")) (initialPos "test")
        result = renameBinderVarsG sig actuals body
    
    case result of
      Lam name _ _ -> name `shouldBe` "y"  -- x should be renamed to y
      _ -> expectationFailure "Expected lambda after renaming"

  it "substitutes non-binder arguments with shifting" $ do
    let sig = [ParamInfo "x" TermK True [], ParamInfo "t" TermK False [0]]
        actuals = [Var "y" 0 (initialPos "test"), Var "body" 0 (initialPos "test")]
        body = Lam "x" (Var "t" 0 (initialPos "test")) (initialPos "test")
        renamed = renameBinderVarsG sig actuals body
        result = substituteArgsG sig actuals renamed
    
    case result of
      Lam _ (Var name idx _) _ -> do
        name `shouldBe` "body"  -- t should be substituted with body
        idx `shouldBe` 1        -- shifted by 1 due to lambda binder
      _ -> expectationFailure "Expected lambda with substituted body"

  it "handles composition without binders" $ do
    let sig = [ParamInfo "R" RelK False [], ParamInfo "S" RelK False []]
        actuals = [RVar "A" 0 (initialPos "test"), RVar "B" 0 (initialPos "test")]
        body = Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")
        result = substituteArgsG sig actuals body
    
    case result of
      Comp (RVar name1 _ _) (RVar name2 _ _) _ -> do
        name1 `shouldBe` "A"  -- R substituted with A
        name2 `shouldBe` "B"  -- S substituted with B
      _ -> expectationFailure "Expected composition with substituted args"

-- Test mix-fix with different parameter orders
mixfixBinderOrderSpec :: Spec
mixfixBinderOrderSpec = describe "Mix-fix parameter order independence" $ do
  it "handles binder-first patterns like λ_._" $ do
    let sig = [ParamInfo "x" TermK True [], ParamInfo "t" TermK False [0]]
        actuals = [Var "var" 0 (initialPos "test"), Var "expr" 0 (initialPos "test")]
        body = Lam "x" (Var "t" 0 (initialPos "test")) (initialPos "test")
        renamed = renameBinderVarsG sig actuals body
        result = substituteArgsG sig actuals renamed
    
    case result of
      Lam name (Var bodyName bodyIdx _) _ -> do
        name `shouldBe` "var"     -- binder renamed
        bodyName `shouldBe` "expr" -- body substituted
        bodyIdx `shouldBe` 1      -- shifted under binder
      _ -> expectationFailure "Expected proper lambda expansion"

  it "handles argument-first patterns like _|λ_" $ do
    -- Pattern where argument comes before binder: arg |λ x . body
    let sig = [ParamInfo "arg" TermK False [], ParamInfo "x" TermK True [], ParamInfo "body" TermK False [1]]
        actuals = [Var "a" 0 (initialPos "test"), Var "y" 0 (initialPos "test"), Var "b" 0 (initialPos "test")]
        macroBody = App (Var "arg" 2 (initialPos "test")) 
                       (Lam "x" (Var "body" 0 (initialPos "test")) (initialPos "test"))
                       (initialPos "test")
        renamed = renameBinderVarsG sig actuals macroBody
        result = substituteArgsG sig actuals renamed
    
    case result of
      App (Var argName argIdx _) (Lam binderName (Var bodyName bodyIdx _) _) _ -> do
        argName `shouldBe` "a"      -- arg substituted
        argIdx `shouldBe` 2         -- shifted by 0 (no binders to left of arg)
        binderName `shouldBe` "y"   -- binder renamed
        bodyName `shouldBe` "b"     -- body substituted
        bodyIdx `shouldBe` 1        -- shifted by 1 (one binder to left of body)
      _ -> expectationFailure "Expected application with lambda"

-- Test nested binders
nestedBinderSpec :: Spec
nestedBinderSpec = describe "Nested binder handling" $ do
  it "handles nested lambdas correctly" $ do
    let sig = [ParamInfo "x" TermK True [], ParamInfo "y" TermK True [], ParamInfo "body" TermK False [0,1]]
        actuals = [Var "a" 0 (initialPos "test"), Var "b" 0 (initialPos "test"), Var "expr" 0 (initialPos "test")]
        macroBody = Lam "x" (Lam "y" (Var "body" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        renamed = renameBinderVarsG sig actuals macroBody
        result = substituteArgsG sig actuals renamed
    
    case result of
      Lam outerName (Lam innerName (Var bodyName bodyIdx _) _) _ -> do
        outerName `shouldBe` "a"    -- x renamed to a
        innerName `shouldBe` "b"    -- y renamed to b
        bodyName `shouldBe` "expr"  -- body substituted
        bodyIdx `shouldBe` 2        -- shifted by 2 (under both binders)
      _ -> expectationFailure "Expected nested lambdas"

  it "tracks dependencies correctly with multiple binders" $ do
    let params = ["x", "y", "body"]
        astBody = Lam "x" (Lam "y" (Var "body" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        inferred = inferParamInfosG params astBody
    
    -- x is a binder
    pBinds (inferred !! 0) `shouldBe` True
    pDeps (inferred !! 0) `shouldBe` []
    
    -- y is a binder that depends on x
    pBinds (inferred !! 1) `shouldBe` True  
    pDeps (inferred !! 1) `shouldBe` [0]
    
    -- body depends on both x and y
    pBinds (inferred !! 2) `shouldBe` False
    Set.fromList (pDeps (inferred !! 2)) `shouldBe` Set.fromList [0, 1]

-- Test error cases
errorHandlingSpec :: Spec
errorHandlingSpec = describe "Error handling" $ do
  it "handles empty parameter lists" $ do
    let inferred = inferParamInfosG [] (Var "x" 0 (initialPos "test"))
    inferred `shouldBe` []

  it "handles unknown variables in macro body" $ do
    let params = ["x"]
        body = Var "unknown" 0 (initialPos "test")
        inferred = inferParamInfosG params body
    
    -- unknown variable should not affect inference
    pBinds (inferred !! 0) `shouldBe` False
    pDeps (inferred !! 0) `shouldBe` []

  it "maintains correct indices with gaps" $ do
    let params = ["a", "b", "c"]
        body = Lam "a" (Var "c" 0 (initialPos "test")) (initialPos "test") -- skips b
        inferred = inferParamInfosG params body
    
    -- a is a binder
    pBinds (inferred !! 0) `shouldBe` True
    
    -- b is not referenced
    pBinds (inferred !! 1) `shouldBe` False
    pDeps (inferred !! 1) `shouldBe` []
    
    -- c depends on a (index 0)
    pBinds (inferred !! 2) `shouldBe` False
    pDeps (inferred !! 2) `shouldBe` [0]