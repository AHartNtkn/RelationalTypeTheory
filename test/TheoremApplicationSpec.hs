module TheoremApplicationSpec (spec) where

import Parser.Legacy (parseFile, runParserEmpty)
import Test.Hspec

-- Test the fundamental theorem application bug
spec :: Spec
spec = describe "Theorem Application" $ do
  it "should parse basic theorem application (most fundamental test)" $ do
    -- Test the absolute basics: theorem_name argument
    let fileContent =
          unlines
            [ "⊢ simple_thm (x : Term) : x [λy.y] x := ι⟨x,(λy.y)⟩;",
              "⊢ use_simple (a : Term) : a [λy.y] a := simple_thm a;"
            ]
    let result = runParserEmpty parseFile fileContent
    result `shouldSatisfy` isRight

  it "should parse theorem application with multiple arguments" $ do
    -- Test theorem application with multiple arguments
    let fileContent =
          unlines
            [ "⊢ two_arg_thm (x : Term) (y : Term) : x [λz.z] y := ι⟨x,(λz.z)⟩;",
              "⊢ use_two_args (a : Term) (b : Term) : a [λz.z] b := two_arg_thm a b;"
            ]
    let result = runParserEmpty parseFile fileContent
    result `shouldSatisfy` isRight

  it "should parse theorem application as direct proof term" $ do
    -- Test using theorem application as the entire proof body
    let fileContent =
          unlines
            [ "⊢ identity_thm (t : Term) : t [λx.x] t := ι⟨t,(λx.x)⟩;",
              "⊢ use_identity : (λw.w) [λx.x] (λw.w) := identity_thm (λw.w);"
            ]
    let result = runParserEmpty parseFile fileContent
    result `shouldSatisfy` isRight

  it "should parse theorem application in lambda abstraction" $ do
    -- Test theorem application inside a lambda
    let fileContent =
          unlines
            [ "⊢ base_thm (x : Term) : x [λy.y] x := ι⟨x,(λy.y)⟩;",
              "⊢ lambda_test (z : Term) : z [λy.y] z := λp:(λy.y). base_thm z;"
            ]
    let result = runParserEmpty parseFile fileContent
    result `shouldSatisfy` isRight

  it "should parse theorem application in pair" $ do
    -- Test theorem application in composition pairs
    let fileContent =
          unlines
            [ "id := λx.x;",
              "⊢ id_thm (t : Term) : t [id] t := ι⟨t,id⟩;",
              "⊢ compose_test (a : Term) (b : Term) : a [id ∘ id] b := (id_thm a, id_thm b);"
            ]
    let result = runParserEmpty parseFile fileContent
    result `shouldSatisfy` isRight

  it "should parse theorem application in parentheses" $ do
    -- Test theorem application with parentheses
    let fileContent =
          unlines
            [ "⊢ paren_thm (x : Term) : x [λy.y] x := ι⟨x,(λy.y)⟩;",
              "⊢ use_parens (a : Term) : a [λy.y] a := (paren_thm a);"
            ]
    let result = runParserEmpty parseFile fileContent
    result `shouldSatisfy` isRight

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False
