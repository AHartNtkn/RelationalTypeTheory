module TheoremApplicationSpec (spec) where

import qualified RawParser as Raw
import Elaborate
import Context (noMacros, noTheorems, extendMacroEnvironment, extendTheoremEnvironment)
import qualified Data.Map as Map
import Text.Megaparsec (runParser, errorBundlePretty)
import Lib
import Test.Hspec

-- Helper functions for two-phase parsing
parseFileWithTwoPhase :: String -> Either String [Declaration]
parseFileWithTwoPhase content = do
  rawDecls <- case runParser Raw.parseFile "test" content of
    Left err -> Left (errorBundlePretty err)
    Right raw -> Right raw
  let ctx = emptyElaborateContext Map.empty noMacros noTheorems
  case elaborateDeclarationsWithAccumulation ctx rawDecls of
    Left err -> Left (show err)
    Right decls -> Right decls

-- Helper function to elaborate declarations while threading the environment
elaborateDeclarationsWithAccumulation :: ElaborateContext -> [Raw.RawDeclaration] -> Either ElaborateError [Declaration]
elaborateDeclarationsWithAccumulation _ [] = Right []
elaborateDeclarationsWithAccumulation ctx (rawDecl:rest) = do
  decl <- elaborateDeclaration ctx rawDecl
  let updatedCtx = updateContextWithDeclaration ctx decl
  restDecls <- elaborateDeclarationsWithAccumulation updatedCtx rest
  return (decl : restDecls)

-- Update context with newly elaborated declaration
updateContextWithDeclaration :: ElaborateContext -> Declaration -> ElaborateContext
updateContextWithDeclaration ctx (MacroDef name params body) =
  let newMacroEnv = extendMacroEnvironment name params body defaultFixity (macroEnv ctx)
  in ctx { macroEnv = newMacroEnv }
updateContextWithDeclaration ctx (FixityDecl fixity name) =
  let currentMacroEnv = macroEnv ctx
      newMacroEnv = currentMacroEnv { macroFixities = Map.insert name fixity (macroFixities currentMacroEnv) }
  in ctx { macroEnv = newMacroEnv }
updateContextWithDeclaration ctx (TheoremDef name bindings judgment proof) =
  let newTheoremEnv = extendTheoremEnvironment name bindings judgment proof (theoremEnv ctx)
  in ctx { theoremEnv = newTheoremEnv }
updateContextWithDeclaration ctx _ = ctx  -- Other declarations don't affect context

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
    let result = parseFileWithTwoPhase fileContent
    result `shouldSatisfy` isRight

  it "should parse theorem application with multiple arguments" $ do
    -- Test theorem application with multiple arguments
    let fileContent =
          unlines
            [ "⊢ two_arg_thm (x : Term) (y : Term) : x [λz.z] y := ι⟨x,(λz.z)⟩;",
              "⊢ use_two_args (a : Term) (b : Term) : a [λz.z] b := two_arg_thm a b;"
            ]
    let result = parseFileWithTwoPhase fileContent
    result `shouldSatisfy` isRight

  it "should parse theorem application as direct proof term" $ do
    -- Test using theorem application as the entire proof body
    let fileContent =
          unlines
            [ "⊢ identity_thm (t : Term) : t [λx.x] t := ι⟨t,(λx.x)⟩;",
              "⊢ use_identity : (λw.w) [λx.x] (λw.w) := identity_thm (λw.w);"
            ]
    let result = parseFileWithTwoPhase fileContent
    result `shouldSatisfy` isRight

  it "should parse theorem application in lambda abstraction" $ do
    -- Test theorem application inside a lambda
    let fileContent =
          unlines
            [ "⊢ base_thm (x : Term) : x [λy.y] x := ι⟨x,(λy.y)⟩;",
              "⊢ lambda_test (z : Term) : z [λy.y] z := λp:(λy.y). base_thm z;"
            ]
    let result = parseFileWithTwoPhase fileContent
    result `shouldSatisfy` isRight

  it "should parse theorem application in pair" $ do
    -- Test theorem application in composition pairs
    let fileContent =
          unlines
            [ "id := λx.x;",
              "⊢ id_thm (t : Term) : t [id] t := ι⟨t,id⟩;",
              "⊢ compose_test (a : Term) (b : Term) : a [id ∘ id] b := (id_thm a, id_thm b);"
            ]
    let result = parseFileWithTwoPhase fileContent
    result `shouldSatisfy` isRight

  it "should parse theorem application in parentheses" $ do
    -- Test theorem application with parentheses
    let fileContent =
          unlines
            [ "⊢ paren_thm (x : Term) : x [λy.y] x := ι⟨x,(λy.y)⟩;",
              "⊢ use_parens (a : Term) : a [λy.y] a := (paren_thm a);"
            ]
    let result = parseFileWithTwoPhase fileContent
    result `shouldSatisfy` isRight

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False
