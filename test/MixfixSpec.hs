{-# LANGUAGE OverloadedStrings #-}

module MixfixSpec (spec) where

import Context (extendMacroEnvironment, extendTheoremEnvironment, noMacros, noTheorems)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lib
import qualified RawParser as Raw
import Elaborate
import PrettyPrint (prettyDeclaration, prettyTerm)
import Test.Hspec
import TestHelpers
import Text.Megaparsec (eof, errorBundlePretty, initialPos, runParser)

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

parseDeclarationWithTwoPhase :: String -> Either String Declaration
parseDeclarationWithTwoPhase content = do
  rawDecl <- case runParser Raw.parseDeclaration "test" content of
    Left err -> Left (errorBundlePretty err)
    Right raw -> Right raw
  let ctx = emptyElaborateContext Map.empty noMacros noTheorems
  case elaborateDeclaration ctx rawDecl of
    Left err -> Left (show err)
    Right decl -> Right decl

parseTermWithTwoPhase :: MacroEnvironment -> [String] -> String -> Either String Term
parseTermWithTwoPhase testMacroEnv testTermVars content = do
  rawTerm <- case runParser Raw.parseTerm "test" content of
    Left err -> Left (errorBundlePretty err)
    Right raw -> Right raw
  let termVarMap = Map.fromList (zip testTermVars (reverse [0 .. length testTermVars - 1]))
      ctx = (emptyElaborateContext Map.empty testMacroEnv noTheorems) { termVars = termVarMap }
  case elaborateTerm ctx rawTerm of
    Left err -> Left (show err)
    Right term -> Right term

parseRTypeWithTwoPhase :: MacroEnvironment -> [String] -> String -> Either String RType
parseRTypeWithTwoPhase testMacroEnv testRelVars content = do
  rawRType <- case runParser Raw.parseRType "test" content of
    Left err -> Left (errorBundlePretty err)
    Right raw -> Right raw
  let relVarMap = Map.fromList (zip testRelVars (reverse [0 .. length testRelVars - 1]))
      ctx = (emptyElaborateContext Map.empty testMacroEnv noTheorems) { relVars = relVarMap }
  case elaborateRType ctx rawRType of
    Left err -> Left (show err)
    Right rtype -> Right rtype

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

spec :: Spec
spec = do
  mixfixIdentifierSpec
  fixityDeclSpec
  mixfixMacroDefSpec
  mixfixPrettyPrintSpec
  mixfixOperatorTableSpec
  mixfixParsingSpec  
  relationalMixfixSpec
  mixfixBugSpec
  mixfixComplexSpec
  mixfixUnicodeSpec
  fixityOrderingSpec

-- Test the mixfixIdentifier parser itself
mixfixIdentifierSpec :: Spec
mixfixIdentifierSpec = describe "mixfixIdentifier parser" $ do
  it "parses underscore-prefixed identifiers" $ do
    testParseIdentifier "_+_" "_+_"
    testParseIdentifier "_*_" "_*_"
    testParseIdentifier "not_" "not_"

  it "parses complex mixfix patterns" $ do
    testParseIdentifier "if_then_else_" "if_then_else_"
    testParseIdentifier "while_do_" "while_do_"

  it "parses operator symbols" $ do
    testParseIdentifier "+++" "+++"
    testParseIdentifier "==>" "==>"
    testParseIdentifier "<->" "<->"
  where
    testParseIdentifier input expected =
      case runParser (Raw.mixfixIdentifier <* eof) "test" input of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right result -> result `shouldBe` expected

-- Test fixity declaration parsing
fixityDeclSpec :: Spec
fixityDeclSpec = describe "Fixity declaration parsing" $ do
  it "parses infixl declarations" $ do
    testParseDecl "infixl 6 _+_;" (FixityDecl (Infixl 6) "_+_")
    testParseDecl "infixl 0 _or_;" (FixityDecl (Infixl 0) "_or_")
    testParseDecl "infixl 9 _compose_;" (FixityDecl (Infixl 9) "_compose_")

  it "parses infixr declarations" $ do
    testParseDecl "infixr 5 _*_;" (FixityDecl (Infixr 5) "_*_")
    testParseDecl "infixr 1 _cons_;" (FixityDecl (Infixr 1) "_cons_")

  it "parses infix declarations" $ do
    testParseDecl "infix 4 _==_;" (FixityDecl (InfixN 4) "_==_")
    testParseDecl "infix 7 _mod_;" (FixityDecl (InfixN 7) "_mod_")

  it "parses prefix declarations" $ do
    testParseDecl "prefix 9 not_;" (FixityDecl (Prefix 9) "not_")
    testParseDecl "prefix 8 neg_;" (FixityDecl (Prefix 8) "neg_")

  it "parses postfix declarations" $ do
    testParseDecl "postfix 9 _!;" (FixityDecl (Postfix 9) "_!")
    testParseDecl "postfix 7 _squared;" (FixityDecl (Postfix 7) "_squared")

  it "rejects invalid precedence levels" $ do
    testParseFailure "infixl 10 _+_;"
    testParseFailure "infixr -1 _*_;"
  where
    testParseDecl input expected =
      case parseDeclarationWithTwoPhase input of
        Left err -> expectationFailure $ "Parse failed: " ++ err
        Right result -> result `shouldBeEqual` expected

    testParseFailure input =
      case parseDeclarationWithTwoPhase input of
        Left _ -> return () -- Expected failure
        Right result -> expectationFailure $ "Expected parse failure, but got: " ++ show result

-- Test mixfix macro definition parsing
mixfixMacroDefSpec :: Spec
mixfixMacroDefSpec = describe "Mixfix macro definition parsing" $ do
  it "parses binary infix macros with auto-parameters" $ do
    testParseDecl "_+_ a b := a;" (MacroDef "_+_" ["a", "b"] (TermMacro (Var "a" 1 (initialPos "test"))))

  it "parses ternary mixfix macros with auto-parameters" $ do
    testParseDecl
      "if_then_else_ c t e := t;"
      ( MacroDef
          "if_then_else_"
          ["c", "t", "e"]
          (TermMacro (Var "t" 1 (initialPos "test")))
      )

  it "parses prefix macros" $ do
    testParseDecl "not_ b := b;" (MacroDef "not_" ["b"] (TermMacro (Var "b" 0 (initialPos "test"))))

  it "parses postfix macros" $ do
    testParseDecl "_! n := n;" (MacroDef "_!" ["n"] (TermMacro (Var "n" 0 (initialPos "test"))))

  it "handles explicit parameters overriding auto-parameters" $ do
    testParseDecl "_+_ x y := x;" (MacroDef "_+_" ["x", "y"] (TermMacro (Var "x" 1 (initialPos "test"))))
  where
    testParseDecl input expected =
      case parseDeclarationWithTwoPhase input of
        Left err -> expectationFailure $ "Parse failed: " ++ err
        Right result -> result `shouldBeEqual` expected

-- Test mixfix pretty printing
mixfixPrettyPrintSpec :: Spec
mixfixPrettyPrintSpec = describe "Mixfix pretty printing" $ do
  it "pretty prints binary infix notation" $ do
    let term = TMacro "_+_" [Var "a" 0 (initialPos "test"), Var "b" 1 (initialPos "test")] (initialPos "test")
    prettyTerm term `shouldBe` "a + b"

  it "pretty prints ternary mixfix notation" $ do
    let term = TMacro "if_then_else_" [Var "c" 2 (initialPos "test"), Var "t" 1 (initialPos "test"), Var "e" 0 (initialPos "test")] (initialPos "test")
    prettyTerm term `shouldBe` "if c then t else e"

  it "pretty prints prefix notation" $ do
    let term = TMacro "not_" [Var "b" 0 (initialPos "test")] (initialPos "test")
    prettyTerm term `shouldBe` "not b"

  it "pretty prints postfix notation" $ do
    let term = TMacro "_!" [Var "n" 0 (initialPos "test")] (initialPos "test")
    prettyTerm term `shouldBe` "n !"

  it "pretty prints fixity declarations" $ do
    prettyDeclaration (FixityDecl (Infixl 6) "_+_") `shouldBe` "infixl 6 _+_;"
    prettyDeclaration (FixityDecl (Prefix 9) "not_") `shouldBe` "prefix 9 not_;"
    prettyDeclaration (FixityDecl (Postfix 7) "_!") `shouldBe` "postfix 7 _!;"

-- Test complex mixfix scenarios
mixfixComplexSpec :: Spec
mixfixComplexSpec = describe "Complex mixfix scenarios" $ do
  it "parses complete mixfix file" $ do
    let content =
          unlines
            [ "infixl 6 _+_;",
              "_+_ a b := a;",
              "infixr 5 _*_;",
              "_*_ x y := x;",
              "prefix 9 not_;",
              "not_ b := b;",
              "if_then_else_ c t e := t;"
            ]
    case parseFileWithTwoPhase content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right decls -> length decls `shouldBe` 7

  it "handles holes function correctly" $ do
    holes "_+_" `shouldBe` 2
    holes "if_then_else_" `shouldBe` 3
    holes "not_" `shouldBe` 1
    holes "_!" `shouldBe` 1
    holes "regular" `shouldBe` 0

  it "handles splitMixfix function correctly" $ do
    splitMixfix "_+_" `shouldBe` ["+"]
    splitMixfix "if_then_else_" `shouldBe` ["if", "then", "else"]
    splitMixfix "not_" `shouldBe` ["not"]
    splitMixfix "_!" `shouldBe` ["!"]
    splitMixfix "regular" `shouldBe` ["regular"]

  it "handles parseMixfixPattern function correctly" $ do
    parseMixfixPattern "_+_" `shouldBe` [Hole, Literal "+", Hole]
    parseMixfixPattern "if_then_else_" `shouldBe` [Literal "if", Hole, Literal "then", Hole, Literal "else", Hole]
    parseMixfixPattern "not_" `shouldBe` [Literal "not", Hole]
    parseMixfixPattern "_!" `shouldBe` [Hole, Literal "!"]
    parseMixfixPattern "regular" `shouldBe` [Literal "regular"]

  it "handles mixfixKeywords function correctly" $ do
    let env =
          MacroEnvironment
            { macroDefinitions =
                Map.fromList
                  [ ("_+_", (["a", "b"], TermMacro (Var "dummy" 0 (initialPos "test")))),
                    ("if_then_else_", (["c", "t", "e"], TermMacro (Var "dummy" 0 (initialPos "test")))),
                    ("not_", (["x"], TermMacro (Var "dummy" 0 (initialPos "test"))))
                  ],
              macroFixities = Map.empty
            }
    mixfixKeywords env `shouldBe` Set.fromList ["+", "if", "then", "else", "not"]

  it "preserves round-trip parsing and pretty printing" $ do
    let originalDecls =
          [ FixityDecl (Infixl 6) "_+_",
            MacroDef "_+_" ["a", "b"] (TermMacro (Var "a" 1 (initialPos "test")))
          ]
    let prettyPrinted = unlines (map prettyDeclaration originalDecls)
    case parseFileWithTwoPhase prettyPrinted of
      Left err -> expectationFailure $ "Re-parse failed: " ++ err
      Right reparsedDecls -> reparsedDecls `shouldBeEqual` originalDecls

-- Test unicode support in mixfix operations
mixfixUnicodeSpec :: Spec
mixfixUnicodeSpec = describe "Unicode mixfix operations" $ do
  it "parses unicode infix macro identifiers" $ do
    testParseIdentifier "_∪_" "_∪_"
    testParseIdentifier "_∩_" "_∩_"
    testParseIdentifier "_≤_" "_≤_"
    testParseIdentifier "_≥_" "_≥_"
    testParseIdentifier "_≠_" "_≠_"
    testParseIdentifier "_⊆_" "_⊆_"

  it "parses unicode prefix macro identifiers" $ do
    testParseIdentifier "¬_" "¬_"
    testParseIdentifier "√_" "√_"
    testParseIdentifier "∀_" "∀_"
    testParseIdentifier "∃_" "∃_"

  it "parses unicode postfix macro identifiers" $ do
    testParseIdentifier "_†" "_†"
    testParseIdentifier "_⁻¹" "_⁻¹"
    testParseIdentifier "_°" "_°"
    testParseIdentifier "_★" "_★"

  it "parses unicode ternary mixfix identifiers" $ do
    testParseIdentifier "⟨_∣_∣_⟩" "⟨_∣_∣_⟩"
    testParseIdentifier "∑_∈_·_" "∑_∈_·_"
    testParseIdentifier "if_then_else_fi" "if_then_else_fi"

  it "parses fixity declarations with unicode operators" $ do
    testParseDecl "infixl 6 _∪_;" (FixityDecl (Infixl 6) "_∪_")
    testParseDecl "infixr 7 _∩_;" (FixityDecl (Infixr 7) "_∩_")
    testParseDecl "prefix 9 ¬_;" (FixityDecl (Prefix 9) "¬_")
    testParseDecl "postfix 8 _†;" (FixityDecl (Postfix 8) "_†")

  it "parses unicode macro definitions" $ do
    testParseDecl "_∪_ a b := a;" (MacroDef "_∪_" ["a", "b"] (TermMacro (Var "a" 1 (initialPos "test"))))
    testParseDecl "¬_ x := x;" (MacroDef "¬_" ["x"] (TermMacro (Var "x" 0 (initialPos "test"))))
    testParseDecl "_† n := n;" (MacroDef "_†" ["n"] (TermMacro (Var "n" 0 (initialPos "test"))))

  it "pretty prints unicode mixfix operations" $ do
    let unionTerm = TMacro "_∪_" [Var "A" 1 (initialPos "test"), Var "B" 0 (initialPos "test")] (initialPos "test")
    prettyTerm unionTerm `shouldBe` "A ∪ B"

    let negTerm = TMacro "¬_" [Var "p" 0 (initialPos "test")] (initialPos "test")
    prettyTerm negTerm `shouldBe` "¬ p"

    let daggerTerm = TMacro "_†" [Var "M" 0 (initialPos "test")] (initialPos "test")
    prettyTerm daggerTerm `shouldBe` "M †"
  where
    testParseIdentifier input expected =
      case runParser (Raw.mixfixIdentifier <* eof) "test" input of
        Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
        Right result -> result `shouldBe` expected

    testParseDecl input expected =
      case parseDeclarationWithTwoPhase input of
        Left err -> expectationFailure $ "Parse failed: " ++ err
        Right result -> result `shouldBeEqual` expected

-- Test fixity declaration ordering
fixityOrderingSpec :: Spec
fixityOrderingSpec = describe "Fixity declaration ordering" $ do
  it "preserves fixity declarations when they come before macro definitions" $ do
    let content = "infixr 7 _*_;\n_*_ x y := x;"
    case parseFileWithTwoPhase content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right decls -> do
        let env = buildEnvironmentFromDecls decls
        case Map.lookup "_*_" (macroFixities env) of
          Nothing -> expectationFailure "No fixity found for _*_"
          Just fixity -> fixity `shouldBe` Infixr 7

  it "applies fixity declaration regardless of order" $ do
    let content = "_*_ x y := x;\ninfixr 7 _*_;"
    case parseFileWithTwoPhase content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right decls -> do
        let env = buildEnvironmentFromDecls decls
        case Map.lookup "_*_" (macroFixities env) of
          Nothing -> expectationFailure "No fixity found for _*_"
          Just fixity -> fixity `shouldBe` Infixr 7

  it "uses default fixity when no declaration is provided" $ do
    let content = "_*_ x y := x;"
    case parseFileWithTwoPhase content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right decls -> do
        let env = buildEnvironmentFromDecls decls
        case Map.lookup "_*_" (macroFixities env) of
          Nothing -> expectationFailure "No fixity found for _*_"
          Just fixity -> fixity `shouldBe` defaultFixity -- Use library default

  it "handles multiple fixity declarations correctly" $ do
    let content =
          unlines
            [ "infixr 7 _*_;",
              "infixl 6 _+_;",
              "_*_ x y := x;",
              "_+_ a b := a;"
            ]
    case parseFileWithTwoPhase content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right decls -> do
        let env = buildEnvironmentFromDecls decls
        case (Map.lookup "_*_" (macroFixities env), Map.lookup "_+_" (macroFixities env)) of
          (Just multFixity, Just plusFixity) -> do
            multFixity `shouldBe` Infixr 7
            plusFixity `shouldBe` Infixl 6
          _ -> expectationFailure "Missing fixity declarations"
  where
    -- Helper to build macro environment from parsed declarations (mirrors parser logic)
    buildEnvironmentFromDecls :: [Declaration] -> MacroEnvironment
    buildEnvironmentFromDecls decls = foldl processDecl noMacros decls
      where
        processDecl env (MacroDef name args body) =
          if '_' `elem` name
            then -- Mixfix macro: use declared fixity or default
              let fixity = case Map.lookup name (macroFixities env) of
                    Just declaredFixity -> declaredFixity -- Use declared fixity
                    Nothing -> case holes name of -- Use default fixity
                      2 -> Infixl 6 -- default infix for binary operators
                      _ -> Prefix 9 -- default prefix for other mixfix
               in extendMacroEnvironment name args body fixity env
            else -- Regular macro: add without fixity (use dummy fixity that won't be used)
              extendMacroEnvironment name args body (Prefix 9) env
        processDecl env (FixityDecl fixity name) =
          env {macroFixities = Map.insert name fixity (macroFixities env)}
        processDecl env _ = env

-- Test operator table generation (converted to test mixfix desugaring)
mixfixOperatorTableSpec :: Spec
mixfixOperatorTableSpec = describe "Dynamic operator table generation" $ do
  it "generates operator table from macro environment" $ do
    let env =
          MacroEnvironment
            { macroDefinitions = Map.fromList [("_+_", (["a", "b"], TermMacro (Var "dummy" 0 (initialPos "test"))))],
              macroFixities = Map.fromList [("_+_", Infixl 6)]
            }
    -- Test that parsing with macro environment works correctly via two-phase parsing
    case parseTermWithTwoPhase env ["a", "b"] "a + b" of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result -> result `shouldBeEqual` (TMacro "_+_" [Var "a" 1 (initialPos "test"), Var "b" 0 (initialPos "test")] (initialPos "test"))

-- Test actual mixfix parsing in expressions (converted to test desugaring)
mixfixParsingSpec :: Spec
mixfixParsingSpec = describe "Mixfix expression parsing" $ do
  it "parses binary infix expressions" $ do
    let env = createMixfixEnv [("_+_", (["a", "b"], Infixl 6))]
    case parseTermWithTwoPhase env ["a", "b"] "a + b" of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result -> result `shouldBeEqual` (TMacro "_+_" [Var "a" 1 (initialPos "test"), Var "b" 0 (initialPos "test")] (initialPos "test"))

  it "parses ternary mixfix expressions" $ do
    let env = createMixfixEnv [("if_then_else_", (["c", "t", "e"], Prefix 9))]
    case parseTermWithTwoPhase env ["c", "t", "e"] "if c then t else e" of
      Left err -> expectationFailure $ "Parse failed: " ++ err  
      Right result -> result `shouldBeEqual` (TMacro "if_then_else_" [Var "c" 2 (initialPos "test"), Var "t" 1 (initialPos "test"), Var "e" 0 (initialPos "test")] (initialPos "test"))

  it "parses prefix expressions" $ do
    let env = createMixfixEnv [("not_", (["b"], Prefix 9))]
    case parseTermWithTwoPhase env ["b"] "not b" of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result -> result `shouldBeEqual` (TMacro "not_" [Var "b" 0 (initialPos "test")] (initialPos "test"))

  it "respects precedence in complex expressions" $ do
    let env = createMixfixEnv [("_+_", (["a", "b"], Infixl 6)), ("_*_", (["x", "y"], Infixl 7))]
    case parseTermWithTwoPhase env ["a", "b", "c"] "a + b * c" of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result -> result `shouldBeEqual` 
        (TMacro "_+_" 
          [ Var "a" 2 (initialPos "test"),
            TMacro "_*_" [Var "b" 1 (initialPos "test"), Var "c" 0 (initialPos "test")] (initialPos "test")
          ]
          (initialPos "test"))
  where
    createMixfixEnv :: [(String, ([String], Fixity))] -> MacroEnvironment
    createMixfixEnv specs =
      let defs = Map.fromList [(name, (params, TermMacro (Var "dummy" 0 (initialPos "test")))) | (name, (params, _)) <- specs]
          fixities = Map.fromList [(name, fixity) | (name, (_, fixity)) <- specs]
       in MacroEnvironment defs fixities

-- Test relational mixfix macros (converted to two-phase parsing)
relationalMixfixSpec :: Spec
relationalMixfixSpec = describe "Relational mixfix macros" $ do
  it "parses relational infix macro applications" $ do
    let env =
          MacroEnvironment
            { macroDefinitions = Map.fromList [("_+R+_", (["A", "B"], RelMacro (Comp (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))))],
              macroFixities = Map.fromList [("_+R+_", Infixl 6)]
            }
    case parseRTypeWithTwoPhase env ["X", "Y"] "X +R+ Y" of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "_+R+_" [RVar "X" 1 (initialPos "test"), RVar "Y" 0 (initialPos "test")] (initialPos "test"))

  it "parses relational prefix macro applications" $ do
    let env =
          MacroEnvironment
            { macroDefinitions = Map.fromList [("notR_", (["A"], RelMacro (Conv (RVar "A" 0 (initialPos "test")) (initialPos "test"))))],
              macroFixities = Map.fromList [("notR_", Prefix 9)]
            }
    case parseRTypeWithTwoPhase env ["X"] "notR X" of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "notR_" [RVar "X" 0 (initialPos "test")] (initialPos "test"))

  it "parses relational postfix macro applications" $ do
    let env =
          MacroEnvironment
            { macroDefinitions = Map.fromList [("_converse", (["A"], RelMacro (Conv (RVar "A" 0 (initialPos "test")) (initialPos "test"))))],
              macroFixities = Map.fromList [("_converse", Postfix 8)]
            }
    case parseRTypeWithTwoPhase env ["X"] "X converse" of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "_converse" [RVar "X" 0 (initialPos "test")] (initialPos "test"))

  it "parses relational ternary mixfix macro applications" $ do
    let env =
          MacroEnvironment
            { macroDefinitions = Map.fromList [("if_then_else_", (["C", "T", "E"], RelMacro (RVar "T" 1 (initialPos "test"))))],
              macroFixities = Map.fromList [("if_then_else_", Prefix 5)]
            }
    case parseRTypeWithTwoPhase env ["C", "T", "E"] "if C then T else E" of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "if_then_else_" [RVar "C" 2 (initialPos "test"), RVar "T" 1 (initialPos "test"), RVar "E" 0 (initialPos "test")] (initialPos "test"))

-- Test for the mixfix parser bug with multiple holes and repeated literals
mixfixBugSpec :: Spec  
mixfixBugSpec = describe "Mixfix parser bug with repeated literals" $ do
  it "should parse _·_·_ pattern with three arguments" $ do
    let env =
          MacroEnvironment
            { macroDefinitions = Map.fromList [("_·_·_", (["t1", "R", "t2"], RelMacro (Comp (Comp (RVar "t1" 2 (initialPos "test")) (RVar "R" 1 (initialPos "test")) (initialPos "test")) (Conv (RVar "t2" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))))],
              macroFixities = Map.fromList []
            }
    -- This should parse as a single application of _·_·_ with three arguments
    case parseRTypeWithTwoPhase env ["t", "R"] "t · R · t" of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "_·_·_" [RVar "t" 1 (initialPos "test"), RVar "R" 0 (initialPos "test"), RVar "t" 1 (initialPos "test")] (initialPos "test"))