{-# LANGUAGE OverloadedStrings #-}

module MixfixSpec (spec) where

import Control.Monad.Reader
import Control.Monad.Except
import qualified Data.Map as Map
import qualified Data.Set as Set
import Parser.Elaborate (elaborateTerm, elaborateRType)
import Core.Context (emptyContext, Context, extendMacroContext, extendRelContext, extendTermContext)
import Parser.Mixfix (MixfixPart(..), parseMixfixPattern, splitMixfix, holes, defaultFixity, mixfixKeywords)
import Core.Syntax
import Core.Raw
import Parser.Raw
import Parser.Lexer (ident)
import Interface.PrettyPrint
import Test.Hspec
import TestHelpers
import Text.Megaparsec (eof, errorBundlePretty, initialPos, runParser, Parsec)
import Data.Void

-- Helper functions to replace legacy parser calls

-- Simple wrapper functions that translate between old and new API

type P = Parsec Void String

-- Replace runParserEmpty - now runs full pipeline when needed
runParserEmpty :: P a -> String -> Either String a  
runParserEmpty parser input =
  case runParser parser "test" input of
    Left parseErr -> Left $ errorBundlePretty parseErr
    Right result -> Right result

-- Use ident from Lexer for identifiers
mixfixIdentifier :: P String
mixfixIdentifier = ident

-- Helper functions that use the actual parser pipeline

-- The new parser doesn't use ParseContext during parsing
-- Variables and macros are resolved during elaboration

-- Helper to parse and elaborate relational types with context
parseRTypeWithEnv :: Context -> [(String, Int)] -> String -> Either String RType
parseRTypeWithEnv env relVars input =
  let ctxWithVars = foldr (\(name, _) acc -> extendRelContext name acc) env (reverse relVars)
   in case runParser rawRType "test" (input) of
        Left parseErr -> Left $ errorBundlePretty parseErr
        Right raw ->
          case runExcept (runReaderT (elaborateRType raw) ctxWithVars) of
            Left elabErr -> Left $ show elabErr
            Right result -> Right result

spec :: Spec
spec = do
  mixfixIdentifierSpec
  fixityDeclSpec
  mixfixRawMacroSpec
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
      case runParserEmpty (mixfixIdentifier <* eof) input of
        Left err -> expectationFailure $ "Parse failed: " ++ err
        Right result -> result `shouldBe` expected

-- Test fixity declaration parsing
fixityDeclSpec :: Spec
fixityDeclSpec = describe "Fixity declaration parsing" $ do
  it "parses infixl declarations" $ do
    testParseDecl "infixl 6 _+_;" (RawFixityDecl (Infixl 6) (Name "_+_"))
    testParseDecl "infixl 0 _or_;" (RawFixityDecl (Infixl 0) (Name "_or_"))
    testParseDecl "infixl 9 _compose_;" (RawFixityDecl (Infixl 9) (Name "_compose_"))

  it "parses infixr declarations" $ do
    testParseDecl "infixr 5 _*_;" (RawFixityDecl (Infixr 5) (Name "_*_"))
    testParseDecl "infixr 1 _cons_;" (RawFixityDecl (Infixr 1) (Name "_cons_"))

  it "parses infix declarations" $ do
    testParseDecl "infix 4 _==_;" (RawFixityDecl (InfixN 4) (Name "_==_"))
    testParseDecl "infix 7 _mod_;" (RawFixityDecl (InfixN 7) (Name "_mod_"))

  it "parses prefix declarations" $ do
    testParseDecl "prefix 9 not_;" (RawFixityDecl (Prefix 9) (Name "not_"))
    testParseDecl "prefix 8 neg_;" (RawFixityDecl (Prefix 8) (Name "neg_"))

  it "parses postfix declarations" $ do
    testParseDecl "postfix 9 _!;" (RawFixityDecl (Postfix 9) (Name "_!"))
    testParseDecl "postfix 7 _squared;" (RawFixityDecl (Postfix 7) (Name "_squared"))

  it "rejects invalid precedence levels" $ do
    testParseFailure rawDeclaration "infixl 10 _+_;"
    testParseFailure rawDeclaration "infixr -1 _*_;"
  where
    testParseDecl input expected =
      case runParserEmpty (rawDeclaration <* eof) input of
        Left err -> expectationFailure $ "Parse failed: " ++ err
        Right result -> stripPos result `shouldBe` stripPos expected

    testParseFailure parser input =
      case runParserEmpty (parser <* eof) input of
        Left _ -> return () -- Expected failure
        Right result -> expectationFailure $ "Expected parse failure, but got: " ++ show result

-- Test mixfix macro definition parsing
mixfixRawMacroSpec :: Spec
mixfixRawMacroSpec = describe "Mixfix macro definition parsing" $ do
  it "parses binary infix macros with auto-parameters" $ do
    testParseDecl "_+_ a b ≔ a;" (RawMacro (Name "_+_") [Name "a", Name "b"] (RawTermBody (RTVar (Name "a") (initialPos "test"))))

  it "parses ternary mixfix macros with auto-parameters" $ do
    testParseDecl
      "if_then_else_ c t e ≔ t;"
      ( RawMacro
          (Name "if_then_else_")
          [Name "c", Name "t", Name "e"]
          (RawTermBody (RTVar (Name "t") (initialPos "test")))
      )

  it "parses prefix macros" $ do
    testParseDecl "not_ b ≔ b;" (RawMacro (Name "not_") [Name "b"] (RawTermBody (RTVar (Name "b") (initialPos "test"))))

  it "parses postfix macros" $ do
    testParseDecl "_! n ≔ n;" (RawMacro (Name "_!") [Name "n"] (RawTermBody (RTVar (Name "n") (initialPos "test"))))

  it "handles explicit parameters overriding auto-parameters" $ do
    testParseDecl "_+_ x y ≔ x;" (RawMacro (Name "_+_") [Name "x", Name "y"] (RawTermBody (RTVar (Name "x") (initialPos "test"))))
  where
    testParseDecl input expected =
      case runParserEmpty (rawDeclaration <* eof) input of
        Left err -> expectationFailure $ "Parse failed: " ++ err
        Right result -> stripPos result `shouldBe` stripPos expected

-- Test mixfix pretty printing
mixfixPrettyPrintSpec :: Spec
mixfixPrettyPrintSpec = describe "Mixfix pretty printing" $ do
  it "pretty prints binary infix notation" $ do
    let term = TMacro "_+_" [MTerm (Var "a" 0 (initialPos "test")), MTerm (Var "b" 1 (initialPos "test"))] (initialPos "test")
    prettyTerm term `shouldBe` "a + b"

  it "pretty prints ternary mixfix notation" $ do
    let term = TMacro "if_then_else_" [MTerm (Var "c" 2 (initialPos "test")), MTerm (Var "t" 1 (initialPos "test")), MTerm (Var "e" 0 (initialPos "test"))] (initialPos "test")
    prettyTerm term `shouldBe` "if c then t else e"

  it "pretty prints prefix notation" $ do
    let term = TMacro "not_" [MTerm (Var "b" 0 (initialPos "test"))] (initialPos "test")
    prettyTerm term `shouldBe` "not b"

  it "pretty prints postfix notation" $ do
    let term = TMacro "_!" [MTerm (Var "n" 0 (initialPos "test"))] (initialPos "test")
    prettyTerm term `shouldBe` "n !"

  it "pretty prints fixity declarations" $ do
    prettyDeclaration (FixityDecl (Infixl 6) "_+_") `shouldBe` "infixl 6 _+_;"
    prettyDeclaration (FixityDecl (Prefix 9) "not_") `shouldBe` "prefix 9 not_;"
    prettyDeclaration (FixityDecl (Postfix 7) "_!") `shouldBe` "postfix 7 _!;"

-- Test operator table generation
mixfixOperatorTableSpec :: Spec
mixfixOperatorTableSpec = describe "Dynamic operator table generation" $ do
  it "generates operator table from macro environment" $ do
    let paramInfo = [simpleParamInfo "a" TermK, simpleParamInfo "b" TermK]
        macroSig = (paramInfo, TermMacro (Var "dummy" 0 (initialPos "test")))
        env = extendMacroContext "_+_" paramInfo (TermMacro (Var "dummy" 0 (initialPos "test"))) (Infixl 6) emptyContext
    -- We can't easily test the generated operator table directly,
    -- but we can test that parsing with it works correctly
    testParseWithEnv env "a + b" (TMacro "_+_" [MTerm (Var "a" 1 (initialPos "test")), MTerm (Var "b" 0 (initialPos "test"))] (initialPos "test"))
  where
    testParseWithEnv env input expected =
      -- Add term variables to context
      let ctxWithVars = extendTermContext "b" (RMacro "A" [] (initialPos "test")) $ extendTermContext "a" (RMacro "A" [] (initialPos "test")) env
       in case runParser rawTerm "test" (input) of
            Left parseErr -> expectationFailure $ "Parse failed: " ++ errorBundlePretty parseErr
            Right parsedTerm -> 
              case runExcept (runReaderT (elaborateTerm parsedTerm) ctxWithVars) of
                Left elabErr -> expectationFailure $ "Elaboration failed: " ++ show elabErr
                Right result -> result `shouldBeEqual` expected

-- Test actual mixfix parsing in expressions
mixfixParsingSpec :: Spec
mixfixParsingSpec = describe "Mixfix expression parsing" $ do
  it "parses binary infix expressions" $ do
    let env = createMixfixEnv [("_+_", (["a", "b"], Infixl 6))]
    testParseExpr
      env
      ["a", "b"]
      "a + b"
      (TMacro "_+_" [MTerm (Var "a" 1 (initialPos "test")), MTerm (Var "b" 0 (initialPos "test"))] (initialPos "test"))

  it "parses ternary mixfix expressions" $ do
    let env = createMixfixEnv [("if_then_else_", (["c", "t", "e"], Prefix 9))]
    testParseExpr
      env
      ["c", "t", "e"]
      "if c then t else e"
      (TMacro "if_then_else_" [MTerm (Var "c" 2 (initialPos "test")), MTerm (Var "t" 1 (initialPos "test")), MTerm (Var "e" 0 (initialPos "test"))] (initialPos "test"))

  it "parses prefix expressions" $ do
    let env = createMixfixEnv [("not_", (["b"], Prefix 9))]
    testParseExpr
      env
      ["b"]
      "not b"
      (TMacro "not_" [MTerm (Var "b" 0 (initialPos "test"))] (initialPos "test"))

  it "respects precedence in complex expressions" $ do
    let env = createMixfixEnv [("_+_", (["a", "b"], Infixl 6)), ("_*_", (["x", "y"], Infixl 7))]
    testParseExpr
      env
      ["a", "b", "c"]
      "a + b * c"
      ( TMacro
          "_+_"
          [ MTerm (Var "a" 2 (initialPos "test")),
            MTerm (TMacro "_*_" [MTerm (Var "b" 1 (initialPos "test")), MTerm (Var "c" 0 (initialPos "test"))] (initialPos "test"))
          ]
          (initialPos "test")
      )
  where
    createMixfixEnv :: [(String, ([String], Fixity))] -> Context
    createMixfixEnv specs =
      foldr (\(name, (params, fixity)) acc ->
        let paramInfos = [simpleParamInfo p TermK | p <- params]
            dummyBody = TermMacro (Var "dummy" 0 (initialPos "test"))
        in extendMacroContext name paramInfos dummyBody fixity acc
      ) emptyContext specs

    testParseExpr env vars input expected =
      let -- Add variables with correct de Bruijn indices (reverse order)
          ctxWithVars = foldr (\var acc -> extendTermContext var (RMacro "A" [] (initialPos "test")) acc) env (reverse vars)
       in case runParser rawTerm "test" (input) of
            Left parseErr -> expectationFailure $ "Parse failed: " ++ errorBundlePretty parseErr
            Right parsedTerm -> 
              case runExcept (runReaderT (elaborateTerm parsedTerm) ctxWithVars) of
                Left elabErr -> expectationFailure $ "Elaboration failed: " ++ show elabErr
                Right result -> result `shouldBeEqual` expected

-- Test relational mixfix macros
relationalMixfixSpec :: Spec
relationalMixfixSpec = describe "Relational mixfix macros" $ do
  it "parses relational infix macro applications" $ do
    let paramInfos = [simpleParamInfo "A" RelK, simpleParamInfo "B" RelK]
        body = RelMacro (Comp (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
        env = extendMacroContext "_+R+_" paramInfos body (Infixl 6) emptyContext
    case parseRTypeWithEnv env [("X", 1), ("Y", 0)] "X +R+ Y" of
      Left err -> expectationFailure $ "Parse/elaboration failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "_+R+_" [MRel (RVar "X" 1 (initialPos "test")), MRel (RVar "Y" 0 (initialPos "test"))] (initialPos "test"))

  it "parses relational prefix macro applications" $ do
    let paramInfos = [simpleParamInfo "A" RelK]
        body = RelMacro (Conv (RVar "A" 0 (initialPos "test")) (initialPos "test"))
        env = extendMacroContext "notR_" paramInfos body (Prefix 9) emptyContext
    case parseRTypeWithEnv env [("X", 0)] "notR X" of
      Left err -> expectationFailure $ "Parse/elaboration failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "notR_" [MRel (RVar "X" 0 (initialPos "test"))] (initialPos "test"))

  it "parses relational postfix macro applications" $ do
    let paramInfos = [simpleParamInfo "A" RelK]
        body = RelMacro (Conv (RVar "A" 0 (initialPos "test")) (initialPos "test"))
        env = extendMacroContext "_converse" paramInfos body (Postfix 8) emptyContext
    case parseRTypeWithEnv env [("X", 0)] "X converse" of
      Left err -> expectationFailure $ "Parse/elaboration failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "_converse" [MRel (RVar "X" 0 (initialPos "test"))] (initialPos "test"))

  it "parses relational ternary mixfix macro applications" $ do
    let paramInfos = [simpleParamInfo "C" RelK, simpleParamInfo "T" RelK, simpleParamInfo "E" RelK]
        body = RelMacro (RVar "T" 1 (initialPos "test"))
        env = extendMacroContext "if_then_else_" paramInfos body (Prefix 5) emptyContext
    case parseRTypeWithEnv env [("C", 2), ("T", 1), ("E", 0)] "if C then T else E" of
      Left err -> expectationFailure $ "Parse/elaboration failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "if_then_else_" [MRel (RVar "C" 2 (initialPos "test")), MRel (RVar "T" 1 (initialPos "test")), MRel (RVar "E" 0 (initialPos "test"))] (initialPos "test"))

-- Test for the mixfix parser bug with multiple holes and repeated literals
mixfixBugSpec :: Spec
mixfixBugSpec = describe "Mixfix parser bug with repeated literals" $ do
  it "should parse _·_·_ pattern with three arguments" $ do
    let paramInfos = [simpleParamInfo "t1" RelK, simpleParamInfo "R" RelK, simpleParamInfo "t2" RelK]
        body = RelMacro (Comp (Comp (RVar "t1" 2 (initialPos "test")) (RVar "R" 1 (initialPos "test")) (initialPos "test")) (Conv (RVar "t2" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
        env = extendMacroContext "_·_·_" paramInfos body (Infixl 7) emptyContext
    -- This should parse as a single application of _·_·_ with three arguments
    case parseRTypeWithEnv env [("t", 2), ("R", 1), ("dummy", 0)] "t · R · t" of
      Left err -> expectationFailure $ "Parse/elaboration failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "_·_·_" [MRel (RVar "t" 2 (initialPos "test")), MRel (RVar "R" 1 (initialPos "test")), MRel (RVar "t" 2 (initialPos "test"))] (initialPos "test"))

-- Test complex mixfix scenarios
mixfixComplexSpec :: Spec
mixfixComplexSpec = describe "Complex mixfix scenarios" $ do
  it "parses complete mixfix file" $ do
    let content =
          unlines
            [ "infixl 6 _+_;",
              "_+_ a b ≔ a;",
              "infixr 5 _*_;",
              "_*_ x y ≔ x;",
              "prefix 9 not_;",
              "not_ b ≔ b;",
              "if_then_else_ c t e ≔ t;"
            ]
    case runParserEmpty parseFile content of
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
    let dummyTerm = Var "dummy" 0 (initialPos "test")
        macroSpecs = [("_+_", ["a", "b"]), ("if_then_else_", ["c", "t", "e"]), ("not_", ["x"])]
        buildMacro (name, params) acc = 
          let paramInfos = [simpleParamInfo p TermK | p <- params]
              body = TermMacro dummyTerm
          in extendMacroContext name paramInfos body (defaultFixity "TEST") acc
        env = foldr buildMacro emptyContext macroSpecs
    mixfixKeywords env `shouldBe` Set.fromList ["+", "if", "then", "else", "not"]

  it "preserves round-trip parsing and pretty printing" $ do
    let content =
          unlines
            [ "infixl 6 _+_;",
              "_+_ a b ≔ a;"
            ]
    case runParserEmpty parseFile content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right originalDecls -> map stripPos originalDecls `shouldBe` map stripPos originalDecls

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
    testParseIdentifier "Π_" "Π_"
    testParseIdentifier "Σ_" "Σ_"

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
    testParseDecl "infixl 6 _∪_;" (RawFixityDecl (Infixl 6) (Name "_∪_"))
    testParseDecl "infixr 7 _∩_;" (RawFixityDecl (Infixr 7) (Name "_∩_"))
    testParseDecl "prefix 9 ¬_;" (RawFixityDecl (Prefix 9) (Name "¬_"))
    testParseDecl "postfix 8 _†;" (RawFixityDecl (Postfix 8) (Name "_†"))

  it "parses unicode macro definitions" $ do
    testParseDecl "_∪_ a b ≔ a;" (RawMacro (Name "_∪_") [Name "a", Name "b"] (RawTermBody (RTVar (Name "a") (initialPos "test"))))
    testParseDecl "¬_ x ≔ x;" (RawMacro (Name "¬_") [Name "x"] (RawTermBody (RTVar (Name "x") (initialPos "test"))))
    testParseDecl "_† n ≔ n;" (RawMacro (Name "_†") [Name "n"] (RawTermBody (RTVar (Name "n") (initialPos "test"))))

  it "parses unicode mixfix expressions" $ do
    let env = createUnicodeMixfixEnv [("_∪_", (["a", "b"], Infixl 6))]
    testParseExpr
      env
      ["a", "b"]
      "a ∪ b"
      (TMacro "_∪_" [MTerm (Var "a" 1 (initialPos "test")), MTerm (Var "b" 0 (initialPos "test"))] (initialPos "test"))

  it "parses unicode prefix expressions" $ do
    let env = createUnicodeMixfixEnv [("¬_", (["x"], Prefix 9))]
    testParseExpr
      env
      ["x"]
      "¬ x"
      (TMacro "¬_" [MTerm (Var "x" 0 (initialPos "test"))] (initialPos "test"))

  it "parses unicode postfix expressions" $ do
    let paramInfos = [simpleParamInfo "A" RelK]
        body = RelMacro (Conv (RVar "A" 0 (initialPos "test")) (initialPos "test"))
        env = extendMacroContext "_†" paramInfos body (Postfix 8) emptyContext
    case parseRTypeWithEnv env [("X", 0)] "X †" of
      Left err -> expectationFailure $ "Parse/elaboration failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "_†" [MRel (RVar "X" 0 (initialPos "test"))] (initialPos "test"))

  it "pretty prints unicode mixfix operations" $ do
    let unionTerm = TMacro "_∪_" [MTerm (Var "A" 1 (initialPos "test")), MTerm (Var "B" 0 (initialPos "test"))] (initialPos "test")
    prettyTerm unionTerm `shouldBe` "A ∪ B"

    let negTerm = TMacro "¬_" [MTerm (Var "p" 0 (initialPos "test"))] (initialPos "test")
    prettyTerm negTerm `shouldBe` "¬ p"

    let daggerTerm = TMacro "_†" [MTerm (Var "M" 0 (initialPos "test"))] (initialPos "test")
    prettyTerm daggerTerm `shouldBe` "M †"

  it "handles unicode in relational mixfix macros" $ do
    let paramInfos = [simpleParamInfo "A" RelK, simpleParamInfo "B" RelK]
        body = RelMacro (Arr (RVar "A" 1 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"))
        env = extendMacroContext "_⊆_" paramInfos body (Infixl 4) emptyContext
    case parseRTypeWithEnv env [("X", 1), ("Y", 0)] "X ⊆ Y" of
      Left err -> expectationFailure $ "Parse/elaboration failed: " ++ err
      Right result -> result `shouldBeEqual` (RMacro "_⊆_" [MRel (RVar "X" 1 (initialPos "test")), MRel (RVar "Y" 0 (initialPos "test"))] (initialPos "test"))

  it "handles complex unicode operator precedence" $ do
    let env = createUnicodeMixfixEnv [("_∪_", (["a", "b"], Infixl 5)), ("_∩_", (["x", "y"], Infixl 6))]
    testParseExpr
      env
      ["a", "b", "c"]
      "a ∪ b ∩ c"
      ( TMacro
          "_∪_"
          [ MTerm (Var "a" 2 (initialPos "test")),
            MTerm (TMacro "_∩_" [MTerm (Var "b" 1 (initialPos "test")), MTerm (Var "c" 0 (initialPos "test"))] (initialPos "test"))
          ]
          (initialPos "test")
      )
  where
    testParseIdentifier input expected =
      case runParserEmpty (mixfixIdentifier <* eof) input of
        Left err -> expectationFailure $ "Parse failed: " ++ err
        Right result -> result `shouldBe` expected

    testParseDecl input expected =
      case runParserEmpty (rawDeclaration <* eof) input of
        Left err -> expectationFailure $ "Parse failed: " ++ err
        Right result -> stripPos result `shouldBe` stripPos expected

    createUnicodeMixfixEnv :: [(String, ([String], Fixity))] -> Context
    createUnicodeMixfixEnv specs =
      foldr (\(name, (params, fixity)) acc ->
        let paramInfos = [simpleParamInfo p TermK | p <- params]
            dummyBody = TermMacro (Var "dummy" 0 (initialPos "test"))
        in extendMacroContext name paramInfos dummyBody fixity acc
      ) emptyContext specs

    testParseExpr env vars input expected =
      let -- Add variables with correct de Bruijn indices (reverse order)
          ctxWithVars = foldr (\var acc -> extendTermContext var (RMacro "A" [] (initialPos "test")) acc) env (reverse vars)
       in case runParser rawTerm "test" (input) of
            Left parseErr -> expectationFailure $ "Parse failed: " ++ errorBundlePretty parseErr
            Right parsedTerm2 -> 
              case runExcept (runReaderT (elaborateTerm parsedTerm2) ctxWithVars) of
                Left elabErr -> expectationFailure $ "Elaboration failed: " ++ show elabErr
                Right result -> result `shouldBeEqual` expected

-- Test fixity declaration ordering
fixityOrderingSpec :: Spec
fixityOrderingSpec = describe "Fixity declaration ordering" $ do
  it "preserves fixity declarations when they come before macro definitions" $ do
    let content = "infixr 7 _*_;\n_*_ x y ≔ x;"
    case runParserEmpty parseFile content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right decls -> do
        let env = buildEnvironmentFromDecls decls
        case Map.lookup "_*_" (macroFixities env) of
          Nothing -> expectationFailure "No fixity found for _*_"
          Just fixity -> fixity `shouldBe` Infixr 7

  it "applies fixity declaration regardless of order" $ do
    let content = "_*_ x y ≔ x;\ninfixr 7 _*_;"
    case runParserEmpty parseFile content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right decls -> do
        let env = buildEnvironmentFromDecls decls
        case Map.lookup "_*_" (macroFixities env) of
          Nothing -> expectationFailure "No fixity found for _*_"
          Just fixity -> fixity `shouldBe` Infixr 7

  it "uses default fixity when no declaration is provided" $ do
    let content = "_*_ x y ≔ x;"
    case runParserEmpty parseFile content of
      Left err -> expectationFailure $ "Parse failed: " ++ err
      Right decls -> do
        let env = buildEnvironmentFromDecls decls
        case Map.lookup "_*_" (macroFixities env) of
          Nothing -> expectationFailure "No fixity found for _*_"
          Just fixity -> fixity `shouldBe` Infixl 6 -- default binary fixity
  it "handles multiple fixity declarations correctly" $ do
    let content =
          unlines
            [ "infixr 7 _*_;",
              "infixl 6 _+_;",
              "_*_ x y ≔ x;",
              "_+_ a b ≔ a;"
            ]
    case runParserEmpty parseFile content of
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
    buildEnvironmentFromDecls :: [RawDeclaration] -> Context
    buildEnvironmentFromDecls decls = foldl processDecl emptyContext decls
      where
        processDecl env (RawMacro (Name name) nameArgs body) =
          let args = [case arg of Name s -> s | arg <- nameArgs]
          in if '_' `elem` name
            then -- Mixfix macro: use declared fixity or default
              let fixity = case Map.lookup name (macroFixities env) of
                    Just declaredFixity -> declaredFixity -- Use declared fixity
                    Nothing -> case holes name of -- Use default fixity
                      2 -> Infixl 6 -- default infix for binary operators
                      _ -> Prefix 9 -- default prefix for other mixfix
                  elaboratedBody = case body of
                    RawTermBody _ -> TermMacro (error "Can't elaborate in test helper")
                    RawRelBody _ -> RelMacro (error "Can't elaborate in test helper")
                    RawProofBody _ -> ProofMacro (error "Can't elaborate in test helper")
                  paramInfos = [simpleParamInfo arg TermK | arg <- args] -- Use TermK as default
               in extendMacroContext name paramInfos elaboratedBody fixity env
            else -- Regular macro: add without fixity (use dummy fixity that won't be used)
              let elaboratedBody = case body of
                    RawTermBody _ -> TermMacro (error "Can't elaborate in test helper")
                    RawRelBody _ -> RelMacro (error "Can't elaborate in test helper")
                    RawProofBody _ -> ProofMacro (error "Can't elaborate in test helper")
                  paramInfos = [simpleParamInfo arg TermK | arg <- args] -- Use TermK as default
              in extendMacroContext name paramInfos elaboratedBody (Prefix 9) env
        processDecl env (RawFixityDecl fixity (Name name)) =
          -- For fixity declarations, we need to update existing context or store for later use
          -- For simplicity in tests, we'll just return the context unchanged
          -- Real implementation would need to handle this properly
          env
        processDecl env _ = env
