{-# LANGUAGE OverloadedStrings #-}

module RawParserSpec (spec) where

import RawParser
import Test.Hspec
import Text.Megaparsec (eof, errorBundlePretty)
import qualified Text.Megaparsec as M
import Data.Void

-- Helper function to test parsing
testRawParse :: (Show a, Eq a) => M.Parsec Void String a -> String -> a -> Expectation
testRawParse parser input expected =
  case M.runParser (parser <* eof) "test" input of
    Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
    Right result -> result `shouldBe` expected

-- Helper function to test parsing failures
testRawParseFailure :: (Show a) => M.Parsec Void String a -> String -> Expectation
testRawParseFailure parser input =
  case M.runParser (parser <* eof) "test" input of
    Left _ -> return () -- Expected failure
    Right result -> expectationFailure $ "Expected parse failure, but got: " ++ show result

spec :: Spec
spec = do
  termParserSpec
  rTypeParserSpec  
  proofParserSpec

termParserSpec :: Spec
termParserSpec = describe "Raw term parser" $ do
  it "parses simple variables" $ do
    testRawParse parseTerm "x" (RTVar "x")
    testRawParse parseTerm "foo" (RTVar "foo")
    testRawParse parseTerm "x'" (RTVar "x'")
    testRawParse parseTerm "x_1" (RTVar "x_1")

  it "parses lambda expressions" $ do
    testRawParse parseTerm "\\x. x" (RTLam "x" (RTVar "x"))
    testRawParse parseTerm "λx. x" (RTLam "x" (RTVar "x"))
    testRawParse parseTerm "\\x. \\y. x" (RTLam "x" (RTLam "y" (RTVar "x")))

  it "parses applications" $ do
    testRawParse parseTerm "f x" (RTApp (RTVar "f") (RTVar "x"))
    testRawParse parseTerm "f x y" (RTApp (RTApp (RTVar "f") (RTVar "x")) (RTVar "y"))

  it "parses parenthesized terms" $ do
    testRawParse parseTerm "(x)" (RTVar "x")
    testRawParse parseTerm "f (x y)" (RTApp (RTVar "f") (RTApp (RTVar "x") (RTVar "y")))

  it "parses macro calls" $ do
    testRawParse parseTerm "f x" (RTApp (RTVar "f") (RTVar "x"))  -- This could be either app or macro
    testRawParse parseTerm "identity a" (RTApp (RTVar "identity") (RTVar "a"))

  it "handles whitespace correctly" $ do
    testRawParse parseTerm "  x  " (RTVar "x")
    testRawParse parseTerm " f   x " (RTApp (RTVar "f") (RTVar "x"))

  it "fails on empty input" $ do
    testRawParseFailure parseTerm ""

  it "fails on invalid syntax" $ do
    testRawParseFailure parseTerm "("
    testRawParseFailure parseTerm "λ"
    testRawParseFailure parseTerm "λx"

rTypeParserSpec :: Spec
rTypeParserSpec = describe "Raw relation type parser" $ do
  it "parses simple relation variables" $ do
    testRawParse parseRType "R" (RRVar "R")
    testRawParse parseRType "foo" (RRVar "foo")

  it "parses arrow types" $ do
    testRawParse parseRType "A -> B" (RRArr (RRVar "A") (RRVar "B"))
    testRawParse parseRType "A → B" (RRArr (RRVar "A") (RRVar "B"))

  it "parses right-associative arrows" $ do
    testRawParse parseRType "A -> B -> C" (RRArr (RRVar "A") (RRArr (RRVar "B") (RRVar "C")))

  it "parses universal quantification" $ do
    testRawParse parseRType "forall x. R" (RRAll "x" (RRVar "R"))
    testRawParse parseRType "∀ x. R" (RRAll "x" (RRVar "R"))

  it "parses promotion" $ do
    testRawParse parseRType "prom x" (RRProm (RTVar "x"))
    testRawParse parseRType "prom (f x)" (RRProm (RTApp (RTVar "f") (RTVar "x")))

  it "parses parenthesized types" $ do
    testRawParse parseRType "(A -> B)" (RRArr (RRVar "A") (RRVar "B"))
    testRawParse parseRType "(A -> B) -> C" (RRArr (RRArr (RRVar "A") (RRVar "B")) (RRVar "C"))

  it "handles complex nested types" $ do
    testRawParse parseRType "forall x. A -> B -> C" 
      (RRAll "x" (RRArr (RRVar "A") (RRArr (RRVar "B") (RRVar "C"))))

proofParserSpec :: Spec
proofParserSpec = describe "Raw proof parser" $ do
  it "parses proof variables" $ do
    testRawParse parseProof "p" (RPVar "p")
    testRawParse parseProof "identity" (RPVar "identity")  -- This is the key test - should parse as RPVar

  it "parses proof lambda" $ do
    testRawParse parseProof "\\x : A. p" (RPLam "x" (RRVar "A") (RPVar "p"))
    testRawParse parseProof "λx : A. p" (RPLam "x" (RRVar "A") (RPVar "p"))

  it "parses type lambda" $ do
    testRawParse parseProof "Λx. p" (RPTyLam "x" (RPVar "p"))
    testRawParse parseProof "TyLam x. p" (RPTyLam "x" (RPVar "p"))

  it "parses proof application" $ do
    testRawParse parseProof "p q" (RPApp (RPVar "p") (RPVar "q"))
    testRawParse parseProof "p q r" (RPApp (RPApp (RPVar "p") (RPVar "q")) (RPVar "r"))

  it "parses type application" $ do
    testRawParse parseProof "p {A}" (RPTyApp (RPVar "p") (RRVar "A"))
    testRawParse parseProof "p {A -> B}" (RPTyApp (RPVar "p") (RRArr (RRVar "A") (RRVar "B")))

  it "parses atomic tokens as identifiers (for elaboration)" $ do
    testRawParse parseProof "∪ᵢ p" (RPApp (RPVar "∪ᵢ") (RPVar "p"))
    testRawParse parseProof "convIntro p" (RPApp (RPVar "convIntro") (RPVar "p"))
    testRawParse parseProof "∪ₑ p" (RPApp (RPVar "∪ₑ") (RPVar "p"))
    testRawParse parseProof "convElim p" (RPApp (RPVar "convElim") (RPVar "p"))

  it "parses iota atomic tokens as applications (for elaboration)" $ do
    -- These should parse as application structures that elaboration can recognize
    testRawParse parseProof "ι⟨ x, y ⟩" (RPApp (RPApp (RPApp (RPApp (RPVar "ι⟨") (RPVar "x")) (RPVar ",")) (RPVar "y")) (RPVar "⟩"))
    testRawParse parseProof "ι< x, y >" (RPApp (RPApp (RPApp (RPApp (RPVar "ι<") (RPVar "x")) (RPVar ",")) (RPVar "y")) (RPVar ">"))
    testRawParse parseProof "iota< x, y >" (RPApp (RPApp (RPApp (RPApp (RPVar "iota<") (RPVar "x")) (RPVar ",")) (RPVar "y")) (RPVar ">"))

  it "parses parenthesized proofs" $ do
    testRawParse parseProof "(p)" (RPVar "p")
    testRawParse parseProof "(p q)" (RPApp (RPVar "p") (RPVar "q"))

  it "handles complex nested proofs" $ do
    testRawParse parseProof "\\x : A. \\y : B. p q" 
      (RPLam "x" (RRVar "A") (RPLam "y" (RRVar "B") (RPApp (RPVar "p") (RPVar "q"))))

  -- This is the crucial test case that should fix the original bug
  it "parses theorem references without environment lookup" $ do
    testRawParse parseProof "use_proof p (identity q)" 
      (RPApp (RPApp (RPVar "use_proof") (RPVar "p")) (RPApp (RPVar "identity") (RPVar "q")))

  it "parses complex applications with theorem references" $ do
    testRawParse parseProof "f (g p) (h q)" 
      (RPApp (RPApp (RPVar "f") (RPApp (RPVar "g") (RPVar "p"))) (RPApp (RPVar "h") (RPVar "q")))

  it "handles whitespace correctly" $ do
    testRawParse parseProof "  p  " (RPVar "p")
    testRawParse parseProof " p   q " (RPApp (RPVar "p") (RPVar "q"))

  it "fails on empty input" $ do
    testRawParseFailure parseProof ""

  it "fails on invalid syntax" $ do
    testRawParseFailure parseProof "("
    testRawParseFailure parseProof "λ"
    testRawParseFailure parseProof "Λ"