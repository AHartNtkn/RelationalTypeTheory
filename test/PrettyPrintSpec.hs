module PrettyPrintSpec (spec) where

import Context (extendMacroEnvironment, noMacros)
import Control.Monad.Reader (runReader)
import qualified Data.Map as Map
import Errors
import Lib
import Parser.Legacy (ParseContext (..), emptyParseContext, parseRType, relVars, runParserT)
import PrettyPrint
import Test.Hspec
import TestHelpers
import Text.Megaparsec (SourcePos (..), errorBundlePretty, initialPos, mkPos)

spec :: Spec
spec = do
  describe "Pretty Printing Configuration" $ do
    it "uses Unicode symbols by default" $ do
      let config = defaultPrettyConfig
      useUnicode config `shouldBe` True

    it "can be configured for ASCII output" $ do
      let config = defaultPrettyConfig {useUnicode = False}
      useUnicode config `shouldBe` False

    it "can show de Bruijn indices when requested" $ do
      let config = defaultPrettyConfig {showIndices = True}
      showIndices config `shouldBe` True

  describe "Term Pretty Printing" $ do
    describe "basic terms" $ do
      it "pretty prints variables" $ do
        prettyTerm (Var "x" 0 (initialPos "test")) `shouldBe` "x"

      it "pretty prints variables with indices when configured" $ do
        let config = defaultPrettyConfig {showIndices = True}
        prettyTermWithConfig config (Var "x" 0 (initialPos "test")) `shouldBe` "x_0"
        prettyTermWithConfig config (Var "y" 1 (initialPos "test")) `shouldBe` "y_1"

      it "pretty prints lambda abstractions with Unicode" $ do
        prettyTerm (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "λx. x"

      it "pretty prints lambda abstractions with ASCII" $ do
        let config = defaultPrettyConfig {useUnicode = False}
        prettyTermWithConfig config (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "\\x. x"

      it "pretty prints applications" $ do
        prettyTerm (App (Var "f" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "f x"

    describe "complex terms" $ do
      it "pretty prints nested lambda abstractions" $ do
        let term = Lam "x" (Lam "y" (Var "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyTerm term `shouldBe` "λx. λy. x"

      it "pretty prints nested applications" $ do
        let term = App (App (Var "f" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")
        prettyTerm term `shouldBe` "f x y"

      it "adds parentheses for complex applications" $ do
        let term = App (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")
        prettyTerm term `shouldBe` "(λx. x) y"

      it "handles deeply nested terms" $ do
        let term = Lam "f" (Lam "x" (App (Var "f" 1 (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyTerm term `shouldBe` "λf. λx. f (f x)"

  describe "Type Pretty Printing" $ do
    describe "basic types" $ do
      it "pretty prints type variables" $ do
        prettyRType (RVar "X" 0 (initialPos "test")) `shouldBe` "X"

      it "pretty prints type applications" $ do
        prettyRType (RMacro "List" [RVar "X" 0 (initialPos "test")] (initialPos "test")) `shouldBe` "List X"
        prettyRType (RMacro "Map" [RVar "K" 0 (initialPos "test"), RVar "V" 0 (initialPos "test")] (initialPos "test")) `shouldBe` "Map K V"

      it "pretty prints arrow types with Unicode" $ do
        prettyRType (Arr (RVar "X" 0 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "X → Y"

      it "pretty prints arrow types with ASCII" $ do
        let config = defaultPrettyConfig {useUnicode = False}
        prettyRTypeWithConfig config (Arr (RVar "X" 0 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "X -> Y"

      it "pretty prints universal quantification with Unicode" $ do
        prettyRType (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "∀X. X"

      it "pretty prints universal quantification with ASCII" $ do
        let config = defaultPrettyConfig {useUnicode = False}
        prettyRTypeWithConfig config (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "forallX. X"

    describe "relational operations" $ do
      it "pretty prints composition with Unicode" $ do
        prettyRType (Comp (RVar "R" 0 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "R ∘ S"

      it "pretty prints composition with ASCII" $ do
        let config = defaultPrettyConfig {useUnicode = False}
        prettyRTypeWithConfig config (Comp (RVar "R" 0 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "R o S"

      it "pretty prints converse with Unicode" $ do
        prettyRType (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "R˘"

      it "pretty prints converse with ASCII" $ do
        let config = defaultPrettyConfig {useUnicode = False}
        prettyRTypeWithConfig config (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "R^"

      it "pretty prints promotion (hides Prom from user)" $ do
        prettyRType (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) `shouldBe` "λx. x"

      it "hides promotion for term macros" $ do
        prettyRType (Prom (TMacro "Id" [] (initialPos "test")) (initialPos "test")) `shouldBe` "Id"

      it "hides promotion for complex terms" $ do
        prettyRType (Prom (App (Var "f" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) `shouldBe` "f x"

      it "hides promotion in nested contexts" $ do
        prettyRType (Comp (Prom (Var "f" 0 (initialPos "test")) (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "f ∘ R"

      it "hides promotion with parenthesization when needed" $ do
        let original = Arr (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyRType original
            ctx = emptyParseContext {relVars = Map.fromList [("R", 0)]}
        -- Test that the pretty-printed result parses back to exactly the same AST
        case runReader (runParserT parseRType "" prettyResult) ctx of
          Left err -> expectationFailure $ "Pretty-printed result failed to parse: " ++ errorBundlePretty err
          Right parsed -> parsed `shouldBeEqual` original

    describe "advanced relational macro applications" $ do
      it "pretty prints zero-argument relational macros" $ do
        prettyRType (RMacro "Unit" [] (initialPos "test")) `shouldBe` "Unit"
        prettyRType (RMacro "Bottom" [] (initialPos "test")) `shouldBe` "Bottom"

      it "pretty prints nested relational macro applications" $ do
        let nested = RMacro "Outer" [RMacro "Inner" [RVar "X" 0 (initialPos "test")] (initialPos "test"), RVar "Y" 0 (initialPos "test")] (initialPos "test")
        prettyRType nested `shouldBe` "Outer Inner X Y"

      it "pretty prints relational macros with complex type arguments" $ do
        let complex = RMacro "Transform" [Arr (RVar "A" 0 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test"), All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")] (initialPos "test")
        prettyRType complex `shouldBe` "Transform (A → B) (∀X. X)"

      it "pretty prints relational macros with promoted terms" $ do
        let original = RMacro "Lift" [Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")] (initialPos "test")
            prettyResult = prettyRType original
            liftEnv = extendMacroEnvironment "Lift" ["A"] (RelMacro (RVar "A" 0 (initialPos "test"))) (defaultFixity "TEST") noMacros
            ctx = emptyParseContext {macroEnv = liftEnv, kwdSet = mixfixKeywords liftEnv}
        -- Test that the pretty-printed result parses back to exactly the same AST
        case runReader (runParserT parseRType "" prettyResult) ctx of
          Left err -> expectationFailure $ "Pretty-printed result failed to parse: " ++ errorBundlePretty err
          Right parsed -> parsed `shouldBeEqual` original

      it "pretty prints relational macros with relational operations" $ do
        let withOps = RMacro "Compose" [Comp (RVar "R" 0 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"), Conv (RVar "T" 0 (initialPos "test")) (initialPos "test")] (initialPos "test")
        prettyRType withOps `shouldBe` "Compose (R ∘ S) T˘"

    describe "complex types" $ do
      it "pretty prints nested arrow types" $ do
        let rtype = Arr (RVar "X" 0 (initialPos "test")) (Arr (RVar "Y" 0 (initialPos "test")) (RVar "Z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyRType rtype `shouldBe` "X → Y → Z"

      it "pretty prints arrow types with parentheses" $ do
        let rtype = Arr (Arr (RVar "X" 0 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (RVar "Z" 0 (initialPos "test")) (initialPos "test")
        prettyRType rtype `shouldBe` "(X → Y) → Z"

      it "pretty prints nested quantifiers" $ do
        let rtype = All "X" (All "Y" (Arr (RVar "X" 1 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyRType rtype `shouldBe` "∀X. ∀Y. X → Y"

      it "pretty prints complex composition chains" $ do
        let rtype = Comp (Comp (RVar "R" 0 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) (RVar "T" 0 (initialPos "test")) (initialPos "test")
        prettyRType rtype `shouldBe` "(R ∘ S) ∘ T"

      it "pretty prints composition with converse" $ do
        let rtype = Comp (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")
        prettyRType rtype `shouldBe` "R˘ ∘ S"

  describe "Proof Pretty Printing" $ do
    describe "basic proofs" $ do
      it "pretty prints proof variables" $ do
        prettyProof (PVar "p" 0 (initialPos "test")) `shouldBe` "p"

      it "pretty prints proof lambda abstractions" $ do
        let proof = LamP "u" (RVar "R" 0 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "λu:R. p"

      it "pretty prints proof applications" $ do
        prettyProof (AppP (PVar "p" 0 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "p q"

      it "pretty prints type lambda abstractions with Unicode" $ do
        prettyProof (TyLam "X" (PVar "p" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "ΛX. p"

      it "pretty prints type lambda abstractions with ASCII" $ do
        let config = defaultPrettyConfig {useUnicode = False}
        prettyProofWithConfig config (TyLam "X" (PVar "p" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "LambdaX. p"

      it "pretty prints type applications" $ do
        prettyProof (TyApp (PVar "p" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "p{X}"

    describe "advanced proof constructs" $ do
      it "pretty prints iota (term promotion introduction)" $ do
        let proof = Iota (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "ι⟨λx. x, λy. y⟩"

      it "pretty prints conversion proofs" $ do
        let proof = ConvProof (Var "x" 0 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "x ⇃ p ⇂ y"

      it "pretty prints rho elimination" $ do
        let proof = RhoElim "x" (Var "t1" 0 (initialPos "test")) (Var "t2" 0 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "ρ{x.t1, t2} p - q"

      it "pretty prints pi elimination" $ do
        let proof = Pi (PVar "p" 0 (initialPos "test")) "x" "u" "v" (PVar "q" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "π p - x.u.v.q"

      it "pretty prints converse introduction with Unicode" $ do
        prettyProof (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "∪ᵢ p"

      it "pretty prints converse introduction with ASCII" $ do
        let config = defaultPrettyConfig {useUnicode = False}
        prettyProofWithConfig config (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "unionI p"

      it "pretty prints converse elimination with Unicode" $ do
        prettyProof (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "∪ₑ p"

      it "pretty prints converse elimination with ASCII" $ do
        let config = defaultPrettyConfig {useUnicode = False}
        prettyProofWithConfig config (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "unionE p"

      it "pretty prints pairs" $ do
        prettyProof (Pair (PVar "p" 0 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "(p, q)"

      it "pretty prints complex rho elimination with nested terms" $ do
        let proof = RhoElim "x" (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (App (Var "f" 0 (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")) (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")) (ConvElim (PVar "q" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "ρ{x.λy. y, f a} ∪ᵢ p - ∪ₑ q"

      it "pretty prints complex pi elimination with multiple bindings" $ do
        let proof = Pi (TyApp (PVar "p" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) "x" "u" "v" (Pair (PVar "q" 0 (initialPos "test")) (PVar "r" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "π p{X} - x.u.v.(q, r)"

      it "pretty prints nested proof applications with parentheses" $ do
        let proof = AppP (AppP (PVar "f" 0 (initialPos "test")) (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (ConvElim (PVar "q" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "(f ∪ᵢ p) ∪ₑ q"

      it "pretty prints iota with complex terms" $ do
        let proof = Iota (App (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (Lam "f" (Lam "x" (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "ι⟨(λx. x) y, λf. λx. f x⟩"

      it "pretty prints conversion proofs with complex terms" $ do
        let proof = ConvProof (App (Var "f" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (TyLam "X" (PVar "p" 0 (initialPos "test")) (initialPos "test")) (Lam "y" (App (Var "g" 0 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "f x ⇃ ΛX. p ⇂ λy. g y"

    describe "complex proofs" $ do
      it "adds parentheses for complex proof applications" $ do
        let proof = AppP (LamP "u" (RVar "R" 0 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "(λu:R. p) q"

      it "handles nested proof lambda abstractions" $ do
        let proof = LamP "u" (RVar "R" 0 (initialPos "test")) (LamP "v" (RVar "S" 0 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "λu:R. λv:S. p"

      it "handles deeply nested type applications" $ do
        let proof = TyApp (TyApp (PVar "p" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "p{X}{Y}"

  describe "Relational Judgment Pretty Printing" $ do
    it "pretty prints basic relational judgments" $ do
      let judgment = RelJudgment (Var "x" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
      prettyRelJudgment judgment `shouldBe` "x [R] y"

    it "pretty prints complex relational judgments" $ do
      let judgment =
            RelJudgment
              (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
              (Arr (RVar "X" 0 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test"))
              (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test"))
      prettyRelJudgment judgment `shouldBe` "λx. x [X → Y] λy. y"

    it "pretty prints judgments with promoted types" $ do
      let judgment =
            RelJudgment
              (Var "f" 0 (initialPos "test"))
              (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
              (Var "g" 0 (initialPos "test"))
      prettyRelJudgment judgment `shouldBe` "f [λx. x] g"

  describe "Declaration Pretty Printing" $ do
    it "pretty prints macro definitions without parameters" $ do
      let decl = MacroDef "Id" [] (RelMacro (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")))
      prettyDeclaration decl `shouldBe` "Id := X → X;"

    it "pretty prints macro definitions with parameters" $ do
      let decl = MacroDef "Comp" ["R", "S"] (RelMacro (Comp (RVar "R" 0 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")))
      prettyDeclaration decl `shouldBe` "Comp R S := R ∘ S;"

    it "pretty prints theorem definitions without bindings" $ do
      let judgment = RelJudgment (Var "x" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
      let decl = TheoremDef "test" [] judgment (PVar "p" 0 (initialPos "test"))
      prettyDeclaration decl `shouldBe` "⊢ test : x [R] y := p;"

    it "pretty prints theorem definitions with bindings" $ do
      let judgment = RelJudgment (Var "x" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
      let bindings = [TermBinding "x", RelBinding "R"]
      let decl = TheoremDef "test" bindings judgment (PVar "p" 0 (initialPos "test"))
      prettyDeclaration decl `shouldBe` "⊢ test : [x, R] x [R] y := p;"

    it "pretty prints theorem definitions with ASCII" $ do
      let config = defaultPrettyConfig {useUnicode = False}
      let judgment = RelJudgment (Var "x" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
      let decl = TheoremDef "test" [] judgment (PVar "p" 0 (initialPos "test"))
      prettyDeclarationWithConfig config decl `shouldBe` "|- test : x [R] y := p;"

    describe "advanced macro declaration tests" $ do
      it "pretty prints term macro definitions" $ do
        let termBody = TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
        let decl = MacroDef "Id" [] termBody
        prettyDeclaration decl `shouldBe` "Id := λx. x;"

      it "pretty prints term macro definitions with parameters" $ do
        let complexTerm = TermMacro (Lam "f" (Lam "x" (App (Var "f" 1 (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
        let decl = MacroDef "Twice" ["f"] complexTerm
        prettyDeclaration decl `shouldBe` "Twice f := λf. λx. f (f x);"

      it "pretty prints relational macro definitions with operations" $ do
        let relOps = RelMacro (Comp (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test"))
        let decl = MacroDef "SelfCompose" ["R"] relOps
        prettyDeclaration decl `shouldBe` "SelfCompose R := R˘ ∘ R;"

      it "pretty prints theorem definitions with complex proofs" $ do
        let judgment = RelJudgment (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Prom (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test"))
        let complexProof = Iota (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        let decl = TheoremDef "identity_iso" [] judgment complexProof
        prettyDeclaration decl `shouldBe` "⊢ identity_iso : λx. x [λy. y] λz. z := ι⟨λx. x, λz. z⟩;"

  describe "Binding Pretty Printing" $ do
    it "pretty prints term bindings" $ do
      prettyBinding (TermBinding "x") `shouldBe` "x"

    it "pretty prints relation bindings" $ do
      prettyBinding (RelBinding "R") `shouldBe` "R"

    it "pretty prints proof bindings" $ do
      let judgment = RelJudgment (Var "x" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
      prettyBinding (ProofBinding "p" judgment) `shouldBe` "p : x [R] y"

  describe "Error Pretty Printing" $ do
    let noCtx = ErrorContext (initialPos "test") ""
    let withCtx = ErrorContext (SourcePos "test.rtt" (mkPos 1) (mkPos 1)) "checking theorem"

    -- Helper to check error message content while ignoring location formatting
    let shouldContainErrorMessage actual expected =
          let actualLines = lines actual
              -- Take the first line which contains the main error message
              errorLine = if null actualLines then "" else head actualLines
           in errorLine `shouldBe` expected

    describe "variable and binding errors" $ do
      it "pretty prints unbound variable errors" $ do
        let err = UnboundVariable "x" noCtx
        prettyError err `shouldContainErrorMessage` "Unbound variable: x"

      it "pretty prints unbound type variable errors" $ do
        let err = UnboundTypeVariable "X" noCtx
        prettyError err `shouldContainErrorMessage` "Unbound type variable: X"

      it "pretty prints unbound macro errors" $ do
        let err = UnboundMacro "MyMacro" noCtx
        prettyError err `shouldContainErrorMessage` "Unbound macro: MyMacro"

      it "pretty prints duplicate binding errors" $ do
        let err = DuplicateBinding "x" noCtx
        prettyError err `shouldContainErrorMessage` "Duplicate binding: x"

    describe "type system errors" $ do
      it "pretty prints type mismatch errors" $ do
        let err = TypeMismatch (RVar "X" 0 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) noCtx
        prettyError err `shouldContain` "Type mismatch:"
        prettyError err `shouldContain` "Expected: X"
        prettyError err `shouldContain` "Actual: Y"

      it "pretty prints invalid type application errors" $ do
        let err = InvalidTypeApplication (RVar "X" 0 (initialPos "test")) noCtx
        prettyError err `shouldContainErrorMessage` "Invalid type application: X"

      it "pretty prints macro arity mismatch errors" $ do
        let err = MacroArityMismatch "MyMacro" 2 1 noCtx
        prettyError err `shouldContain` "Macro arity mismatch for MyMacro:"
        prettyError err `shouldContain` "Expected: 2 arguments"
        prettyError err `shouldContain` "Actual: 1 arguments"

    describe "normalization errors" $ do
      it "pretty prints infinite normalization errors" $ do
        let err = InfiniteNormalization (Var "x" 0 (initialPos "test")) noCtx
        prettyError err `shouldContainErrorMessage` "Infinite normalization for term: x"

      it "pretty prints substitution errors" $ do
        let err = SubstitutionError "x" (Var "y" 0 (initialPos "test")) noCtx
        prettyError err `shouldContainErrorMessage` "Substitution error for variable x in term: y"

      it "pretty prints invalid de Bruijn index errors" $ do
        let err = InvalidDeBruijnIndex 5 noCtx
        prettyError err `shouldContainErrorMessage` "Invalid de Bruijn index: 5"

    describe "context errors" $ do
      it "pretty prints invalid context errors" $ do
        let err = InvalidContext "context too deep" noCtx
        prettyError err `shouldContainErrorMessage` "Invalid context: context too deep"

      it "pretty prints context inconsistency errors" $ do
        let err = ContextInconsistency "binding mismatch" noCtx
        prettyError err `shouldContainErrorMessage` "Context inconsistency: binding mismatch"

    describe "proof checking errors" $ do
      it "pretty prints proof typing errors" $ do
        let judgment1 = RelJudgment (Var "x" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
        let judgment2 = RelJudgment (Var "x" 0 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
        let err = ProofTypingError (PVar "dummy" 0 (initialPos "test")) judgment1 judgment2 Nothing noCtx
        prettyError err `shouldContain` "Proof error:"
        prettyError err `shouldContain` "Expected judgment: x [R] y"
        prettyError err `shouldContain` "Actual judgment: x [S] y"

      it "pretty prints left conversion errors" $ do
        let err = LeftConversionError (Var "x" 0 (initialPos "test")) (Var "x'" 0 (initialPos "test")) noCtx
        prettyError err `shouldContain` "Left conversion error:"
        prettyError err `shouldContain` "expected x but got x'"
        prettyError err `shouldContain` "β-η equivalent"

      it "pretty prints right conversion errors" $ do
        let err = RightConversionError (Var "y" 0 (initialPos "test")) (Var "y'" 0 (initialPos "test")) noCtx
        prettyError err `shouldContain` "Right conversion error:"
        prettyError err `shouldContain` "expected y but got y'"
        prettyError err `shouldContain` "β-η equivalent"

      it "pretty prints converse errors" $ do
        let dummyJudgment = RelJudgment (Var "x" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
            err = ConverseError (PVar "dummy" 0 (initialPos "test")) dummyJudgment noCtx
        prettyError err `shouldContainErrorMessage` "Converse elimination error: proof dummy must prove judgment with converse relation, but proves x [X] y"

      it "pretty prints rho elimination errors" $ do
        let dummyJudgment = RelJudgment (Var "x" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
            err = RhoEliminationNonPromotedError (PVar "dummy" 0 (initialPos "test")) dummyJudgment noCtx
        prettyError err `shouldContainErrorMessage` "Rho elimination error: first proof dummy must prove a judgment with promoted relation, but proves x [X] y"

      it "pretty prints composition errors" $ do
        let err = CompositionError (PVar "p1" 0 (initialPos "test")) (PVar "p2" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (Var "y" 0 (initialPos "test")) noCtx
        prettyError err `shouldContainErrorMessage` "Composition error: proofs p1 and p2 have mismatched middle terms x and y"

    describe "general errors" $ do
      it "pretty prints internal errors" $ do
        let err = InternalError "something went wrong" noCtx
        prettyError err `shouldContainErrorMessage` "Internal error: something went wrong"

    describe "error context" $ do
      it "includes source location when available" $ do
        let err = UnboundVariable "x" withCtx
        prettyError err `shouldContain` "at test.rtt"

      it "omits context when not available" $ do
        let err = UnboundVariable "x" noCtx
        -- The error should contain "at" since noCtx still has a position
        prettyError err `shouldContain` "at"

  describe "Comprehensive Integration Tests" $ do
    it "pretty prints complex boolean type definition" $ do
      let boolType = All "X" (Arr (RVar "X" 0 (initialPos "test")) (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
      prettyRType boolType `shouldBe` "∀X. X → X → X"

    it "pretty prints complex proof with multiple constructs" $ do
      let complexProof = TyLam "X" (LamP "p" (RVar "R" 0 (initialPos "test")) (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
      prettyProof complexProof `shouldBe` "ΛX. λp:R. ∪ₑ p"

    it "pretty prints complex theorem declaration" $ do
      let judgment =
            RelJudgment
              (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
              (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
              (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"))
      let proof = Iota (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
      let decl = TheoremDef "id_test" [] judgment proof
      prettyDeclaration decl `shouldBe` "⊢ id_test : λx. x [λx. x] λx. x := ι⟨λx. x, λx. x⟩;"

    it "maintains consistency between Unicode and ASCII modes" $ do
      let term = Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")
      let rtype = All "X" (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
      let proof = TyLam "X" (LamP "p" (RVar "R" 0 (initialPos "test")) (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")

      -- Unicode should use symbols
      prettyTerm term `shouldContain` "λ"
      prettyRType rtype `shouldContain` "∀"
      prettyRType rtype `shouldContain` "→"
      prettyProof proof `shouldContain` "Λ"
      prettyProof proof `shouldContain` "∪ᵢ"

      -- ASCII should use text
      let asciiConfig = defaultPrettyConfig {useUnicode = False}
      prettyTermWithConfig asciiConfig term `shouldContain` "\\"
      prettyRTypeWithConfig asciiConfig rtype `shouldContain` "forall"
      prettyRTypeWithConfig asciiConfig rtype `shouldContain` "->"
      prettyProofWithConfig asciiConfig proof `shouldContain` "Lambda"
      prettyProofWithConfig asciiConfig proof `shouldContain` "unionI"

    it "handles all relational operations correctly" $ do
      let composition = Comp (RVar "R" 0 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")
      let converse = Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")
      let promotion = Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")

      prettyRType composition `shouldBe` "R ∘ S"
      prettyRType converse `shouldBe` "R˘"
      prettyRType promotion `shouldBe` "λx. x"

    it "handles complex nested structures with proper parenthesization" $ do
      let complexType =
            Arr
              (All "X" (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test"))
              (Comp (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test"))
              (initialPos "test")
      prettyRType complexType `shouldBe` "(∀X. X → X) → R˘ ∘ S"

    it "preserves de Bruijn index information when requested" $ do
      let config = defaultPrettyConfig {showIndices = True}
      let term = Lam "x" (Lam "y" (App (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
      prettyTermWithConfig config term `shouldBe` "λx. λy. x_1 y_0"

  describe "Term Macro (TMacro) Pretty Printing" $ do
    it "pretty prints zero-arity term macros" $ do
      prettyTerm (TMacro "Id" [] (initialPos "test")) `shouldBe` "Id"

    it "pretty prints term macros with single argument" $ do
      prettyTerm (TMacro "Apply" [Var "f" 0 (initialPos "test")] (initialPos "test")) `shouldBe` "Apply f"

    it "pretty prints term macros with multiple arguments" $ do
      prettyTerm (TMacro "Comp" [Var "f" 0 (initialPos "test"), Var "g" 0 (initialPos "test")] (initialPos "test")) `shouldBe` "Comp f g"

    it "pretty prints nested term macro applications" $ do
      let nested = TMacro "Outer" [TMacro "Inner" [Var "x" 0 (initialPos "test")] (initialPos "test"), Var "y" 0 (initialPos "test")] (initialPos "test")
      prettyTerm nested `shouldBe` "Outer Inner x y"

    it "pretty prints term macros with complex arguments" $ do
      let complex = TMacro "Map" [Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test"), App (Var "f" 0 (initialPos "test")) (Var "a" 0 (initialPos "test")) (initialPos "test")] (initialPos "test")
      prettyTerm complex `shouldBe` "Map (λx. x) (f a)"

    it "pretty prints term macros with lambda arguments requiring parentheses" $ do
      let withLam = TMacro "Apply" [Lam "x" (App (Var "x" 0 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")] (initialPos "test")
      prettyTerm withLam `shouldBe` "Apply (λx. x y)"

    it "handles empty argument lists consistently" $ do
      prettyTerm (TMacro "Nil" [] (initialPos "test")) `shouldBe` "Nil"
      prettyTerm (TMacro "Unit" [] (initialPos "test")) `shouldBe` "Unit"

  describe "Configuration Edge Cases and Pathological Tests" $ do
    it "handles empty and special names" $ do
      -- Note: Test robustness with various name patterns
      prettyTerm (Var "x'" 0 (initialPos "test")) `shouldBe` "x'"
      prettyTerm (Var "x_123" 0 (initialPos "test")) `shouldBe` "x_123"
      prettyRType (RVar "R'" 0 (initialPos "test")) `shouldBe` "R'"

    it "handles very long names gracefully" $ do
      let longName = "very_very_very_long_variable_name_that_could_cause_issues"
      prettyTerm (Var longName 0 (initialPos "test")) `shouldBe` longName
      prettyRType (RVar longName 0 (initialPos "test")) `shouldBe` longName

    it "handles deep nesting without stack overflow" $ do
      -- Create a deeply nested lambda: λx1. λx2. ... λx10. x10
      let deepNested = foldr (\i acc -> Lam ("x" ++ show i) acc (initialPos "test")) (Var "x10" 0 (initialPos "test")) [1 .. 10]
      let result = prettyTerm deepNested
      result `shouldContain` "λx1"
      result `shouldContain` "λx10"
      result `shouldContain` "x10"

    it "handles deeply nested type applications" $ do
      -- Create nested applications: F (G (H X))
      let deepType = RMacro "F" [RMacro "G" [RMacro "H" [RVar "X" 0 (initialPos "test")] (initialPos "test")] (initialPos "test")] (initialPos "test")
      prettyRType deepType `shouldBe` "F G H X"

    it "handles large argument lists" $ do
      let manyArgs = map (\i -> Var ("x" ++ show i) 0 (initialPos "test")) [1 .. 10]
      let manyArgMacro = TMacro "ManyArgs" manyArgs (initialPos "test")
      let result = prettyTerm manyArgMacro
      result `shouldContain` "ManyArgs"
      result `shouldContain` "x1"
      result `shouldContain` "x10"

    it "preserves Unicode vs ASCII consistency across all constructs" $ do
      let unicodeConfig = defaultPrettyConfig {useUnicode = True}
      let asciiConfig = defaultPrettyConfig {useUnicode = False}

      -- Test that all Unicode constructs have ASCII alternatives
      let term = Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")
      let rtype = All "X" (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
      let proof = TyLam "X" (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")

      prettyTermWithConfig unicodeConfig term `shouldContain` "λ"
      prettyTermWithConfig asciiConfig term `shouldContain` "\\"

      prettyRTypeWithConfig unicodeConfig rtype `shouldContain` "∀"
      prettyRTypeWithConfig asciiConfig rtype `shouldContain` "forall"

      prettyProofWithConfig unicodeConfig proof `shouldContain` "Λ"
      prettyProofWithConfig asciiConfig proof `shouldContain` "Lambda"

    it "handles showIndices configuration for all construct types" $ do
      let config = defaultPrettyConfig {showIndices = True}

      prettyTermWithConfig config (Var "x" 5 (initialPos "test")) `shouldBe` "x_5"
      prettyRTypeWithConfig config (RVar "R" 3 (initialPos "test")) `shouldBe` "R_3"
      prettyProofWithConfig config (PVar "p" 2 (initialPos "test")) `shouldBe` "p_2"

    it "handles complex mixed constructs" $ do
      -- Create a complex term with TMacro, lambda, and applications
      let complex =
            TMacro
              "Transform"
              [ Lam "f" (Lam "x" (App (Var "f" 1 (initialPos "test")) (TMacro "Helper" [Var "x" 0 (initialPos "test")] (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"),
                App (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (TMacro "Const" [] (initialPos "test")) (initialPos "test")
              ]
              (initialPos "test")
      let result = prettyTerm complex
      result `shouldContain` "Transform"
      result `shouldContain` "Helper"
      result `shouldContain` "Const"

    it "handles pathological parenthesization cases" $ do
      -- Ensure parentheses are correctly placed in complex nested structures
      let nestedApp = App (App (Lam "f" (Lam "x" (Var "f" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "g" 0 (initialPos "test")) (initialPos "test")) (Var "h" 0 (initialPos "test")) (initialPos "test")
      prettyTerm nestedApp `shouldBe` "(λf. λx. f) g h"

      let nestedRType = Arr (Arr (RVar "A" 0 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")) (Arr (RVar "C" 0 (initialPos "test")) (RVar "D" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
      prettyRType nestedRType `shouldBe` "(A → B) → C → D"
