module PrettyPrintSpec (spec) where

import Context (extendMacroEnvironment, noMacros, noTheorems)
import qualified Data.Map as Map
import qualified Errors
import Lib
import qualified RawParser as Raw
import Elaborate
import PrettyPrint
import Test.Hspec
import TestHelpers
import Text.Megaparsec (errorBundlePretty, initialPos, eof, runParser)

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

      it "handles variable shadowing correctly" $ do
        let term = Lam "x" (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyTerm term `shouldBe` "λx. λx. x"

      it "pretty prints term macros" $ do
        let term = TMacro "id" [Var "x" 0 (initialPos "test")] (initialPos "test")
        prettyTerm term `shouldBe` "id x"

      it "pretty prints term macros with multiple arguments" $ do
        let term = TMacro "compose" [Var "f" 2 (initialPos "test"), Var "g" 1 (initialPos "test"), Var "x" 0 (initialPos "test")] (initialPos "test")
        prettyTerm term `shouldBe` "compose f g x"

      it "pretty prints term macros with no arguments" $ do
        let term = TMacro "unit" [] (initialPos "test")
        prettyTerm term `shouldBe` "unit"

      it "handles complex nested term structures" $ do
        let term = App (Lam "f" (Lam "x" (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (Lam "y" (Var "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyTerm term `shouldBe` "(λf. λx. f x) (λy. y)"

      it "handles extremely nested lambda chains" $ do
        let term = Lam "a" (Lam "b" (Lam "c" (Lam "d" (App (App (Var "a" 3 (initialPos "test")) (Var "b" 2 (initialPos "test")) (initialPos "test")) (App (Var "c" 1 (initialPos "test")) (Var "d" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyTerm term `shouldBe` "λa. λb. λc. λd. a b (c d)"

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
        prettyRTypeWithConfig config (All "X" (RVar "X" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "forall X. X"

      it "pretty prints promotion" $ do
        prettyRType (Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) `shouldBe` "(λx. x)̂"

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

      it "pretty prints complex composition chains" $ do
        let ty = Comp (Comp (RVar "R" 2 (initialPos "test")) (RVar "S" 1 (initialPos "test")) (initialPos "test")) (RVar "T" 0 (initialPos "test")) (initialPos "test")
        prettyRType ty `shouldBe` "R ∘ S ∘ T"

      it "pretty prints converse of composition" $ do
        let ty = Conv (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyRType ty `shouldBe` "(R ∘ S)˘"

      it "handles operator precedence correctly" $ do
        let ty = Arr (RVar "A" 2 (initialPos "test")) (Comp (RVar "B" 1 (initialPos "test")) (RVar "C" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyRType ty `shouldBe` "A → B ∘ C"

    describe "advanced relational macro applications" $ do
      it "pretty prints simple relational macros" $ do
        prettyRType (RMacro "Id" [] (initialPos "test")) `shouldBe` "Id"

      it "pretty prints relational macros with single argument" $ do
        prettyRType (RMacro "Sym" [RVar "R" 0 (initialPos "test")] (initialPos "test")) `shouldBe` "Sym R"

      it "pretty prints relational macros with multiple arguments" $ do
        prettyRType (RMacro "Compose" [RVar "R" 1 (initialPos "test"), RVar "S" 0 (initialPos "test")] (initialPos "test")) `shouldBe` "Compose R S"

      it "pretty prints nested relational macro applications" $ do
        let inner = RMacro "Sym" [RVar "R" 0 (initialPos "test")] (initialPos "test")
        let outer = RMacro "Compose" [inner, RVar "S" 0 (initialPos "test")] (initialPos "test")
        prettyRType outer `shouldBe` "Compose (Sym R) S"

    describe "complex types" $ do
      it "pretty prints nested quantifiers" $ do
        let ty = All "X" (All "Y" (Arr (RVar "X" 1 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyRType ty `shouldBe` "∀X. ∀Y. X → Y"

      it "pretty prints quantifiers with composition" $ do
        let ty = All "R" (Comp (RVar "R" 0 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyRType ty `shouldBe` "∀R. R ∘ R"

      it "handles complex type expressions" $ do
        let ty = All "X" (Arr (RVar "X" 0 (initialPos "test")) (All "Y" (Comp (RVar "X" 1 (initialPos "test")) (RVar "Y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyRType ty `shouldBe` "∀X. X → ∀Y. X ∘ Y"

      it "handles deeply nested relational expressions" $ do
        let ty = Conv (Comp (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")) (Conv (RVar "S" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyRType ty `shouldBe` "(R˘ ∘ S˘)˘"

  describe "Proof Pretty Printing" $ do
    describe "basic proofs" $ do
      it "pretty prints proof variables" $ do
        prettyProof (PVar "p" 0 (initialPos "test")) `shouldBe` "p"

      it "pretty prints proof lambda" $ do
        prettyProof (LamP "x" (RVar "R" 0 (initialPos "test")) (PVar "x" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "λx:R. x"

      it "pretty prints type lambda" $ do
        prettyProof (TyLam "X" (PVar "p" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "ΛX. p"

      it "pretty prints proof application" $ do
        prettyProof (AppP (PVar "f" 1 (initialPos "test")) (PVar "x" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "f x"

      it "pretty prints type application" $ do
        prettyProof (TyApp (PVar "p" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "p{X}"

      it "pretty prints iota" $ do
        prettyProof (Iota (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "ι⟨x, y⟩"

    describe "advanced proof constructs" $ do
      it "pretty prints conversion proof" $ do
        let proof = ConvProof (Var "t" 1 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "t ⇃ p ⇂ u"

      it "pretty prints converse introduction" $ do
        prettyProof (ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "∪ᵢ p"

      it "pretty prints converse elimination" $ do
        prettyProof (ConvElim (PVar "p" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "∪ₑ p"

      it "pretty prints rho elimination" $ do
        let proof = RhoElim "x" (Var "t1" 1 (initialPos "test")) (Var "t2" 0 (initialPos "test")) (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "ρ{x. t1, t2} p - q"

      it "pretty prints pi elimination" $ do
        let proof = Pi (PVar "p" 1 (initialPos "test")) "x" "y" "z" (PVar "q" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "π p - x.y.z. q"

      it "pretty prints pairs" $ do
        prettyProof (Pair (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")) `shouldBe` "(p, q)"

    describe "complex proofs" $ do
      it "pretty prints nested proof lambdas" $ do
        let proof = LamP "x" (RVar "R" 0 (initialPos "test")) (LamP "y" (RVar "S" 0 (initialPos "test")) (AppP (PVar "x" 1 (initialPos "test")) (PVar "y" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "λx:R. λy:S. x y"

      it "pretty prints complex type applications" $ do
        let proof = TyApp (TyApp (PVar "p" 0 (initialPos "test")) (RVar "A" 0 (initialPos "test")) (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "p{A}{B}"

      it "handles nested conversion proofs" $ do
        let inner = ConvProof (Var "x" 0 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")
        let outer = ConvProof (Var "z" 0 (initialPos "test")) inner (Var "w" 0 (initialPos "test")) (initialPos "test")
        prettyProof outer `shouldBe` "z ⇃ (x ⇃ p ⇂ y) ⇂ w"

      it "handles complex mixed proof constructs" $ do
        let proof = AppP (TyLam "X" (LamP "p" (RVar "X" 0 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")
        prettyProof proof `shouldBe` "(ΛX. λp:X. p) q"

  describe "Relational Judgment Pretty Printing" $ do
    it "pretty prints simple relational judgments" $ do
      let judgment = RelJudgment (Var "x" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
      prettyRelJudgment judgment `shouldBe` "x [R] y"

    it "pretty prints judgments with complex terms" $ do
      let judgment = RelJudgment (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (Arr (RVar "A" 0 (initialPos "test")) (RVar "B" 0 (initialPos "test")) (initialPos "test")) (Lam "w" (Var "w" 0 (initialPos "test")) (initialPos "test"))
      prettyRelJudgment judgment `shouldBe` "(λz. z) [A → B] (λw. w)"

    it "pretty prints judgments with relational operations" $ do
      let judgment = RelJudgment (Var "x" 2 (initialPos "test")) (Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")) (Var "z" 0 (initialPos "test"))
      prettyRelJudgment judgment `shouldBe` "x [R ∘ S] z"

    it "handles quantified judgments" $ do
      let judgment = RelJudgment (Var "f" 0 (initialPos "test")) (All "X" (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Var "g" 0 (initialPos "test"))
      prettyRelJudgment judgment `shouldBe` "f [∀X. X → X] g"

  describe "Declaration Pretty Printing" $ do
    it "pretty prints macro definitions" $ do
      let decl = MacroDef "id" [] (TermMacro (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")))
      prettyDeclaration decl `shouldBe` "id := λx. x;"

    it "pretty prints parameterized macro definitions" $ do
      let decl = MacroDef "const" ["x", "y"] (TermMacro (Var "x" 1 (initialPos "test")))
      prettyDeclaration decl `shouldBe` "const x y := x;"

    it "pretty prints relational macro definitions" $ do
      let decl = MacroDef "Sym" ["R"] (RelMacro (Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")))
      prettyDeclaration decl `shouldBe` "Sym R := R˘;"

    it "pretty prints theorem definitions" $ do
      let decl = TheoremDef "refl" [TermBinding "x"] (RelJudgment (Var "x" 0 (initialPos "test")) (RMacro "Id" [] (initialPos "test")) (Var "x" 0 (initialPos "test"))) (Iota (Var "x" 0 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test"))
      prettyDeclaration decl `shouldBe` "⊢ refl (x : Term) : x [Id] x := ι⟨x, x⟩;"

    it "pretty prints fixity declarations" $ do
      let decl = FixityDecl (Infixl 6) "_+_"
      prettyDeclaration decl `shouldBe` "infixl 6 _+_;"

    describe "advanced macro declaration tests" $ do
      it "pretty prints complex macro bodies" $ do
        let body = TermMacro (Lam "f" (Lam "g" (Lam "x" (App (Var "f" 2 (initialPos "test")) (App (Var "g" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test"))
        let decl = MacroDef "compose" ["f", "g", "x"] body
        prettyDeclaration decl `shouldBe` "compose f g x := λf. λg. λx. f (g x);"

      it "pretty prints theorems with multiple bindings" $ do
        let bindings = [TermBinding "t", TermBinding "u", RelBinding "R", ProofBinding "p" (RelJudgment (Var "t" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")))]
        let judgment = RelJudgment (Var "t" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "u" 0 (initialPos "test"))
        let proof = PVar "p" 0 (initialPos "test")
        let decl = TheoremDef "identity" bindings judgment proof
        prettyDeclaration decl `shouldBe` "⊢ identity (t : Term) (u : Term) (R : Rel) (p : t [R] u) : t [R] u := p;"

  describe "Binding Pretty Printing" $ do
    it "pretty prints term bindings" $ do
      prettyBinding (TermBinding "x") `shouldBe` "(x : Term)"

    it "pretty prints relation bindings" $ do
      prettyBinding (RelBinding "R") `shouldBe` "(R : Rel)"

    it "pretty prints proof bindings" $ do
      let judgment = RelJudgment (Var "x" 1 (initialPos "test")) (RVar "R" 0 (initialPos "test")) (Var "y" 0 (initialPos "test"))
      prettyBinding (ProofBinding "p" judgment) `shouldBe` "(p : x [R] y)"

    it "handles complex proof bindings" $ do
      let judgment = RelJudgment (Lam "z" (Var "z" 0 (initialPos "test")) (initialPos "test")) (All "X" (Arr (RVar "X" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (Lam "w" (Var "w" 0 (initialPos "test")) (initialPos "test"))
      prettyBinding (ProofBinding "identity" judgment) `shouldBe` "(identity : (λz. z) [∀X. X → X] (λw. w))"

  describe "Error Pretty Printing" $ do
    describe "variable and binding errors" $ do
      it "pretty prints unbound variable errors" $ do
        let ctx = Errors.ErrorContext (initialPos "test") "test context"
        let err = Errors.UnboundVariable "x" ctx
        Errors.formatError err `shouldContain` "Unbound variable: x"

      it "pretty prints type mismatch errors" $ do
        let ctx = Errors.ErrorContext (initialPos "test") "test context"
        let err = Errors.TypeMismatch (RVar "A" 0 (initialPos "test")) (RVar "B" 0 (initialPos "test")) ctx
        Errors.formatError err `shouldContain` "Type mismatch"

      it "pretty prints macro errors" $ do
        let ctx = Errors.ErrorContext (initialPos "test") "test context"
        let err = Errors.UnboundMacro "foo" ctx
        Errors.formatError err `shouldContain` "Unbound macro: foo"

    describe "type system errors" $ do
      it "pretty prints arity mismatch errors" $ do
        let ctx = Errors.ErrorContext (initialPos "test") "test context"
        let err = Errors.MacroArityMismatch "map" 2 1 ctx
        Errors.formatError err `shouldContain` "Macro map expects 2 arguments, but got 1"

      it "pretty prints invalid context errors" $ do
        let ctx = Errors.ErrorContext (initialPos "test") "test context"
        let err = Errors.InvalidContext "test message" ctx
        Errors.formatError err `shouldContain` "Invalid context: test message"

  describe "Round-trip Testing" $ do
    describe "RType round-trips" $ do
      it "preserves simple relation variables through round-trip" $ do
        let original = RVar "R" 0 (initialPos "test")
            prettyResult = prettyRType original
            relVarMap = Map.fromList [("R", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { relVars = relVarMap }
        case runParser (Raw.parseRType <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawRType -> case elaborateRType ctx rawRType of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves arrow types through round-trip" $ do
        let original = Arr (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyRType original
            relVarMap = Map.fromList [("R", 1), ("S", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { relVars = relVarMap }
        case runParser (Raw.parseRType <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawRType -> case elaborateRType ctx rawRType of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves forall types through round-trip" $ do
        let original = All "R" (RVar "R" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyRType original
            ctx = emptyElaborateContext Map.empty noMacros noTheorems
        case runParser (Raw.parseRType <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawRType -> case elaborateRType ctx rawRType of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves composition through round-trip" $ do
        let original = Comp (RVar "R" 1 (initialPos "test")) (RVar "S" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyRType original
            relVarMap = Map.fromList [("R", 1), ("S", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { relVars = relVarMap }
        case runParser (Raw.parseRType <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawRType -> case elaborateRType ctx rawRType of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves converse through round-trip" $ do
        let original = Conv (RVar "R" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyRType original
            relVarMap = Map.fromList [("R", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { relVars = relVarMap }
        case runParser (Raw.parseRType <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawRType -> case elaborateRType ctx rawRType of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves promotion through round-trip" $ do
        let original = Prom (Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")
            prettyResult = prettyRType original
            ctx = emptyElaborateContext Map.empty noMacros noTheorems
        case runParser (Raw.parseRType <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawRType -> case elaborateRType ctx rawRType of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves complex nested types through round-trip" $ do
        let original = All "X" (Arr (RVar "X" 0 (initialPos "test")) (Comp (RVar "X" 0 (initialPos "test")) (Conv (RVar "X" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
            prettyResult = prettyRType original
            ctx = emptyElaborateContext Map.empty noMacros noTheorems
        case runParser (Raw.parseRType <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawRType -> case elaborateRType ctx rawRType of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

    describe "Term round-trips" $ do
      it "preserves variables through round-trip" $ do
        let original = Var "x" 0 (initialPos "test")
            prettyResult = prettyTerm original
            termVarMap = Map.fromList [("x", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { termVars = termVarMap }
        case runParser (Raw.parseTerm <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawTerm -> case elaborateTerm ctx rawTerm of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves lambda abstractions through round-trip" $ do
        let original = Lam "x" (Var "x" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyTerm original
            ctx = emptyElaborateContext Map.empty noMacros noTheorems
        case runParser (Raw.parseTerm <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawTerm -> case elaborateTerm ctx rawTerm of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves applications through round-trip" $ do
        let original = App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyTerm original
            termVarMap = Map.fromList [("f", 1), ("x", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { termVars = termVarMap }
        case runParser (Raw.parseTerm <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawTerm -> case elaborateTerm ctx rawTerm of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves term macros through round-trip" $ do
        let original = TMacro "id" [Var "x" 0 (initialPos "test")] (initialPos "test")
            prettyResult = prettyTerm original
            termVarMap = Map.fromList [("x", 0)]
            testMacroEnv = extendMacroEnvironment "id" ["x"] (TermMacro (Var "x" 0 (initialPos "test"))) defaultFixity noMacros
            ctx = (emptyElaborateContext Map.empty testMacroEnv noTheorems) { termVars = termVarMap }
        case runParser (Raw.parseTerm <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawTerm -> case elaborateTerm ctx rawTerm of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves complex nested terms through round-trip" $ do
        let original = Lam "f" (Lam "x" (App (Var "f" 1 (initialPos "test")) (App (Var "f" 1 (initialPos "test")) (Var "x" 0 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
            prettyResult = prettyTerm original
            ctx = emptyElaborateContext Map.empty noMacros noTheorems
        case runParser (Raw.parseTerm <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawTerm -> case elaborateTerm ctx rawTerm of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

    describe "Proof round-trips" $ do
      it "preserves proof variables through round-trip" $ do
        let original = PVar "p" 0 (initialPos "test")
            prettyResult = prettyProof original
            proofVarMap = Map.fromList [("p", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { proofVars = proofVarMap }
        case runParser (Raw.parseProof <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves proof lambda through round-trip" $ do
        let original = LamP "x" (RVar "R" 0 (initialPos "test")) (PVar "x" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyProof original
            relVarMap = Map.fromList [("R", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { relVars = relVarMap }
        case runParser (Raw.parseProof <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves type lambda through round-trip" $ do
        let original = TyLam "X" (PVar "p" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyProof original
            proofVarMap = Map.fromList [("p", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { proofVars = proofVarMap }
        case runParser (Raw.parseProof <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves proof applications through round-trip" $ do
        let original = AppP (PVar "f" 1 (initialPos "test")) (PVar "x" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyProof original
            proofVarMap = Map.fromList [("f", 1), ("x", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { proofVars = proofVarMap }
        case runParser (Raw.parseProof <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves type applications through round-trip" $ do
        let original = TyApp (PVar "p" 0 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyProof original
            proofVarMap = Map.fromList [("p", 0)]
            relVarMap = Map.fromList [("X", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { proofVars = proofVarMap, relVars = relVarMap }
        case runParser (Raw.parseProof <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves iota through round-trip" $ do
        let original = Iota (Var "x" 1 (initialPos "test")) (Var "y" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyProof original
            termVarMap = Map.fromList [("x", 1), ("y", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { termVars = termVarMap }
        case runParser (Raw.parseProof <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of 
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves conversion proofs through round-trip" $ do
        let original = ConvProof (Var "t" 1 (initialPos "test")) (PVar "p" 0 (initialPos "test")) (Var "u" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyProof original
            termVarMap = Map.fromList [("t", 1), ("u", 0)]
            proofVarMap = Map.fromList [("p", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { termVars = termVarMap, proofVars = proofVarMap }
        case runParser (Raw.parseProof <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves converse operations through round-trip" $ do
        let original = ConvIntro (PVar "p" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyProof original
            proofVarMap = Map.fromList [("p", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { proofVars = proofVarMap }
        case runParser (Raw.parseProof <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves pairs through round-trip" $ do
        let original = Pair (PVar "p" 1 (initialPos "test")) (PVar "q" 0 (initialPos "test")) (initialPos "test")
            prettyResult = prettyProof original
            proofVarMap = Map.fromList [("p", 1), ("q", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { proofVars = proofVarMap }
        case runParser (Raw.parseProof <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original

      it "preserves complex nested proofs through round-trip" $ do
        let original = LamP "x" (RVar "R" 0 (initialPos "test")) (TyLam "X" (AppP (TyApp (PVar "x" 1 (initialPos "test")) (RVar "X" 0 (initialPos "test")) (initialPos "test")) (PVar "x" 1 (initialPos "test")) (initialPos "test")) (initialPos "test")) (initialPos "test")
            prettyResult = prettyProof original
            relVarMap = Map.fromList [("R", 0)]
            ctx = (emptyElaborateContext Map.empty noMacros noTheorems) { relVars = relVarMap }
        case runParser (Raw.parseProof <* eof) "test" prettyResult of
          Left err -> expectationFailure $ "Parse failed: " ++ errorBundlePretty err
          Right rawProof -> case elaborateProof ctx rawProof of
            Left err -> expectationFailure $ "Elaboration failed: " ++ show err
            Right parsed -> parsed `shouldBeEqual` original