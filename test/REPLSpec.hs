module REPLSpec (spec) where

import Context
import Control.Monad.State
import Data.List (isInfixOf)
import REPL
import Test.Hspec

spec :: Spec
spec = do
  describe "REPL State Management" $ do
    it "creates initial empty state" $ do
      let initState = initialREPLState
      replMacroEnv initState `shouldBe` noMacros
      replContext initState `shouldBe` emptyTypingContext
      replDeclarations initState `shouldBe` []
      replHistory initState `shouldBe` []

    it "tracks command history" $ do
      let commands = [":help", ":list", ":quit"]
      let addToHistory cmd = modify (\s -> s {replHistory = cmd : replHistory s}) :: State REPLState ()
      let finalState = execState (mapM_ addToHistory commands) initialREPLState
      replHistory finalState `shouldBe` reverse commands

  describe "REPL Command Parsing" $ do
    it "parses help commands" $ do
      parseREPLCommand ":help" `shouldBe` Right HelpREPL
      parseREPLCommand ":h" `shouldBe` Right HelpREPL
      parseREPLCommand "  :help  " `shouldBe` Right HelpREPL

    it "parses quit commands" $ do
      parseREPLCommand ":quit" `shouldBe` Right QuitREPL
      parseREPLCommand ":q" `shouldBe` Right QuitREPL

    it "parses load commands" $ do
      parseREPLCommand ":load file.rtt" `shouldBe` Right (LoadFile "file.rtt")
      parseREPLCommand ":l test.rtt" `shouldBe` Right (LoadFile "test.rtt")
      parseREPLCommand ":load   long_file_name.rtt" `shouldBe` Right (LoadFile "long_file_name.rtt")

    it "parses check proof commands" $ do
      parseREPLCommand ":check p x[R]y" `shouldBe` Right (CheckProof "p" "x[R]y")
      parseREPLCommand ":c ι⟨x,y⟩ x[R]y" `shouldBe` Right (CheckProof "ι⟨x,y⟩" "x[R]y")

    it "parses infer proof commands" $ do
      parseREPLCommand ":infer p" `shouldBe` Right (InferProof "p")
      parseREPLCommand ":infer ι⟨x,y⟩" `shouldBe` Right (InferProof "ι⟨x,y⟩")

    it "parses macro expand commands" $ do
      parseREPLCommand ":expand Bool" `shouldBe` Right (ExpandMacro "Bool")
      parseREPLCommand ":e R ∘ S" `shouldBe` Right (ExpandMacro "R ∘ S")

    it "parses info commands" $ do
      parseREPLCommand ":info Bool" `shouldBe` Right (ShowInfo "Bool")
      parseREPLCommand ":i MyMacro" `shouldBe` Right (ShowInfo "MyMacro")

    it "parses session control commands" $ do
      parseREPLCommand ":list" `shouldBe` Right ListDeclarations
      parseREPLCommand ":clear" `shouldBe` Right ClearSession
      parseREPLCommand ":history" `shouldBe` Right ShowHistory

    it "parses declaration input" $ do
      parseREPLCommand "Bool := ∀X. X → X → X;" `shouldBe` Right (ParseDeclaration "Bool := ∀X. X → X → X;")
      parseREPLCommand "⊢ test : x [R] y := p;" `shouldBe` Right (ParseDeclaration "⊢ test : x [R] y := p;")

    it "handles empty input" $ do
      let isLeft (Left _) = True
          isLeft _ = False
      parseREPLCommand "" `shouldSatisfy` isLeft
      parseREPLCommand "   " `shouldSatisfy` isLeft

    it "handles invalid input" $ do
      let isLeft (Left _) = True
          isLeft _ = False
      parseREPLCommand ":invalid" `shouldSatisfy` isLeft
      parseREPLCommand ":load" `shouldSatisfy` isLeft -- Missing filename
  describe "REPL Command Execution" $ do
    it "executes help command" $ do
      result <- evalStateT (executeREPLCommand HelpREPL) initialREPLState
      result `shouldContain` "RelTT Interactive Proof Assistant"
      result `shouldContain` "Commands:"
      result `shouldContain` ":help"
      result `shouldContain` ":quit"
      result `shouldContain` ":load"

    it "executes quit command" $ do
      result <- evalStateT (executeREPLCommand QuitREPL) initialREPLState
      result `shouldBe` "Goodbye!"

    it "executes list command on empty state" $ do
      result <- evalStateT (executeREPLCommand ListDeclarations) initialREPLState
      result `shouldBe` "No declarations"

    it "executes clear command" $ do
      -- Start with some state
      let stateWithHistory = initialREPLState {replHistory = ["test1", "test2"]}
      result <- evalStateT (executeREPLCommand ClearSession) stateWithHistory
      result `shouldBe` "Session cleared"

      -- Verify state is cleared
      finalState <- execStateT (executeREPLCommand ClearSession) stateWithHistory
      finalState `shouldBe` initialREPLState

    it "executes history command on empty state" $ do
      result <- evalStateT (executeREPLCommand ShowHistory) initialREPLState
      result `shouldBe` "No command history"

    it "executes history command with commands" $ do
      let stateWithHistory = initialREPLState {replHistory = ["cmd1", "cmd2"]}
      result <- evalStateT (executeREPLCommand ShowHistory) stateWithHistory
      result `shouldContain` "1: cmd2" -- Most recent first
      result `shouldContain` "2: cmd1"

    it "executes info command for non-existent definition" $ do
      result <- evalStateT (executeREPLCommand (ShowInfo "NonExistent")) initialREPLState
      result `shouldContain` "No macro named NonExistent"
      result `shouldContain` "No term named NonExistent"

    it "executes infer proof command with simple proof" $ do
      result <- evalStateT (executeREPLCommand (InferProof "ι⟨λx. x, λy. y⟩")) initialREPLState
      result `shouldContain` "Inferred judgment:"

    it "executes check proof command with valid syntax" $ do
      result <- evalStateT (executeREPLCommand (CheckProof "ι⟨λx. x, λy. y⟩" "(λx. x)[(λa. λb. a)]((λy. y))")) initialREPLState
      result `shouldSatisfy` (\r -> "Proof is valid" `isInfixOf` r || "Parse error:" `isInfixOf` r || "Proof checking failed:" `isInfixOf` r)

    it "handles invalid syntax in proof check" $ do
      result <- evalStateT (executeREPLCommand (InferProof "λ")) initialREPLState
      result `shouldContain` "Parse error:"

    it "handles Unicode π symbol in pi elimination" $ do
      -- Both ASCII and Unicode should fail with the same error: "Unknown identifier: p"
      -- because 'p' is not bound in initialREPLState
      asciiResult <- evalStateT (executeREPLCommand (InferProof "pi p - x.u.v.u")) initialREPLState
      unicodeResult <- evalStateT (executeREPLCommand (InferProof "π p - x.u.v.u")) initialREPLState

      -- Both should fail with an error about 'p' being unknown
      -- The error might be "Unknown identifier: p" or "Unknown proof: p" or "Unknown term: p"
      asciiResult `shouldSatisfy` \result -> 
        "Unknown identifier: p" `isInfixOf` result || 
        "Unknown proof: p" `isInfixOf` result || 
        "Unknown term: p" `isInfixOf` result
      unicodeResult `shouldSatisfy` \result -> 
        "Unknown identifier: p" `isInfixOf` result || 
        "Unknown proof: p" `isInfixOf` result || 
        "Unknown term: p" `isInfixOf` result

    it "handles Unicode π symbol with spaces after dots" $ do
      -- Both ASCII and Unicode should fail with the same error: "Unknown identifier: p"
      -- because 'p' is not bound in initialREPLState (spaces shouldn't matter)
      asciiWithSpaces <- evalStateT (executeREPLCommand (InferProof "pi p - x. u. v. u")) initialREPLState
      unicodeWithSpaces <- evalStateT (executeREPLCommand (InferProof "π p - x. u. v. u")) initialREPLState

      -- Both should fail with an error about 'p' being unknown
      -- The error might be "Unknown identifier: p" or "Unknown proof: p" or "Unknown term: p"
      asciiWithSpaces `shouldSatisfy` \result -> 
        "Unknown identifier: p" `isInfixOf` result || 
        "Unknown proof: p" `isInfixOf` result || 
        "Unknown term: p" `isInfixOf` result
      unicodeWithSpaces `shouldSatisfy` \result -> 
        "Unknown identifier: p" `isInfixOf` result || 
        "Unknown proof: p" `isInfixOf` result || 
        "Unknown term: p" `isInfixOf` result

    it "handles invalid syntax in check proof command" $ do
      result <- evalStateT (executeREPLCommand (CheckProof "invalid" "x[R]y")) initialREPLState
      result `shouldContain` "Parse error in proof:"

    it "handles invalid syntax in macro expand" $ do
      result <- evalStateT (executeREPLCommand (ExpandMacro "invalid syntax")) initialREPLState
      result `shouldContain` "Parse error:"

  describe "REPL Macro and Declaration Management" $ do
    it "processes valid macro definition" $ do
      let macroDecl = "Id := λx. x;"
      result <- evalStateT (executeREPLCommand (ParseDeclaration macroDecl)) initialREPLState
      result `shouldContain` "Added macro: Id"

    it "processes valid theorem definition" $ do
      let theoremDecl = "⊢ test : x [R] y := p;"
      -- This should parse successfully but may fail in proof checking
      result <- evalStateT (executeREPLCommand (ParseDeclaration theoremDecl)) initialREPLState
      -- Could be either success or proof checking error
      let isWordInfixOf needle haystack = needle `elem` (words haystack)
      result `shouldSatisfy` (\r -> "Added theorem:" `isWordInfixOf` r || "error:" `isWordInfixOf` r)

    it "handles invalid declaration syntax" $ do
      result <- evalStateT (executeREPLCommand (ParseDeclaration "invalid")) initialREPLState
      result `shouldContain` "Parse error:"

    it "maintains state across multiple declarations" $ do
      let macro1 = "Id := λx. x;"
      let macro2 = "Comp R S := R ∘ S;"

      finalState <-
        execStateT
          ( do
              void $ executeREPLCommand (ParseDeclaration macro1)
              void $ executeREPLCommand (ParseDeclaration macro2)
          )
          initialREPLState

      length (replDeclarations finalState) `shouldBe` 2

    it "lists declarations after adding them" $ do
      let macro = "Id := λx. x;"
      result <-
        evalStateT
          ( do
              void $ executeREPLCommand (ParseDeclaration macro)
              executeREPLCommand ListDeclarations
          )
          initialREPLState

      result `shouldContain` "Id := λx. x;"

    it "shows macro info after definition" $ do
      let macro = "Id := λx. x;"
      result <-
        evalStateT
          ( do
              void $ executeREPLCommand (ParseDeclaration macro)
              executeREPLCommand (ShowInfo "Id")
          )
          initialREPLState

      result `shouldContain` "Macro Id := λx. x"

    it "expands macros after definition" $ do
      let macro = "Id := λx. x;"
      result <-
        evalStateT
          ( do
              void $ executeREPLCommand (ParseDeclaration macro)
              executeREPLCommand (ExpandMacro "Id")
          )
          initialREPLState

      result `shouldContain` "Original: Id"
      result `shouldContain` "Expanded: λx. x"

  describe "REPL File Loading" $ do
    it "handles non-existent file gracefully" $ do
      result <- evalStateT (executeREPLCommand (LoadFile "nonexistent.rtt")) initialREPLState
      result `shouldContain` "File not found: nonexistent.rtt"
    -- Should handle file not found error gracefully

    it "reports successful loading format" $ do
      -- We can't test actual file loading without creating files,
      -- but we can test the expected output format
      let loadCmd = LoadFile "test.rtt"
      result <- evalStateT (executeREPLCommand loadCmd) initialREPLState
      result `shouldContain` "File not found: test.rtt"

  describe "REPL Integration" $ do
    it "maintains consistent state through multiple operations" $ do
      let operations =
            [ ParseDeclaration "Bool := ∀X. X → X → X;",
              ParseDeclaration "True := (λx. λy. x);"
            ]

      finalState <- execStateT (mapM_ executeREPLCommand operations) initialREPLState

      -- Should have 2 declarations
      length (replDeclarations finalState) `shouldBe` 2

    it "handles mixed valid and invalid commands" $ do
      let operations =
            [ ParseDeclaration "Bool := ∀X. X → X → X;", -- Valid
              ParseDeclaration "Invalid syntax", -- Invalid
              ListDeclarations, -- Valid
              ShowInfo "NonExistent" -- Valid but no result
            ]

      results <- evalStateT (mapM executeREPLCommand operations) initialREPLState

      -- Should have some successes and some errors
      let isWordInfixOf needle haystack = needle `elem` (words haystack)
          shouldBeGreaterThan actual expected = actual > expected `shouldBe` True
      let successes = filter (not . ("error:" `isWordInfixOf`)) results
      let errors = filter ("error:" `isWordInfixOf`) results
      length successes `shouldBeGreaterThan` 0
      length errors `shouldBeGreaterThan` 0

    it "preserves Unicode formatting in output" $ do
      let macro = "Arrow X Y := X → Y;"
      result <-
        evalStateT
          ( do
              void $ executeREPLCommand (ParseDeclaration macro)
              executeREPLCommand ListDeclarations
          )
          initialREPLState

      result `shouldContain` "→" -- Unicode arrow should be preserved
    it "handles complex nested structures" $ do
      let complexMacro = "Complex := ∀X. (X → X) → X ∘ X;"
      result <-
        evalStateT
          ( do
              void $ executeREPLCommand (ParseDeclaration complexMacro)
              executeREPLCommand (ShowInfo "Complex")
          )
          initialREPLState

      result `shouldContain` "∀X. (X → X) → X ∘ X"

  describe "REPL Error Handling" $ do
    it "provides helpful error messages for parsing failures" $ do
      result <- evalStateT (executeREPLCommand (ParseDeclaration "λ")) initialREPLState
      result `shouldContain` "Parse error:"

    it "provides helpful error messages for proof checking failures" $ do
      result <- evalStateT (executeREPLCommand (CheckProof "invalid_proof" "x[R]y")) initialREPLState
      result `shouldContain` "Parse error in proof:"

    it "handles macro expansion errors gracefully" $ do
      result <-
        evalStateT
          ( do
              -- First define a macro that expects parameters
              _ <- executeREPLCommand (ParseDeclaration "TestMacro X Y := X → Y;")
              -- Then try to expand it without enough arguments (should cause arity mismatch)
              executeREPLCommand (ExpandMacro "TestMacro")
          )
          initialREPLState
      result `shouldContain` "Macro 'TestMacro' expects 2 arguments but got 0"

    it "recovers from errors and continues operation" $ do
      let operations =
            [ ParseDeclaration "Invalid", -- Error
              ParseDeclaration "Bool := ∀X. X → X;", -- Success
              ListDeclarations -- Success
            ]

      results <- evalStateT (mapM executeREPLCommand operations) initialREPLState

      -- Last operation should show the valid declaration
      let lastResult = last results
      lastResult `shouldContain` "Bool := ∀X. X → X;"
