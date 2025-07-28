# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

RelTT-Haskell is a Haskell implementation of Relational Type Theory (RelTT). The codebase implements a complete proof assistant with parsing, type checking, and proof verification for a language with relational types, including operations like composition (∘), converse (˘), and promotion (̂).

## Semantic Guidance

**IMPORTANT**: Any time you're thinking about the semantics of the theory, read the examples/demo.rtt file for theory reference. NEVER speculate. If you have a question about how the theory works, use that as your source of truth.

**DON'T LIE TO ME!!!!!**

## Development Standards

### Code Quality Requirements

**NEVER** do any of the following:

1. **No TODOs or Temporary Implementations**
   - Never leave TODO comments in code
   - Never implement "temporary" solutions that bypass proper logic
   - Every implementation must be complete and correct from the start
   - If you cannot implement something properly, ask for clarification rather than leaving a placeholder

2. **No Test Bypassing or Weakening**
   - Never bypass a failing test by commenting it out or modifying the test expectations
   - Never delete test assertions to make tests pass
   - Never change test expectations to match broken behavior
   - If a test fails, fix the implementation, not the test
   - Never accept "any error is fine" when specific error types should be validated

3. **No Trivial or Misleading Tests**
   - Never write tests that only verify language constructs (like record field assignment)
   - Never write tests that give false confidence about system functionality
   - Every test must validate meaningful behavior
   - Test descriptions must accurately reflect what is being tested
   - Tests must fail when the functionality they test is broken

4. **Proper Error Handling**
   - Every error case must have specific, appropriate error types
   - Never use generic error handling when specific validation is needed
   - Error messages must be informative and actionable
   - Error formatting tests must validate complete message structure, not just substring presence

5. **Implementation Completeness**
   - Never work around known bugs in tests - fix the bugs
   - Never implement partial functionality and claim it's complete
   - All edge cases must be properly handled

### Violation Consequences

Any code that violates these standards will be considered broken and must be fixed immediately. These standards exist to maintain code quality and prevent the accumulation of technical debt.

## Development Tips

- If you need a function for testing but it isn't exported, just add it to the export list.

## Build and Development Commands

### Building
```bash
stack build                 # Build the project
stack build --fast         # Build without optimizations for faster development
```

### Running
```bash
stack run                           # Run the interactive REPL (default)
stack run -- --repl                 # Run the interactive REPL (explicit)
stack run -- --check <file>         # Type check and verify all proofs in file
stack run -- --verbose <file>       # Type check with verbose output
stack run -- --parse-only <file>    # Parse-only mode (explicit)
stack exec reltt-haskell-exe        # Alternative way to run
```

### Testing
```bash
stack test                 # Run test suite
```

### REPL
```bash
stack repl                 # Start GHCi with the project loaded
stack repl src/Lib.hs     # Load specific module in REPL
```

### Code Quality
```bash
stack build --pedantic    # Build with all warnings as errors
```

## Architecture

### Core Modules

- **Lib.hs**: Core data types for the language
  - `Term`: Lambda calculus terms (variables, lambdas, applications)
  - `RType`: Relational types with operations (arrows, quantifiers, composition, converse, promotion)
  - `Proof`: Proof terms including relational operations
  - `Declaration`: Top-level declarations (macros and theorems)

- **Parser.hs**: Megaparsec-based parser
  - Implements complete term parsing with operator precedence
  - Uses expression parsers for handling infix/postfix operators
  - Supports Unicode syntax for relational operations

- **ProofChecker.hs**: Type checking and proof verification
  - Implements complete proof checking according to RelTT rules
  - Validates side conditions for lambda abstractions and pi elimination
  - Supports macro expansion and optimization

- **Context.hs**: Context management and free variable analysis
  - Manages typing contexts for terms and proof terms
  - Implements free variable analysis for side condition checking
  - Supports context extension and lookup operations

- **MacroValidation.hs**: Macro environment validation
  - Validates macro definitions for cycles and consistency
  - Manages macro expansion and substitution
  - Ensures macro environments are well-formed

### Example Files

The `examples/` folder contains RelTT demonstration files:

- **demo.rtt**: Comprehensive demonstration of all RelTT proof constructors and rules
  - Shows every typing rule from the paper in action
  - Includes composition laws, identity laws, and complex proof patterns
  - **CRITICAL**: Use this as the authoritative reference for RelTT semantics
- **comprehensive_bool.rtt**: Extended boolean library with proven theorems

### Language Features

The language supports Unicode syntax for relational operations:
- Arrow types: `→` (alternative to `->`)
- Composition: `∘`
- Converse: `˘`
- Promotion: `̂`
- Converse introduction/elimination: `∪ᵢ`, `∪ₑ`

Example syntax is demonstrated in `examples/comprehensive_bool.rtt` which shows macro definitions and theorem declarations for boolean logic.

### Proof Checking Capabilities

The RelTT proof assistant provides complete proof verification:

- **Macro System**: Supports parameterized macros with cycle detection and validation
- **Type Checking**: Full type checking for lambda calculus terms and relational types
- **Proof Verification**: Validates proof terms according to RelTT rules including:
  - Terms as functional relations (ι⟨⟩)
  - Pi introduction/elimination with side condition validation
  - Lambda abstractions with free variable constraints
  - Composition and converse operations
- **Error Reporting**: Detailed error messages for type mismatches and invalid proofs

### Interactive REPL

The RelTT proof assistant includes an interactive Read-Eval-Print Loop (REPL) for exploratory proof development:

- **Session Management**: Maintains state across commands with macro and theorem definitions
- **File Loading**: Load and check RelTT files with `:load <file>`
- **Definition Querying**: 
  - `:info <name>` - Show information about definitions
  - `:expand <macro>` - Expand macro definitions
  - `:check <proof>` - Check proof correctness
  - `:type <term>` - Show term information
- **Session Control**:
  - `:list` - List all declarations
  - `:clear` - Clear session state
  - `:history` - Show command history
  - `:help` - Show available commands
- **Interactive Definition**: Enter macro definitions and theorems directly

### Dependencies

Key dependencies (defined in package.yaml):
- `megaparsec`: Parser combinators
- `prettyprinter`: Pretty printing support
- `parser-combinators`: Additional parser utilities

The project uses Stack with LTS 24.0 snapshot.