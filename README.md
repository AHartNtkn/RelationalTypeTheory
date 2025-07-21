# RelTT-Haskell

A complete implementation of Relational Type Theory (RelTT) in Haskell, providing a proof assistant for relational programming and verification.

## Overview

RelTT-Haskell implements the type system and proof checker described in the paper [Relational Type Theory](https://arxiv.org/pdf/2101.09655). This system defines a theory of first-class relations between untyped lambda expressions, enabling direct reasoning about relational properties.

The implementation includes:

- **Complete parser** for RelTT syntax with Unicode support
- **Type checker and proof verifier** implementing all RelTT rules
- **Interactive REPL** for exploratory proof development
- **Macro system** with cycle detection and validation
- **Comprehensive error reporting** with source location information

## Capabilities

This theory is expressive enough to act as a foundation for mathematics, despite lacking anything like a universe of types. It avoids this by not begging the question. Instead of types that can contain anything, the first-class objects are relations between untyped lambda expressions. There's nothing like a thing that could contain more of that thing in the first place.

That this theory is expressive enough to act as a foundation of mathematics is less obvious, but boils down to the ability to express ordinary system-F types as partial equivalence relations (PERs), combined with lambda expressions which are (functional) relations between lambda expressions. This allows one to define:

- **Propositional relations** - relations that relate anything to anything else iff they are true, and nothing to anything else iff they are false
- **Sub-typing and relational equivalence** - as fairly simple propositional relations
- **Inductive data types** - encoded using a simplte trick using the sub-typing relation
- **Type-level application** - a la subtyping approaches to realizability
- **Singleton types** - using type-level application, we can encode PERs that relate, up to beta-eta, a single lambda expression to itself
- **Dependent types**: we can encode dependent types using well-known singleton type tricks

It's a very different way of doing things which is extraordinarily simple and aesthetically pleasing.

## Core Features

### Relational Types

RelTT extends lambda calculus with relational types that capture relationships between terms:

- **Arrow types**: `A → B` for functional relations
- **Composition**: `R ∘ S` for sequential composition of relations
- **Converse**: `R˘` for inverse relations
- **Promotion**: `f̂` for treating functions as relations
- **Universal quantification**: `∀X.R` over relation variables

### Proof System

The proof checker validates all RelTT proof constructors:

- **Terms as relations**: `ι⟨t, f⟩` proves `t [f̂] (f t)`
- **Composition introduction**: `(p, q)` for sequential composition
- **Pi elimination**: `π p - x.u.v.q` for decomposing compositions
- **Rho elimination**: `ρ{x.t₁,t₂} p - q` for substitution under promoted types
- **Converse operations**: `∪ᵢ p` and `∪ₑ p` for relation reversal
- **Conversion**: `t₁ ⇃ p ⇂ t₂` for β-η equivalent endpoints

### Interactive Development

The REPL provides commands for interactive proof development:

- `:load <file>` - Load and check RelTT files
- `:info <name>` - Show information about definitions
- `:expand <macro>` - Expand macro definitions
- `:check <proof>` - Verify proof correctness
- `:type <term>` - Display term information

## Usage

### Building

The project uses Stack for dependency management:

```bash
stack build                 # Build the project
stack test                  # Run test suite
stack run                   # Start interactive REPL
```

### Command Line Interface

```bash
stack run -- --repl                 # Interactive REPL (default)
stack run -- --check <file>         # Type check and verify file
stack run -- --verbose <file>       # Type check with verbose output
stack run -- --parse-only <file>    # Parse-only mode
```

### Example Usage

```bash
# Check all proofs in the demonstration file
stack run -- --check examples/demo.rtt

# Start interactive session
stack run -- --repl

# In REPL:
RelTT> :load examples/demo.rtt
RelTT> :info pi_left_id
RelTT> :check ι⟨x, f⟩
```

## Examples

The `examples/` directory contains demonstration files:

- **`demo.rtt`**: Comprehensive demonstration of all RelTT proof constructors, showing every typing rule from the paper in practical use
- **`comprehensive_bool.rtt`**: Boolean library implementation using Church encoding

## Language Syntax

RelTT supports both ASCII and Unicode syntax:

### Terms
- Variables: `x`, `y`, `z`
- Lambda abstraction: `λx.t` or `\x.t`
- Application: `f x`

### Relations  
- Arrow types: `A → B` or `A -> B`
- Composition: `R ∘ S` 
- Converse: `R˘`
- Universal quantification: `∀X.R` or `forall X.R`

### Proofs
- Iota: `ι⟨t, f⟩` or `iota⟨t, f⟩`
- Composition: `(p, q)`
- Pi elimination: `π p - x.u.v.q`
- Rho elimination: `ρ{x.t₁,t₂} p - q`
- Converse intro/elim: `∪ᵢ p`, `∪ₑ p` or `convIntro p`, `convElim p`
- Conversion: `t₁ ⇃ p ⇂ t₂` or `t₁ convl p convr t₂`

### Declarations
- Macros: `Name (args) := definition ;`
- Theorems: `⊢ name (args) : judgment := proof ;`

## Architecture

The implementation is structured into several key modules:

- **`Lib.hs`**: Core data types for terms, relations, and proofs
- **`Parser.hs`**: Megaparsec-based parser with operator precedence
- **`ProofChecker.hs`**: Type checking and proof verification engine
- **`Context.hs`**: Context management and variable scoping
- **`Errors.hs`**: Comprehensive error reporting with source locations
- **`REPL.hs`**: Interactive proof development environment

## Implementation Details

### Error Reporting

The system provides detailed error messages with:
- Source location information with context
- Clear descriptions of type mismatches
- Specific guidance for common proof errors
- Multi-error reporting for batch checking

## References

- [Relational Type Theory](https://arxiv.org/pdf/2101.09655) - The foundational paper describing the theory
- See `examples/demo.rtt` for practical demonstrations of all proof rules

