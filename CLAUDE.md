# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

Owl is a tool for developing cryptographic protocols with formal, machine-checked guarantees of security. It consists of:
- A verifier that enables developers to prove security using information-flow and refinement types
- A secure compiler that translates verified protocols into performant Rust libraries verified using Verus (a deductive Rust program verifier)


## Language and Build System

Owl is written in Haskell and uses Cabal as its build system. The main executable is `owl`.

### Common Commands

**Build:**
```bash
cabal build owl              
```

**Run Owl on a protocol:**
```bash
cabal run owl -- path/to/protocol.owl
```

**Type check with extraction to Verus:**
```bash
cabal run owl -- --extract path/to/protocol.owl
```

**Verify extracted code with Verus:**
```bash
cd extraction/
./run_verus.sh $PWD
```
(Requires `verus` and `verusfmt` in PATH)

**Run test suite:**
```bash
cabal run owl -- --test
```

**Other useful flags:**
- `--debug FILE` - Log debugging messages to file
- `--log-smt` - Log SMT queries
- `--clean-smt-cache` - Clean SMT cache
- `--extract-only-specs` - Extract only specs
- `--debug-extraction` - Debug extraction
- `--bufopt` / `--optimize-buffers` - Optimize buffer usage for extraction
- `--lax` - Lax checking (skip some SMT queries)
- `--local-errors` - Localize type errors to path condition
- `--log-typecheck` - Log typechecker progress
- `--only-check FUNCNAME` - Only check the given function

## Architecture

### Source Code Structure (`src/`)

The Owl compiler is organized into several core modules:

**Core AST and Parsing:**
- `AST.hs` - Abstract syntax tree definitions for the Owl language
- `Parse.hs` - Parser for `.owl` protocol files
- `Pretty.hs` - Pretty-printing infrastructure

**Type System and Verification:**
- `Typing.hs` - Main type checker implementation
- `TypingBase.hs` - Type checking infrastructure and utilities
- `LabelChecking.hs` - Information flow label checking (security properties)
- `SMT.hs` / `SMTBase.hs` - SMT solver interface and query generation (uses Z3)

**Compiler Passes (`src/Pass/`):**
- `ANFPass.hs` - A-Normal Form transformation
- `PathResolution.hs` - Module path resolution
- `ModuleFlattening.hs` - Module system flattening
- `Timestamping.hs` - Timestamp generation for operation ordering (NEW in this branch)

**Code Extraction to Verus (`src/Extraction/`):**
- `ExtractionTop.hs` - Top-level extraction orchestration
- `ExtractionBase.hs` - Base extraction infrastructure
- `ConcreteAST.hs` - Concrete AST for extraction target
- `Concretify.hs` - Convert abstract AST to concrete form
- `Verus.hs` - Verus code generation AST
- `GenVerus.hs` - Generate Verus code
- `PrettyVerus.hs` - Pretty-print Verus output
- `SpecExtraction.hs` - Extract specifications
- `LowerImmut.hs` - Lower immutable data structures
- `LowerBufOpt.hs` - Buffer optimization lowering

**Utilities:**
- `Main.hs` - Entry point, command-line argument processing
- `CmdArgs.hs` - Command-line argument definitions
- `Test.hs` - Test harness for running protocol test suites

### Test Organization

Tests are in `tests/` with ~133 `.owl` protocol files:
- `tests/success/` - Protocols expected to type check successfully
- `tests/failure/` - Protocols expected to fail type checking
- `tests/should_succeed/` - Additional success cases that may not work yet
- `tests/should_fail/` - Additional failure cases that may not work yet
- `tests/wip/` - Work in progress large-scale case studies

Example protocols include: Kerberos, Diffie-Hellman key exchange, Denning-Sacco, Needham-Schroeder, various key derivation patterns.

### Owl Language

Owl protocols consist of:
- **Localities** - Protocol parties (e.g., `locality alice`)
- **Names** - Cryptographic secrets with types (e.g., `name k : enckey t @ alice`)
- **Name types** - `nonce`, `enckey t`, `sigkey t`, `mackey t`, `DH`, etc.
- **Definitions** - Protocol procedures (e.g., `def alice_main () @ alice : ...`)
- **Cryptographic operations** - `enc`, `dec`, `sign`, `verify`, `mac`, `dh`, `kdf`, etc.
- **Information flow types** - Labels like `Data<adv>` for attacker-controlled data

Key features:
- Strong typing for cryptographic operations
- Information flow security via labels
- Computational security model (probabilistic adversaries)
- Compositional verification (parties checked independently)

## Dependencies

**Required:**
- `ghc` and `cabal` (install via [ghcup](https://www.haskell.org/ghcup/))
- Z3 SMT solver version 4.12.5 (binary releases [here](https://github.com/Z3Prover/z3/releases))

**Optional (for extraction):**
- [Verus](https://github.com/verus-lang/verus/) - Rust verification tool
- [verusfmt](https://github.com/verus-lang/verusfmt/) - Verus code formatter

## Extraction Workflow

1. Type check and extract: `cabal run owl -- --extract protocol.owl`
2. Generated code goes to: `extraction/src/lib.rs`
3. Verify with Verus: `cd extraction && ./run_verus.sh $PWD`
4. The extracted code is verified Rust implementing the protocol

The `extraction/` directory contains a Rust Cargo project with Verus-annotated code.

## Working with the Type Checker

The type checker (`Typing.hs`) is the heart of Owl's security verification:
- Uses Z3 to discharge proof obligations
- Tracks information flow labels to ensure security properties
- Implements refinement types and dependent types
- The `TypingBase.hs` module contains core infrastructure (environments, contexts, utilities)

When debugging type errors:
- Use `--log-typecheck` to see progress
- Use `--local-errors` to narrow down error locations
- Use `--only-check funcname` to focus on specific functions
- Check SMT queries with `--log-smt`

## Code Conventions

- Module names match file names
- The AST uses `unbound-generics` for name binding
- Lenses from `Control.Lens` are used extensively for record access
- Pretty-printing uses the `prettyprinter` library
- IO and state management uses `IORef` and monad transformers
