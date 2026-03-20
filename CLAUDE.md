# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Branch purpose: `kdf-groups-expts`

This branch (`kdf-groups-expts`) is dedicated to designing and implementing the new `kdf_group` declaration syntax for Owl's key derivation framework. The goal is to replace the old `kdf`/`dualkdf`/`odh` mechanism with a single unified block that collects all KDF chain steps, DH key names, and ODH assumptions in one place.

**Documentation:**
- Design spec: `docs/internals/claude-docs/kdf-groups.md`
- Known issues/limitations: `docs/internals/claude-docs/kdf-group-issues.md`

**Case study conversions (in `tests/wip/kdf_group/`):**
- `wg/` — WireGuard (8-step KDF chain, `kdf_group WG_KDF`): conversion largely complete; issues I1–I12 documented
- `hpke/` — HPKE (KEM + key-schedule, `kdf_group HPKE_KDF`): conversion in progress; additional issues I13–I16 documented (concatenated DH secrets, function-wrapped DH/kdfkey in ikm, unindexed ghost labels)

**Open issues summary (see `kdf-group-issues.md` for details):**

| # | Summary | Status |
|---|---------|--------|
| I1 | Public computed values in salt/info | Open (syntax gap) |
| I2 | DH public keys in ikm | Open (syntax gap) |
| I3 | Index-inequality between overlapping rules | Open (soundness risk) |
| I4 | No catch-all/negation pattern | Open |
| I5 | Type provenance soundness | Open |
| I6–I8, I16 | Ghost function / label indexing issues | Resolved |
| I9 | Multi-label kdf call semantics | Open (tentative syntax) |
| I10 | PSK/no-PSK branch label selection | Open (design reminder) |
| I11 | Session-index specificity of C1 | Open |
| I12 | `dualkdf` removal positional annotation | Open |
| I13 | Concatenated DH secrets in ikm (HPKE) | Open (syntax gap) |
| I14 | Function-wrapped DH in ikm (HPKE) | Open (syntax gap) |
| I15 | Function-wrapped kdfkey in ikm (HPKE) | Open (syntax gap) |

---

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
The build may take 5-10 minutes to complete.

**Run Owl on a protocol:**
```bash
cabal run owl -- --no-color-output path/to/protocol.owl
```
Always pass `--no-color-output` so error output is free of ANSI escape codes and readable in logs.

**Type check with extraction to Verus:**
```bash
cabal run owl -- --no-color-output --extract path/to/protocol.owl
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
- **`pcase P`** — a ghost proof annotation (no runtime effect) that splits the type checker into two branches: one where predicate `P` holds and one where it does not. Because it is ghost-only, the same runtime expression (e.g., a multi-label `kdf` call listing all applicable labels) can be used in both branches; the type checker narrows which labels apply per branch. Similarly `corr_case N` is equivalent to `pcase sec(N)`: it splits on whether name `N` is secret or corrupt.

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

## Important Implementation Notes

The implementation lives on branch `kdf-groups-impl` at the repository root.

### kdf_group — type system internals

**Path resolution for kdf_group names:**
- `kdf_group` is a **pure container** — it has no namespace effect.  Names
  declared inside (`name X : DH @ loc`, `name k : kdfkey`, `nametype Cx :
  kdfkey`) are registered at top level with their bare names, not qualified.
- `DeclKDFGroup "G" entries rules` registers `"G"` in `defPaths` (for
  call-site `kdf<L<i>; ...>` rule lookup) and adds entry names to `namePaths`
  (and `nameTypePaths` for `KGENameType`) so that rule bodies can resolve bare
  references like `C1`, `X`, `Y` without a group qualifier.
- `KGEDHName` and `KGEKdfKey` localities are resolved during path resolution;
  `KGENameType` has no locality to resolve.

**`SecName(KDF<L<i>; kdfkey; 0>(...))` — how it typechecks:**
- The new `KDF<rule_refs; nks; j>(a,b,c)` parser format stores refs in `KDFName`'s
  new `[KDFGroupRuleRef]` field (8th argument; empty for old format).
- `tryHint` for a `KDFStrict` rule with a secret salt returns
  `TRefined (TName (KDFName ... [hint])) ".res" (pNot (pFlow (nameLbl ne) advLbl))`.
  This embeds the label secrecy directly in the type so `checkSubRefinement` can
  prove `SecName`'s `[ne] !<= adv` constraint without needing ODH axioms in the SMT.
- `subKDFName` compares `[KDFGroupRuleRef]` alpha-equality when both sides are
  non-empty, replacing `subNameType` (ref equality implies type compatibility).
- For a public (adversary-controlled) salt, `tryHint` returns `tData advLbl advLbl`
  even for `KDFStrict` rules — secrecy is only granted when the salt is actually a name.

**`KDFName` AST node (8 arguments):**
```haskell
KDFName AExpr AExpr AExpr [NameKind] Int NameType (Ignore Bool) [KDFGroupRuleRef]
--      salt  ikm   info  nks        j   nt        trusted?      rule refs (new syntax)
```
The `[KDFGroupRuleRef]` field is `[]` for the old `KDF<nks; j; nt>` format and
non-empty for the new `KDF<L<i>; kdfkey; 0>` format.

**SMT / label checking:**
- `prelude.smt2` at the repo root defines the base SMT theory. `KDFName` is declared
  as `(declare-fun KDFName (Bits Bits Bits Int Int) Name)`. `LabelOf(KDFName(...))`
  is an opaque SMT term with no built-in flow axioms — secrecy must be injected via
  type refinements (as above) rather than SMT axioms.
- `inODHProp` in `TypingBase.hs` is currently a stub returning `pFalse` — the old
  ODH checking via `PInODH` in SMT was replaced by `tryHint` in `Typing.hs`.
- Flow axioms for name types are emitted by `nameDefFlows` in `LabelChecking.hs`.
  `NT_KDF` emits no flow axioms (`return sTrue`).

### Reserved words

`dh_combine` must **not** be in `reservedNames` — it appears as a function call in
expression position (e.g., `dh_combine(dhpk(get(X)), get(Y))`). Adding it to
`reservedNames` breaks expression-level parsing. The keywords `kdf_group`, `kdfkey`,
`odh`, `kdf`, `where`, `nametype`, and `public` are correctly reserved.

### Indexed localities

Localities with index parameters must be declared with explicit arity:
```
locality Initiator : 1   -- takes one PId index
locality Responder : 1
```
An unindexed `locality alice` has arity 0. Using `alice<n>` with arity-0 locality
produces a "Wrong arity" error.

### `addNameDef` — registering names

`addNameDef n (is1, is2) (nt, locs) k` registers name `n` with session indices
`is1`, PId indices `is2`, name type `nt`, and localities `locs`. For kdf_group
names, the bare string `"C1"` (not `"G.C1"`) is used as the key in `curMod.nameDefs`.
The `locs` list can have multiple elements (e.g., PSK shared across two localities).
