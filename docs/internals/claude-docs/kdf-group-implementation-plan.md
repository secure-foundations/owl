# Implementation Plan: `kdf_group` (Breaking Change)

## Context

The `kdf_group` declaration replaces the old `nametype Cx = kdf/dualkdf`,
top-level `odh`, and numeric-selector `kdf<salt_case; odh L[i]; nks; j>` call
syntax with a single unified block. This is a **breaking change**: old AST
constructors are updated or removed; the new ones take their place. Design spec:
`docs/internals/claude-docs/kdf-groups.md`. New-syntax case studies:
`tests/wip/kdf_group/wg/` and `tests/wip/kdf_group/hpke/`.

No test suite migration. Parser-only testing via a new `--only-parse` flag and
dedicated parse test files in `tests/parse/kdf_group/`.

---

## Architectural decisions

1. **Native, not desugared.** `kdf_group` is a first-class construct with its own
   elaboration and type-checking logic.

2. **Breaking change.** `KDFPos`, `KDFBody`, `KDFSelector` are removed. `NT_KDF`
   is kept but its payload is changed (see below). `DeclODH` is removed. `CKDF`
   fields are updated. `ModBody._odh` is removed.

3. **`NT_KDF` reused as bare kdfkey label.** Rather than adding `NT_KdfBare`, the
   existing `NT_KDF` constructor is kept but its payload `KDFPos KDFBody` is
   removed. `NT_KDF` becomes a bare marker with no arguments.

4. **Single `KDFGroupRule` with `isODH` flag.** Rather than `KGRKdf | KGROdh`,
   a single record type with `_kgrIsODH :: Bool`.

5. **Reuse ODH SMT machinery.** `symInODHProp`, `pInODH`, `PInODH` are reused
   unchanged. Result-type refinement (`TRefined`) and `buildKDFName` reuse
   existing code. The old `matchKDF` / `matchODH` case-search logic is removed.

6. **Ghost KDF calls stay label-free.** `AEKDF` (`gkdf<nks; j>(a, b, c)`) unchanged.

---

## What is removed / changed

| Old | New |
|-----|-----|
| `NT_KDF KDFPos KDFBody` | `NT_KDF` (bare, no payload) |
| `KDFPos`, `KDFBody` | removed |
| `DeclODH` | removed; replaced by rules inside `DeclKDFGroup` |
| `CKDF [KDFSelector] [Either ...]` | `CKDF [KDFGroupRuleRef] [NameKind] Int` |
| `KDFSelector = (Int, [Idx])` | removed; replaced by `KDFGroupRuleRef` |
| `ModBody._odh` | removed; replaced by `ModBody._kdfGroups` |
| `checkDecl DeclODH` | `checkDecl DeclKDFGroup` |
| `matchKDF`, `matchODH` | `tryHint` + `checkSaltMatch`, `checkIKMMatch`, `checkInfoMatch`, `checkWhere` |
| `findValidSaltCalls`, `findValidIKMCalls` | inlined into `tryHint` |
| `getODHNameInfo` | `lookupKDFGroupRule` |
| `nametype = kdf/dualkdf` parser | `kdf_group` parser |
| `odh` decl parser | part of `kdf_group` parser |
| Old `kdf<digit...>` call parser | new `kdf<Group.Label; nks; j>` parser |

---

## Step 1: Parser testing (`--only-parse` flag)

### 1a. Add `--only-parse` to `src/CmdArgs.hs` and `src/Main.hs`

When `--only-parse` is set: run the parser only; print the parsed module as
pretty-printed Owl (or a success/failure message); exit before type checking.

### 1b. Test files in `tests/parse/kdf_group/`

Each file is checked with `cabal run owl -- --only-parse tests/parse/kdf_group/<file>.owl`.

| File | Tests |
|------|-------|
| `basic_dh_name.owl` | `name N : DH @ loc` inside kdf_group |
| `basic_kdfkey_name.owl` | `name psk : kdfkey` inside kdf_group |
| `basic_nametype.owl` | `nametype C : kdfkey` inside kdf_group |
| `kdf_rule_simple.owl` | `kdf L : C1, psk, 0x -> strict C2` |
| `odh_rule_simple.owl` | `odh L<i> : C1, dh_combine(A, B), 0x -> strict C2` |
| `where_clause.owl` | `odh L<n_eph@n,m> where n_eph !=idx n : ...` |
| `info_wildcard.owl` | `odh L<i> : 0x, dh_combine(A,B), _ -> strict T` |
| `multi_output.owl` | `kdf L : C, k, info -> strict T1 \|\| strict T2` |
| `call_site_single.owl` | `kdf<G.L<i>; kdfkey; 0>(s, k, 0x)` |
| `call_site_multi.owl` | `kdf<G.L1<i>, G.L2<i>; kdfkey; 0>(s, k, 0x)` |
| `ikm_concat.owl` | `odh L : 0x, dh_combine(A,B) ++ dh_combine(C,D), 0x -> ...` |
| `ikm_func_wrap.owl` | `odh L<i> : 0x, lbl_ikm(f(), g(), dh_combine(A,B)), 0x -> ...` |
| `full_wg_group.owl` | Stripped-down WG_KDF block (no defs, just the kdf_group) |


---

## Step 2: New AST types (`src/AST.hs`)

### 2a. `NT_KDF` — bare kdfkey label (updated)

```haskell
-- Before: NT_KDF KDFPos KDFBody
-- After:
NT_KDF     -- bare marker; no payload
```

Remove `KDFPos` and `KDFBody` type aliases entirely. Remove `KDF_SaltPos` /
`KDF_IKMPos` constructors.

`NT_KDF` is now used for:
- Intermediate kdfkey nametype labels: `nametype C2<@n,m> : kdfkey` inside a group
- Plain kdfkey names: `name psk : kdfkey` inside a group

### 2b. Supporting expression types for group rules

```haskell
data IKMAtom
    = IKMPublicExpr AExpr                  -- hex const, dhpk(N), public func(...)
    | IKMKdfKeyName NameExp                -- named kdfkey name from this group
    | IKMDhCombine NameExp NameExp         -- dh_combine(A, B)

data SaltExpr
    = SaltNameType Path ([Idx], [Idx])     -- nametype label from this group
    | SaltPublicExpr AExpr                 -- hex const or public func

data InfoExpr
    = InfoPublic AExpr                     -- concrete public value
    | InfoWildcard                         -- _

newtype KDFGroupWhere = KDFGroupWhere [(IdxVar, IdxVar, Bool)]
-- (i, j, True) = i !=idx j;  (i, j, False) = i =idx j

data KDFOutputSpec = KDFOutputSpec [(KDFStrictness, NameType)]
-- ||-separated output row; index j selects the output
```

### 2c. `KDFGroupRuleBody` and `KDFGroupRule`

```haskell
data KDFGroupRuleBody = KDFGroupRuleBody {
    _kgrbWhere  :: KDFGroupWhere,
    _kgrbSalt   :: SaltExpr,
    _kgrbIkm    :: [IKMAtom],    -- non-empty; odh rule has >=1 IKMDhCombine
    _kgrbInfo   :: InfoExpr,
    _kgrbOutput :: KDFOutputSpec,
    _kgrbSelf   :: DataVar       -- bound to the salt value in output type exprs
}

data KDFGroupRule = KDFGroupRule {
    _kgrIsODH :: Bool,           -- True = odh, False = kdf
    _kgrLabel :: String,
    _kgrIdxs  :: Bind ([IdxVar], [IdxVar]) KDFGroupRuleBody
}
```

### 2d. `KDFGroupEntry` — name/nametype declarations inside a group

```haskell
data KDFGroupEntry
    = KGEDHName   String (Bind ([IdxVar], [IdxVar]) Locality)
    | KGEKdfKey   String (Bind ([IdxVar], [IdxVar]) ())
    | KGENameType String (Bind ([IdxVar], [DataVar]) ())
```

### 2e. `DeclKDFGroup`

```haskell
-- Added to DeclX:
| DeclKDFGroup String [KDFGroupEntry] [KDFGroupRule]
--             name   entries          rules
```

### 2f. `KDFGroupRuleRef` — rule reference at call sites

```haskell
data KDFGroupRuleRef = KDFGroupRuleRef {
    _kgrrGroup :: Path,
    _kgrrLabel :: String,
    _kgrrIdxs  :: ([Idx], [Idx])
}
```

### 2g. Updated `CKDF`

```haskell
-- Before: CKDF [KDFSelector] [Either KDFSelector (...)] [NameKind] Int
-- After:
CKDF [KDFGroupRuleRef] [NameKind] Int
```

---

## Step 3: Parser changes (`src/Parse.hs`)

### 3a. Remove

- `parseKDFSelector`
- `nametype = kdf { ... }` / `dualkdf { ... }` cases in `parseNameType`
- `odh` declaration parser in `parseDecl`
- Old `kdf<digit,... ; odh ...; nks; j>` parser form
- `KDFPos` / `KDFBody` / `kdfCase` parsers

### 3b. `NT_KDF` in `parseNameType`

```haskell
reserved "kdfkey" >> return (mkSpanned NT_KDF)
```

### 3c. Add `kdf_group` parser

```
kdf_group <Name> {
  ( name N<idxs> : DH @ loc
  | name k<idxs> : kdfkey
  | nametype Cx<idxs> : kdfkey
  | (kdf | odh) L<idxs> [where <cstrs>] : salt , ikm , info -> output )*
}
```

New sub-parsers:
- `parseKDFGroupEntry :: Parser KDFGroupEntry`
- `parseKDFGroupRule :: Parser KDFGroupRule` — parses `(kdf|odh)` keyword (sets
  `_kgrIsODH`), label, index binding, optional `where`, then body
- `parseSaltExpr :: Parser SaltExpr`
- `parseIKMAtomList :: Parser [IKMAtom]` — parses `++`-concatenation; recognises
  `dh_combine(A, B)`, `dhpk(...)`, hex constants, and path applications. Func
  application expansion (e.g., `lbl_ikm(s, l, x)` → `pub ++ pub ++ pub ++ x`) is
  deferred to type checking; the parser stores the func call as `IKMPublicExpr`
  wrapping the application, and elaboration expands it.
- `parseInfoExpr :: Parser InfoExpr` — `symbol "_" >> return InfoWildcard` or public expr
- `parseKDFGroupWhere :: Parser KDFGroupWhere`
- `parseKDFOutputSpec :: Parser KDFOutputSpec` — `[strict|public]? nt [|| ...]`

### 3d. Updated `CKDF` call site parser

```
kdf < Group.Label<idxs> [, Group.Label<idxs>]* ; nks ; j > (salt, ikm, info)
```

Detection: if the token after `<` is a path identifier (not a digit), parse as new
form using `parseKDFGroupRuleRef`.

### 3e. `gkdf` ghost calls — unchanged

---

## Step 4: Pretty-printing changes (`src/Pretty.hs`)

**`src/Pretty.hs`:** Add pretty-printers for all new types so `--debug` output
is human-readable. Output format should match the syntax in `kdf-groups.md`.

---

## Step 7: `ModBody` / `TypingBase.hs`

### 7a. Remove `_odh`, add `_kdfGroups`

```haskell
-- In ModBody, remove:
_odh :: Map String (Bind ([IdxVar], [IdxVar]) (NameExp, NameExp, KDFBody))

-- Add:
_kdfGroups :: Map String KDFGroupDef

data KDFGroupDef = KDFGroupDef {
    _kgdRules    :: Map String (Bind ([IdxVar], [IdxVar]) KDFGroupRuleBody),
    _kgdOdhPairs :: [(String, NameExp, NameExp)]  -- (label, ne1, ne2)
}
```

### 7b. Replace `getODHNameInfo` with `lookupKDFGroupRule`

```haskell
lookupKDFGroupRule :: Path -> String -> ([Idx], [Idx]) -> TcM (Maybe KDFGroupRuleBody)
```

---

## Step 8: Elaboration (`src/Typing.hs`)

Replace `checkDecl DeclODH` with `checkDecl DeclKDFGroup groupName entries rules`:

### 8a. Entries

- `KGEDHName n b` → register `GroupName.n` in `_nameDefs` with `NT_DH`
- `KGEKdfKey n b` → register `GroupName.n` in `_nameDefs` with `NT_KDF`
- `KGENameType n b` → register `GroupName.n` in `_nameTypeDefs` with `NT_KDF`

### 8b. Rules

For each `KDFGroupRule`:

**Well-formedness:**
- Salt `SaltNameType p idxs`: `p` resolves to `NT_KDF` nametype; arity matches
- Salt `SaltPublicExpr e`: label-check `e` flows to `advLbl`
- IKM atoms: `IKMDhCombine ne1 ne2` → both must be `KGEDHName` entries;
  `IKMKdfKeyName ne` → must be `KGEKdfKey` or `KGENameType` entry
- `_kgrIsODH = True` → must have >=1 `IKMDhCombine` atom
- Info: `InfoPublic e` → label-check public; `InfoWildcard` → ok
- Output types: call `checkNameType` on each nt in `KDFOutputSpec`
- `where` clause: all IdxVars appear in the rule's index binding

**ODH disjointness (for odh rules):**
Collect `(ne1, ne2)` from odh rules; check no two share a DH pair; reuse
`ensureODHDisjoint` logic.

**Store:**
Add to `curMod._kdfGroups[groupName]` → rule body keyed by label; for odh rules,
push to `_kgdOdhPairs`.

### 8c. `checkNameType NT_KDF`

```haskell
NT_KDF -> return ()   -- bare marker; no cases to check
```

Remove the old `NT_KDF pos body` case with disjointness query.

---

## Step 8 (continued): Rewrite `CKDF` type checking (`src/Typing.hs`)

```haskell
CKDF hints nks j -> do
    assert "KDF takes 3 args" $ length args == 3
    let [(saltE,saltT),(ikmE,ikmT),(infoE,infoT)] = args
    results <- catMaybes <$> mapM (\h -> tryHint h saltE saltT ikmE ikmT infoE infoT nks j) hints
    when (null results) $ typeError "No kdf_group hint matches"
    unifyHintResults results nks j
```

### 8a. `tryHint`

1. `lookupKDFGroupRule` by group + label + idxs
2. Check `_kgrbWhere` via `checkWhere` (SMT index inequality queries)
3. Check `_kgrbSalt` via `checkSaltMatch`
4. Check `_kgrbIkm` via `checkIKMMatch` (for `IKMDhCombine`: emit `PInODH` via `symInODHProp`)
5. Check `_kgrbInfo` via `checkInfoMatch`
6. On full match: substitute `_kgrbSelf` → `saltE` in output type; call existing
   `buildKDFName` + `TRefined` construction

### 8b. `checkSaltMatch`

- `SaltPublicExpr e`: `tyFlowsTo saltT advLbl`
- `SaltNameType p idxs`: use `extractNameFromType saltT` → check extracted path
  and indices alpha-equal the instantiated rule path/indices

### 8c. `checkIKMMatch`

Match `ikmE` against the list of `IKMAtom`s after func expansion:
- `IKMPublicExpr e`: corresponding sub-expression is public
- `IKMKdfKeyName ne`: sub-expression has type `TName ne`
- `IKMDhCombine ne1 ne2`: sub-expression equals `dh_combine(dhpk(get(ne1)), get(ne2))`;
  **emit ODH security** via `symInODHProp` (reusing existing machinery directly)

Func expansion: during elaboration, call `_funcDefs` lookup to inline one level of
known public func applications before matching against the atom list.

### 8d. `checkInfoMatch`

- `InfoWildcard`: `return True`
- `InfoPublic e`: `checkEntails (PEq infoE e)` via SMT

### 8e. `checkWhere`

For each `(i, j, neq)`:
- `checkEntails $ if neq then PNot (PEq (aeIdx i) (aeIdx j)) else PEq (aeIdx i) (aeIdx j)`

### 8f. `unifyHintResults`

If all results agree → return common type. If they differ → return join via
existing `joinTy` / weakest-strictness logic.

### 8g. Remove

`matchKDF`, `matchODH`, `findValidSaltCalls`, `findValidIKMCalls`.

---

## Step 9: Label-Checking

**`src/LabelChecking.hs`:** Add `NT_KDF -> return []` case (bare label, no flow axioms).
Remove old `NT_KDF pos body` case.

---

## Steps 10: SMT

**`src/SMT.hs` / `src/SMTBase.hs`:** Add `NT_KDF` interpretation as a bare kdfkey
SMT sort (same sort as before; just remove the conditional-body machinery). Keep
`symInODHProp`, `pInODH`, `PInODH`, `getKDFArgs` unchanged.

---

## Implementation order

1. `src/CmdArgs.hs` + `src/Main.hs`: add `--only-parse` flag
2. `src/AST.hs`: update/remove old types; add new types
3. `src/Parse.hs`: new parsers; remove old parsers
4. `src/Pretty.hs`: add pretty-printers for new types (needed for `--only-parse` output)
5. Create `tests/parse/kdf_group/` and the parse test files
6. Verify parse tests pass with `cabal run owl -- --only-parse tests/parse/kdf_group/*.owl`
7. `src/TypingBase.hs`: update `ModBody`, add `lookupKDFGroupRule`
8. `src/Typing.hs`: add `DeclKDFGroup` elaboration; rewrite `CKDF` case
9. `src/LabelChecking.hs`: update `NT_KDF` case
10. `src/SMT.hs` / `src/SMTBase.hs`: update `NT_KDF` interpretation
11. Verify end-to-end build: `cabal build owl`

---

## Agent orchestration

The implementation is executed as a sequence of sub-agent calls. The orchestrating
agent (Sonnet) manages the sequence; specialized agents perform each step.

### Model selection rationale

| Steps | Model | Reason |
|-------|-------|--------|
| 1 — CmdArgs + Main | `sonnet` | Minimal change; no complex reasoning |
| 2 — AST.hs | `sonnet` | Large but mechanical: add/remove data constructors |
| 3+4 — Parse.hs + Pretty.hs | `sonnet` | Parser combinators + pretty-printers; mechanical |
| 5+6 — Test files + verification | `sonnet` | File creation + CLI invocation |
| 7+8 — TypingBase + Typing | `opus` | Most complex: monadic type-checker rewrite, subtle semantic choices |
| 9+10 — LabelChecking + SMT | `sonnet` | Narrow changes; existing machinery mostly intact |
| 11 — End-to-end verification | `sonnet` | Build + fix compile errors |

### Worktree isolation

**Base branch: `kdf-groups-expts`** (the current working branch). All work
stays local — do **not** push to the remote at any point.

Step 1 runs directly on the `kdf-groups-expts` branch (small, non-breaking
change).

Steps 2–11 run in a **git worktree** (`isolation: "worktree"`) branched off
`kdf-groups-expts`. The AST change (step 2) immediately breaks the build across
many files; isolation prevents destabilizing the base branch during the
multi-step process.

Because each agent starts from a fresh worktree, steps must be **sequential**
and each agent commits its changes before the next begins. The exception:
steps 3 and 4 (Parse + Pretty) can be run in parallel within the same worktree
branch if launched as background agents that each commit on completion. Similarly,
steps 9 and 10 can run in parallel.

### Parallelism opportunities

```
Step 1 (main tree)
  └── Step 2 (worktree: AST)
        ├── Step 3 (Parse)  ─┐ parallel, same worktree branch
        └── Step 4 (Pretty) ─┘
              └── Steps 5+6 (test files + parse verification)
                    └── Step 7 (TypingBase)
                          └── Step 8 (Typing)   ← opus
                                ├── Step 9 (LabelChecking) ─┐ parallel
                                └── Step 10 (SMT)          ─┘
                                      └── Step 11 (end-to-end compilation)
```

### Commit discipline and resumability

Each agent commits **locally only** (no `git push`) with a labelled message before returning, e.g.:
```
kdf_group step 1: add --only-parse flag to CmdArgs/Main
kdf_group step 2: AST — add new types, remove KDFPos/KDFBody/KDFSelector
kdf_group step 3: Parse — new kdf_group parser, remove old parsers
...
```

To resume after a usage-limit interruption: in a new conversation, point Claude
at this file, run `git log --oneline` on the worktree branch, and ask Claude to
continue from the first step that has no commit.

**Step 8 (Typing.hs) sub-commits** — this is the longest step; the agent commits
incrementally after each sub-task:

```
kdf_group step 8a: Typing — add tryHint and sub-checkers (checkSaltMatch etc.)
kdf_group step 8b: Typing — rewrite CKDF case to use tryHint + unifyHintResults
kdf_group step 8c: Typing — add DeclKDFGroup elaboration
kdf_group step 8d: Typing — remove matchKDF, matchODH, findValidSaltCalls/IKMCalls
```

---

## Progress

Track completed steps here. Each agent checks off a line before committing.

- [x] Step 1: `--only-parse` flag (CmdArgs + Main)
- [x] Step 2: AST.hs
- [x] Step 3: Parse.hs
- [x] Step 4: Pretty.hs
- [x] Step 5+6: Parse test files + verification
- [ ] Step 7: TypingBase.hs
- [ ] Step 8a: Typing — tryHint + sub-checkers
- [ ] Step 8b: Typing — CKDF case rewrite
- [ ] Step 8c: Typing — DeclKDFGroup elaboration
- [ ] Step 8d: Typing — remove old functions
- [ ] Step 9: LabelChecking.hs
- [ ] Step 10: SMT.hs / SMTBase.hs
- [ ] Step 11: End-to-end compilation

---

## Files to modify

| File | Change |
|------|--------|
| `src/AST.hs` | Update `NT_KDF` (bare); add new types; remove `KDFPos`, `KDFBody`, `KDFSelector`; update `CKDF`; add `DeclKDFGroup`, `KDFGroupRule`, `KDFGroupEntry`, `KDFGroupRuleRef` |
| `src/Parse.hs` | New `kdf_group` parser; updated `CKDF` parser; add `kdfkey` as bare nametype; remove old parsers |
| `src/CmdArgs.hs` | Add `--only-parse` flag |
| `src/Main.hs` | Wire `--only-parse` to skip type checking |
| `src/TypingBase.hs` | Remove `_odh`; add `_kdfGroups`, `KDFGroupDef`, `lookupKDFGroupRule` |
| `src/Typing.hs` | Add `DeclKDFGroup` case; rewrite `CKDF` case; remove `matchKDF/ODH` etc. |
| `src/LabelChecking.hs` | Update `NT_KDF` case |
| `src/SMT.hs` / `src/SMTBase.hs` | Update `NT_KDF` SMT interpretation |
| `src/Pretty.hs` | Add pretty-printers for new types |
| `tests/parse/kdf_group/` | New directory with ~12 parse test files |

## Deferred

- Extraction (`src/Extraction/`) — new `CKDF` maps to same runtime `hkdf` call; defer
- I5 (type provenance soundness) and I12 (positional annotation)
- `_` wildcard disjointness (open design question in `hpke/defs.owl` TODOs)
- Test suite migration (not in scope for this implementation)
