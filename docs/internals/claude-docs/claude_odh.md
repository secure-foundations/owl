ODH (Oracle Diffie-Hellman) in Owl
===================================

This document describes how Owl handles `odh` declarations and `kdf` calls that
use Diffie-Hellman shared secrets as input keying material (IKM), relying on the
PRF-ODH assumption. It is structured to complement the general KDF documentation
in `kdf.md`.


## 1. Background: PRF-ODH

The PRF-ODH (Pseudo-Random Function -- Oracle Diffie-Hellman) assumption lets us
treat the output of `kdf(salt, dh_combine(g^X, Y), info)` as a fresh
cryptographic name, provided:

1. The DH pair `(X, Y)` has been declared in an `odh` block that covers this KDF
   pattern.
2. Both `X` and `Y` are secret (neither flows to `adv`).
3. The case predicate in the `odh` declaration is satisfied.

When any of these conditions fails, the KDF output is treated as public data
(`Data<adv>`), possibly after verifying that it is safe to do so (via the
`kdfOOB` / `pubIKM` checks).


## 2. Concrete syntax

### 2.1 ODH declarations

```
odh <handle> [<sid_indices>, <pid_indices>] :
    <name1>, <name2> -> {<salt_var> <info_var> [<self_var>].
        <pred1> -> <strictness1> <nametype1_0> || <nametype1_1> || ...,
        <pred2> -> <strictness2> <nametype2_0> || <nametype2_1> || ...,
        ...
    }
```

Here:
- `<handle>` is a string name for this ODH declaration (e.g., `L`).
- `<name1>`, `<name2>` are `NameExp`s, each of type `DH`, and must be local to
  the module.
- The body has the same structure as a KDF body: it binds three variables
  (`salt`, `info`, `self`), and has a list of cases, each with a predicate and a
  row of `(strictness, nametype)` pairs.
- `<self_var>` is optional and defaults to `%self`.

**Example** (from `tests/success/odh.owl`):
```
name X : DH @ alice
name Y : DH @ alice

odh L :
    X, Y -> {salt info.
        salt == 0x -> strict enckey Name(n)
    }
```

**Example** (from `tests/success/dhke.owl`):
```
odh L : X, Y ->
    {salt info.
        True -> enckey Name(d)
    }
```

### 2.2 KDF call sites with ODH hints

```
kdf<salt_selectors ; odh <handle>[<case_selector>] ; output_name_kinds ; output_index>(salt, ikm, info)
```

The second annotation position (IKM annotations, called `oann2` in the code)
accepts either:
- `Left (i, is_case)` -- a plain KDF selector (for regular `dualkdf`-style IKM
  keys), or
- `Right (handle, (sid_idxs, pid_idxs), (i, is_case))` -- an ODH selector
  referencing an `odh` declaration.

**Example**:
```
kdf<;odh L[0];enckey;0>(0x, dh_combine(dhpk(get(X)), get(Y)) ++ 0x1234, 0x)
```

This says: use ODH declaration `L`, case 0, expecting an `enckey` output at
position 0.


## 3. AST representation

### 3.1 Declarations (`AST.hs:341`)
```haskell
DeclODH String (Bind ([IdxVar], [IdxVar]) (NameExp, NameExp, KDFBody))
```
- `String`: the handle name
- `([IdxVar], [IdxVar])`: session and participant index variables
- `(NameExp, NameExp)`: the two DH key names (`ne1`, `ne2`)
- `KDFBody`: the case body (same type as in `NT_KDF`)

### 3.2 KDFBody (`AST.hs:322-323`)
```haskell
type KDFBody = Bind ((String, DataVar), (String, DataVar), (String, DataVar))
                    [Bind [IdxVar] (Prop, [(KDFStrictness, NameType)])]
```
Binds `(salt_var, info_var, self_var)` over a list of cases. Each case binds
additional index variables and contains `(predicate, [(strictness, nametype)])`.

### 3.3 CryptOp (`AST.hs:441-443`)
```haskell
CKDF [KDFSelector]                                          -- oann1 (salt selectors)
     [Either KDFSelector (String, ([Idx],[Idx]), KDFSelector)] -- oann2 (IKM / ODH selectors)
     [NameKind]                                              -- output name kind row
     Int                                                     -- output index j
```
The `Right` variant in `oann2` carries `(odh_handle, (sid, pid), selector)`.

### 3.4 PInODH (`AST.hs:196`)
```haskell
PInODH AExpr AExpr AExpr   -- PInODH salt ikm info
```
A proposition used in the SMT encoding to express "the triple `(salt, ikm, info)` falls within some ODH declaration in scope."

### 3.5 Module environment (`TypingBase.hs:143`)
```haskell
_odh :: Map String (Bind ([IdxVar], [IdxVar]) (NameExp, NameExp, KDFBody))
```
Each module tracks its ODH declarations by handle name.


## 4. Notation

- `G` -- the typing context.
- `G |- e : T` -- expression `e` has type `T` under `G`.
- `G |- l <= adv` -- label `l` flows to the adversary label.
- `G |- l !<= adv` -- label `l` does NOT flow to the adversary.
- `dh(X, Y)` -- shorthand for `dh_combine(dhpk(get(X)), get(Y))`.
- `gkdf<nks,j>(a,b,c)` -- the ghost KDF expression `AEKDF a b c nks j`.
- `KDFName(a,b,c,nks,j,nt)` -- a KDF-derived name expression.
- For a `KDFBody`, we write its contents as:
  ```
  {salt info self. case_0, case_1, ...}
  ```
  where each `case_i` has the form `p_i -> str_i  nt_i0 || nt_i1 || ...`.
- `|nks[j]|` -- the expected output length for name kind `nks[j]`.
- `lbl(n)` -- the information-flow label of name `n` (i.e., `nameLbl n` in the
  code). `lblbl(n) <= adv` means `n` is compromised; `lbl(n) !<= adv` means `n`
  is secret/honest.


## 5. Well-formedness of ODH declarations

When the type checker encounters `DeclODH s b`, it performs the following checks
(`Typing.hs:1309-1326`):

```
G[ne1] has type DH
G[ne2] has type DH
ne1 is local to the current module
ne2 is local to the current module
all index variables in the declaration appear in ne1 or ne2
the KDFBody is a well-formed KDF name type (checked as NT_KDF KDF_IKMPos)
the DH pair (ne1, ne2) is disjoint from all existing ODH declarations
-----------------------------------------------------------------------
odh s : ne1, ne2 -> {body}   is well-formed
```

### 5.1 Disjointness (`ensureODHDisjoint`)

For every existing ODH declaration `(ne1', ne2')` already in scope, the checker
verifies via SMT that neither:
- `get(ne1) == get(ne1') /\ get(ne2) == get(ne2')`, nor
- `get(ne2) == get(ne1') /\ get(ne1) == get(ne2')`

can hold. This ensures that no DH pair is covered by two different ODH
declarations (which would be unsound).

### 5.2 No concrete defs before names

`ensureNoConcreteDefs` enforces that all ODH (and name) declarations appear
before any `def` declarations. This prevents adding ODH declarations that
retroactively change the meaning of previously-checked code.


## 6. Typing rules for KDF with ODH

### 6.1 Top-level rule: `CKDF` in `checkCryptoOp`

The CKDF handler (`Typing.hs:3006-3057`) has two main branches:

**Fully public case**: If `a`, `b`, and `c` all flow to `adv`:
```
G |- a <= adv     G |- b <= adv     G |- c <= adv
--------------------------------------------------
G |- kdf<ann1,ann2,nks,j>(a,b,c) :
    x:Data<adv>{ |x| = |nks[j]| /\ x = gkdf<nks,j>(a,b,c) }
```

**General case**: Otherwise, require `c <= adv`, then:
1. Compute `kdfCaseSplits` via `findGoodKDFSplits` -- a list of propositions of
   the form `lbl(n) <= adv` for each name `n` appearing in the arguments or ODH
   annotations.
2. Case-split on all combinations of these propositions (via `manyCasePropTy`).
3. Under each case, compute:
   - `saltResult <- findValidSaltCalls ...`
   - `ikmResult  <- findValidIKMCalls ...`
   - `unif <- unifyKDFCallResult [saltResult, ikmResult]`
4. The unified result determines the output type (see Section 6.5).


### 6.2 `findGoodKDFSplits`

Collects all cryptographic names appearing in:
- The salt argument `a` (if it has type `TName n` or `TSS n m`)
- Each component of the IKM argument `b` (after splitting concats), including DH
  secret keys obtained via `getLocalDHComputation`
- The DH key pairs `(ne1, ne2)` from each ODH annotation in `oann2`

Returns `[lbl(n) <= adv | n in all_names]` -- used to generate an exhaustive case
split over which keys are compromised.


### 6.3 `findValidIKMCalls` (the ODH path)

This is the core function for ODH matching (`Typing.hs:2670-2699`).

```
bs <- unconcatIKM(b)              // split IKM into concat components
dhs <- extract DH pairs from ODH annotations
for each component b' in bs:
    for each annotation in oann2:
        if annotation is Right(s, ips, i):
            result <- matchODH(dhs, a, (b,b'), c, (s,ips,i), j, nks)
        if annotation is Left(i, is_case):
            // ... regular dualkdf IKM matching (see kdf.md) ...
    best <- findBestKDFCallResult(results)
unifyKDFCallResult(all_component_results)
```

Key behavior:
- Every concat component of the IKM must be either matched by an annotation or
  shown to be public. This is enforced by `unifyKDFCallResult`.
- The DH shared secret `dh(X, Y)` should appear as one of the concat components.


### 6.4 `matchODH`

The core ODH matching function (`Typing.hs:2711-2736`).

```
(odhName, ips, (i, is_case)) in ann2          // from the odh annotation
G |- getODHNameInfo(odhName, ips, a, c, i, j) = (ne1, ne2, p, str_nts)
nameKinds(str_nts) is compatible with nks
(str, nt) = str_nts[j]
real_ss = dh_combine(dhpk(get(ne1)), get(ne2))
G |- b == real_ss                              // SMT check
G |- p is true                                 // case predicate holds
G |- ne1 !<= adv                              // first DH key is secret
G |- ne2 !<= adv                              // second DH key is secret
-----------------------------------------------------------------------
matchODH returns Right(str, KDFName(a, bFull, c, nks2, j, nt, true))
```

If any of the last four conditions fails, `matchODH` falls through to
`kdfArgPublic`, which checks whether the IKM component can be treated as public.


### 6.5 Result types

After unifying salt and IKM results via `unifyKDFCallResult`:

**Good case** (`Right (strictness, ne)`):
```
G |- kdf<...>(a,b,c) :
    x:Name(ne){
        strictnessOf(ne, strictness)
        /\ |x| = |nks[j]|
        /\ x = gkdf<nks,j>(a,b,c)
    }
```

where:
```
strictnessOf(ne, KDFStrict)   := ne !<= adv
strictnessOf(ne, KDFPub)      := ne <= adv
strictnessOf(ne, KDFUnstrict) := True
```

**Public case** (`Left True`):
```
G |- kdf<...>(a,b,c) :
    x:Data<adv>{ |x| = |nks[j]| /\ x = gkdf<nks,j>(a,b,c) }
```

**Ill-typed case** (`Left False`):
The checker calls `enforcePublicArguments`, which requires all arguments to flow
to `adv` and returns `Data<adv>`.


## 7. The `pubIKM` / `kdfOOB` mechanism

When `matchODH` (or `matchKDF` in IKM position) fails to match a concrete
declaration, the checker must decide whether the IKM component is "public" --
i.e., whether it can safely be treated as `Data<adv>`. This is handled by
`kdfArgPublic` -> `pubIKM` -> `kdfOOB`.

### 7.1 `pubIKM(dhs, a, b, c)` (`Typing.hs:2783-2786`)
```
G |- b <= adv
-------------------
pubIKM returns True
```

```
G |- b !<= adv
G |- kdfOOB(dhs, a, b, c) = True
-------------------
pubIKM returns True
```

### 7.2 `kdfOOB(matchedSecrets, a, b, c)` (`Typing.hs:2792-2809`)

Determines whether a DH shared secret used as IKM is "out of bounds" with
respect to all ODH declarations. Returns `True` if the KDF output should be
treated as public by PRF-ODH reasoning.

```
getLocalDHComputation(b) = Nothing     // b is not a DH computation at all
-------------------------------------------
kdfOOB returns False (not out of bounds -- will cause a type error upstream)
```

```
getLocalDHComputation(b) = Just _
G, SMT |- not(inODH(a, b, c))          // b is not covered by any ODH declaration
-------------------------------------------
kdfOOB returns True (out of bounds -> public by PRF-ODH)
```

```
getLocalDHComputation(b) = Just _
G, SMT |- inODH(a, b, c)               // b IS covered by some ODH declaration
exists (ne1, ne2) in matchedSecrets:
    G |- b == dh(ne1, ne2)
    G |- ne1 <= adv  or  ne2 <= adv     // but one of the keys is compromised
-------------------------------------------
kdfOOB returns True (in ODH, but keys compromised -> public)
```


## 8. The `inODH` predicate in SMT

The `PInODH salt ikm info` proposition is compiled into an SMT predicate
`%inODHProp(salt, ikm, info)` (`SMTBase.hs:270-291`).

Its definition is the disjunction over all ODH declarations `(ne1_k, ne2_k, body_k)`:
```
inODH(salt, ikm, info) :=
    OR over all odh decls k:
        EXISTS is_k, ps_k.
            ikm == dh_combine(dhpk(get(ne1_k)), get(ne2_k))
            /\ inKDFBody(body_k, salt, info, ikm)
```

where `inKDFBody` checks whether the salt/info/self values satisfy at least one
case predicate in the KDF body.

This predicate is used in `kdfOOB` to determine whether a given DH shared secret
falls within the scope of any ODH declaration.


## 9. `getODHNameInfo` helper

This function (`TypingBase.hs:739-761`) is the primary lookup for ODH
declarations. Given an ODH handle name, indices, and the salt/info arguments, it:

1. Looks up the handle in the module's `_odh` map.
2. Instantiates the index variables.
3. Extracts `(ne1, ne2, kdfBody)`.
4. Selects the `i`-th case, substitutes `salt := a`, `info := c`, `self := ikm`.
5. Returns `(ne1, ne2, predicate, [(strictness, nametype)])`.

Note the substitution order: `salt_var := a`, `info_var := c`, `self_var := ikm`
(line 753 of `TypingBase.hs`: `subst x a $ subst y c $ subst z ikm`). The
`self` binding is set to the **full IKM argument** passed to the KDF, not to
`dh(ne1, ne2)`. This means `%self` in ODH case predicates refers to the entire
IKM (which may be a concatenation of multiple DH shared secrets), enabling
predicates like `self == correct_bmaster_arg()` in x3dh.


## 10. `getLocalDHComputation`

This function (`Typing.hs:2813-2840`) tries to decompose an expression into a DH
shared secret `(pk, sk)` where `sk` is a name local to the module.

It handles two patterns:
- **Direct `dh_combine(pk, get(sk))`**: If the second argument is a local DH
  name and the first is a valid group element.
- **Type-based**: If the expression has type `TSS n m`, it checks whether `n` or
  `m` is local.

This is used by `kdfOOB` to determine whether an IKM expression is a DH
computation at all (if not, `kdfOOB` returns `False` immediately -- the value is
not a DH shared secret so the ODH reasoning doesn't apply).


## 11. `unconcatIKM`

Recursively splits the IKM argument along `concat` boundaries
(`Typing.hs:2852-2873`). Only the following forms are accepted as atomic
components:

- `get(n)` -- a name lookup
- `dh_combine(_, _)` -- a DH shared secret
- `dhpk(_)` -- a DH public key
- Hex constants (`0x...`)
- Expressions with type `TSS`, `TDH_PK`, `THexConst`, or `TName`
- Values provably satisfying `is_group_elem(x) == true`

Anything else causes a type error. This restriction prevents smuggling in
untracked concats.


## 12. End-to-end example

Consider `tests/success/dhke.owl`:

```
name X : DH @ alice
name Y : DH @ bob

odh L : X, Y -> {salt info. True -> enckey Name(d) }

...
let ss = dh_combine(bobs_pk, get(X)) in
let k = kdf<;odh L[0];enckey;0>(0x, ss, 0x) in
let c = aenc(k, get(d)) in
```

Type checking proceeds as follows:

1. **Parse**: `kdf<;odh L[0];enckey;0>` produces
   `CKDF [] [Right ("L", ([], []), (0, []))] [NK_Enc] 0`.

2. **CKDF handler**: `info = 0x` flows to `adv`. Not all args public (the DH
   shared secret is secret). Enter the general case.

3. **`findGoodKDFSplits`**: Collects `[X, Y]` from the ODH annotation. Returns
   `[lbl(X) <= adv, lbl(Y) <= adv]`.

4. **Case split**: Under each combination of `X`/`Y` corruption:

   - **Both secret** (`X !<= adv, Y !<= adv`):
     - `findValidSaltCalls`: salt is `0x` (public), returns `Left True`.
     - `findValidIKMCalls`:
       - `unconcatIKM(ss)` = `[ss]` (single DH component).
       - Annotation is `Right ("L", ...)`, so calls `matchODH`.
       - `getODHNameInfo` returns `(X, Y, True, [(KDFStrict?, enckey Name(d))])`.
       - Checks `ss == dh_combine(dhpk(get(X)), get(Y))` via SMT (uses `pcase`
         from user code).
       - Predicate `True` holds.
       - `X !<= adv` and `Y !<= adv` confirmed.
       - Returns `Right (strict, KDFName(0x, ss, 0x, [NK_Enc], 0, enckey Name(d)))`.
     - `unifyKDFCallResult [Left True, Right ...]` = `Right (strict, ...)`.
     - Result type: `Name(KDFName(...))` with `ne !<= adv`.

   - **X compromised** (`X <= adv`):
     - `matchODH` fails the `ne1 !<= adv` check, falls to `kdfArgPublic`.
     - `pubIKM`: `ss` doesn't flow to `adv` directly, so calls `kdfOOB`.
     - `kdfOOB`: DH computation exists; `inODH` holds; `X <= adv` so returns `True`.
     - Result: `Left True` -> `Data<adv>`.

   - **Y compromised** or **both compromised**: Similar, yields `Data<adv>`.

5. **Final type**: A case type over corruption scenarios, either `Name(...)` or
   `Data<adv>`.


## 13. Rules vs. heuristics

The ODH/KDF type-checking logic mixes two different concerns:

1. **Rules** -- steps that encode cryptographic reasoning and determine the
   output type. These are the logical core: they justify *why* a particular type
   is sound.
2. **Heuristics** -- steps that help the checker *find* the right rule to apply.
   They are search/resolution strategies. A different heuristic could produce the
   same result; getting the heuristic wrong means Owl fails to type-check valid
   code, but does not produce an unsound result.

Below we classify every major step in the ODH path.


### 13.1 Rules (soundness-critical)

These are the steps that a pen-and-paper proof would also need. Changing any of
them would change what programs are considered secure.

**R1. ODH well-formedness checks** (`Typing.hs:1309-1326`)
- Both names must have type `DH`.
- Both names must be local to the module.
- The KDF body must be well-formed (as `NT_KDF KDF_IKMPos`).
- Disjointness of DH pairs across ODH declarations (`ensureODHDisjoint`).
- All ODH declarations must precede all `def`s (`ensureNoConcreteDefs`).

*Cryptographic justification*: PRF-ODH requires each DH pair to be used in at
most one ODH assumption. Locality ensures the module controls the secret keys.
Ordering prevents retroactive unsoundness.

**R2. Fully-public shortcut** (`Typing.hs:3012-3023`)
```
a <= adv, b <= adv, c <= adv  =>  result : Data<adv>
```
*Justification*: If all inputs are public, the adversary can compute the KDF
output itself, so the result is public data. No cryptographic assumption needed.

**R3. Info must be public** (`Typing.hs:3026`)
```
c <= adv   (required in the non-fully-public case)
```
*Justification*: The PRF-ODH assumption models `info` as a public value visible
to the adversary. If `info` were secret, the assumption would not apply.

**R4. The core `matchODH` judgment** (`Typing.hs:2724-2733`)

Four conditions, each individually necessary:

| # | Condition | Check | Justification |
|---|-----------|-------|---------------|
| R4a | `b == dh_combine(dhpk(get(ne1)), get(ne2))` | SMT `decideProp` | The IKM must actually be the DH shared secret from the ODH declaration. |
| R4b | Case predicate `p` holds | SMT `decideProp` | The KDF case is guarded by `p`; we must be in a context where `p` is true. |
| R4c | `ne1 !<= adv` | `flowsTo` check | PRF-ODH requires the first DH key to be honest. |
| R4d | `ne2 !<= adv` | `flowsTo` check | PRF-ODH requires the second DH key to be honest. |

When all four hold, the result is `Right(str, KDFName(...))` -- a fresh
cryptographic name. When any fails, the call falls through to `kdfArgPublic`.

**R5. Strictness refinement on the result** (`Typing.hs:3039-3045`)

When the good case fires, the output type is `Name(ne)` refined with:
- `KDFStrict` => `ne !<= adv` (the output name is secret).
  *Justification*: In the good case, at least one DH key is secret (R4c/R4d), so
  by PRF-ODH the KDF output is indistinguishable from random -- hence secret.
- `KDFPub` => `ne <= adv` (the output name is public).
- `KDFUnstrict` => no additional constraint.

**R6. `pubIKM` / `kdfOOB` -- public fallback for DH secrets**
(`Typing.hs:2783-2809`)

When `matchODH` fails (e.g. a key is compromised), we must still justify why
it's safe to type the output as `Data<adv>`:

| Sub-rule | Condition | Justification |
|----------|-----------|---------------|
| R6a | `b <= adv` | The IKM itself is already public; adversary can compute the KDF. |
| R6b | `b` is a DH value *not* covered by any ODH declaration (`!inODH`) | By PRF-ODH, the adversary gains no advantage from this DH pair (it's not part of any security-critical pattern). |
| R6c | `b` is covered by an ODH declaration, but one of the DH keys `ne1`/`ne2` flows to `adv` | The DH shared secret is compromised because one key is corrupt, so the adversary can reconstruct it. |

R6b is the most subtle: it says that a DH shared secret not declared in any
`odh` block can be treated as public. This is sound because PRF-ODH gives the
adversary oracle access to the PRF on all *non-challenge* DH values.

**R7. `kdfOOB`: `getLocalDHComputation` returns `Nothing`** (`Typing.hs:2795-2796`)

If `b` is not recognizable as a DH computation at all, `kdfOOB` returns `False`.
This is *not* "out of bounds" -- it means the value is an opaque non-DH term
that hasn't been shown public. The caller (`pubIKM`) will then return `False`,
causing the overall result to be `Left False` (ill-typed). This forces the user
to prove that the arguments are public.

*Justification*: We cannot silently treat an unrecognized expression as public.
If it's not DH and not public, the code may be unsound.

**R8. `enforcePublicArguments` on ill-typed KDF** (`Typing.hs:3037`)

When `unifyKDFCallResult` returns `Left False` (no annotation matched and the
arguments weren't shown public), the checker calls `enforcePublicArguments`,
which *asserts* that all of `a`, `b`, `c` flow to `adv` (raising a type error
if not). The output is then `Data<adv>`.

*Justification*: If we can't apply any cryptographic assumption, the only sound
fallback is to require everything to be public.

**R9. Case-split soundness** (`manyCasePropTy`, `casePropTy` in `TypingBase.hs:1548-1567`)

The case split produces a `TCase p t1 t2` type: "if `p` then `t1`, else `t2`".
Both branches are checked independently. The SMT solver is used to determine
whether `p` is known true, known false, or undecidable; if undecidable, both
branches are computed and the result is a case type.

*Justification*: Standard case analysis. The output type is the *join* of the
two branches, so it covers all possibilities.

**R10. Concat component uniformity** (`unifyKDFCallResult` over `bs`)

Every concat component of the IKM must individually be either public or matched
by a KDF/ODH annotation. If *any* component is `Left False` (ill-typed), the
entire call is ill-typed.

*Justification*: The adversary can observe the overall KDF output. If any part
of the IKM is an unaccounted-for secret, the adversary could potentially learn
information about it from the KDF output. All components must be justified.

**R11. `unifyKDFCallResult` combining salt and IKM** (`Typing.hs:3035`)

The salt result and IKM result are unified: if both are `Left True`, the output
is public; if any is `Right(...)`, the output is a name; if any is `Left False`,
the call is ill-typed.

*Justification*: A KDF call can be justified either by the salt-position key or
the IKM-position key. Having *either* one be a valid honest key suffices for
security. But if neither works and one is ill-typed, the call is ill-typed
overall.

**R12. Name kind row compatibility** (`matchODH`, `Typing.hs:2717`)

The annotation's name kind row `nks` must be a prefix of the declaration's name
kind row `nks2`.

*Justification*: Ensures the user's annotation is consistent with what the ODH
declaration actually produces.

**R13. `inODH` predicate definition** (`TypingBase.hs:612-624`)

The `inODH(salt, ikm, info)` predicate is defined as the disjunction over all
ODH declarations. It checks both that `ikm == dh(ne1, ne2)` and that the
salt/info satisfy at least one case predicate.

*Justification*: This precisely characterizes which KDF calls fall within the
scope of an ODH assumption. Used by `kdfOOB` (R6b) to determine whether a DH
value is "covered."


### 13.2 Heuristics (search strategies)

These steps help Owl *find* the right typing derivation. They don't affect
soundness: if a heuristic fails to find a match, Owl rejects the program (a
false negative), but it never accepts an unsound program due to a heuristic.

**H1. `findGoodKDFSplits` -- choosing which names to case-split on**
(`Typing.hs:3214-3242`)

This function collects names from:
- The types of the salt and IKM arguments
- The ODH annotations
- DH keys inferred by `getLocalDHComputation`

and generates `lbl(n) <= adv` propositions for case splitting. The set of names
collected is a heuristic: if a relevant name is missed, the checker might not
find the right case split. But adding more names only increases precision (at the
cost of an exponential blowup in case splits, since `manyCasePropTy` generates
all 2^n combinations).

*If this were different*: Missing a name means the checker might not separately
consider the case where that name is compromised, leading to a false negative.
Including extra names is always safe (just slower).

**H2. `unconcatIKM` -- decomposing the IKM into atomic components**
(`Typing.hs:2852-2873`)

Splits `concat(a, b)` recursively and classifies each leaf. The whitelist of
accepted forms (names, DH values, hex constants, group elements) is a heuristic
restriction.

*If this were different*: A more permissive decomposition could accept more
programs. A more restrictive one would reject more. The restriction exists to
ensure that the checker can reliably determine what each component is. A
component that doesn't match any known form causes a type error (safe but
incomplete).

**H3. `findBestKDFCallResult` -- choosing among multiple annotation matches**
(`Typing.hs:2638-2648`)

When multiple annotations are tried for a single concat component, this function
picks the "best" result:
- If any annotation produced `Right(str, ne)` (a matched KDF/ODH case), prefer
  that. If multiple did, `unifyValidKDFResults` checks they all agree (and errors
  if they don't).
- If none matched, check whether *all* results were `Left True` (public). If so,
  return `Left True`. If any was `Left False`, return `Left False`.

*If this were different*: This is an OR over annotations (any annotation
matching suffices). The preference for `Right` over `Left True` is a heuristic
that maximizes precision -- it's always sound to return `Left True` when `Right`
is also available, but it would lose type information.

**H4. `unifyValidKDFResults` -- consistency of multiple matches**
(`Typing.hs:2587-2609`)

When multiple annotations match (multiple produce `Right`), this function checks
they all compute the same name (via SMT) and have the same strictness. If not,
it's a type error.

This is partly a heuristic (it determines how the checker resolves ambiguity)
and partly a rule (the consistency check prevents unsoundness from contradictory
annotations). The *error on inconsistency* is a rule; the *selection strategy* is
a heuristic.

**H5. `getLocalDHComputation` -- recognizing DH computations**
(`Typing.hs:2813-2840`)

This function tries to decompose an expression into `(pk, sk)` form. It uses
two strategies:
1. Syntactic: look for `dh_combine(pk, get(sk))` directly.
2. Type-based: check if the type is `TSS n m` and one of `n`/`m` is local.

*If this were different*: A smarter version might recognize more DH computations
(e.g., through more levels of ANF resolution). Missing a DH computation causes
`kdfOOB` to return `False` ("not a DH computation"), which is safe (the value
won't be treated as public -- it will cause a type error if it should have been
recognized).

**H6. `extractNameFromType` -- extracting a name from a type**

Used in `findValidSaltCalls` and `findValidIKMCalls` to determine if an argument
has a `TName` type. If the type is not a simple `TName`, the function returns
`Nothing` and the checker falls through to the public check.

*If this were different*: A smarter extraction could handle more complex types.
Returning `Nothing` is always safe (leads to a public check or type error).

**H7. ANF resolution** (`resolveANF` calls throughout)

Several functions (`unconcatIKM`, `getLocalDHComputation`, the equality checks in
`matchODH`) resolve let-bindings to get to the underlying expression. This is
purely a heuristic: if ANF resolution fails to simplify far enough, the SMT
equality check may not be able to prove `b == dh(ne1, ne2)`.

**H8. `doAssertFalse` -- pruning unreachable branches** (`Typing.hs:3029-3031`)

Under a case split, if the path condition is unsatisfiable (SMT proves `False`),
the checker returns `tAdmit` (any type). This prunes unreachable branches.

*Justification as a rule*: ex falso quodlibet (from contradiction, anything
follows). This is logically sound. But the *choice* to check for
unsatisfiability is a heuristic optimization -- the checker would be correct
(but slower and less precise) without it.


### 13.3 Summary table

| Step | Kind | Function | What it does |
|------|------|----------|-------------|
| Both DH keys must be secret | Rule (R4c/R4d) | `matchODH` | PRF-ODH requires honest keys |
| IKM equals declared DH value | Rule (R4a) | `matchODH` | PRF-ODH applies to the right DH pair |
| Case predicate holds | Rule (R4b) | `matchODH` | KDF case is guarded |
| Info is public | Rule (R3) | `checkCryptoOp` CKDF | PRF-ODH models info as public |
| ODH disjointness | Rule (R1) | `ensureODHDisjoint` | Each DH pair used at most once |
| DH not in any ODH => public | Rule (R6b) | `kdfOOB` | Non-challenge DH values are public by PRF-ODH |
| Compromised DH key => public | Rule (R6c) | `kdfOOB` | Corrupt key means adversary knows the shared secret |
| Strictness annotation | Rule (R5) | `checkCryptoOp` CKDF | Refines output type with secrecy info |
| All-public shortcut | Rule (R2) | `checkCryptoOp` CKDF | Public inputs => public output |
| Ill-typed => enforce public | Rule (R8) | `checkCryptoOp` CKDF | No assumption => must be public |
| Each concat component justified | Rule (R10) | `unifyKDFCallResult` | All IKM components must be accounted for |
| Choosing names for case split | Heuristic (H1) | `findGoodKDFSplits` | Which corruption scenarios to enumerate |
| Decomposing IKM concats | Heuristic (H2) | `unconcatIKM` | Splitting `a ++ b` into components |
| Choosing best annotation match | Heuristic (H3) | `findBestKDFCallResult` | Prefer `Right` over `Left True` |
| Checking annotation consistency | Both (H4) | `unifyValidKDFResults` | Error is a rule; selection is a heuristic |
| Recognizing DH computations | Heuristic (H5) | `getLocalDHComputation` | Decompose `dh_combine(pk, get(sk))` |
| Extracting name from type | Heuristic (H6) | `extractNameFromType` | Is this a `TName`? |
| ANF resolution | Heuristic (H7) | `resolveANF` | Simplify let-bindings |
| Pruning unreachable branches | Both (H8) | `doAssertFalse` | Logic is a rule; checking is optional |


## 14. Comparison with regular KDF (salt/IKM position)

| Aspect | Regular KDF (salt/IKM) | ODH |
|--------|----------------------|-----|
| Key source | A name with type `NT_KDF KDF_SaltPos/IKMPos` | A DH shared secret `dh(X,Y)` |
| Declaration | `name k : kdf ...` or `name k : dualkdf ...` | `odh L : X, Y -> {...}` |
| Annotation syntax | `kdf<i;j;...>` | `kdf<;odh L[i];...>` |
| Key secrecy check | `ne !<= adv` (single name) | `ne1 !<= adv /\ ne2 !<= adv` (both DH keys) |
| Public fallback | `tyFlowsTo` for salt; `pubIKM` for IKM | `pubIKM` -> `kdfOOB` (PRF-ODH reasoning) |
| Body substitution | `salt/ikm := arg`, `info := c`, `self := key` | `salt := a`, `info := c`, `self := ikm` (the full IKM argument, not `dh(ne1,ne2)`) |
