# Key Derivation Functions and `kdf_scope`s

Owl models key derivation functions (KDFs) using *KDF scopes*: named blocks
that encapsulate all the ways that a particular set of names can be used with
the key derivation function. This includes the DH key names that may participate 
in ODH, the pre-shared kdfkeys, any intermediate nametypes used to describe 
KDF outputs, and the labeled derivation rules that say which salt + ikm + info 
combination produces which output.

This document describes the surface syntax of `kdf_scope` declarations, the
well-formedness constraints that scopes and their rules must satisfy, the
call-site syntax of the `kdf`/`gkdf`/`KDF<...>` forms, and the typing
rules that the checker uses to give a type to a KDF call. A more formal
reference appears in the *Typing rules* section at the bottom.

A running example that uses almost every feature is
[tests/success/kdf-enc.owl](../tests/success/kdf-enc.owl). For the simplest
ODH call see [tests/success/odh_kdfkey_salt.owl](../tests/success/odh_kdfkey_salt.owl).

---

## 1. The `kdf_scope` block

A KDF scope groups together all of the names and rules that share a single KDF
derivation chain. The block has the form:

```
kdf_scope GroupName {
    // Key material declarations
    name X  : DH     @ loc1
    name Y  : DH     @ loc2
    name k  : kdfkey @ alice, bob

    // (optional) helper nametypes, funcs, predicates
    nametype Chain1 : ...
    predicate p(x) = ...
    func mkinfo arity 1

    // Derivation rules
    kdf L1 : k, 0x, 0x01 -> enckey Name(secret)
    odh L2 : k, dh_ss(X, Y), 0x -> strict kdfkey
    // ...
}
```

The block does not act as a namespace. Names declared inside are registered at the
top level with their bare identifiers and can be referred to from anywhere
else in the file as `get(X)`, `dhpk(X)`, `[k]`, etc., and there is no `G.` or
`GroupName.` qualifier on ordinary uses.

### 1.1 What can appear inside a `kdf_scope`

Only the following declarations are allowed:

- `name n : DH @ loc`---a Diffie–Hellman name for this group's ODH rules.
- `name k : kdfkey @ locs`---a pre-shared kdfkey that may appear in the
  salt or ikm of a rule.
- `nametype Cx : <any nametype>`---a nametype used to describe the behavior
  of a KDF output. Any Owl nametype is permitted here (`kdfkey`,
  `enckey t`, `sigkey t`, `nonce`, `st_aead ...`, and so on); it is not
  restricted to `kdfkey`. Actual KDF output names use the
  `KDF<hint;namekinds;j>` name expression syntax (§3.3).
- `predicate p(...) = ...`---regular Owl predicates.
- `func f arity n` / `func f(...) = ...`---regular Owl pure user-defined
  functions.
- `kdf L ...` / `odh L ...`---KDF derivation rules (see §2).

The checker rejects everything else inside a scope. In particular, `name`
declarations inside a `kdf_scope` must have base name type `DH` or `kdfkey`
(no other kinds are accepted, and abstract names and name abbreviations
are also rejected).

Conversely, `kdf` and `odh` rules are only legal *inside* a scope---writing
one at the top level is a type error.

### 1.2 Where to place a scope in your file

Since names declared inside a scope are registered at the top level, any
`corr` declaration, `def`, or predicate that refers to `get(X)` / `[k]` must
appear *after* the `kdf_scope` that introduces them. Scopes may appear
before or after other `name`/`nametype` declarations as long as the
references they contain are themselves in scope.

### 1.3 Multiple scopes in one file

A file may declare several independent `kdf_scope` blocks; each one's DH keys
and kdfkeys are independent and cannot interact with each other.

---

## 2. KDF rules

Each rule inside a scope has the form

```
(kdf | odh) Label<indices>(params) [where Constraint] :
    salt_expr ,
    ikm_expr  ,
    info_expr
    -> output_spec
```

- `Label` is an identifier that names the rule. Labels are *global* across
  every `kdf_scope` in the file---when the checker resolves a label at a
  call site, it searches every scope until it finds a match
  ([src/TypingBase.hs:736-753](../src/TypingBase.hs#L736-L753)). This may
  change in the future.
- `<indices>` is an optional list of `<i@j>` style session/PId index
  parameters (same syntax as name and def declarations).
- `(params)` is an optional list of bytestring-valued parameters that the
  rule body may refer to---these become free variables in the salt, ikm,
  and info expressions. They are supplied at the call site as bytestring arguments
  (see §3).
- `where Constraint` is an optional `Prop` that narrows when the rule fires.

`kdf` is used when no Diffie–Hellman secret appears in the ikm. `odh` must be
used when the ikm contains a `dh_ss(A, B)` atom. Internally these are handled
the same way, but the syntax requires the programmer to be explicit about uses
of the PRF-ODH assumption.

### 2.1 `salt_expr`

The `salt_expr` is one of:

- **A name**: a bare group kdfkey (e.g. `k`), or a derived kdfkey name
  `KDF<OtherLabel<idxs>(args); kind1 || ... ; j>` that names the `j`-th
  output of another rule in the same chain.
- **A public expression**: a hex constant (`0x`, `0x01`), or any public
  function applied to public arguments.

### 2.2 `ikm_expr`

The `ikm_expr` is a `++` concatenation of one or more *atoms*, each of which
is one of:

- **A public expression**: a hex constant, a DH public key `dhpk(N)`, or a
  public function applied to public arguments.
- **A group kdfkey name**: a bare `k` (or a derived kdfkey name
  `KDF<OtherLabel; kdfkey; j>`).
- **A DH shared secret**: `dh_ss(A, B)` where `A` and `B` are both DH names
  declared in *the current KDF scope*. This is the only form the parser accepts
  for a Diffie–Hellman secret inside a rule body, and the checker rejects
  the rule when `A` or `B` comes from a different scope
  ([tests/failure/kdf-scope-cross-scope-dh.owl](../tests/failure/kdf-scope-cross-scope-dh.owl)).

A rule is classified as `odh` if and only if its ikm contains at least one
`dh_ss` atom. Otherwise, it is a `kdf` rule.

### 2.3 `info_expr`

The `info_expr` is a single public expression (hex constant or public
function application).

### 2.4 `output_spec`

The output is a `||`-separated list of

```
[strict | public]? NameType
```

entries. The three strictnesses are:

- `strict T`---the output is a secret name of nametype `T`. If the inputs are secret,
  the call-site result is refined with `sec(ne)` (i.e. `[ne] !<= adv`).
- `public T`---the output is declared publicly derivable (the call-site
  result is refined with `corr(ne)`).
- bare `T`---unstrict: no secrecy refinement is added to the result.

Each `NameType` must be *uniform*---it must be a name type whose members
have a fixed, public bit-length and are uniformly distributed among bytestrings
of that length. Group elements are not uniform, so `DH` is rejected as an output
([tests/failure/kdf-scope-nonuniform-output.owl](../tests/failure/kdf-scope-nonuniform-output.owl)).

A single rule with several `||`-separated outputs is how one `kdf` call at
runtime produces several independent keys. The `j` index at the call site
picks which of the outputs is being extracted.

### 2.5 Well-formedness of KDF rules

When the checker processes a scope, it validates each rule
([src/Typing.hs:1141-1207](../src/Typing.hs#L1141-L1207)):

1. **Scope binding.**  At least one of the following must hold:
   - the salt is a group kdfkey name (or a derived kdfkey whose j-th output
     has `NK_KDF` kind),
   - the ikm contains at least one group kdfkey name, or
   - the ikm contains a `dh_ss(A, B)` where both `A` and `B` are declared
     in *this* scope.

   A rule whose salt and ikm are entirely public with no scope-owned secret
   is rejected
   ([tests/failure/kdf-scope-no-secret.owl](../tests/failure/kdf-scope-no-secret.owl)).

2. **Every index parameter is used.**  Each session / PId index declared in
   the rule header must appear free in the salt, ikm, or info expression
   ([tests/failure/kdf-scope-unused-idx.owl](../tests/failure/kdf-scope-unused-idx.owl)).

3. **Every data parameter is used.**  Each bytestring argument must appear
   free in the salt, ikm, or info expression
   ([tests/failure/kdf-scope-unused-dvar.owl](../tests/failure/kdf-scope-unused-dvar.owl)).

4. **Output types typecheck and are uniform.**  Each declared output
   nametype must pass `checkNameType` and `nameTypeUniform`.

5. **Pairwise disjointness of (salt, ikm, info, where).**  For every pair of
   rules in the same scope, the SMT solver must prove that their
   salt-equality, ikm-equality, info-equality, *and* both `where`-clauses
   cannot simultaneously hold
   ([src/Typing.hs:1248-1273](../src/Typing.hs#L1248-L1273)). Duplicate
   rules with the same shape fail this check
   ([tests/failure/kdf-scope-dup-sii.owl](../tests/failure/kdf-scope-dup-sii.owl)).

5b. **Self-disjointness of each rule.**  Each individual rule must also be
    disjoint with itself: two distinct choices of its own index / data
    parameters must not yield the same `(salt, ikm, info)` under its
    `where` predicate
    ([src/Typing.hs:1208-1246](../src/Typing.hs#L1208-L1246)). For example,
    `kdf L(a, b): k, 0x, a ++ b -> ...` is rejected, because
    `(a=0x12, b=0x34)` and `(a=0x1234, b=0x)` produce the same
    `info = 0x1234`, yet `(a, b)` differ. A rule with no index or data
    parameters trivially satisfies this check.

6. **Name identifier uniqueness.**  Names declared inside a scope must not
   collide with any other top-level name
   ([tests/failure/kdf-scope-repeated-name.owl](../tests/failure/kdf-scope-repeated-name.owl)).

---

## 3. Using KDF rules in code

### 3.1 Runtime KDF calls: `kdf<hints; kinds; j>(...)`

The call-site form is

```
kdf<Label<idxs>(args), Label2<...>, ...; kind1 || kind2 || ... ; j>(salt, ikm, info)
```

- The first angle-bracket field is a non-empty comma-separated list of
  **rule hints**. Each hint is a `KDFScopeRuleRef`: a label, an optional
  `<idxs>` index list, and optional `(args)` bytestring arguments. The
  checker tries each hint and uses the one (if any) that actually matches.
- The second field is a `||`-separated list of the rule's output `NameKind`s
  (`kdfkey`, `nonce`, `enckey`, `mackey`, `sigkey`, `pkekey`). Its
  length and contents must match what the chosen rule declares.
- `j` is the index into the `||` list: which output is being extracted.

Concretely, from [tests/success/kdf-enc.owl](../tests/success/kdf-enc.owl):

```owl
let ek  = kdf<L1_enc; enckey; 0>(get(k), 0x, 0x01) in       // one hint
let k2  = kdf<L1_kdf; kdfkey; 0>(get(k), 0x, 0x02) in
let ek2 = kdf<L2_enc; enckey; 0>(0x,     k2,  0x01) in
let k1  = kdf<L4; nonce || nonce; 0>(get(kk), 0x, 0x) in    // two outputs
let k2  = kdf<L4; nonce || nonce; 1>(get(kk), 0x, 0x) in
```

Multiple hints are passed as a comma-separated list and are commonly used
when different rules can apply in different branches of the typechecker.
All hints must produce compatible outputs (i.e., the name kinds for each output must be equal).

### 3.2 Ghost KDF calls: `gkdf<...>(...)`

The same syntax is used in ghost position (inside `func` bodies, struct
ghost fields, etc.) as in the old version:

```
gkdf<Label<idxs>(args); kinds; j>(salt, ikm, info)
```

### 3.3 Derived KDF outputs inside rule bodies and struct field types

The `KDF<Label<idxs>(args); kinds; j>` form is a *name expression*. It
uniquely defines a name, since KDF rules must have disjoint domains and so
(by the injectivity assumption on KDF) have disjoint codomains.

---

## 4. How a `kdf` call is type-checked

The logic lives in [src/Typing.hs:3286-3303](../src/Typing.hs#L3286-L3303)
and the helpers it calls. At a high level, given a call

```
kdf<h1, h2, ...; nks; j>(saltE, ikmE, infoE)
```

the checker proceeds in three stages.

### 4.1 Stage 1---match the hints

For each hint `h_k`, `tryKDFRuleHint`
([src/Typing.hs:2975-3031](../src/Typing.hs#L2975-L3031)) looks up the rule
body (substituting the hint's index and bytestring arguments) and then checks:

1. `checkSaltMatch`: the runtime salt expression is provably equal
   to the rule's `salt_expr`.
2. `checkIKMMatch`: the runtime ikm is provably equal to the concatenation
   of the rule's ikm atoms.
3. `checkInfoMatch`: the runtime info is provably equal to the rule's
   `info_expr`.
4. `checkWhereClause`: the rule's `where` predicate is provable in the
   current path condition.

If any of these fails, the hint doesn't match and returns `Nothing`. If all
pass, the call-site name-kind row `nks` is checked against the rule's
declared output kinds, and the hint is matched.

The three possible outcomes are:

- **Exactly one hint matches.**  The checker returns the matched rule's
  output type (see §4.2 for how it picks between a secret and a public
  shape).
- **More than one hint matches.**  The call is *ambiguous* and rejected
  with `"Ambiguous KDF call: multiple hints matched"`.
- **No hint matches.**  Fall through to stage 2 (§4.3).

### 4.2 Output type of a matching hint

Assume hint `h` matched and the rule declares output `j` with strictness `S`
and nametype `T`. Let `saltPub` / `ikmPub` be `true` if the corresponding
runtime argument flows to `adv`. Write `saltHasKey` for "the rule's salt
is a name" and `ikmHasKey` for "the rule's ikm contains a kdfkey name or a
`dh_ss`". Then the result type is:

| condition | result |
|-----------|--------|
| `saltPub ∧ ikmPub` | `Data<adv>` (public KDF output) |
| `¬saltPub ∧ saltHasKey` or `¬ikmPub ∧ ikmHasKey` | refined `Name(KDFName...)` with strictness refinement from `S` |
| otherwise | type error |

The info argument must always be public---the checker asserts this
unconditionally.

The name expression returned is `KDF<h; namekinds; j>`.

The strictness-derived refinement is:

| strictness | refinement added to `.res` |
|------------|----------------------------|
| `strict` | `¬([res] <= adv)`, i.e. `sec(res)` |
| `public` | `[res] <= adv`, i.e. `corr(res)` |
| unstrict | `True` |

### 4.3 Stage 2---no hint matched

`handleKDFNoMatch` ([src/Typing.hs:3164-3218](../src/Typing.hs#L3164-L3218))
handles the remaining cases.

**Fast path---all-public arguments.** If the salt, ikm, and info are all
public (flow to `adv`) then the KDF output is `Data<adv>` and no further
analysis is needed.

**Locate the scope.**  All hints (if any) must refer to labels in the same
scope; the checker looks up that scope.

**Provably out of bounds.**  For every rule in the scope, the checker asks
SMT whether the call's (salt, ikm, info) *could* match the rule's
(salt, ikm, info, where condition). Two outcomes are acceptable:

- If at least one rule might match, the call is
  potentially in-bounds and we continue.
- If *every* rule's match proposition is provably false, the call is
  provably out of bounds and the output is `Data<adv>`. This is how
  deliberately-wrong hint mismatches (e.g., calling with a wrong salt
  key) fall through to a public output
  ([tests/failure/kdf-scope-wrong-salt.owl](../tests/failure/kdf-scope-wrong-salt.owl)).

If the result is inconclusive (some rules possibly match and the
checker cannot rule them all out) the call is rejected with
`"Inconclusive: cannot match this KDF call with a rule or prove that it
doesn't match any of the rules"`.

**Scope-bound + public fallback.**  Otherwise (at least one rule can't be proven not to match
but no hint matches exactly), the checker requires that the call is
provably bound to this scope *and* that every one of its arguments is
already public:

- At least one of `(saltE, ikmE-atom₁, ikmE-atom₂, …)` must be a
  *local scope binding expression*: a name from the scope used as a salt/ikm
  atom, or a `dh_combine(pk, sk)` whose `pk` or `sk` is a scope DH name.
- *Every* component must also be public (flow to `adv`).

If those hold, the output is `Data<adv>`. Otherwise the call is rejected.

At a site with no matching hint, the call may still be
accepted, but only when the checker can prove either that no rule in the
scope could possibly apply or that every component of the call is already
public. The intent is to rule out cases where Owl expects a KDF call to 
match rule `L1`, but the adversary supplies inputs that match rule `L2` and
confuse the typechecker into generating (and possibly releasing) unrelated secrets.

---

## 5. A worked example

[tests/success/kdf-enc.owl](../tests/success/kdf-enc.owl) exercises a short
chain:

```owl
kdf_scope G {
    name k : kdfkey @ alice, bob

    kdf L1_enc : k, 0x, 0x01 -> enckey Name(alice1)
    kdf L1_kdf : k, 0x, 0x02 -> strict kdfkey
    kdf L2_enc : 0x, KDF<L1_kdf;kdfkey;0>, 0x01 -> enckey Name(alice2)
    kdf L2_kdf : 0x, KDF<L1_kdf;kdfkey;0>, 0x02 -> strict kdfkey
    kdf L3_enc : KDF<L2_kdf;kdfkey;0>, 0x, 0x01 -> enckey Name(alice3)
}

def alice_main() @ alice : Unit =
    let ek = kdf<L1_enc;enckey;0>(get(k), 0x, 0x01) in
    let c  = aenc(ek, get(alice1)) in
    output c to endpoint(bob);
    let k2  = kdf<L1_kdf;kdfkey;0>(get(k), 0x, 0x02) in
    let ek2 = kdf<L2_enc;enckey;0>(0x, k2, 0x01) in
    let c2  = aenc(ek2, get(alice2)) in
    output c2 to endpoint(bob);
    ()
```

- `L1_enc` and `L1_kdf` share the salt `k` and differ only in their info
  (`0x01` vs `0x02`); the salt-ikm-info-disjointness SMT check verifies they cannot
  both match.
- `L2_enc` and `L2_kdf` take a chained salt: the rule's salt is
  `KDF<L1_kdf; kdfkey; 0>`, and the call-site salt is `k2`, the runtime
  value produced by the `kdf<L1_kdf;kdfkey;0>(…)` call. The checker
  recognizes `k2`'s type as `KDFName … L1_kdf`, which matches the rule's
  declared salt.
- Because `L1_kdf` is `strict`, `k2` is typed as a secret
  `Name(KDFName… L1_kdf)` refined with `sec(k2)`, allowing it to be passed
  in the salt position of the L2 rules.

---

## 6. Typing rules

The rules below mirror the style of
[docs/internals/kdf.md](internals/kdf.md)---each premise is on its own
line, and indices and capture-avoiding substitutions are written
explicitly where they matter. They ignore:

- the `findScopeForLabel` lookup (labels are global across scopes, so each
  hint resolves to a unique scope);
- the `unconcatIKM` concatenation handling on the call side (treated as if
  the runtime ikm arrives as a single value that is provably equal to the
  rule's concatenation);
- the ghost `gkdf` / `KDF<...>` forms, which reuse the same rule machinery
  as `kdf`.

### Notation

- `G` is the overall typing context.
- `G[k]` looks up `k` as a name definition; `G[L]` looks up `L` as a KDF
  scope rule.
- `p[x := y]` is capture-avoiding substitution.
- `gkdf<L<is>(as), nks, j>(a,b,c)` is the ghost KDF value.
- `adv` is the adversary label; `sec(n) ≜ ¬([n] <= adv)`;
  `corr(n) ≜ [n] <= adv`.
- `dhpk(n)` is not written explicitly on DH names when used in `dh_combine`.

### Rule lookup: `ruleOfRef(ref, body)`

Given a call-site reference `ref = L<is>(as)`, we look up `body` in some
scope `GName`:

```
(GName, gdef) ∈ G.kdfScopes
gdef.rules[L] = kdf L<is'>(dvars'): ruleBody
|is| = |is'|      |as| = |dvars'|
body = ruleBody[is' := is][dvars' := as]
-----------------------------------------------------
G |- ruleOfRef(L<is>(as), body)
```

When several scopes define the same label, the first matching one wins;
labels are expected to be globally unique.

### Hint match: `hintMatches(ref, (a,b,c))`

Given `body` as above, with output spec
`[(S_0, T_0), ..., (S_{m-1}, T_{m-1})]`:

```
G |- ruleOfRef(ref, body)
G |- a = body.salt              
G |- b = body.ikm  (atoms concatenated)
G |- c = body.info
G |- body.where                 
---------------------------------------------------------------
G |- hintMatches(ref, (a,b,c))  with body, outputs
```

### Well-typed KDF with a matching hint

Let `ref = L<is>(as)` and suppose exactly one hint `ref_i ∈ {ref_1, ..., ref_k}`
satisfies `hintMatches`. Let the matched rule's j-th output be
`(S_j, T_j)` with name kind `nks[j]`. Let
`ne = KDFName(nks, j, true, ref_i)`.

**Fully public case** (salt and ikm both adversary-controlled):

```
G |- hintMatches(ref_i, (a,b,c))
G |- nks matches outputs
G |- c <= adv                    // info always public
G |- a <= adv
G |- b <= adv
-----------------------------------------------
G |- kdf<{ref_1,...,ref_k}; nks; j>(a,b,c) :
    x : Data<adv> { |x| = |nks[j]| ∧ x = gkdf<ref_i, nks, j>(a,b,c) }
```

**Honest case** (some secret ingredient present in a key position of the
rule):

```
G |- hintMatches(ref_i, (a,b,c))
G |- nks matches outputs
G |- c <= adv
(a !<= adv ∧ body.salt is a name)
  ∨ (b !<= adv ∧ body.ikm contains a kdfkey-name or dh_ss atom)
---------------------------------------------------------
G |- kdf<{ref_1,...,ref_k}; nks; j>(a,b,c) :
    x : Name(ne) {
        strictnessOf(ne, S_j)
        ∧ |x| = |nks[j]|
        ∧ x = gkdf<ref_i, nks, j>(a,b,c)
    }
```

**Ambiguous hints.**  If more than one `ref_i` matches simultaneously, the
checker raises a type error---the rule body is undefined.

### No hint matched---out-of-bounds case

Let `scope(refs) = GName` with rules `rules = {(L_1, body_1), ..., (L_n, body_n)}`.

```
∀ k ∈ {1..|refs|}. ¬ hintMatches(refs[k], (a,b,c))
∀ i ∈ {1..n}. G |- ¬ ∃ is dvars. (a = body_i.salt ∧ b = body_i.ikm
                                  ∧ c = body_i.info ∧ body_i.where)
G |- c <= adv
--------------------------------------------------------
G |- kdf<refs; nks; j>(a,b,c) :
    x : Data<adv> { |x| = |nks[j]| ∧ x = gkdf<refs[0], nks, j>(a,b,c) }
```

### No hint matched---public-arguments fallback

Let `entryNames(GName)` be the kdfkeys and DH names declared in the scope.
Write `LSBE(e)` for "`e` is a name from `entryNames`, or `e =
dh_combine(pk, sk)` where `pk` or `sk` is a DH name from `entryNames`".

```
∀ k ∈ {1..|refs|}. ¬ hintMatches(refs[k], (a,b,c))
∃ i. G |- ∃ is dvars. (a = body_i.salt ∧ b = body_i.ikm
                       ∧ c = body_i.info ∧ body_i.where)    // not all provably out-of-bounds
G |- c <= adv
b = b_1 ++ ... ++ b_p                 // expose the ikm atoms
LSBE(a) ∨ ∃ q. LSBE(b_q)              // call is bound to this scope
G |- a <= adv ∧ b_1 <= adv ∧ ... ∧ b_p <= adv
--------------------------------------------------------
G |- kdf<refs; nks; j>(a,b,c) :
    x : Data<adv> { |x| = |nks[j]| ∧ x = gkdf<refs[0], nks, j>(a,b,c) }
```

Both "no-hint" rules are special cases of the overapproximating rule from
[docs/internals/kdf.md](internals/kdf.md): they return `Data<adv>` but only
when the checker is able to prove that this is safe. If neither applies,
the call is rejected with `"Inconclusive: cannot match this KDF call with
a rule or prove that it doesn't match any of the rules"` (inconclusive SMT
result) or `"This KDF call isn't bound to scope 'G': it must contain a
name or DH secret from the scope"` (no LSBE component).

### `strictnessOf(ne, strictness)`

```
strictnessOf(ne, strict)   ≜ ¬([ne] <= adv)
strictnessOf(ne, public)   ≜ [ne] <= adv
strictnessOf(ne, unstrict) ≜ True
```

### Well-formedness of rules (`validateKDFScopeRule`)

For a rule `R = (kdf|odh) L<is>(dvars) [where W] : s, k, i -> outputs` in
scope `GName` with entry names `N = kdfkeys ∪ dhs`:

```
scopeHasKey(R) ≜
  (s is a name whose leaf symbol ∈ kdfkeys, or a `KDF<...>`
   reference with kdfkey kind)
  ∨ (∃ atom ∈ k. atom is a kdfkey name from kdfkeys,
                 or a `KDF<...>` reference with kdfkey kind)
  ∨ (∃ atom ∈ k. atom = dh_ss(A, B) with A, B ∈ dhs)

fv(s) ∪ fv(k) ∪ fv(i) ⊇ is ∪ dvars
each output T_j typechecks and is uniform
∀ R' ∈ scope rules, R' ≠ R.
    G |- ¬ ∃ is' dvars'. (s = s' ∧ k = k' ∧ i = i' ∧ W ∧ W')
-----------------------------------------------------------
G |- validateRule(GName, R)
```

Failure of any of these premises produces a compile-time error at the
`kdf_scope` block itself.

---

## 7. Design notes

- **Why one rule per case.**  Where the old `kdf {ikm info. … }` nametype
  syntax used predicate branches to discriminate cases, `kdf_scope` uses
  one labeled rule per case. The condition is expressed structurally: a
  `Chain1`-typed salt can only arise from the rule that produced it. 
  This is easier to audit and lets the SII-disjointness SMT check cover all overlap.

- **Why `where` clauses.**  They exist so that two rules that differ only
  by a relation on their indices---commonly a "correct session" vs. a
  "wrong session" variant---can coexist without overlap, or to capture "off-chain"
  cases where some but not all of the input to the KDF doesn't match the expected form.

- **Why hints are *ghost*.**  At runtime, a KDF call is just a call to the
  underlying KDF primitive; the hint list only affects the type the checker
  gives to the result. The multi-hint form is useful when different branches
  of the typechecker (e.g., different `corr_case`s or index conditions) require
  different hints to typecheck.

- **Soundness assumption: type provenance.**  The checker trusts that a
  value typed as `Name(KDFName…)` could only have been produced by the
  corresponding rule's KDF call, and uses this to type derived kdfkeys
  like `KDF<L1; kdfkey; 0>` as salt arguments of later rules. 
