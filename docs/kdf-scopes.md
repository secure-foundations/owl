# Key derivation functions and `kdf_scope`

## Overview

A key derivation function (KDF) takes three inputs and produces
pseudorandom bytes:

- the **salt**, usually a key;
- the **input key material** (**ikm**), for example a Diffie-Hellman shared
  secret, or several values concatenated together;
- the **info**, a public string that tells different uses of the same keys
  apart.

Real protocols such as WireGuard, HPKE, and Signal chain many KDF calls
together. Each output becomes the key of the next call, or an encryption key,
or a MAC key. To verify such a protocol, Owl has to answer two questions for
every KDF call:

1. What is the type of the output? Owl needs to give it a name type (such as an
   encryption key for some plaintext type) so the rest of the program can use
   it.
2. Could this same output also come from some *other* KDF call somewhere in
   the protocol? If it could, the two uses might conflict, for example if one
   use treats the value as secret and another treats it as public.

Owl answers these questions with **KDF scopes**. A KDF scope is a block that
lists:

- the secret keys that are fed into the KDF: `kdfkey` names and
  Diffie-Hellman (`DH`) names;
- any helper functions and predicates that the rules need;
- a list of **rules**. Each rule describes one way to use the KDF:
  which salt, ikm, and info go in, how many outputs come out, what name type
  each output has, and any secrecy assumptions about each output.

Each output of a rule is a **derived name**, written
`KDF<L<idxs>(args); kinds; j>`. Read this as "output number `j` of rule `L`,
at these indices and arguments". A derived name can be used anywhere an
ordinary Owl name can. A rule may be **recursive** in one of its session
indices. This lets us write a ratchet, where each key is derived from the
previous one, as a single rule. Several rules may also be mutually recursive.

### Why scopes?

A key difficulty when typing a KDF call is ruling out *unintended* matches. When
Owl checks a call, it is not enough to confirm that the call does what the
protocol intended at that point in the program. Owl must also make sure
that the inputs cannot coincide with any *other* use of the KDF anywhere in
the protocol. If two calls shared their inputs, they would compute the same value but
might type it differently.

A scope lists every intended use of the KDF with the scope's keys. In effect,
scopes divide the possible inputs of the KDF into separate groups, 
and any one KDF call can only belong to one group. So when Owl checks
a call, it only has to compare it against the rules of one scope, not against
every KDF use in the whole protocol.

### How this document is organized

- Sections 1 to 3 describe the syntax: the `kdf_scope` block (section 1), the
  rules inside it and the checks Owl runs when it reads them (section 2), and
  the ways a program calls the KDF (section 3).
- Section 4 explains how Owl typechecks a `kdf` call.
- Section 5 walks through two examples.
- Section 6 describes the facts Owl gives to the SMT solver.
- Section 7 lists the ghost lemmas related to KDFs.
- Section 8 states the cryptographic assumptions, sketches why the design is
  sound, and lists the known gaps.
- Section 9 states the typing rules semi-formally.
- Section 10 records the design decisions and the alternatives they were
  chosen over.

### Where the code lives

| What | Where |
|---|---|
| Parsing of scopes, rules, hints, derived names, index expressions | `parseKDFRuleDecl`, `parseKDFRuleRef`, `parseIdx` in [src/Parse.hs](../src/Parse.hs) |
| Rule representation | `KDFRule`, `KDFCases`, `KDFRuleRef` in [src/AST.hs](../src/AST.hs) |
| Cases of a rule, applicability | `kdfInsts`, `kdfInstAt`, `kdfApplicable` at the end of [src/TypingBase.hs](../src/TypingBase.hs) |
| Declaration checks, the `kdf` call, lemmas | the section "KDF scopes" at the end of [src/Typing.hs](../src/Typing.hs) |
| Generated SMT theory | `declareKDFRules`, `setupKDFRules` in [src/SMT.hs](../src/SMT.hs); `kdf_collision_resistant_on_large_slices`, `Index*` in [prelude.smt2](../prelude.smt2) |

### Examples to read alongside this document

- [tests/success/kdf-enc.owl](../tests/success/kdf-enc.owl): a short chain of
  KDF calls.
- [tests/success/odh_kdfkey_salt.owl](../tests/success/odh_kdfkey_salt.owl):
  the simplest call that uses a Diffie-Hellman secret (an ODH call).
- [tests/success/rec_kdf_chain.owl](../tests/success/rec_kdf_chain.owl): a
  recursive chain.
- [tests/success/rec_kdf_mutual.owl](../tests/success/rec_kdf_mutual.owl): two
  mutually recursive rules.
- The case studies: WireGuard ([tests/wip/wg](../tests/wip/wg)), HPKE
  ([tests/wip/hpke](../tests/wip/hpke)), and Signal
  ([tests/wip/signal](../tests/wip/signal)). The Signal case study contains
  X3DH and a double ratchet written as mutually recursive ODH rules.

---

## 1. The `kdf_scope` block

Here is an example scope:

```
kdf_scope G {
    name X : DH     @ alice
    name Y : DH     @ bob
    name k : kdfkey @ alice, bob

    func mkinfo arity 1                 // optional helpers
    predicate p(x) = ...

    kdf L1 : k, 0x, 0x01 -> enckey Name(secret)
    odh L2 : k, dh_ss(X, Y), 0x -> strict kdfkey

    rec_kdf<i> L3<i>
        | 0        : k,                        0x, 0x02
        | succ(i') : KDF<L3<i'>; kdfkey; 0>,   0x, 0x02
        -> strict kdfkey
}
```

The scope declares two DH names `X` and `Y` and a shared key `k`, and then
three rules. Each rule is written as `salt, ikm, info -> outputs`:

- `L1` uses `k` as the salt, an empty ikm, and the info `0x01`. Its single
  output is an encryption key for the name `secret`.
- `L2` uses `k` as the salt and the Diffie-Hellman shared secret of `X` and
  `Y` as the ikm. Its output is a new `kdfkey`. The keyword `odh` marks that
  the rule relies on the Diffie-Hellman (ODH) assumption, and `strict` says
  that the output is secret whenever the rule applies (section 2.3).
- `L3` is a chain of keys indexed by `i`. The first key (`i = 0`) is derived
  with `k` as the salt. Each later key (`i = succ(i')`) is derived with the
  previous key in the chain, `KDF<L3<i'>; kdfkey; 0>`, as the salt.

### 1.1 A KDF scope is not a namespace

Names declared inside a scope are registered at the top level under their
plain names. Elsewhere in the file you write `get(X)`, `dhpk(X)`, `[k]`, and
so on, without mentioning the scope. A scope only exists to mark out the
names and rules that belong to one group of KDF calls, so Owl does not treat
it as a module or a namespace.

### 1.2 What a KDF scope can contain

A `kdf_scope` block can contain:

- Names of type `kdfkey` or `DH` (`name n : DH @ loc` and
  `name k : kdfkey @ locs`). A name of any other type, an abstract name, or a
  name abbreviation is rejected.
- Rules: `kdf`, `odh`, `rec_kdf<i>`, and `rec_odh<i>` (section 2). Rules can
  appear *only* inside a scope.
- Ordinary declarations that contain no code: `func`, `predicate`,
  `nametype`, `struct`, `enum`, `corr`, and so on. These behave exactly as if
  they were declared outside the scope.

The following are not allowed inside a scope: `locality`, `def`, def
headers, `table`, `module`, `include`, and nested `kdf_scope` blocks.

A file can contain any number of KDF scopes.

### 1.3 Index expressions and recursive names

To write chains of keys, we need to be able to talk about "the next index"
and "the first index". So wherever Owl expects an index, it accepts an
**index expression**: an ordinary index variable `i`, the constant `0`, or
`succ(e)` for another index expression `e`. Index expressions are allowed in:

- name references (`n<succ(i)>`);
- rule references (`KDF<L<succ(0)>; ...>`);
- struct parameters (`msg<succ(i)>`);
- the indices of a call;
- `pack`.

Where an index is *introduced* (`name k<i>`, `def f<i>`, or the index
parameters of a rule), it must still be a plain variable. `succ` can only be
applied to session indices and ghost indices, and `0` is always a session
index.

In the SMT solver, the `Index` type has a zero (`IndexZero`), a successor
function (`IndexSucc`), and a predecessor function. The predecessor function
is only there to make `succ` injective: `succ(i) = succ(j)` implies `i = j`. 
Each index also has a size, a natural number, which grows by one with each `succ`. 
This ensures that `succ^k(i)` is never equal to `i` for `k >= 1`. 
There is no axiom saying that every index is either `0` or a successor.

#### Recursive base names

The name type of a base name may mention that name itself at other indices:

```
name k2<i> : enckey Name(k2<succ(i)>)     // recursive
```

Here each key `k2<i>` encrypts the next key, `k2<succ(i)>`.

Owl accepts such a self-reference only if it points to strictly larger
indices. Specifically, each session-index position of the reference must hold
`succ^n` of the variable bound at that same position (with `n >= 0`), and at
least one position must have `n >= 1`. In the example above, the reference
`k2<succ(i)>` has `n = 1` at the only position.

Under this condition, every reference points to an instance with a strictly
larger sum of indices. So following references can never lead back to an
earlier instance, and the chain of references from any concrete instance is
finite (section 8 lists the assumptions this relies on). Without the
condition, a key could end up encrypting itself. For example,
`name k<i> : enckey Name(k<succ(0)>)` is rejected, because at `i = succ(0)`
the key `k<succ(0)>` would encrypt itself. The tests
[tests/failure/recursive_name_non_increasing.owl](../tests/failure/recursive_name_non_increasing.owl),
[tests/failure/key_cycle_rec_name_succ_zero.owl](../tests/failure/key_cycle_rec_name_succ_zero.owl),
and
[tests/failure/key_cycle_rec_name_dropped_index.owl](../tests/failure/key_cycle_rec_name_dropped_index.owl)
show rejected declarations.

---

## 2. Rules

A rule has one of these two forms:

```
(kdf | odh) Label<idxs>(params) [where P] : salt , ikm , info -> out_1 || ... || out_m

(rec_kdf | rec_odh)<i> Label<idxs>(params) [where P]
    | 0        : salt_0 , ikm_0 , info_0
    | succ(i') : salt_1 , ikm_1 , info_1
    -> out_1 || ... || out_m
```

The parts are:

- **`<idxs>`**: session and party index parameters, written with the usual
  `<i@n>` syntax.
- **`(params)`**: bytestring parameters. Inside the rule they are ghost
  variables. At a call site, the programmer supplies values for them as
  arguments to the hint, as in `L(e)` (section 3.1).
- **`where P`**: a proposition over the parameters that restricts which
  values of the parameters are allowed. It may only talk about concrete
  properties of the indices and parameters, such as equalities. It may not
  mention labels, secrecy or corruption, `happened` events, or
  `honest_pk_enc`/`honest_kem_encaps`, either directly or through a
  predicate. The reason is that these properties depend on the particular
  execution's path condition, while the soundness argument in section 8 
  needs the inputs of an instance *alone* to determine which derived name it is. 
  The tests
  [tests/failure/kdf_where_label.owl](../tests/failure/kdf_where_label.owl),
  [kdf_where_label_through_predicate.owl](../tests/failure/kdf_where_label_through_predicate.owl),
  and [kdf_where_event.owl](../tests/failure/kdf_where_event.owl) show
  rejected where clauses.
- **`odh`** instead of `kdf`: required when the ikm contains a
  Diffie-Hellman secret `dh_ss(A, B)`. It marks the rules that rely on the
  ODH assumption.
- **`rec_kdf<i>`** / **`rec_odh<i>`**: a recursive rule. The recursion index
  `i` must be one of the rule's session-index parameters. The rule has two
  cases. The zero case gives the salt, ikm, and info for `i = 0`. The succ
  case gives them for `i = succ(i')`, and may mention both `i'` and `i`.

  The outputs are written **once**, after both cases, in terms of the rule's
  own index parameters `idxs`. They can mention `i`, but not `0` or `i'`. So
  for any index expression `i_expr`, including a plain variable, the derived
  name `KDF<L<i_expr>; nks; j>` has the name type `out_j` with `i` replaced
  by `i_expr`.

Two shorthands are available in a rule body:

- `dh_ss(A, B)` stands for `dh_combine(dhpk(get(A)), get(B))`, the
  Diffie-Hellman shared secret of the DH names `A` and `B`.
- A bare name `k` or `KDF<...>` stands for `get(k)` or `get(KDF<...>)`. (A
  bare identifier that is one of the rule's parameters stays a variable.)

A **rule instance** `L<is>(es)` is the rule `L` with concrete values
supplied for its indices and bytestring parameters, where those values
satisfy the rule's where clause. Each rule instance has exactly one
`(salt, ikm, info)` input. Because of this, an instance determines its
outputs, and each output gets its own derived name `KDF<L<is>(es); kinds; j>`.

### 2.1 Cases

A recursive rule describes two different shapes of input: one for the first
step and one for every later step. To handle both kinds of rules in the same
way, Owl splits every rule into **cases**. All of the checks and SMT axioms
described below work on cases. A case has its own parameters, and consists of
the instance it defines, the where clause, and the `(salt, ikm, info)` input.

- A non-recursive rule has one case, over the rule's parameters.
- A recursive rule has a **zero case**, where `i` is replaced by `0` and is
  no longer a parameter, and a **succ case**, where `i` is replaced by
  `succ(i')` and the parameter `i'` takes the place of `i`.
- Some recursive rules are **uniform**: the succ case does not mention `i'`,
  and the zero case is exactly the succ case with `i = 0`. In other words,
  every step of the chain looks the same. A uniform rule is treated as a
  single case over `i`.

When a program refers to an instance `L<is>(es)`, Owl selects a case by
matching the given indices against each case:

- `0` selects the zero case;
- `succ(p)` selects the succ case, with `i' := p`;
- an index variable selects a case only if the rule is uniform.

So an instance of a non-uniform recursive rule at an index variable, such as
`L<i>`, is **opaque**. It still has a name type, taken from the rule's
outputs, but Owl does not know its inputs. This prevents Owl from unfolding a
recursive rule forever. It is also enough in practice: a rule that connects
step `L<i>` to step `L<succ(i)>` should not need to know whether `i` itself
is `0` or a successor.

### 2.2 Salt, ikm, and info

The **salt** is one of the following:

- a name: `k`, or a derived `kdfkey` `KDF<L'<..>(..); ..; j>`;
- a public constant;
- a **term salt**: a `gkdf(...)` expression (section 3.2) that stands for a
  KDF output that is public, for example the result of an earlier KDF call
  that the adversary fed incorrect inputs;
- a bytestring parameter.

The **ikm** is a concatenation (with `++`) of **atoms**. An atom is a public
expression, a name, a DH secret `dh_ss(A, B)`, a parameter, or an arbitrary
term such as `dh_combine(x, get(E))` where `x` is a bytestring parameter.

The **info** is a single expression and must be public.

### 2.3 Outputs

The outputs are a `||`-separated list. Each output has the form

```
out_j ::= [strict | public]? NameType
```

Every output name type must be well formed and **uniform**: its values must
be uniformly random bytestrings of a fixed length, as KDF outputs are. The
uniform name types are `nonce`, `enckey`, `st_aead`, `mackey`, and `kdfkey`.
`DH` is rejected, because DH group elements are not uniformly distributed
over all bytestrings of the same length.

Output types may mention the rule's parameters (see
[tests/success/kdf_scope_arg_in_rhs.owl](../tests/success/kdf_scope_arg_in_rhs.owl)).

The optional marker says how secret the output is:

- `strict` promises that the output is secret whenever the instance is
  applicable (section 2.4);
- `public` says that the output is always corrupt;
- an unmarked output adds no secrecy or corruption fact by default.

### 2.4 Applicability

A KDF only protects its output if it has a secret key among its inputs. If all of
its inputs are public, the adversary can compute the output just as well as
the honest parties can. Owl captures this with the notion of
**applicability**: a rule case is applicable when some secret input appears in a
**key position**. The key positions are the salt and the atoms of the ikm.

Formally, Owl computes applicability as follows:

```
atomApp(get(n))                           = sec(n)
atomApp(dh_combine(dhpk(get(x)), get(y))) = sec(x) /\ sec(y)
atomApp(p), p a parameter of the rule     = exists idxs. p == get(k<idxs>) /\ sec(k<idxs>),  over the base kdfkeys k of the scope
atomApp(anything else)                    = False
applicable(case) = atomApp(salt) \/ atomApp(ikm_1) \/ ... \/ atomApp(ikm_p)
```

In words: a name in a key position counts if it is secret; a DH secret counts
if both of its DH names are secret; and a parameter in a key position counts
if its value is a secret base `kdfkey` of the scope.

An instance that is not applicable has only public inputs. The adversary can run it themselves and learn its output, so such
an instance never gets a secret name. This is also why collisions between two
non-applicable instances do no harm.

Applicability is a property of a *rule instance*. Owl computes it once, on
the rule with symbolic parameters, and then fills in the parameters as
needed. Some further points about applicability:

- **Parameters in key positions.** WireGuard has the rule
  `kdf L6(ikm) where (ikm == zeros \/ ikm == get(psk)) : C6, ikm, 0x`. It has
  two key positions: the salt `C6`, which is the key derived by the previous
  rule `L5`, and the parameter `ikm`. So an instance `L6(v)` is applicable
  when `C6` is secret, *or* when the value `v` is a secret `kdfkey` of the
  scope. In particular, `L6(get(psk))` is still applicable when `C6` is
  corrupt, as long as `psk` is secret. `L6(zeros)` is applicable only through
  `C6`. See
  [tests/success/kdf_param_key_pinned.owl](../tests/success/kdf_param_key_pinned.owl),
  [tests/failure/kdf_param_key_pinned_refute.owl](../tests/failure/kdf_param_key_pinned_refute.owl),
  and
  [tests/failure/kdf_param_key_unpinned_name.owl](../tests/failure/kdf_param_key_unpinned_name.owl).
- **Adversarial DH values.** An ikm atom `dh_combine(x, get(E))`, where `x`
  is a parameter, is never a key position. Here `x` stands for a group
  element chosen by the adversary. A DH secret between two honest keys must
  be written `dh_ss(A, B)`. For the same reason, a hint may not pass an
  honest public key `dhpk(get(A))` as the value of such a parameter (see
  [tests/failure/kdf_hint_dh_base_param_honest_key.owl](../tests/failure/kdf_hint_dh_base_param_honest_key.owl)).
- **Term salts.** A term salt never makes a case applicable, even if it has
  secret names somewhere within it.

### 2.5 Checks when a rule is declared

Owl runs the following checks when it reads a rule. For a recursive rule,
checks 1 to 3 are run on each case separately.

1. **Well formed.** The where clause is a well-formed proposition. The salt,
   ikm, and info typecheck using the case's indices and parameters. The
   outputs are uniform name types.
2. **Every parameter is used.** Every index and bytestring parameter of a
   case appears in its salt, ikm, or info. This makes sure that the inputs of
   an instance determine its parameters. See
   [tests/failure/kdf-scope-unused-idx.owl](../tests/failure/kdf-scope-unused-idx.owl)
   and
   [tests/failure/kdf-scope-unused-dvar.owl](../tests/failure/kdf-scope-unused-dvar.owl).
3. **The rule is tied to its scope.** At least one key position of the case
   holds a key from *this* scope: a base `kdfkey` of the scope, a `kdfkey`
   derived by a rule of the scope, or `dh_ss(A, B)` where `A` and `B` are
   both DH names of the scope. Also, no key position may hold a name that is
   *not* such a key. See
   [tests/failure/kdf-scope-no-secret.owl](../tests/failure/kdf-scope-no-secret.owl),
   [tests/failure/kdf-scope-cross-scope-dh.owl](../tests/failure/kdf-scope-cross-scope-dh.owl),
   and
   [tests/failure/kdf_scope_foreign_derived_salt.owl](../tests/failure/kdf_scope_foreign_derived_salt.owl).
   A rule that has a `dh_ss` atom must be declared with `odh`.
4. **No key cycle through the outputs** (section 2.7).
5. **Disjointness.** No two instances may share the same input while either
   of them is applicable. Concretely, for every pair of cases `a` and `b`,
   with separate fresh indices and parameters, the solver must prove

   ```
   not ( where_a /\ where_b /\ (applicable_a \/ applicable_b)
         /\ salt_a == salt_b /\ ikm_a == ikm_b /\ info_a == info_b )
   ```

   Owl checks this both within one rule and between rules:

   - **Self-disjointness:** two *different* instances of the same rule (with
     different index or bytestring arguments) never have equal inputs.
   - **Cross-disjointness:** an instance of one rule never has the same input
     as an instance of another rule of the same scope.

   Each new rule is checked against itself and against every rule of the
   scope that was checked before it, so every pair of rules is checked once.
   The query also assumes a few facts about how names in key positions
   compare to each other; section 8 ("Comparing names as names") explains
   them and section 9 states them precisely.

   For example, `kdf L(a, b) : k, a ++ b, 0x` fails self-disjointness: the
   arguments `(0x12, 0x34)` and `(0x1234, 0x)` give the same ikm. See
   [tests/failure/kdf-scope-self-disjoint-ikm.owl](../tests/failure/kdf-scope-self-disjoint-ikm.owl)
   and
   [tests/failure/kdf-scope-dup-sii.owl](../tests/failure/kdf-scope-dup-sii.owl).

### 2.6 Rules may not refer to each other in an endless chain

Rules can refer to each other: the salt of one rule can be the output of
another, and a recursive rule refers to its own earlier steps. A derived name
is only well defined if following these references always ends at base names
after finitely many steps. Owl checks this when it reads the scope.

Say that there is a *reference* from rule `L` to rule `M` whenever `KDF<M<..>>`
appears in the salt, ikm, or info of a case of `L`. (A rule may not hide such
a reference inside a `func`, so that Owl can find all references by reading
the rule's text.) References that are not part of a cycle are unrestricted.
For a reference from `L` to `M` that is part of a cycle:

- both `L` and `M` must be recursive rules;
- the reference must point to an instance that comes earlier in a fixed
  order. Each instance has a rank: the pair (value of its recursion index, position of its rule in the
  declaration order). The rank must strictly decrease along the reference,
  comparing first by index and then by position.

In terms of syntax, this means that the index `e` that the reference puts in
`M`'s recursion position must be one of the following:

| in the succ case of `L` (`i = succ(i')`) | in the zero case of `L` (`i = 0`) |
|---|---|
| `i'`, for any `M` (the previous step) | |
| `0`, for any `M` (the first step) | `0` or `i`, if `M` is declared before `L` |
| `i`, if `M` is declared before `L` (the same step, in an earlier rule) | |

These tests show rejected references:
[rec_kdf_self_ref.owl](../tests/failure/rec_kdf_self_ref.owl),
[rec_kdf_mutual_same_index.owl](../tests/failure/rec_kdf_mutual_same_index.owl),
[rec_kdf_mutual_zero_forward.owl](../tests/failure/rec_kdf_mutual_zero_forward.owl),
[rec_kdf_mutual_succ_index.owl](../tests/failure/rec_kdf_mutual_succ_index.owl),
[rec_kdf_mutual_foreign_index.owl](../tests/failure/rec_kdf_mutual_foreign_index.owl),
[rec_kdf_mutual_nonrec.owl](../tests/failure/rec_kdf_mutual_nonrec.owl).

### 2.7 No key cycles through output types

A **key cycle** happens when a key is used to protect a value that the key
itself depends on, for example when a key encrypts itself. Standard
encryption security says nothing about such situations, so Owl must rule
them out.

Owl's soundness argument replaces the names in a protocol by fresh random
values, one at a time. It needs an order in which each name comes after:

- every name its value is derived from, and
- every key whose plaintext type mentions it.

Section 2.6 makes sure the derivations can be ordered. This check makes sure
that the output types of rules do not create a cycle when combined with the
derivations.

The **plaintext positions** of an output name type are the payload types of
`enckey`, `st_aead` (not its additional data), and `mackey`. Owl looks
through structs, enums, refinements, and type abbreviations to find them. In
these positions, the outputs of a rule `L` may not mention:

- a **base name** that is among the inputs of `L`, or among the inputs of any
  rule that `L` is (directly or indirectly) derived from. See
  [tests/failure/key_cycle_kdf_output_salt.owl](../tests/failure/key_cycle_kdf_output_salt.owl)
  and
  [key_cycle_odh_output_exponent.owl](../tests/failure/key_cycle_odh_output_exponent.owl).
- a **derived name** `KDF<M<e>>`, where `M` is a rule that `L` is derived from
  (including `L` itself). There are two exceptions:
  - The derived name is a *later* output of the same instance (see below).
  - `L` and `M` are recursive rules that refer to each other (or `M` is `L`),
    and the index `e` at `M`'s recursion position is `succ^n(i)`, where `i`
    is `L`'s recursion index. This is allowed when:
    - `n >= 1`, so the mentioned name belongs to a later step; or
    - `n = 0` and `M` is declared after `L`; or
    - `n = 0`, `M` is `L`, and the mentioned output is a later output.

  See
  [tests/failure/key_cycle_rec_kdf_output_zero.owl](../tests/failure/key_cycle_rec_kdf_output_zero.owl)
  and
  [key_cycle_rec_kdf_mutual_output.owl](../tests/failure/key_cycle_rec_kdf_mutual_output.owl).

The outputs of one instance are ordered: output `j` may mention output `j'`
of the same instance only if `j' > j`. Without this order, an output could
encrypt itself, or two outputs could encrypt each other. See
[tests/failure/key_cycle_kdf_output_self.owl](../tests/failure/key_cycle_kdf_output_self.owl),
[key_cycle_kdf_output_siblings.owl](../tests/failure/key_cycle_kdf_output_siblings.owl),
and
[key_cycle_rec_kdf_output_earlier_sibling.owl](../tests/failure/key_cycle_rec_kdf_output_earlier_sibling.owl).

A name counts as mentioned wherever a value of the type could depend on it:
in `Name(..)`, but also in a label, a refinement, or the condition of a case
type.

[tests/success/key_cycle_ok_shapes.owl](../tests/success/key_cycle_ok_shapes.owl)
and [key_cycle_ok_later_sibling.owl](../tests/success/key_cycle_ok_later_sibling.owl)
list shapes that are still allowed.

---

## 3. Calling the KDF

There are three ways to talk about a KDF output in a program: a runtime
`kdf` call, a ghost `gkdf` term, and a derived name.

### 3.1 Runtime calls: `kdf<hints; kinds; j>(salt, ikm, info)`

Examples:

```
kdf<L1<i@n>(e), L1_bad<i@n>(e); kdfkey || enckey; 0>(s, k, 0x)
kdf<L_step<succ(i)>; kdfkey; 0>(k_prev, 0x, 0x02)
kdf<; kdfkey; 0>(C0, e_init, 0x)
```

- **`hints`** is a comma-separated list of rule instances, and may be empty.
  The hints tell Owl which rule the programmer expects the call to match.
  They are ghost information: the compiled call is just the HKDF primitive
  applied to three bytestrings. A call can list several hints when it matches
  different rules in different branches of the typechecker (for example,
  after a `corr_case`). All hints must belong to the same scope, and each
  must have output kinds equal to `kinds`. See
  [tests/failure/kdf-hints-incompatible-nks.owl](../tests/failure/kdf-hints-incompatible-nks.owl),
  [kdf-wrong-nks-count.owl](../tests/failure/kdf-wrong-nks-count.owl), and
  [kdf-wrong-nks-kind.owl](../tests/failure/kdf-wrong-nks-kind.owl).
- **`kinds`** is the `||`-separated list of the kinds of the outputs, and
  **`j`** chooses which output this call computes.

### 3.2 Ghost terms: `gkdf<kinds; j>(salt, ikm, info)`

`gkdf` describes the bytestring that a `kdf` call computes, without running
it. It has type `Ghost`. In the SMT solver it is
`KDF(salt, ikm, info, start, seg)`: `start` is the total length of the
outputs before output `j`, and `seg` is the length of output `j`. In other
words, the call's result is the slice of the KDF's output that belongs to
output `j`.

### 3.3 Derived names: `KDF<L<idxs>(args); kinds; j>`

This is the name of output `j` of the rule instance `L<idxs>(args)`. Its name
type is output `j` of the rule, with the indices and arguments filled in.
`kinds` must be the kinds of the rule's outputs (see
[tests/failure/kdf-wrong-nks-annotation.owl](../tests/failure/kdf-wrong-nks-annotation.owl)).
A derived name can be used just like any other Owl name.

---

## 4. Typing a `kdf` call

A call `kdf<H; nks; j>(a, b, c)` has salt `a`, ikm `b`, and info `c`.
Typechecking it has one of three outcomes. In each case, the result type `T`
carries this refinement:

```
x : T { |x| == |nks[j]|  /\  x == gkdf<nks; j>(a, b, c) }
```

That is, the result has the length of output `j`, and its value is the
corresponding KDF output.

**Outcome 1: everything is public.** If the salt, every ikm atom, and the
info are all public, the result has type `Data<adv>`. A KDF of public inputs
is a public function of those inputs, so the adversary can compute the
result too. An atom counts as public if its type flows to `adv`, or if its
type is `shared_secret(n, m)` and `n` or `m` is corrupt. Owl does not look at
the hints in this case.

**Otherwise, some input is secret**, and the call must meet these
conditions:

- the info is public;
- `H` contains at least one hint;
- the salt and each ikm atom is either public, or a *key of the hinted scope
  in a key position*. That means a `kdfkey` of the scope (judged by its
  type), or a DH shared secret (a `shared_secret` value or a `dh_combine`)
  that involves a DH key of the scope.

The reason for the last condition is that a KDF does not hide its inputs in
general. Only the keys in key positions are protected, by the cryptographic
assumptions of section 8, and the keys of another scope are only covered by
that other scope's rules. Without this condition, Owl could treat a KDF of
secret data as public, or give a value a second name when a rule of another
scope already names it. See
[tests/failure/kdf_oob_secret_ikm_public.owl](../tests/failure/kdf_oob_secret_ikm_public.owl),
[kdf_oob_secret_info_public.owl](../tests/failure/kdf_oob_secret_info_public.owl),
[kdf_oob_cross_scope_key.owl](../tests/failure/kdf_oob_cross_scope_key.owl),
[kdf_oob_cross_scope_odh.owl](../tests/failure/kdf_oob_cross_scope_odh.owl),
and
[kdf_cross_scope_param_key.owl](../tests/failure/kdf_cross_scope_param_key.owl).

Given these conditions, one of the next two outcomes must hold.

**Outcome 2: a hint matches.** A hint `h = L<is>(es)` *matches* when it
selects a case (section 2.1), and the solver can prove, in the current
context, that

```
where  /\  applicable  /\  a == salt  /\  b == ikm  /\  c == info
```

for that case. In words: the instance is allowed by the where clause, it is
applicable, and the call's arguments are exactly its inputs. The result then
has type `Name(KDF<h; nks; j>)`. For a `strict` output, the type also records
that the name is secret (`sec(..)`); for a `public` output, that it is
corrupt (`corr(..)`). If more than one hint matches, disjointness (section
2.5) guarantees that they refer to the same instance, and Owl uses the first
one.

**Outcome 3: no rule matches.** Otherwise, the solver must prove that the
call matches *no* applicable instance of *any* rule in the hinted scope. That
is, for every case of every rule in the scope:

```
forall params.  not ( where /\ applicable /\ a == salt /\ b == ikm /\ c == info )
```

Owl first tries to prove this for the whole scope in one query. If that
fails, it tries the rules one at a time, so that the error message can name
the rules that it could not rule out (see
[tests/failure/kdf_inj_genuine_overlap.owl](../tests/failure/kdf_inj_genuine_overlap.owl)).

When this outcome holds, the call uses the scope's keys on an input that no
rule of the scope covers. The adversary learns nothing about the inputs from
the output of such a call (section 8), so Owl can safely give the result the
type `Data<adv>`.

**If neither outcome 2 nor outcome 3 can be proved, the call is a type
error.** This usually happens because a label or an equality is not decided
in the current branch of the typechecker. The typical fix is to add a
`corr_case` or `pcase` before the call. (Arguments with a conditional type,
such as the result of `dh_combine`, are split into cases automatically, as
for every cryptographic operation.)

---

## 5. Worked examples

### 5.1 A non-recursive chain

From [tests/success/kdf-enc.owl](../tests/success/kdf-enc.owl):

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
    corr_case k in
    let ek = kdf<L1_enc;enckey;0>(get(k), 0x, 0x01) in
    let c  = aenc(ek, get(alice1)) in
    output c to endpoint(bob);
    let k2  = kdf<L1_kdf;kdfkey;0>(get(k), 0x, 0x02) in
    let ek2 = kdf<L2_enc;enckey;0>(0x, k2, 0x01) in
    let c2  = aenc(ek2, get(alice2)) in
    output c2 to endpoint(bob);
    ()
```

- `L1_enc` and `L1_kdf` have the same salt `k` but different info strings.
  The cross-disjointness check tells them apart because `0x01 != 0x02`.
- `corr_case k` splits the typechecker into two branches: one where `k` is
  secret and one where it is corrupt.
- When `k` is secret, the `L1_kdf` call matches its hint: the instance is
  applicable because its salt `k` is secret. So `k2` gets the type
  `Name(KDF<L1_kdf;kdfkey;0>) { sec(..) }`. The `L2_enc` call then matches as
  well, because `k2` has the value of that name, and the instance is
  applicable through its ikm.
- When `k` is corrupt, every input is public, and both calls get the type
  `Data<adv>`.

### 5.2 A recursive chain

From [tests/success/rec_kdf_chain.owl](../tests/success/rec_kdf_chain.owl):

```owl
kdf_scope KChain {
    name k0 : kdfkey @ alice

    rec_kdf<i> L_step<i>
        | 0        : k0,                          0x, 0x02
        | succ(i') : KDF<L_step<i'>; kdfkey; 0>,  0x, 0x02
        -> strict kdfkey
}

def step_i<i>(k_prev : Name(KDF<L_step<i>; kdfkey; 0>)) @ alice
    : if sec(KDF<L_step<i>; kdfkey; 0>) then Name(KDF<L_step<succ(i)>; kdfkey; 0>) else Data<adv> ||kdfkey|| =
    corr_case KDF<L_step<i>; kdfkey; 0> in
    kdf<L_step<succ(i)>; kdfkey; 0>(k_prev, 0x, 0x02)
```

- **No endless chain (section 2.6):** the succ case refers to `L_step` at
  `i'`, the previous step.
- **Self-disjointness** checks three pairs of cases:
  - zero case against zero case: this case has no parameters, so there is
    nothing to check;
  - succ case against succ case: `KDF<L_step<i'>>` and `KDF<L_step<i''>>`
    must differ when `i' != i''`;
  - zero case against succ case: `k0` must differ from a derived name.

  The last two follow from comparing names as names (section 8).
- **In `step_i`,** the hint `L_step<succ(i)>` selects the succ case with
  `i' := i`. The salt of that case is exactly the name in the type of the
  argument `k_prev`. The instance is applicable when
  `sec(KDF<L_step<i>>)` holds, which the `corr_case` decides. In the branch
  where the previous key is corrupt, all inputs are public, and the result is
  `Data<adv>`.

---

## 6. The SMT theory

Owl proves most facts about KDFs by passing them to an SMT solver. This
section lists the declarations and axioms that it gives the solver.

A reminder about how the solver uses quantified axioms: an axiom
`forall x. P(x)` is only used when the solver sees a term that matches one of
the axiom's **triggers** (patterns). Choosing triggers carefully matters. A
trigger that is too broad can cause a *matching loop*, where each use of an
axiom creates a new term that triggers it again, forever.

### 6.1 Declarations and axioms for each rule

For every rule `L` with parameters `p` (the indices, then the bytestrings),
Owl declares two functions:

```
%kdf_L : Index^k x Bits^m x Int -> Name        output j of the instance L(p) is the name %kdf_L(p, j)
%app_L : Index^k x Bits^m -> Bool              the instance L(p) satisfies its where clause and is applicable
```

Once the rule has passed its declaration checks, it gets the following
axioms. The first group has one axiom per rule and output `j`, triggered by
the term `%kdf_L(p, j)`:

| Name in SMT | Statement | Meaning |
|---|---|---|
| `kdf_kind_L_j` | `HasNameKind(%kdf_L(p, j), kind_j)` (which fixes the length of its value) | output `j` has the `j`th name kind of the rule |
| `kdf_label_L_j` | `not %app_L(p)  ==>  Flows(LabelOf(%kdf_L(p, j)), adv)`; for a `public` output, `Flows(LabelOf(..), adv)` | a non-applicable (or `public`) output is corrupt |
| `kdf_flows_L_j` | `where_L(p) ==>` the flow axioms of output `j`'s name type (as for a base name) | output `j` gets the label flows of its name type |
| `kdf_tag_L_j` | `(%app_L(p) ==> %kdftag_S(v) = id_L)  /\  (%kdftag_S(v) = id_L \/ %kdftag_S(v) = 0)`, with `v = ValueOf(%kdf_L(p, j))` and `S` the scope of `L` | an applicable output is tagged `L`, and is not the output of any other rule |
| `kdf_self_disj_L` | `(%app_L(p) \/ %app_L(q)) /\ ValueOf(%kdf_L(p, j)) == ValueOf(%kdf_L(q, j'))  ==>  p = q /\ j = j'` | an applicable output comes from exactly one instance and output index |

The second group has one axiom per *case* (section 2.1), quantified over that
case's parameters. For a recursive rule, the instance in these axioms is
`%kdf_L(IndexZero, ..)` or `%kdf_L(IndexSucc(i'), ..)`:

| Name in SMT | Statement | Meaning |
|---|---|---|
| `kdf_app_L_c` | `%app_L(p) = (where(p) /\ applicable(p))`, triggered by `%app_L(p)` | defines applicability for case `c` |
| `kdf_valueof_L_c_j` | `where(p) ==> ValueOf(%kdf_L(p, j)) = KDF(salt(p), ikm(p), info(p), start_j, seg_j)`, triggered by `%kdf_L(p, j)` | the value of output `j` is the KDF of case `c`'s inputs |

Because the succ-case axioms are triggered only by a literal `IndexSucc(..)`
term, the solver unfolds a recursive rule only as far as the `IndexSucc`
terms that already appear in the query. An instance of a non-uniform rule at
a plain variable stays opaque.

**The tag function `%kdftag_S`.** We want to say that different rules never
produce the same value. Stating this directly would need one axiom for every
pair of rules. Instead, for each scope `S`, the function `%kdftag_S(v)`
returns the identifier of the rule of `S` that has an applicable instance
with value `v`, or `0` if there is none. Every base name `n` gets
`%kdftag_S(ValueOf(n)) = 0`. This needs only one axiom per rule. The
cross-disjointness check (section 2.5) is what makes `%kdftag_S` well
defined: an applicable instance of `L` never has the value of an instance of
another rule of `S`, or of a base name. There is one tag function per scope,
because rules of different scopes are never compared with each other
(section 8).

**Corruption flows down a chain automatically.** Thanks to `kdf_label`, the
programmer does not need to write `corr` declarations for derived names. A
derived name can only be secret if its instance is applicable, that is, if
some key position is secret. See
[tests/success/kdf_generated_corr_chain.owl](../tests/success/kdf_generated_corr_chain.owl)
and
[kdf_generated_corr_param_rule.owl](../tests/success/kdf_generated_corr_param_rule.owl).
The opposite direction, that a `strict` output of an applicable instance is
secret, is *not* an axiom. It appears instead in the type of a matched call
(section 4) and in `kdf_label_lemma` (section 7).

A rule that has been registered but not yet checked only has its two
functions declared, and no axioms.

**Triggers for quantified `corr` declarations.** A quantified `corr`
declaration, such as `corr<i> [KDF<LA<i>; ..>] ==> [a<succ(i)>]`, is
triggered by its conclusion `Flows(l2, adv)`, as long as the conclusion
mentions every bound variable.

**Triggers for user `forall`s.** A user proposition `forall i:idx. P` or
`forall x:bv. P` is given one explicit trigger: the largest subterm of `P`
that applies an uninterpreted function and mentions the bound variable. The
prelude's `eq` function counts, so a fact `x != t(i)` is triggered by the
equation `x == t(i)` itself. An `exists` gets no trigger. Triggers only limit
when the solver uses a hypothesis, so they can never make a false query
succeed.

### 6.2 Prelude

These axioms live in [prelude.smt2](../prelude.smt2) and are the same for
every protocol:

| Name in SMT | Statement |
|---|---|
| `kdf_length` | `i, j >= 0 ==> len(KDF(x, y, z, i, j)) = j` |
| `MinKDFSliceLen` | an uninterpreted security parameter, in bytes. `|kdfkey|`, `|enckey|`, and `|mackey|` are assumed to be at least this long. `NonceLength` is not tied to it |
| `kdf_collision_resistant_on_large_slices` | `i, i' >= 0 /\ j, j' >= MinKDFSliceLen /\ KDF(a, b, c, i, j) == KDF(a', b', c', i', j')  ==>  a == a' /\ b == b' /\ c == c'`, triggered by the `eq` term |
| `isconstant_neq_name` | `IsConstant(x) ==> x != ValueOf(n)` |
| `isconstant_crh`, `isconstant_concat` | hashes and concatenations of constants are constants |
| `valueof_name_inj` | `ValueOf(n1) == ValueOf(n2) ==> n1 = n2` |
| index axioms | `IndexPred(IndexSucc(x)) = x`, `IndexToNat(IndexZero) = 0`, `IndexToNat(IndexSucc(x)) = IndexToNat(x) + 1 >= 1` |

#### The collision resistance axiom

`kdf_collision_resistant_on_large_slices` states collision resistance: if two
KDF output slices are equal, their inputs are equal. The solver uses it when
it sees an explicit equality between two KDF terms. The guards on the slice
lengths keep the axiom believable. A short slice can collide with
non-negligible probability, so short slices get no such guarantee.
`--extract` prints the largest value that `MinKDFSliceLen` can take, given
the concrete key sizes.

**Keeping the theory consistent.** Several axioms say that some function is
injective: `kdf_collision_resistant_on_large_slices`, `valueof_name_inj`, the
generated `self_disj_*` and `kdf_self_disj_*` axioms, and `eq_concat`. These
axioms can only all be true while nothing limits how many `Bits` values of a
given length there are. (An injective function cannot map infinitely many
inputs into a finite set.) So facts about exhaustiveness may only be stated
under a `HasType` guard, and the solver option `smt.mbqi` stays off. The
prelude states this rule at its top. The test
[tests/failure/smt_theory_consistent.owl](../tests/failure/smt_theory_consistent.owl)
(and its `_secret_branch` twin) ends with `assert(false)`. If the theory ever
becomes inconsistent, this test typechecks, and the test suite reports the
problem.

**There is no general KDF disequality axiom.** In the plain model, nothing
can be concluded about the value of a KDF whose inputs are all public. So
every fact of the form "a KDF output differs from X" has a guard: either
applicability (`kdf_tag`, `kdf_self_disj`), or the premise of
`secret_neq_lemma` (section 7).

---

## 7. Related ghost lemmas

These lemmas are ghost code: they have no effect at run time, and only add
facts for the solver to use.

- **`kdf_inj_lemma(x, y)`** gives the collision-resistance fact from
  `kdf_collision_resistant_on_large_slices` for two given `gkdf` terms of the
  same kind, and for the `gkdf` terms nested inside their inputs. The solver
  finds these facts on its own through the axiom; the lemma lets a proof
  state them explicitly. Like the axiom, it only applies to slices
  longer than `MinKDFSliceLen`, and gives nothing for shorter slices.
- **`secret_neq_lemma(x, w)`** says that a value the adversary can compute
  is not a secret. One of the two arguments (in either position) must be
  public: its type flows to `adv`, or it is a DH secret with a corrupt
  exponent, or it is a `gkdf` term whose inputs are all public. Owl splits
  the other argument into the atoms of its concatenation (if it is one). For
  each atom that is `get(n)`, for a base or derived name `n`, the lemma gives
  `sec(n) ==> x != w`. For each atom that is `dh_ss(m, n)` of base names, it
  gives `sec(m) /\ sec(n) ==> x != w`. The lemma may be called inside a
  `forall x:bv`. A bound bitstring has type `Ghost`, so it never counts as the
  public argument. See
  [tests/success/secret_neq_lemma.owl](../tests/success/secret_neq_lemma.owl),
  [secret_neq_lemma_secret_target.owl](../tests/success/secret_neq_lemma_secret_target.owl),
  [secret_neq_lemma_derived_target.owl](../tests/success/secret_neq_lemma_derived_target.owl),
  and `secret_neq_lemma_ghost_arg` and `secret_neq_lemma_no_public_arg` in
  `tests/failure`.
- **`dh_exp_lemma<s, n>(y)`** takes a public `y`, a base DH name `s`, and a
  base name `n` (any indices of `n` that are left out are quantified over).
  It gives `sec(s) /\ n != s ==> dh_combine(y, get(s)) != get(n)`: raising a
  public value to a secret exponent does not produce another base name. If
  `n` is secret, this follows because `n` is uniformly random; if `n` is
  public, it follows from the hardness of inverse DH. See
  [tests/success/dh_exp_lemma.owl](../tests/success/dh_exp_lemma.owl).
- **`cross_dh_lemma<N>(x)`** takes a public `x`. For every `dh_ss(A, B)` atom
  in a rule of `N`'s scope, it gives
  `sec(N) /\ N != A /\ N != B ==> dh_combine(x, get(N)) != dh_ss(A, B)`.
- **`kdf_label_lemma<KDF<L<..>; kinds; j>>()`** gives
  `sec(KDF<L<..>>) ==> where /\ applicable`, and for a `strict` output also
  the reverse direction. The reference must select a case (section 2.1). See
  [tests/success/kdf_label_lemma.owl](../tests/success/kdf_label_lemma.owl)
  and
  [tests/failure/kdf_label_lemma_bare_nonuniform.owl](../tests/failure/kdf_label_lemma_bare_nonuniform.owl).
- **`is_constant_lemma(e)`, `pcase P`, `corr_case n`** work as elsewhere in
  Owl.

---

## 8. Assumptions and soundness notes

### Cryptographic assumptions

Owl works in the **plain model**: the KDF is not modeled as a random oracle.
Instead, Owl assumes that the KDF is:

- a **PRF** in its salt: with a secret salt, its outputs look random;
- a **dual PRF** in its ikm: with a secret key in the ikm, its outputs look
  random;
- **PRF-ODH** secure: when the ikm contains the DH combination of two secret
  DH names, its outputs look random, even if the adversary can query the KDF
  on other DH values;
- **collision resistant**.

Collision resistance is assumed for output *slices*: two slices of at least
`MinKDFSliceLen` bytes, at any offsets, are equal only if their inputs are
equal (section 6.2). This is somewhat stronger than collision resistance of
the whole output.

There is **no** random-oracle assumption and no preimage-resistance
assumption. A KDF whose salt and ikm are both public is just a fixed public
function, and nothing can be concluded about its output.

### Where names come from

A KDF output only gets a name type through a matched hint, and a hint only
matches an applicable instance. This is why every distinctness fact can be
guarded by applicability. It is also why a corrupted chain becomes public
automatically: its rule instances are not applicable, so they cannot match
the chain's KDF calls, and those calls are typed as public.

### Disjointness

The declaration checks establish that two different instances, at least one
of them applicable, never have the same `(salt, ikm, info)`. By collision
resistance, they then have different values. This is what `kdf_self_disj` and
`kdf_tag` assert.

The security proof is a *hybrid argument*: it replaces the outputs of each
applicable instance by fresh random values, one step at a time. Disjointness
makes sure that the replaced value is not also the output of some other
instance, which would still need to see the real value.

### Comparing names as names

The disjointness query (section 2.5) treats names in key positions as
distinct objects without asking whether they are applicable. Specifically,
it assumes that two instances of one rule with different parameters are
different names, and that a derived name is different from a base name.

The justification is an induction over the order of section 2.6:

- An instance without bytestring parameters has the same value no matter
  which names are corrupted. So a collision that shows up only when the
  instance is not applicable would also show up when it is applicable, and
  the declaration check rules that out.
- An instance with bytestring parameters can collide while not applicable
  only if the adversary chooses the parameter. In that case, neither
  instance gets a name type.

These facts are used only to prove that rules are disjoint. They are never
given to the solver anywhere else.

### Well-founded names

Recursive rules and recursive base names are only sound because:

- every chain of references from a concrete instance is finite (sections 1.3
  and 2.6), and
- no key encrypts a name that it is derived from (section 2.7).

The hybrid argument over a chain of `n` derived names takes `n` PRF,
dual-PRF, or ODH steps, and the security losses of the steps add up. This
relies on two assumptions about the meta-theory:

- Index terms are unary (`succ(succ(...))`), so a party running in time `t`
  can only mention indices of depth at most `t`.
- A def whose argument has type `Name(KDF<L<i>>)` is only ever called with a
  value produced by an honest chain of `i` steps.

### Out-of-bounds calls

A call that Owl has refuted against every rule of its scope (outcome 3 in
section 4) is typed as public. Here is why that is safe. Such a call is a
query to the KDF with the scope's keys, on an input that no rule instance
uses. In the security game for the relevant assumption — PRF for a salt key,
dual PRF for an ikm key, or PRF-ODH for a DH pair — the reduction can answer
such a query. And rule disjointness guarantees that the output is not one of
the named outputs.

This argument only covers secret inputs that are keys *of the hinted scope*
in a key position. A KDF hides nothing about its other inputs, so all other
inputs must be public. Refutation only considers the hinted scope, so a call
keyed by another scope's key is rejected, not refuted.

### Scopes are independent

Owl never checks rules of different scopes against each other for
disjointness, so it asserts nothing about how their values relate. What stops
one value from getting a name in two scopes is the condition on calls
(section 4): every secret input must be a key of the hinted scope. Suppose
`L1(..)` in scope `S1` and `L2(..)` in scope `S2` had the same inputs, each
applicable through a key of its own scope. Then a call matching `L1` would
have the key of `S2` among its inputs. That key is neither public nor a key
of `S1`, so the call is rejected.

### Labels of derived names

A derived name can only be secret if its instance is applicable
(`kdf_label`). However, a user `corr` declaration that flows *into* a derived
name is not checked against the rule. A flow that contradicts a `strict`
output makes the context of a matched call inconsistent. **This is a known
gap.** For example, with `corr [x] ==> [KDF<L;kdfkey;0>]`, where `x` is
corrupt and the key of `L` is secret, a matched call asserts both `sec` and
`corr` of the derived name, and after that anything typechecks.

Rejecting every `corr` declaration into a `strict` output would close the
gap. But WireGuard declares twenty such flows and needs them: `init.owl`
fails without them. Nor are all of them implied by non-applicability
(`L3_corr(x)` is applicable when `x == get(psk)`). So fixing the gap first
requires changing the WireGuard model.

### Known gap: "a derived name is not a base name"

The declaration-time disjointness query assumes two facts about the
identity of names in key positions *without any guard*:

- the value of a derived name differs from the value of every base name;
- derived names of different rules have different values.

The induction under "Comparing names as names" does not justify these facts
in every situation. It fails when the keys involved are corrupt and the
derived name belongs to a rule with a bytestring parameter. Consider:

```owl
kdf M(x)  : k, x, 0x01 -> kdfkey
kdf L3(x) : KDF<M(x);kdfkey;0>, k2, 0x -> strict enckey Name(secretmsg)
kdf L4    : kp, k2, 0x -> public enckey Name(secretmsg)
```

`L3` and `L4` are disjoint only if `get(KDF<M(x)>) != get(kp)`. Now suppose
`k` and `kp` are corrupt and `k2` is secret. Then `M(x)` is not applicable,
`x` is chosen by the adversary, and both `L3(x)` and `L4` are applicable
through `k2`. In this situation, the fact says that the adversary cannot find
an `x` with `KDF(k, x, 0x01) = kp`, where `k` and `kp` are public. That is a
preimage-resistance claim, which the plain model does not make. An adversary
who could find such an `x` would get a single value that is a `strict` secret
key under `L3(x)` and a public key under `L4`. The checker accepts this
scope, and a complete program that derives a key under `L3(x)` and outputs
the `L4` value typechecks.

Guarding the two facts by secrecy (requiring `sec` of the derived name, or of
the base name) rejects both the scope and the program. But it also rejects
the double ratchet when its scope is declared: comparing `LB_bad(s)` with
`LB` compares the base salt `r0` with a derived salt, and the situation with
a corrupt chain and an adversary-chosen `s` is exactly the one above. So the
code has not been changed. The open design question is whether to:

- accept the base-name fact based on a PRF plus collision-resistance
  argument, restricted to uniform base names of at least
  security-parameter length; or
- require such rules to be separated by their `info`.

### Other known gaps

- Rule labels must be unique across scopes only within one module.
- The flow axioms of a recursive `nametype` are not supported. (Only
  recursive base names are.)

---

## 9. Typing rules

This section states the typing rules semi-formally. The notation is:

- `G |- P` means that the solver proves `P` in the current context `G`.
- `sec(n) := not ([n] <= adv)`.
- `cases(L)` are the cases of rule `L` (section 2.1). Each case is a tuple
  `(params, inst, W, (salt, ikm, info), app)`: its parameters, the instance
  it defines, its where clause, its inputs, and its applicability (section
  2.4).
- The ikm of a call is `b = b_1 ++ ... ++ b_p`.
- `scopeKey_S(e)` means that `e` is a key of scope `S` in a key position
  (section 4).
- In the out-of-bounds rule, `split(cases(L))` splits a case further when it
  refers to a non-uniform recursive rule at one of its own index variables
  `i`: it becomes one case with `i = 0` and one with `i = succ(i')`, so that
  the solver can see the inputs of the referenced instance.

**Selecting a case.** A reference `h` selects the case whose instance
matches it:

```
h = L<is>(es)      (xs, inst, W, (s, k, c'), app) in cases(L)      inst[xs := ts] = h
-------------------------------------------------------------------------  (kdfInstAt)
caseAt(h) = (W, (s, k, c'), app)[xs := ts]
```

**Outcome 1: all inputs are public.**

```
G |- a <= adv     forall i. pub(b_i)     G |- c <= adv
-------------------------------------------------------------------------  (all public)
G |- kdf<H; nks; j>(a, b, c) : R(Data<adv>)

where pub(e) := G |- e : T, T <= adv,   or   G |- e : shared_secret(n, m) and G |- corr(n) \/ corr(m)
```

**Outcome 2: a hint matches.**

```
h in H     caseAt(h) = (W, (s, k, c'), app)     kinds(L) = nks     G |- c <= adv
G |- W /\ app /\ a == s /\ b == k /\ c == c'
G |- a <= adv  or  scopeKey_S(a)          forall i. pub(b_i)  or  scopeKey_S(b_i)
-------------------------------------------------------------------------  (hint)
G |- kdf<H; nks; j>(a, b, c) : R(x : Name(KDF<h; nks; j>) { strictness_j })
```

**Outcome 3: no rule matches.**

```
no hint matches     S the scope of H     G |- c <= adv
forall L in S, (xs, _, W, (s, k, c'), app) in split(cases(L)).
      G |- forall xs. not (W /\ app /\ a == s /\ b == k /\ c == c')
G |- a <= adv  or  scopeKey_S(a)          forall i. pub(b_i)  or  scopeKey_S(b_i)
-------------------------------------------------------------------------  (out of bounds)
G |- kdf<H; nks; j>(a, b, c) : R(Data<adv>)
```

In all three outcomes, the result type carries the refinement

```
R(T) := x : T { |x| == |nks[j]| /\ x == gkdf<nks; j>(a, b, c) }
```

**Disjointness at declaration time.** Here `distinct(A, B)` says that `A`
and `B` are different instances; it only adds something when `A` and `B` are
the same case, since instances of different cases are always different.

```
for all cases A of L and B of L or of a rule checked before L, over fresh parameters:
      G, params |- not ( W_A /\ W_B /\ (app_A \/ app_B) /\ identity(A, B)
                         /\ s_A == s_B /\ k_A == k_B /\ c_A == c_B /\ distinct(A, B) )
-------------------------------------------------------------------------  (disjointness)
L is disjoint

identity(A, B) := for name atoms n of A and m of B:
      n = KDF<M(p)>, m = KDF<M(q)>          get(n) == get(m) ==> p = q
      n, m derived by different rules       get(n) != get(m)
      one derived, one a base name          get(n) != get(m)
```

`identity(A, B)` contains the facts described in section 8 under "Comparing
names as names".

---

## 10. Design decisions

The guiding idea is that a rule is a *definition* of a family of names.
Everything else follows from three things that Owl computes once for each
case: the instance, its inputs, and its applicability. The typechecker builds
propositions from these and hands them to the solver. It does not reason
about KDF terms itself.

Here are the main decisions, each with the alternative it was chosen over:

1. **KDF injectivity is a single prelude axiom**
   (`kdf_collision_resistant_on_large_slices`), triggered by an equality
   between two KDF terms. *Alternative:* the checker unfolds variables,
   derived names, and functions into `gkdf` terms (up to a fixed depth), and
   adds injectivity facts to each query. The axiom states the same fact as
   `kdf_inj_lemma`, and the solver finds the instances it needs through the
   `kdf_valueof` axioms and the `x == gkdf(..)` refinements.
2. **A derived name is a first-class name in SMT**, `%kdf_L(p, j)`. Its value
   is given by `kdf_valueof`, and it is identified by the output index `j`
   instead of by `(start, seg)`. In the AST, a derived name is just the rule
   reference, the kinds, and `j`.
3. **Applicability is a predicate `%app_L(p)`, defined per case**, and it
   includes the where clause. *Alternative:* a family of prelude predicates
   (`KDFSecretInput`, `BitsAreSecretName`, ...) with rules for introducing
   them, plus separate axioms relating them to labels. In the chosen design,
   one axiom defines `%app_L` and one axiom (`kdf_label`) ties it to the
   label.
4. **Disjointness of derived names needs a number of axioms linear in the
   number of rules** (using `%kdftag_S`), rather than one axiom per pair of
   cases.
5. **Applicability is computed on the rule, then instantiated.** A parameter
   in a key position counts when its value *is* a secret `kdfkey` of the
   scope. *Alternative:* a syntactic analysis of where clauses to find
   "pinned" parameters, with a separate check at hint sites to keep hint
   matching and refutation consistent. In the chosen design, they are
   consistent by construction.
6. **A uniform recursive rule has one case.** This removes the need for a
   special rule about `kdf_label_lemma` at a plain index variable, and lets
   such instances unfold at a plain index variable.
7. **A `kdf` call has three outcomes**: all public, a matching hint, or no
   matching rule. *Alternative:* a fourth outcome, a "scope-bound, all-public
   fallback", for a call that provably matches an applicable rule without
   saying which one. In the chosen design, such a call is a type error: its
   hint is missing. There is also no "matched but public" outcome, since a
   match requires applicability.
8. **Refutation is one solver query per call**, not one per rule.
9. **The `odh` keyword is checked** in one direction: a rule with a `dh_ss`
   atom must be declared `odh`.
10. **Names are compared as names only in the declaration-time disjointness
    query** (section 8), where the facts are hypotheses about the name atoms
    of the two cases.
11. **Every call with a secret input must be keyed by its own scope**,
    whether or not it matches a hint, and a rule may not use a name from
    outside its scope as a key. *Alternative:* apply the condition only to
    out-of-bounds calls. With parameters in key positions, that would let
    two scopes name the same value (see
    [tests/failure/kdf_cross_scope_param_key.owl](../tests/failure/kdf_cross_scope_param_key.owl)).
12. **There is one disequality lemma, with no knowledge of KDFs**
    (`secret_neq_lemma`), and no proof hints at a rule declaration.
    *Alternative:* a lemma that unfolds its argument to a `gkdf` term and
    classifies its inputs, usable in a `disjoint_from` block on a rule. That
    block is unsound whatever type it gives the rule's parameters (section
    2.5), and the case studies only need the fact that "a value the adversary
    can compute is not a secret".
13. **`kdf_collision_resistant_on_large_slices` is guarded by an
    uninterpreted security parameter** (section 6.2). So it says nothing
    about short slices, and a later fact about strings of some fixed length
    cannot make it inconsistent.

Two things are the way they are because the alternative was tried and
failed: the label axiom only goes in one direction, and quantified `corr`
flows and user `forall`s have explicit triggers (section 6.1).

Some related changes outside KDFs:

- The prelude has no `concat` associativity axiom, and no unguarded "a KDF
  output is not a constant" axiom (sections 6.1 and 6.2).
- A lemma call whose arguments have conditional types may be the body of a
  `forall`. (Its type is a case split over the lemma's possible types.)
- `0` and `succ(..)` are accepted as function parameters
  (`msg<succ(i)>(..)`).
