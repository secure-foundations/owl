# Issues and Ambiguities with the `kdf_group` Syntax

This document records issues discovered while converting the WireGuard case study
(`tests/wip/wg/`) and the HPKE case study (`tests/wip/hpke`) to the new `kdf_group` syntax
(`tests/wip/kdf_group/`).

## Summary table

| # | Category | Severity | Affects |
|---|----------|----------|---------|
| I1 | Public constant as salt | Syntax gap | `L0` rule in `defs.owl` |
| I2 | DH public key in ikm | Syntax gap | `L0`, `L3` rules |
| I3 | Index-inequality between rules | Soundness risk | `L2`/`L2_corr`, `L5`/`L5_corr` |
| I4 | No catch-all / negation pattern | Expressiveness | Many rules |
| I5 | Implicit honesty via types (C6_dual) | Soundness assumption | `L6` rules |
| I6 | Index-parametric helper functions | Mechanical | `tk1_of_c6`, `tk2_of_c6` |
| I7 | Labels as values in output-type predicates | Syntax gap | `L6` output types |
| I8 | `honest_cx` functions and new label syntax | Mechanical | `defs.owl` |
| I9 | Multi-witness kdf calls | Syntax gap | `init.owl`, `resp.owl` |
| I10 | PSK/no-PSK branch and rule selection | Design reminder | `init.owl`, `resp.owl` |
| I11 | Session-index specificity of C1 | Type precision | `defs.owl` |
| I12 | `dualkdf` keyword removed | Design change | `defs.owl` |
| I13 | Concatenated DH secrets in ODH ikm (HPKE) | Syntax gap | `L_kem<i>`, `L_kem_corr<i>` rules |
| I14 | Function-wrapped DH expressions in ikm (HPKE) | Syntax gap | `L_kem*` rules, `L_sched*` rules |
| I15 | Function-wrapped kdfkey in ikm (`dh_secret_kdf_ikm`) (HPKE) | Syntax gap | `L_sched*` rules |
| I16 | Unindexed ghost label for `AuthDecap_shared_secret` (HPKE) | Mechanical | `defs.owl` |


---

## I1 — Public constant as salt

**Rule:** The `kdf_group` spec says the **salt** argument may contain
`kdfkey`s and hex constants.

**Problem:** WireGuard's first KDF step derives C1 as

```
C1 = KDF(crh(construction()), dhpk(E_init), 0x)
```

where the salt is `crh(construction())` — a collision-resistant hash of a
public string constant.  This is neither a named `kdfkey` nor a bare hex
literal; it is a *computed* public constant.

**Impact:** The rule `kdf L0` in the new `defs.owl` writes

```
kdf L0<i@n> : crh(construction()), dhpk(E_init<i@n>), 0x -> C1<@n>
```

which is outside the stated syntactic envelope.

**Suggested resolution:** Allow arbitrary *public functions of public
values* (i.e., terms whose label is `adv`) in the salt and info positions,
not just literal hex constants.  Alternatively, treat named `func`
definitions that return a constant as sugar for hex constants.

---

## I2 — DH public key in the ikm position

**Rule:** The **ikm** argument may contain `kdfkey`s, DH shared secrets
(`dh_combine(X,Y)`), and hex constants.

**Problem 1 (C1 derivation):** As noted in I1, the ikm for the C1 step is
`dhpk(E_init<i@n>)` — the *public* DH key, not a shared secret.  This is
used as part of the `MixHash`/`MixKey` logic in Noise and is not a secret
at all.

**Problem 2 (C4 derivation):** WireGuard's C3→C4 step (new rule `L3`)
uses the responder's ephemeral *public key* as ikm:

```
C4 = KDF(C3, dhpk(E_resp), 0x)
```

This binds the hash chain to the responder's ephemeral without a DH
exchange.  `dhpk(E_resp)` is a group element in the public part of the
transcript, not a DH shared secret.

**Impact:** The rules `L0` and `L3` both use `dhpk(...)` in the ikm
position, which falls outside the stated categories.

**Suggested resolution:** Add a fourth allowed form for the ikm position:
**DH public keys** (`dhpk(N)` for a group name `N` declared in the
`kdf_group`), distinct from DH shared secrets (`dh_combine(N1,N2)`).  The
security treatment would be that of a regular PRF (no ODH assumption
needed, since no secret is in ikm).

---

## I3 — Index-inequality constraints between rules (L2/L2_corr and L5/L5_corr)

**Problem:** The old ODH declarations had explicit case conditions:

```
odh L2<@n,m> : S_init<@n>, S_resp<@m> -> {salt info.
    (exists i. salt == honest_c2<i,n,m>()) -> strict C3<@n,m> || ...
    <n_eph> n_eph !=idx n /\ (...) -> strict C3_corr || ...
}
```

The second branch carries the constraint `n_eph !=idx n`, which prevents
it from applying when `n_eph = n` (where the first branch already applies).

In the new syntax, the same logic is split into two rules:

```
odh L2<@n,m>          : C2<@n,m>,    dh_combine(S_init<@n>, S_resp<@m>), 0x -> C3<@n,m>
odh L2_corr<n_eph@n,m>: C2<@n_eph,m>,dh_combine(S_init<@n>, S_resp<@m>), 0x -> C3_corr
```

When `n_eph = n`, both rules have the *same* salt type `C2<@n,m>`, so
they **overlap**.  Without an explicit inequality constraint or a
priority/specificity rule, the type checker may be unsound (an adversary
could force the use of `L2_corr` even in the honest case, weakening the
security guarantee).

The same issue arises for `L5 / L5_corr`.

**Suggested resolution (option A):** Add a `where` clause to kdf/odh rules
for index (in)equality constraints:

```
odh L2_corr<n_eph@n,m> where n_eph !=idx n : C2<@n_eph,m>, ...
```

**Suggested resolution (option B):** Adopt a "first match wins" semantics,
where L2 (listed first, more specific) takes priority over L2_corr when
`n_eph = n`.  This requires the rules to be ordered within the group and
the semantics to be documented explicitly.

---

## I4 — No "catch-all" or negation patterns

**Problem:** Several old nametypes had an explicit negation or catch-all
case, for example:

```
nametype C4<@n,m> = kdf {ikm info.
    (exists i,j. ikm == dh_combine(dhpk(E_init<i@n>), E_resp<j@m>)) -> strict C5<@n,m>
    (forall i,j. ikm != ...)                                          -> strict C5_corr
}
```

The new syntax has no way to express "this rule applies only if no other
rule in the group matches".  I3 above is a specific instance of this
general problem.

**Suggested resolution:** Consider adding a `default` or `otherwise` rule
keyword that acts as a catch-all when all other rules for that salt type
fail to match.

---

## I5 — Implicit vs. explicit honesty conditions for C6 (C6_dual semantics)

**Background:** The old design encoded honesty conditions via the
`C6_dual<@n,m>` nametype (a `dualkdf`):

```
nametype C6_dual<@n,m> = dualkdf {salt info self.
    (exists i,j. salt == honest_c6<i,j,n,n,m>()) -> strict C7<@n,m> || ...
    (forall i,j. salt != ...)                      -> strict C7_corr || ...
}
```

The `honest_c6` condition explicitly checked whether the *runtime value*
of the salt equalled an honest derivation.

**In the new design:** Rules `L6` and `L6_corr` use *type-level*
conditions: if the salt has type `C6<@n,m>` (produced only by rule `L5`)
then output is `C7<@n,m>`; if the salt has type `C6_corr` (produced by
`L5_corr`) then output is `C7_corr`.

**Issue:** The type-level guarantee is only as strong as the claim that the
only way to obtain a value of type `C6<@n,m>` is via rule `L5<j@n,m>`.
This claim must be made into a formal invariant of the type system (a
"type provenance" or "capability" property).  If such an invariant is not
enforced, an adversary who manufactures a bitstring that happens to have
the right length/structure could circumvent the condition.

**Suggested resolution:** The `kdf_group` design implicitly relies on
kdfkey types being *unforgeable* (cannot be produced except by the
designated rules).  This should be stated explicitly as a soundness
requirement and enforced in the type system.

---

## I6 — `tk1_of_c6` / `tk2_of_c6` functions need index parameters

**Problem:** The old functions

```
func tk1_of_c6(x, psk) = gkdf<enckey||enckey;0>(gkdf<kdfkey||nonce||enckey;0>(x, psk, 0x), 0x, 0x)
```

used unlabeled `gkdf<type;index>` calls.  In the new syntax, every
`gkdf` call must reference a specific group label, e.g.,
`gkdf<WG_KDF.L6<@n,m>; ...>`.  But `L6` carries index parameters `@n,m`,
so `tk1_of_c6` must be made parametric in `@n,m`:

```
func tk1_of_c6<@n,m>(x, psk) = gkdf<WG_KDF.L7<@n,m>; enckey||enckey; 0>(
    gkdf<WG_KDF.L6<@n,m>; kdfkey||nonce||enckey; 0>(x, psk, 0x), 0x, 0x)
```

This is a mechanical change but requires the function definition syntax to
support index parameters, and the usage sites inside output-type
predicates (inside `kdf_group` rule bodies) to instantiate those indices.

---

## I7 — Passing kdf_group labels as arguments to output-type predicates

**Problem:** The L6 rule's output type references the authentication events
`happened(key_confirm_responder_recv<@m>(tk1_of_c6<@n,m>(L6)))`.  Here
`L6` is being passed as an argument to `tk1_of_c6` to select which gkdf
label to use internally.

The new syntax has no established mechanism for passing kdf_group labels
as values in output-type expressions.  In the old `C6_dual` nametype, the
equivalent used `salt` and `self` bound variables that referred to the
runtime values of the salt and ikm respectively.

**Suggested resolution:** Either

(a) Retain `self`/`salt` binding as in the old nametype syntax, allowing
output-type expressions to reference the inputs to the current rule; or

(b) Introduce a first-class concept of "the current rule label" that can
be referenced inside an output-type expression.

In the new `defs.owl` we write `tk1_of_c6<@n,m>(L6)` as a tentative
notation; the exact mechanism needs to be designed.

---

## I8 — Updating `honest_cx` ghost functions for new label syntax

**Problem:** The `honest_c1` through `honest_c7` functions are used in
proof obligations (`kdf_inj_lemma`, `cross_dh_lemma`, etc.) in `init.owl`
and `resp.owl`.  They use `gkdf<type;index>` calls without labels.  In the
new system every `gkdf` call must carry a group label.

The updated functions `honest_c3`, `honest_c4`, and `honest_c5` reference
multiple nested gkdf calls.  In particular `honest_c4` now calls
`gkdf<WG_KDF.L3<j,n_pk,m>; ...>` but the original L3 rule for C4 has an
index structure `L3<j@n,m>` (where `n` is the initiator and `j@m` is the
responder's ephemeral session).  The exact index assignment in `honest_c4`
needs careful review.

---

## I9 — Multi-witness (multi-label) kdf calls

**Problem:** Several points in `init.owl` and `resp.owl` use a single KDF
call with *two* ODH witnesses simultaneously, e.g.:

```
// Old syntax:
let c5 = kdf<0,1; odh L4<i,j@n,m>[0], odh L4<i,j@n,m2>[1]; kdfkey; 0>(c4, ss, 0x)
```

This says: "the salt `c4` satisfies either the first or the second case of
the C4 nametype, and the corresponding ODH witnesses are L4 for `m` and L4
for `m2`."

In the new syntax, each rule covers one case.  Using two labels in a
comma-separated list (as written in the new `init.owl`)

```
let c5 = kdf<WG_KDF.L4<i,j@n,m>, WG_KDF.L4<i,j@n,m2>; kdfkey; 0>(c4, ss, 0x)
```

is **tentative** — the semantics of a multi-label kdf call is not defined
in the new syntax specification.  The verifier would need to understand
this as "the salt can match either rule; use whichever applies".

**Suggested resolution:** Define a multi-label kdf call as a "disjunctive
witness": the call succeeds if at least one of the listed labels matches
the runtime arguments.  The output type would be the *intersection* of the
output types of the matching rules (or the weakest type that covers all
cases, if they differ).

The affected call sites in the WireGuard translation are:
- `c5` derivation (L4 / L4 for two `m` values)
- `c6` derivation (L5 / L5 for two `m` values)
- `c7`, `tau`, `k0` derivation (L6 / L6_corr for correct vs. wrong C6)
- `tk1`, `tk2` derivation (L7 / L7_corr)
- `C3`, `k1` derivation in the responder (L2 / L2_corr)

---

## I10 — PSK/no-PSK branch and rule selection

**Problem:** The protocol uses `pcase HasPSK?(opsk)` to split into two
branches.  In the HasPSK branch, `L6<@n,m>` (with the PSK in ikm) should
be used.  In the NoPSK branch, `L6_zeros<@n,m>` (with `zeros_32()` in
ikm) should be used.  In `resp.owl` the responder also needs `L6_corr` /
`L6_corr_zeros` when the C6 chain may be incorrect.

In the new `resp.owl`, the NoPSK branch of the `pcase` is left implicit
(the `pcase` creates the two branches, but the kdf calls shown use `L6`
and `L6_corr`).  The full treatment requires four kdf labels:
`L6`, `L6_zeros`, `L6_corr`, `L6_corr_zeros`, selected by the
combination of (HasPSK?, chain-correct?).

**Suggested resolution:** This is not a syntax issue per se, but a reminder
that each `pcase` branch may need to use different group labels.  Nested
`pcase` or `case` expressions should select the appropriate label.

---

## I11 — Nametype C1 index structure and session specificity

**Problem:** In the old design, `nametype C1<@n,m>` was indexed by party
indices `n` and `m`.  But C1 is derived from `crh(construction())` and
`dhpk(E_init<i@n>)`, which depend on the *session* index `i` (not on `m`).

The new design declares `nametype C1<@n>` (without `m`), which is correct
for derivation, but then uses `C1<@n>` as the salt for `odh L1<i@n,m>`,
where `m` reappears.  This means *any* C1 for party `n` (regardless of
which session `i` it was derived in) can serve as the salt for L1, which
is an over-approximation: in reality, only `C1<i@n>` derived in the same
session should be usable as the salt for `L1<i@n,m>`.

**Suggested resolution:** Index C1 by session too: `nametype C1<i@n>`,
and have `L0<i@n>` produce `C1<i@n>` and `L1<i@n,m>` consume `C1<i@n>`.
This requires the session index to thread through the group nametype
declarations, which is currently unsupported in the example syntax.

---

## I12 — Removal of `dualkdf` keyword

**Background:** The old `name psk<@n,m> : C6_dual<@n,m>` used a `dualkdf`
nametype, which signified that the PSK should be placed in the **ikm**
position (not salt position) of the KDF.

**In the new design:** The PSK is declared as `name psk<@n,m> : kdfkey`
and appears in the ikm position of rules `L6` and `L6_zeros`.  The
distinction between "salt position kdfkey" and "ikm position kdfkey" is no
longer encoded in the name's type — it is captured by which rule uses it
and in which argument slot.

**Issue:** If a kdfkey name can appear in *either* position in different
rules, the type system must ensure that a name used as ikm in one rule is
not accidentally used as salt in another rule, or that such cross-use does
not violate the intended security model.  The original `kdf` vs. `dualkdf`
distinction was an explicit guard against this.

**Suggested resolution:** Consider retaining a positional annotation on
name declarations (e.g., `name psk<@n,m> : kdfkey ikm`) to record the
intended argument position, or add a lint check that flags kdfkeys used in
unexpected positions.

---


## HPKE-specific issues

The following issues were discovered while converting the HPKE case study
(`tests/wip/hpke/`) to `tests/wip/kdf_group/hpke/`. Issues I1–I12 (above)
were identified during the WireGuard conversion. Where an HPKE issue is a
new instance of a WireGuard issue, it is cross-referenced below.

---

## I13 — Concatenated DH secrets in the ODH ikm position (HPKE)

**Background:** The WireGuard ODH rules use exactly one DH secret per rule:

```
odh L1<i@n,m> : C1<@n>, dh_combine(E_init<i@n>, S_resp<@m>), 0x -> ...
```

**Problem:** HPKE's KEM step computes:

```
shared_secret = KDF(0x,
    lbl_ikm(kem_suite_id(), eae_prk(), dh(skE<i>, skR) ++ dh(skS, skR)),
    lbl_info(...))
```

The ikm contains the **concatenation** of two DH secrets: `dh_combine(skE<i>, skR)`
and `dh_combine(skS, skR)`.  In the old syntax this was handled by declaring
two separate ODH instances (`odh ss` and `odh se<i>`) and listing both as
witnesses at call sites.

In the new syntax, each `odh` rule has a single `dh_combine(X, Y)` in the
ikm position.  A concatenation of two DH secrets is not a valid ikm pattern
in the stated syntax.

**In the HPKE conversion:** We write:

```owl
odh L_kem<i> : 0x,
    lbl_ikm(kem_suite_id(), eae_prk(), dh_combine(skE<i>, skR) ++ dh_combine(skS, skR)),
    AuthEncap_honest_info<session i>() -> strict SS_t
```

The `dh_combine(X1,Y1) ++ dh_combine(X2,Y2)` concatenated form in the ikm
position is **tentative** and requires a syntax extension.

**Impact:** Rules `L_kem<i>` and `L_kem_corr<i>` are both outside the stated
syntactic envelope.

**Suggested resolution:** Extend the ikm syntax to allow a finite list of
`dh_combine(X, Y)` terms to be concatenated.  The security treatment would
apply the ODH assumption to each DH pair independently (analogous to how the
old multi-witness call applied two ODH assumptions).  Alternatively, add a
dedicated `multi_odh` rule form that explicitly lists multiple DH pairs.

---

## I14 — Function-wrapped DH expressions in the ikm position (HPKE)

**Problem:** Beyond the concatenation issue (I13), the DH secrets in HPKE's
KEM step are further wrapped in `lbl_ikm(suite_id, label_string, ...)`:

```
lbl_ikm(kem_suite_id(), eae_prk(), dh_val)
  = hpke_v1() ++ kem_suite_id() ++ eae_prk() ++ dh_val
```

The actual bytes passed as the ikm to the underlying HKDF Extract call are
a concatenation of public constants with the DH secret bytes.  The new syntax
allows only a bare `dh_combine(X, Y)` in the ikm position of an `odh` rule —
not a function applied to it.

This is distinct from I13 (which concerns multiple DH secrets) and from I2
(which concerns DH *public* keys in ikm): here the ikm is a function of a
DH *secret*, but not directly the secret itself.

**In the HPKE conversion:** We write `lbl_ikm(..., dh_combine(skE<i>, skR) ++ ...)`
as the ikm pattern, treating `lbl_ikm` as a function the rule system must
look through.  This requires a syntax extension.

**Related:** I1 notes a similar issue for public functions in the salt/info
positions.  I14 is the ikm-position analogue for functions applied to
(possibly secret) DH expressions.

**Suggested resolution:** Allow arbitrary *public-prefix-padded* DH expressions
in the ikm position, i.e., `f(dh_combine(X, Y))` where `f` is a public
function (a `func` definition whose arguments are all public except for the
DH secret component).  The type system would strip the public prefix and apply
the ODH assumption only to the DH component.

---

## I15 — Function-wrapped kdfkey in the ikm position (`dh_secret_kdf_ikm`) (HPKE)

**Problem:** In WireGuard, the PSK appears directly as the ikm of the L6 rule:

```owl
kdf L6<@n,m> : C6<@n,m>, psk<@n,m>, 0x -> strict C7<@n,m> || ...
```

In HPKE, the PSK bytes are embedded inside a function call before being used
as ikm:

```
dh_secret_kdf_ikm(psk_bytes) = lbl_ikm(hpke_suite_id(), secret_string(), psk_bytes)
  = hpke_v1() ++ hpke_suite_id() ++ "secret" ++ psk_bytes
```

The actual kdf call uses `dh_secret_kdf_ikm(get(psk))` as the ikm, not the
raw psk bytes.  The new kdf rule syntax for the ikm position allows bare
kdfkey names, bare `dh_combine(X,Y)`, and hex constants.  It does not allow
`f(kdfkey_name)` where `f` is a public function.

**In the HPKE conversion:** We write:

```owl
kdf L_sched_nonce : SS_t, dh_secret_kdf_ikm(psk), base_nonce_kdf_info() -> ...
```

where `dh_secret_kdf_ikm(psk)` is a function application on a kdfkey name.
This is **tentative** and requires a syntax extension.

**Impact:** All six `L_sched_*` rules in `HPKE_KDF` use this pattern.

**Relationship to I12:** I12 notes that the `dualkdf` keyword is removed. I15
is the deeper consequence: in the old `dualkdf` design, `self` referred to the
raw psk bytes and the condition `ikm == dh_secret_kdf_ikm(self)` was an
*explicit* runtime check. In the new design, that check must be expressed as
a structural pattern in the rule, requiring function application in ikm.

**Suggested resolution:** Allow `f(kdfkey_name)` in the ikm position of a kdf
rule, where `f` is a `func` definition whose argument is a kdfkey. The security
model would treat `f(psk)` as ikm, relying on the PRF assumption for the KDF
with that composite ikm. Alternatively, introduce a `wrapped_kdfkey` type for
keys that are always used through a specific wrapper function.

---

## I16 — Unindexed ghost label for `AuthDecap_shared_secret` (HPKE)

**Problem:** The function `AuthDecap_shared_secret(eph)` computes the ideal
KDF output for an arbitrary ephemeral group element `eph`.  In the new syntax,
every `gkdf` call must reference a specific group label, e.g.,
`gkdf<HPKE_KDF.L_kem<i>; kdfkey; 0>(...)`.  But `L_kem<i>` is indexed by a
session `i`, and `AuthDecap_shared_secret` does not take a session index —
it is defined for any `eph`.

In contrast, `AuthEncap_shared_secret<i>()` always has a concrete session index
and can use `HPKE_KDF.L_kem<i>` directly.

**In the HPKE conversion:** We write the tentative notation:

```owl
func AuthDecap_shared_secret(eph) =
    gkdf<HPKE_KDF.L_kem; kdfkey; 0>(...)
```

where `HPKE_KDF.L_kem` without an index means "the KEM rule at any session".

**Impact:** The `adr_shared_secret_inj` ghost field in `AuthDecapResult`
and the `kdf_inj_lemma` calls in `AuthDecap` rely on `AuthDecap_shared_secret`
being well-defined. At the point where `choose_idx i` gives a concrete index,
using `L_kem<i>` inside `AuthDecap` itself (for `shared_secret_ghost`) is
possible — but the top-level ghost function definition still lacks a concrete
index.

**Relationship to I6 (WireGuard):** I6 notes that `tk1_of_c6` / `tk2_of_c6`
needed index parameters in the new syntax. I16 is the dual problem: a ghost
function that should ideally be *index-polymorphic* rather than parametric
in a fixed index.

**Suggested resolution:** Either

(a) Make `AuthDecap_shared_secret` parametric in `i` (mirroring
`AuthEncap_shared_secret<i>`), accepting that callers must supply a session
index even when it is existentially quantified; or

(b) Introduce a `gkdf<Group.Label_family; type; index>(...)` form where
`Label_family` refers to a family of indexed labels (e.g., all instances of
`L_kem<i>` for any `i`), with the semantics that the ghost value is
determined by the runtime arguments regardless of which concrete `i` applies.
