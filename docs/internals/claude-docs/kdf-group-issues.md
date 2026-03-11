# Issues and Ambiguities with the `kdf_group` Syntax

This document records issues discovered while converting the WireGuard case study
(`tests/wip/wg/`) and the HPKE case study (`tests/wip/hpke`) to the new `kdf_group` syntax
(`tests/wip/kdf_group/`).

## Summary table

| # | Category | Severity | Affects |
|---|----------|----------|---------|
| ~~I1~~ | ~~Public constant as salt~~ | **Resolved** | `L0` rule in `defs.owl` |
| ~~I2~~ | ~~DH public key in ikm~~ | **Resolved** | `L0`, `L3` rules |
| I3 | Index-inequality between rules | Soundness risk | `L2`/`L2_corr`, `L5`/`L5_corr` |
| ~~I4~~ | ~~No catch-all / negation pattern~~ | **Subsumed by I3** | Many rules |
| I5 | Implicit honesty via types (C6_dual) | Soundness assumption | `L6` rules |
| ~~I6~~ | ~~Index-parametric helper functions~~ | **Resolved** | `tk1_of_c6`, `tk2_of_c6` |
| ~~I7~~ | ~~Labels as values in output-type predicates~~ | **Resolved** | `L6` output types |
| ~~I8~~ | ~~`honest_cx` functions and new label syntax~~ | **Resolved** | `defs.owl` |
| I9 | Multi-witness kdf calls | Syntax gap | `init.owl`, `resp.owl` |
| ~~I10~~ | ~~PSK/no-PSK branch and rule selection~~ | **Resolved** | `init.owl`, `resp.owl` |
| I11 | Session-index specificity of C1 | Type precision | `defs.owl` |
| I12 | `dualkdf` keyword removed | Design change | `defs.owl` |
| ~~I13~~ | ~~Concatenated DH secrets in ODH ikm (HPKE)~~ | **Resolved** | `L_kem<i>`, `L_kem_corr<i>` rules |
| ~~I14~~ | ~~Function-wrapped DH expressions in ikm (HPKE)~~ | **Resolved** | `L_kem*` rules, `L_sched*` rules |
| ~~I15~~ | ~~Function-wrapped kdfkey in ikm (`dh_secret_kdf_ikm`) (HPKE)~~ | **Resolved** | `L_sched*` rules |
| ~~I16~~ | ~~Unindexed ghost label for `AuthDecap_shared_secret` (HPKE)~~ | **Resolved** | `defs.owl` |


---

## ~~I1 — Public constant as salt~~ **[RESOLVED]**

**Resolution:** Any `func` applied to public arguments produces a public result
(label `adv`) and is now allowed in the `salt_expr` and `info_expr` positions.
Additionally, `kdf L0` has been removed: C1 is computed inline at call sites
using an unlabeled `kdf` call, so no `kdf_group` rule for that step is needed.
The remaining instance — `honest_c1<i@n>()` in the salt of `odh L1` — is a
public function of public arguments and is valid under this rule.

~~**Problem:** The salt `crh(construction())` in the C1 derivation was a computed
public constant, not a bare kdfkey or hex literal, so `kdf L0` fell outside the
stated syntactic envelope.~~

---

## ~~I2 — DH public key in the ikm position~~ **[RESOLVED]**

**Resolution:** The `ikm_expr` grammar now allows any **public expression** as
an ikm atom, including `dhpk(N)` for a group DH name `N`.  Since `dhpk(N)` is
public (label `adv`), it requires no ODH assumption; the rule is classified `kdf`
and the security treatment is standard PRF.  Both `L0` (ikm = `dhpk(E_init)`)
and `L3` (ikm = `dhpk(E_resp)`) are valid under the new grammar.

~~**Problem:** `dhpk(N)` — the DH public key — appeared in the ikm position of
rules `L0` and `L3` but fell outside the originally stated categories (kdfkey,
hex constant, dh_combine).~~

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

## ~~I4 — No "catch-all" or negation patterns~~ **[SUBSUMED BY I3]**

**Why this is subsumed:** In WireGuard, I4 is entirely eliminated by the
`kdf_group` design: every correct/corrupted distinction is expressed at the
type level (e.g., `C6<@n,m>` vs `C6_corr` as salt types), so no runtime
negation condition is needed.  C6 and C6_dual have been merged into a single
`C6<@n,m>` kdfkey; the "forall salt ≠ honest" catch-all branch of C6_dual
is replaced by the L6_corr rule whose salt simply has type `C6_corr`.

In HPKE, two instances remain (L_kem_corr<i> and L_kem_ss_corr needing
"info ≠ honest_info"), but both resolve the same way as I3: under priority
semantics (first match wins), rules listed earlier take precedence and later
rules become implicit fallbacks.  No separate `default` keyword is required.

~~**Problem:** The old syntax had explicit negation conditions (`forall i,j. ikm !=
...`) that the new rule syntax could not express. I3 was identified as a specific
instance of this general problem.~~

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

## ~~I6 — `tk1_of_c6` / `tk2_of_c6` functions need index parameters~~ **[RESOLVED]**

**Resolution:** `gkdf` calls use the label-free form `gkdf<type; index>(...)`, so
helper functions like `tk1_of_c6` do not need to reference a specific group label
and do not need to be made parametric in session indices for this reason.  The
functions can remain unindexed (or be indexed only for other reasons).

~~**Problem:** The old functions~~

~~used unlabeled `gkdf<type;index>` calls.  In the new syntax, every `gkdf` call
must reference a specific group label.  But `L6` carries index parameters `@n,m`,
so `tk1_of_c6` must be made parametric in `@n,m`.~~

---

## ~~I7 — Passing kdf_group labels as arguments to output-type predicates~~ **[RESOLVED]**

**Resolution:** `gkdf` calls use the label-free form `gkdf<type; index>(self, ...)`,
where `self` is a bound variable referring to the runtime value of the current
rule's salt.  Helper functions such as `tk1_of_c6` do not need a label argument
to select the right `gkdf` — they take the salt value directly.  No label-passing
mechanism is required.

~~**Problem:** The L6 rule's output type passes `L6` as an argument to `tk1_of_c6`
to select which gkdf label to use internally.  The new syntax had no mechanism
for passing kdf_group labels as values in output-type expressions.~~

---

## ~~I8 — Updating `honest_cx` ghost functions for new label syntax~~ **[RESOLVED]**

**Resolution:** `gkdf` calls use the label-free form `gkdf<type; index>(...)`.
The `honest_c1` through `honest_c7` functions (and the HPKE equivalents) do not
need to reference group labels at all — the ghost value is determined entirely by
the runtime arguments.  No label-threaded rewrite of these functions is required.

~~**Problem:** The `honest_c1` through `honest_c7` functions used `gkdf<type;index>`
calls without labels, and in the new system every `gkdf` call was required to
carry a group label, creating a mechanical rewrite burden and index-assignment
questions for functions like `honest_c4`.~~

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

## ~~I10 — PSK/no-PSK branch and rule selection~~ **[RESOLVED]**

**Resolution:** `pcase P` is a **ghost proof annotation**: it tells the
type checker to split into two branches (one where `P` holds, one where it
does not), but it has no effect on runtime behavior.  Therefore the runtime
KDF call does not need to select a single label per branch.  Instead, all
four applicable labels are listed in a single multi-label call:

```owl
kdf<WG_KDF.L6<@n,m>, WG_KDF.L6_zeros<@n,m>,
    WG_KDF.L6_corr<@n,m>, WG_KDF.L6_corr_zeros; ...; ...>(c6, ikm, 0x)
```

Within each `pcase` branch the type checker can narrow which labels are
consistent with the branch condition (`HasPSK?` true or false) and derive
the appropriate output type.  No source-level branch-specific label
selection is needed.

Note: the soundness of multi-label calls still depends on I9's formal
semantics being defined.

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

## ~~I13 — Concatenated DH secrets in the ODH ikm position (HPKE)~~ **[RESOLVED]**

**Resolution:** The `ikm_expr` grammar now allows `++`-concatenation of ikm
atoms.  Multiple `dh_combine` atoms are valid; the rule is classified `odh` and
the ODH assumption is applied to each DH pair independently.  The HPKE rule

```owl
odh L_kem<i> : 0x,
    lbl_ikm(kem_suite_id(), eae_prk(), dh_combine(skE<i>, skR) ++ dh_combine(skS, skR)),
    AuthEncap_honest_info<session i>() -> strict SS_t
```

is now within the stated syntactic envelope (see also I14).

~~**Problem:** Each `odh` rule was restricted to a single `dh_combine(X, Y)` in
the ikm position; HPKE's KEM step concatenates two DH secrets, which fell outside
the stated syntax.~~

---

## ~~I14 — Function-wrapped DH expressions in the ikm position (HPKE)~~ **[RESOLVED]**

**Resolution:** The `ikm_expr` grammar allows any `++`-concatenation of public
expressions and DH secret atoms.  When a `func` definition (such as `lbl_ikm`)
appears in the `ikm_expr`, the checker expands it; the result is a concatenation
of public atoms and `dh_combine` atoms, all of which are valid.  For example,
`lbl_ikm(kem_suite_id(), eae_prk(), dh_combine(A,B) ++ dh_combine(C,D))`
expands to `pub ++ pub ++ pub ++ dh_combine(A,B) ++ dh_combine(C,D)`, which is
a valid `odh`-rule ikm expression.

~~**Problem:** The old syntax allowed only a bare `dh_combine(X, Y)` in the ikm
position of an `odh` rule; `lbl_ikm(...)` applied to DH secrets fell outside the
stated syntactic envelope.~~

---

## ~~I15 — Function-wrapped kdfkey in the ikm position (`dh_secret_kdf_ikm`) (HPKE)~~ **[RESOLVED]**

**Resolution:** The `ikm_expr` grammar allows `++`-concatenations of public
expressions and kdfkey atoms.  When a `func` definition such as
`dh_secret_kdf_ikm(psk) = hpke_v1() ++ hpke_suite_id() ++ "secret" ++ psk`
appears in the `ikm_expr`, the checker expands it; the result is a sequence of
public atoms followed by a kdfkey atom, all of which are valid.  The rule is
classified `kdf` (no `dh_combine` present) and PRF security applies to the
composite ikm.

~~**Problem:** The old syntax allowed only bare kdfkey names, `dh_combine`, or
hex constants in the ikm position; `dh_secret_kdf_ikm(psk)` — a public function
applied to a kdfkey — fell outside the stated syntactic envelope.~~

---

## ~~I16 — Unindexed ghost label for `AuthDecap_shared_secret` (HPKE)~~ **[RESOLVED]**

**Resolution:** `gkdf` calls use the label-free form `gkdf<type; index>(...)`.
`AuthDecap_shared_secret(eph)` can be defined as:

```owl
func AuthDecap_shared_secret(eph) =
    gkdf<kdfkey; 0>(0x, lbl_ikm(kem_suite_id(), eae_prk(), AuthDecap_dh(eph)),
                       lbl_info(kem_suite_id(), kdfkey_len(), shared_secret_string(),
                       AuthDecap_kem_context(eph)))
```

with no session index and no group-qualified label.  The ghost value is
determined entirely by the runtime arguments `(eph, skR, skS)`.  The tentative
`HPKE_KDF.L_kem` (unindexed label family) notation is not needed.

~~**Problem:** Every `gkdf` call was required to reference a specific group label
such as `gkdf<HPKE_KDF.L_kem<i>; ...>`, but `AuthDecap_shared_secret` takes no
session index `i`, making it impossible to supply a concrete label.~~
