# The `kdf_group` Declaration

This document explains Owl's `kdf_group` syntax: what it is, why it exists, how
to read and write a `kdf_group` block, and how call sites change.  It is
intended to stand alone as reference documentation.

For a catalogue of known limitations and open design questions, see
`docs/internals/kdf-group-issues.md`.  For worked conversion examples, see the
annotated diffs in `tests/wip/kdf_group/wg/annotated-diff.md` (WireGuard) and
`tests/wip/kdf_group/hpke/annotated-diff.md` (HPKE).

---

## 1. Motivation

Owl's security model for key derivation rests on two cryptographic assumptions:

- **PRF security**: a keyed hash function with a secret key is indistinguishable
  from a random function.
- **ODH (Oracle Diffie-Hellman)**: when the shared Diffie-Hellman secret
  `dh_combine(X, Y)` is used as the input key material of a KDF call, an
  adversary who does not know the secret cannot distinguish the KDF output from
  a uniformly random value, even if given access to a "KDF oracle" that answers
  queries on *other* ikm values.

Both assumptions are scoped: they apply to a **specific named group of keys**.
The `kdf_group` declaration makes that scope explicit and machine-checkable.

### The old design (before `kdf_group`)

Previously, Owl had three separate mechanisms:

1. `nametype Cx = kdf { ikm info self. ... }` — a nametype for a kdfkey whose
   output types are conditional on the salt (`self`), ikm, and info arguments
   of KDF calls that use it.
2. `nametype Cx = dualkdf { salt info self. ... }` — same but the key goes in
   the **ikm** position rather than the salt position.
3. `odh L : A, B -> { salt info. ... }` — a top-level Oracle Diffie-Hellman
   declaration: when `dh_combine(A, B)` appears in the ikm of a KDF call, the
   salt/info conditions determine the output type.

KDF calls used numeric indices to select which nametype case applied:
```owl
kdf<salt_case_index; odh_witness_index; output_type; output_index>(salt, ikm, info)
```

This worked but had several drawbacks:
- The ODH assumption and the nametype conditions were specified in different
  places, making the KDF chain hard to read as a whole.
- Multi-case nametypes required runtime-predicate conditions on the ikm/info,
  which were hard to audit and easy to mis-specify.
- The `kdf` and `dualkdf` distinction encoded a positional constraint (which
  argument the key goes in) in the type, separate from the derivation logic.
- Ghost `gkdf` calls used unparameterized `gkdf<type; index>(...)` forms that
  did not identify which KDF step they corresponded to.

### The new design

A single `kdf_group` declaration collects:
- All DH key names that participate in ODH instances for this group.
- The PSK (if any), declared as a plain `kdfkey`.
- Intermediate kdfkey nametypes (labels for the chained KDF outputs).
- Named rules (`kdf` and `odh`) that specify exactly which salt + ikm + info
  combination produces which output type.

The complete KDF chain for a protocol is then readable as an ordered sequence
of labelled edges in a derivation graph, all in one place.

---

## 2. Declaration syntax

A `kdf_group` block looks like this:

```owl
kdf_group GroupName {

    // ── DH key names ────────────────────────────────────────────────────
    name X : DH @ Locality1
    name Y : DH @ Locality2

    // ── Plain kdfkey names (PSK, etc.) ──────────────────────────────────
    name psk : kdfkey  // @ Locality1, Locality2

    // ── Intermediate kdfkey nametypes ───────────────────────────────────
    nametype Chain1 : kdfkey
    nametype Chain2 : kdfkey
    nametype Chain2_corr : kdfkey   // "junk" variant for wrong-index cases

    // ── Plain KDF rules (no DH secret in ikm) ───────────────────────────
    //   kdf Label : salt_expr, ikm_expr, info_expr -> output_type
    kdf L1 : Chain1, 0x, 0x -> strict Chain2

    // ── ODH rules (DH shared secret in ikm) ─────────────────────────────
    //   odh Label : salt_expr, dh_combine(A, B), info_expr -> output_type
    odh L2<i> : Chain1, dh_combine(X, Y), 0x -> strict Chain2

    // ── Multi-output rules ───────────────────────────────────────────────
    //   Use || to separate multiple simultaneous outputs from one rule
    odh L3 : Chain2, dh_combine(X, Y), 0x ->
        strict Chain3 ||
        strict st_aead (SomeType) aad x. some_pred[x] nonce some_counter

} // end kdf_group GroupName
```

### 2.1 Name declarations inside the group

**DH names** (`name N : DH @ locality`): Any DH key used in an `odh` rule
inside this group must be declared here.  Outside the group, these names are
referenced as `GroupName.N`.

**Plain kdfkey names** (`name k : kdfkey`): Keys that appear in the **ikm**
or **salt** position of `kdf` rules (but not as a DH shared secret) are
declared here.  The pre-shared key (PSK) is a typical example.  Previously
PSKs were declared as `dualkdf` nametypes; they are now plain kdfkeys, with
their usage encoded in the rule that consumes them.

**Intermediate nametypes** (`nametype Cx : kdfkey`): These are labels for
chained KDF outputs — they have no separate runtime storage; they exist only
to give names to the types of intermediate kdfkeys so that rules can reference
them as salt types.  A `_corr` variant is typically provided for each
intermediate type to cover the case where an earlier step in the chain produced
a "junk" value (e.g., a wrong-index DH secret).

### 2.2 Rule declarations

Each rule has the form:

```
(kdf | odh) Label<optional_indices> :
    salt_expr ,
    ikm_expr  ,
    info_expr
    -> output_spec
```

**Label**: An identifier (with optional index parameters) that names this rule.
Outside the group, this label is referenced as `GroupName.Label<indices>`.

**`kdf` vs `odh`**: Use `kdf` when no DH shared secret appears in `ikm_expr`.
Use `odh` when `ikm_expr` contains a `dh_combine(A, B)` term — this triggers
the ODH security assumption for the key pair `(A, B)`.

**`salt_expr`**: The first KDF argument. Allowed forms:
- A nametype kdfkey declared in this group (e.g., `Chain1`).
- A hex constant (e.g., `0x`).
- Any public expression: a `func` applied to public arguments (e.g., `crh(construction())`,
  `honest_c1<i@n>()`).

**`ikm_expr`**: The second KDF argument (the key material). An `ikm_expr` is a
`++`-concatenation of one or more **ikm atoms**, where each atom is one of:

- A **public expression**: a hex constant (`0x`), a DH public key (`dhpk(N)` for
  a group DH name `N`), or any public function applied to public arguments (e.g.,
  `kem_suite_id()`, `lbl_ikm(suite_id, label, 0x)`).
- A **kdfkey name** declared in this group (e.g., `psk`).
- A **DH shared secret**: `dh_combine(A, B)` where `A` and `B` are DH names
  declared in this group.

A single atom with no `++` is the common case. When a `func` definition appears
in the `ikm_expr`, the checker expands it and re-checks the resulting atom
sequence. The `odh` / `kdf` classification follows from the expanded form: a rule
is `odh` if and only if at least one atom is a `dh_combine` term; otherwise it is
a `kdf` rule.

Representative examples:
- `psk` — bare kdfkey atom (`kdf` rule)
- `0x` — hex constant, a public atom (`kdf` rule)
- `dhpk(E_resp)` — DH public key, a public atom (`kdf` rule)
- `dh_combine(A, B)` — single DH secret atom (`odh` rule)
- `dh_combine(A,B) ++ dh_combine(C,D)` — two DH secret atoms (`odh` rule)
- `lbl_ikm(kem_suite_id(), eae_prk(), dh_combine(A,B) ++ dh_combine(C,D))` —
  expands to `pub ++ pub ++ pub ++ dh_combine(A,B) ++ dh_combine(C,D)` (`odh` rule)
- `dh_secret_kdf_ikm(psk)` — expands to `pub ++ pub ++ pub ++ psk` (`kdf` rule)

**`info_expr`**: The third KDF argument. Allowed forms:
- A hex constant (e.g., `0x`).
- Any public expression: a `func` applied to public arguments (e.g., `base_nonce_kdf_info()`,
  `AuthEncap_honest_info<session i>()`).

**`output_spec`**: Describes what type(s) the KDF output has. Forms:
- `-> T` — a single output of type `T`.
- `-> strict T` — the output is a secret name of type `T`.
- `-> public T` — the output is a public name of type `T`.
- `-> strict T1 || strict T2 || ...` — the rule produces multiple simultaneous
  outputs (different index positions); the `||` separates them.

The output types `T` may be any Owl nametype (including `enckey`, `nonce`,
`st_aead`, kdfkey nametypes from this group, etc.) and may reference predicates
and functions defined elsewhere in the file.

---

## 3. Call-site syntax

### 3.1 Runtime KDF calls

Old syntax:
```owl
kdf<salt_case; odh_witnesses; output_type; output_index>(salt, ikm, info)
```

New syntax:
```owl
kdf<GroupName.Label<indices>; output_type; output_index>(salt_val, ikm_val, info_val)
```

The group label replaces both the `salt_case` and `odh_witnesses` fields.
`output_type` and `output_index` remain, identifying which of the rule's
`||`-separated outputs is being extracted.

**Example** (from WireGuard, `init.owl`):
```owl
// Old:
let C2 = kdf<; odh L1<i@n,m>[0]; kdfkey||enckey; 0>(C1, ss_S_resp_E_init, 0x) in
let k0 = kdf<; odh L1<i@n,m>[0]; kdfkey||enckey; 1>(C1, ss_S_resp_E_init, 0x) in

// New:
let C2 = kdf<WG_KDF.L1<i@n,m>; kdfkey||enckey; 0>(C1, ss_S_resp_E_init, 0x) in
let k0 = kdf<WG_KDF.L1<i@n,m>; kdfkey||enckey; 1>(C1, ss_S_resp_E_init, 0x) in
```

### 3.2 Multi-label calls

When the type checker cannot statically determine which of two rules applies
(e.g., because the responder does not know if the incoming ephemeral key belongs
to the correct session), both rules are listed as a comma-separated label set:

```owl
// Tentative syntax — semantics not yet formally defined (see Issue I9):
let C3 = kdf<WG_KDF.L2<n,m>, WG_KDF.L2_corr<n3,n,m>; kdfkey||enckey; 0>(C2, ss, 0x) in
```

The intended semantics is: "the salt satisfies at least one of the listed rules;
use whichever one matches at runtime." The output type is the intersection (most
conservative type) of the matching rules' outputs.

### 3.3 Ghost `gkdf` calls

Old syntax:
```owl
gkdf<output_type; output_index>(salt, ikm, info)
```

New syntax:
```owl
gkdf<GroupName.Label<indices>; output_type; output_index>(salt_val, ikm_val, info_val)
```

Ghost KDF calls appear in `func` definitions, struct field ghost constraints,
and proof obligations.  They use the same label-based syntax as runtime calls.

**Example** (from WireGuard, `defs.owl`):
```owl
// Old:
func honest_c2<i@n_eph,m>() =
    gkdf<kdfkey||enckey;0>(honest_c1<...>(),
        dh_combine(dhpk(get(E_init<i@n_eph>)), get(S_resp<@m>)), 0x)

// New:
func honest_c2<i@n_eph,m>() =
    gkdf<WG_KDF.L1<i@n_eph,m>; kdfkey||enckey; 0>(honest_c1<...>(),
        dh_combine(dhpk(get(WG_KDF.E_init<i@n_eph>)), get(WG_KDF.S_resp<@m>)), 0x)
```

### 3.4 `KDF<...>` type references in struct fields

Old syntax:
```owl
SecName(KDF<output_type; output_index; NameType>(salt, ikm, info))
```

New syntax:
```owl
SecName(KDF<GroupName.Label<indices>; output_type; output_index>(salt_val, ikm_val, info_val))
```

This form appears in struct field type annotations and conditional type
expressions in `if ... then ... else ...` type branches.

**Example** (from WireGuard, `defs.owl`):
```owl
// Old:
tki_k_init_send : if init_clean<...> then
    (x:SecName(KDF<enckey||enckey; 0; transp_key_init_send<@n,m>>(tki_c7, 0x, 0x)){...})

// New:
tki_k_init_send : if init_clean<...> then
    (x:SecName(KDF<WG_KDF.L7<@n,m>; enckey||enckey; 0>(tki_c7, 0x, 0x)){...})
```

### 3.5 External name references

Any name declared inside a `kdf_group` must be qualified outside the group:

```owl
// Inside the group:
name skR : DH @ receiver

// Outside the group (everywhere else in the file):
get(HPKE_KDF.skR)       // get the secret key
dhpk(HPKE_KDF.skR)      // public key expression
sec(HPKE_KDF.skR)       // secrecy predicate
[HPKE_KDF.skR]          // label in corr declarations
```

---

## 4. Where to place the `kdf_group` block

The `kdf_group` block should be placed in `defs.owl`:

- **After** all `func` and `type` definitions that are referenced inside the
  group's rule output types or rule expressions (e.g., helper functions like
  `base_nonce_kdf_info()`, counter declarations, junk-secret nametypes like
  `hpke_corr_key_t`).
- **Before** any top-level `nametype`, `predicate`, or `struct` definitions
  that reference names declared inside the group (using the `GroupName.X`
  qualified form).
- **Before** `corr` declarations that reference group names.

Owl supports forward references in most positions (predicates and functions
used inside rule output types may be defined after the group), consistent with
the WireGuard example where `valid_h6` and `h3_pred` are defined after
`kdf_group WG_KDF`.

---

## 5. Design principles and conventions

### 5.1 One rule per case

Where the old syntax used a single nametype with conditional branches (e.g.,
`kdf { (cond1) -> T1, (cond2) -> T2 }`), the new syntax uses one rule per
case.  The "condition" is expressed structurally: the salt type identifies
which case applies (a `Chain1`-typed salt can only arise from the rule that
produced it), and the info is given as a literal pattern in the rule.

### 5.2 Correct vs. `_corr` rule pairs

For each step in the KDF chain that can produce either a "real" or a "junk"
output (depending on which party's key was used), provide two rules:
- `L_step<indices>`: the correct case, producing the typed-and-useful kdfkey.
- `L_step_corr<...>`: the corrupted/wrong-index case, producing a `_corr`
  kdfkey whose downstream outputs encrypt only `False` (i.e., are never used).

The responder and other parties who may not know which case applies use
multi-label calls (see §3.2).

### 5.3 Naming conventions

- **Group name**: `ALLCAPS_KDF` (e.g., `WG_KDF`, `HPKE_KDF`).
- **Rule names**: short descriptive labels with index parameters matching those
  of the salt type (e.g., `L1<i@n,m>`, `L_kem<i>`, `L_sched_nonce`).
- **Intermediate nametypes**: `C1`, `C2`, ..., `C1_corr`, `C2_corr` (WireGuard
  style), or descriptive names like `SS_t`, `SS_corr_t` (HPKE style).
- **External references**: always `GroupName.name` — never the bare name.

### 5.4 Ghost functions referencing the group

All `func` definitions that compute ghost "honest" KDF values must use the new
label-based `gkdf<GroupName.Label; type; index>(...)` syntax and must qualify
all DH names as `GroupName.X`.  These functions are typically placed after the
`kdf_group` block since they reference `GroupName.*` names.

---

## 6. Comparison with the old syntax

| Old concept | New equivalent |
|-------------|---------------|
| `nametype Cx = kdf { ... }` | `nametype Cx : kdfkey` inside group + `kdf Lx : ...` rule |
| `nametype Cx = dualkdf { ... }` | `name psk : kdfkey` inside group + rules where psk is in ikm |
| `odh L : A, B -> { salt info. cond -> T }` | `odh L : salt_type, dh_combine(A,B), info -> strict T` rule inside group |
| `kdf<s; odh L[i]; type; idx>(...)` | `kdf<GroupName.L; type; idx>(...)` |
| `kdf<s; odh L1[i], odh L2[j]; type; idx>(...)` | `kdf<GroupName.L1, GroupName.L2; type; idx>(...)` *(tentative)* |
| `gkdf<type; idx>(...)` | `gkdf<GroupName.L; type; idx>(...)` |
| `KDF<type; idx; NameType>(...)` | `KDF<GroupName.L; type; idx>(...)` |
| `name N : DH @ loc` (top-level) | `name N : DH @ loc` inside `kdf_group` |
| `name psk : DualKdfType` (top-level) | `name psk : kdfkey` inside `kdf_group` |

---

## 7. Worked examples

### 7.1 WireGuard: `kdf_group WG_KDF`

See `tests/wip/kdf_group/wg/defs.owl` for the complete declaration, and
`tests/wip/kdf_group/wg/annotated-diff.md` for the step-by-step conversion
from the old syntax.

The WireGuard KDF chain has eight steps (L0–L7):

```
C1  = KDF(crh(construction()), dhpk(E_init),   0x)   [kdf L0 — public inputs]
C2  = KDF(C1,  dh(E_init, S_resp),              0x)   [odh L1]
C3  = KDF(C2,  dh(S_init, S_resp),              0x)   [odh L2]
C4  = KDF(C3,  dhpk(E_resp),                    0x)   [kdf L3 — public key in ikm]
C5  = KDF(C4,  dh(E_init, E_resp),              0x)   [odh L4]
C6  = KDF(C5,  dh(S_init, E_resp),              0x)   [odh L5]
C7  = KDF(C6,  psk (or zeros_32),               0x)   [kdf L6 / L6_zeros]
TK  = KDF(C7,  0x,                              0x)   [kdf L7]
```

Key points:
- Each step has exactly one DH secret in ikm (or none for L0, L3, L6, L7).
- The salt at each step is a typed kdfkey from the previous step.
- `_corr` rule variants exist for L2, L3, L4, L5, L6, and L7.

### 7.2 HPKE: `kdf_group HPKE_KDF`

See `tests/wip/kdf_group/hpke/defs.owl` for the complete declaration, and
`tests/wip/kdf_group/hpke/annotated-diff.md` for the step-by-step conversion.

The HPKE KDF chain has two stages:

**KEM stage** (one derivation that combines two DH secrets):
```
shared_secret = KDF(0x,
    lbl_ikm(kem_suite_id, eae_prk, dh(skE<i>, skR) ++ dh(skS, skR)),
    lbl_info(kem_suite_id, kdfkey_len, shared_secret_string, kem_context))
                                                      [odh L_kem<i>]
```

**Key schedule stage** (three derivations from the shared secret):
```
base_nonce = KDF(shared_secret, dh_secret_kdf_ikm(psk), base_nonce_kdf_info())
                                                      [kdf L_sched_nonce]
key        = KDF(shared_secret, dh_secret_kdf_ikm(psk), key_kdf_info())
                                                      [kdf L_sched_key]
export     = KDF(shared_secret, dh_secret_kdf_ikm(psk), export_kdf_info())
                                                      [kdf L_sched_export]
```

HPKE introduces several syntax gaps beyond those seen in WireGuard (issues
I13–I16 in `kdf-group-issues.md`):
- The KEM ikm is a **concatenation** of two DH secrets (I13).
- Both the KEM ikm and the key-schedule ikm are wrapped in public functions
  (`lbl_ikm`, `dh_secret_kdf_ikm`) rather than appearing bare (I14, I15).
- The `AuthDecap_shared_secret` ghost function cannot carry a session index
  for its `gkdf` label (I16).

---

## 8. Known limitations

The following limitations are catalogued in detail in `kdf-group-issues.md`.
The issue numbers below refer to that document.

| # | Summary | Severity |
|---|---------|----------|
| ~~I1~~ | ~~Public computed values (e.g., `crh(f())`) not allowed in salt/info~~ | **Resolved** |
| ~~I2~~ | ~~DH public keys (`dhpk(N)`) not allowed in ikm~~ | **Resolved** |
| I3 | No index-inequality constraints between overlapping rules | Soundness risk |
| I4 | No catch-all / negation pattern for rule conditions | Expressiveness |
| I5 | Implicit honesty via type provenance (replaces old explicit predicates) | Soundness assumption |
| ~~I6~~ | ~~Helper functions in output-type predicates need index parameters~~ | **Resolved** |
| ~~I7~~ | ~~No mechanism to pass a group label as a value in output-type expressions~~ | **Resolved** |
| ~~I8~~ | ~~`honest_cx`-style ghost functions must be updated to use group labels~~ | **Resolved** |
| I9 | Multi-label kdf calls have no formally defined semantics | Syntax gap |
| I10 | PSK/no-PSK branch requires selecting different labels | Design reminder |
| I11 | Session-index specificity of C1-style nametypes | Type precision |
| I12 | `dualkdf` keyword removed; positional annotation may be needed | Design change |
| ~~I13~~ | ~~Concatenated DH secrets in ikm (HPKE)~~ | **Resolved** |
| ~~I14~~ | ~~Function-wrapped DH expression in ikm (HPKE)~~ | **Resolved** |
| ~~I15~~ | ~~Function-wrapped kdfkey in ikm, e.g., `dh_secret_kdf_ikm(psk)` (HPKE)~~ | **Resolved** |
| ~~I16~~ | ~~Unindexed ghost label for index-polymorphic ghost functions (HPKE)~~ | **Resolved** |
