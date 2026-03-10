# Annotated Diff: HPKE `kdf_group` Conversion

This document explains each significant change made when converting the HPKE
case study from `tests/wip/hpke/` to `tests/wip/kdf_group/hpke/`.

---

## `defs.owl`

### 1. DH name declarations moved inside `kdf_group HPKE_KDF`

**Before (`tests/wip/hpke/defs.owl`, lines 16–22):**
```owl
name skR : DH @ receiver
name skE<i> : DH @ sender
name skS : DH @ sender
```

**After:**
```owl
kdf_group HPKE_KDF {
    name skR : DH @ receiver
    name skE<i> : DH @ sender
    name skS : DH @ sender
    ...
}
```

**Reason:** The new `kdf_group` syntax requires all DH names involved in ODH
instances to be declared inside the group. All external references to these
names gain the `HPKE_KDF.` qualifier (e.g., `HPKE_KDF.skR`).

---

### 2. `name psk : psk_t` and `nametype psk_t` replaced by `name psk : kdfkey`

**Before:**
```owl
nametype psk_t = dualkdf {salt info self.
    (info == base_nonce_kdf_info()) -> public nonce |counter|,
    (exists i:idx. salt == AuthEncap_shared_secret<session i>()) /\ info == key_kdf_info() ->
         strict st_aead plaintext_t ...,
    (forall i:idx. salt != AuthEncap_shared_secret<session i>()) /\ info == key_kdf_info() ->
         strict hpke_corr_key_t,
    (info == export_kdf_info()) -> strict nonce
}
name psk : psk_t @ sender, receiver
```

**After:**
```owl
kdf_group HPKE_KDF {
    ...
    name psk : kdfkey // @ sender, receiver
    ...
    kdf L_sched_nonce      : SS_t,      dh_secret_kdf_ikm(psk), base_nonce_kdf_info() -> public nonce |counter|
    kdf L_sched_key        : SS_t,      dh_secret_kdf_ikm(psk), key_kdf_info()        -> strict st_aead ...
    kdf L_sched_export     : SS_t,      dh_secret_kdf_ikm(psk), export_kdf_info()     -> strict nonce
    kdf L_sched_key_corr   : SS_corr_t, dh_secret_kdf_ikm(psk), key_kdf_info()        -> strict hpke_corr_key_t
    kdf L_sched_nonce_corr : SS_corr_t, dh_secret_kdf_ikm(psk), base_nonce_kdf_info() -> public nonce |counter|
    kdf L_sched_export_corr: SS_corr_t, dh_secret_kdf_ikm(psk), export_kdf_info()     -> strict nonce
}
```

**Reason:** The old `dualkdf` nametype encoded two things: (a) that psk goes in
the *ikm* position and (b) conditional outputs depending on `salt` and `info`.
In the new design, (a) is captured by placing `dh_secret_kdf_ikm(psk)` in the
ikm argument of the L_sched_* rules, and (b) is split into six separate rules
(three for correct SS_t, three for corrupted SS_corr_t). The old conditional
on `exists i. salt == AuthEncap_shared_secret<session i>()` is replaced
type-structurally: a value of type `SS_t` can only arise from rule `L_kem<i>`,
implying honest derivation (see ISSUE I5). See also ISSUE I12 and ISSUE I15.

---

### 3. `nametype shared_secret_t` and `nametype shared_secret_corr_t` replaced by group nametypes + rules

**Before (example):**
```owl
nametype shared_secret_t =
    kdf {ikm info self.
        (ikm == dh_secret_kdf_ikm(get(psk))) /\ info == base_nonce_kdf_info()
            -> public nonce |counter|,
        (ikm == dh_secret_kdf_ikm(get(psk))) /\ info == key_kdf_info()
            -> strict st_aead ...,
        (ikm == dh_secret_kdf_ikm(get(psk))) /\ info == export_kdf_info()
            -> strict nonce
    }

nametype shared_secret_corr_t =
    kdf {ikm info self.
        (ikm == dh_secret_kdf_ikm(get(psk))) /\ info == key_kdf_info()
            -> strict hpke_corr_key_t,
        ...
    }
```

**After:**
```owl
kdf_group HPKE_KDF {
    nametype SS_t      : kdfkey  // replaces shared_secret_t
    nametype SS_corr_t : kdfkey  // replaces shared_secret_corr_t
    ...
    kdf L_sched_nonce  : SS_t,      dh_secret_kdf_ikm(psk), base_nonce_kdf_info() -> ...
    kdf L_sched_key    : SS_t,      dh_secret_kdf_ikm(psk), key_kdf_info()        -> ...
    kdf L_sched_export : SS_t,      dh_secret_kdf_ikm(psk), export_kdf_info()     -> ...
    kdf L_sched_*_corr : SS_corr_t, ...
}
```

**Reason:** The old `nametype Cx = kdf { ... }` bundled the type and output
specification together. The new design separates them: `nametype SS_t : kdfkey`
declares an intermediate kdfkey, while the L_sched_* rules specify what each
can be used to derive. The three conditional branches in `shared_secret_t`
(conditioned on `info`) become three separate rules with distinct info patterns.

---

### 4. Old ODH declarations replaced by ODH rules inside the group

**Before (example):**
```owl
odh ss : skR, skS -> { salt info.
    (exists i:idx. info == AuthEncap_honest_info<session i>()) -> strict shared_secret_t,
    (forall i:idx. info != AuthEncap_honest_info<session i>()) -> strict shared_secret_corr_t
}

odh se<i> : skR, skE<i> -> {salt info.
    (info == AuthEncap_honest_info<session i>()) -> strict shared_secret_t,
    (info != AuthEncap_honest_info<session i>()) -> strict shared_secret_corr_t
}
```

**After:**
```owl
kdf_group HPKE_KDF {
    ...
    /* RESOLVED (I13, I14): multi-DH concatenation and lbl_ikm wrapping are valid ikm atoms */
    odh L_kem<i>       : 0x, lbl_ikm(..., dh_combine(skE<i>, skR) ++ dh_combine(skS, skR)),
                         AuthEncap_honest_info<session i>() -> strict SS_t

    odh L_kem_corr<i>  : 0x, lbl_ikm(..., dh_combine(skE<i>, skR) ++ dh_combine(skS, skR)),
                         0x /* placeholder */ -> strict SS_corr_t

    odh L_kem_ss_corr  : 0x, lbl_ikm(..., dh_combine(skS, skR)),
                         0x /* placeholder */ -> strict SS_corr_t
}
```

**Reason:** The old top-level `odh` declarations encoded salt conditions as
runtime predicates. The new syntax places the info value directly in the rule
as a typed pattern. The two old multi-case ODH declarations (`odh ss` and
`odh se<i>`) become three rules:
- `L_kem<i>`: correct case (ephemeral present, info matches session i)
- `L_kem_corr<i>`: wrong-info case for session i (ephemeral present)
- `L_kem_ss_corr`: static-only DH, no matching honest ephemeral

Note the key structural difference from WireGuard: in WG, each ODH step
processes exactly ONE DH secret. In HPKE, the KEM step concatenates two DH
secrets (`dh(skE<i>, skR) ++ dh(skS, skR)`). This requires ISSUE I13.

---

### 5. Reordering: `hpke_corr_key_t` moved before `kdf_group`

**Before:** `hpke_corr_key_t` was defined after the ODH declarations.

**After:** `hpke_corr_key_t` is defined before `kdf_group HPKE_KDF`, because
it is referenced in the output type of rule `L_sched_key_corr` inside the group.
Similarly, `plaintext_t`, `send_counter`, and all `func` definitions are placed
before the group.

**Reason:** The kdf_group rule output types may reference nametypes defined
elsewhere in the file. Those nametypes must either be defined before the group
or be forward-referenced (Owl appears to support forward references for
predicates, as evidenced by WireGuard's `valid_h6` pattern).

---

### 6. `corr` declarations updated to use `HPKE_KDF`-qualified names

**Before:**
```owl
corr<i> [skE<i>] /\ [skS] /\ [psk] ==> [channel_secret]
corr [skR] /\ [psk] ==> [channel_secret]
```

**After:**
```owl
corr<i> [HPKE_KDF.skE<i>] /\ [HPKE_KDF.skS] /\ [HPKE_KDF.psk] ==> [channel_secret]
corr [HPKE_KDF.skR] /\ [HPKE_KDF.psk] ==> [channel_secret]
```

**Reason:** Since the DH key names and psk are now declared inside `kdf_group
HPKE_KDF`, all external references require the `HPKE_KDF.` qualifier.

---

### 7. Ghost functions updated to use group-qualified names and new `gkdf` syntax

**Before (example):**
```owl
func AuthEncap_dh<i>() =
    dh_combine(dhpk(get(skR)), get(skE<i>))
    ++ dh_combine(dhpk(get(skR)), get(skS))

func AuthEncap_shared_secret<i>() =
    gkdf<kdfkey;0>(0x, lbl_ikm(kem_suite_id(), eae_prk(), AuthEncap_dh<session i>()),
                       lbl_info(...))
```

**After:**
```owl
func AuthEncap_dh<i>() =
    dh_combine(dhpk(get(HPKE_KDF.skR)), get(HPKE_KDF.skE<i>))
    ++ dh_combine(dhpk(get(HPKE_KDF.skR)), get(HPKE_KDF.skS))

func AuthEncap_shared_secret<i>() =
    gkdf<HPKE_KDF.L_kem<i>; kdfkey; 0>(0x, lbl_ikm(kem_suite_id(), eae_prk(), AuthEncap_dh<session i>()),
                       lbl_info(...))
```

**Reason:** Ghost `gkdf` calls must reference a specific group label in the new
system. `AuthEncap_shared_secret<i>()` uses `HPKE_KDF.L_kem<i>` to identify
the correct KEM rule. Name references inside these functions also gain the
`HPKE_KDF.` qualifier. See also ISSUE I16 for `AuthDecap_shared_secret`.

---

### 8. `nametype hpke_key_t<i>` updated to use `gkdf` with group label

**Before:**
```owl
nametype hpke_key_t<i> =
    st_aead plaintext_t
        ...
        pattern i. xor(i, gkdf<nonce |counter|;0>(AuthEncap_shared_secret<session i>(),
                                                dh_secret_kdf_ikm(get(psk)),
                                                base_nonce_kdf_info()))
```

**After:**
```owl
nametype hpke_key_t<i> =
    st_aead plaintext_t
        ...
        pattern i. xor(i, gkdf<HPKE_KDF.L_sched_nonce; nonce |counter|; 0>(
                                    AuthEncap_shared_secret<session i>(),
                                    dh_secret_kdf_ikm(get(HPKE_KDF.psk)),
                                    base_nonce_kdf_info()))
```

**Reason:** The unlabeled `gkdf<type;index>` form is replaced by the
label-based `gkdf<group.label; type; index>` form. The label `HPKE_KDF.L_sched_nonce`
identifies the rule that maps an `SS_t`-typed salt and the psk-derived ikm to
a base nonce.

---

### 9. `KDF<...>` references in struct field types updated

**Before (example from `sender.owl`, `AuthEncapResult`):**
```owl
SecName(KDF<kdfkey;0;shared_secret_t>(0x,
    lbl_ikm(..., AuthEncap_dh<session i>()),
    lbl_info(...)))
```

**After:**
```owl
SecName(KDF<HPKE_KDF.L_kem<i>; kdfkey; 0>(0x,
    lbl_ikm(..., AuthEncap_dh<session i>()),
    lbl_info(...)))
```

**Reason:** The old `KDF<type; index; nametype>(...)` syntax referenced a
nametype to identify the KDF step. The new syntax uses a group label
`KDF<group.label; type; index>(...)`. The same change applies to all struct
field types in `AuthEncapResult`, `ContextS`, `AuthDecapResult`, and `ContextR`.

A summary of all KDF reference updates:

| Old form | New form |
|----------|----------|
| `KDF<kdfkey;0;shared_secret_t>(...)` | `KDF<HPKE_KDF.L_kem<i>; kdfkey; 0>(...)` |
| `KDF<kdfkey;0;shared_secret_corr_t>(...)` | `KDF<HPKE_KDF.L_kem_corr<i>, HPKE_KDF.L_kem_ss_corr; kdfkey; 0>(...)` |
| `KDF<nonce \|counter\|;0;nonce \|counter\|>(...)` | `KDF<HPKE_KDF.L_sched_nonce; nonce \|counter\|; 0>(...)` |
| `KDF<enckey;0;hpke_key_t<i>>(...)` | `KDF<HPKE_KDF.L_sched_key; enckey; 0>(...)` |
| `KDF<nonce;0;nonce>(...)` | `KDF<HPKE_KDF.L_sched_export; nonce; 0>(...)` |

---

## `sender.owl`

### 10. All name qualifications (`HPKE_KDF.X`) in sender

**Before:** `get(psk)`, `sec(psk)`, `sec(skR)`, `sec(skS)`, `sec(skE<i>)`,
`dhpk(skE<i>)`, `dhpk(skR)`, `dhpk(skS)` etc.

**After:** `get(HPKE_KDF.psk)`, `sec(HPKE_KDF.psk)`, `sec(HPKE_KDF.skR)`,
`sec(HPKE_KDF.skS)`, `sec(HPKE_KDF.skE<i>)`, `dhpk(HPKE_KDF.skE<i>)`, etc.

**Reason:** Since the DH key names and psk are now declared inside `HPKE_KDF`,
all external references require the qualified form.

---

### 11. KDF call syntax in `AuthEncap` updated

**Before:**
```owl
let shared_secret = kdf<; odh ss[0], odh se<i>[0];kdfkey;0>(0x,
    lbl_ikm(kem_suite_id(), eae_prk(), dh),
    lbl_info(kem_suite_id(), kdfkey_len(), shared_secret_string(), kem_context)) in
```

**After:**
```owl
let shared_secret = kdf<HPKE_KDF.L_kem<i>; kdfkey; 0>(0x,
    lbl_ikm(kem_suite_id(), eae_prk(), dh),
    lbl_info(kem_suite_id(), kdfkey_len(), shared_secret_string(), kem_context)) in
```

**Reason:** The old syntax listed two ODH witnesses (`odh ss[0], odh se<i>[0]`)
separately. The new syntax unifies these into a single group label. Because the
sender knows exactly which session is being used (`<i>`), only `L_kem<i>` (the
correct case) is needed here; no multi-label call is required.

---

### 12. KDF calls in `KeyScheduleS` updated

**Before:**
```owl
let base_nonce = kdf<0;0;nonce |counter|;0>(shared_secret, dh_secret_kdf_ikm(get(psk)), base_nonce_kdf_info()) in
let sk = kdf<1;1;enckey;0>(shared_secret, dh_secret_kdf_ikm(get(psk)), key_kdf_info()) in
let exp = kdf<2;3;nonce;0>(shared_secret, dh_secret_kdf_ikm(get(psk)), export_kdf_info()) in
```

**After:**
```owl
let base_nonce = kdf<HPKE_KDF.L_sched_nonce; nonce |counter|; 0>(shared_secret,
    dh_secret_kdf_ikm(get(HPKE_KDF.psk)), base_nonce_kdf_info()) in
let sk = kdf<HPKE_KDF.L_sched_key; enckey; 0>(shared_secret,
    dh_secret_kdf_ikm(get(HPKE_KDF.psk)), key_kdf_info()) in
let exp = kdf<HPKE_KDF.L_sched_export; nonce; 0>(shared_secret,
    dh_secret_kdf_ikm(get(HPKE_KDF.psk)), export_kdf_info()) in
```

**Reason:** The old `kdf<salt_case; ikm_case; type; index>` format used numeric
indices to identify cases. The new format uses group labels directly. The sender
always uses the correct rules (not corr variants) since it controls session i.

---

## `receiver.owl`

### 13. All name qualifications (`HPKE_KDF.X`) in receiver

Same as Change 10 for `sender.owl`. All occurrences of `skR`, `skS`, `skE<i>`,
`psk` gain the `HPKE_KDF.` prefix.

---

### 14. KDF call in `AuthDecap` uses multi-label form

**Before:**
```owl
let shared_secret = kdf<; odh ss[0], odh ss[1], odh se<i>[0], odh se<i>[1];kdfkey;0>(0x,
    lbl_ikm(kem_suite_id(), eae_prk(), dh),
    lbl_info(kem_suite_id(), kdfkey_len(), shared_secret_string(), kem_context)) in
```

**After:**
```owl
// ISSUE (I9): multi-label kdf call
let shared_secret = kdf<HPKE_KDF.L_kem<i>, HPKE_KDF.L_kem_corr<i>, HPKE_KDF.L_kem_ss_corr; kdfkey; 0>(0x,
    lbl_ikm(kem_suite_id(), eae_prk(), dh),
    lbl_info(kem_suite_id(), kdfkey_len(), shared_secret_string(), kem_context)) in
```

**Reason:** The receiver does not know whether the incoming ephemeral key
matches an honest session and whether the info matches the correct session.
The four old ODH witnesses (`odh ss[0]`, `odh ss[1]`, `odh se<i>[0]`,
`odh se<i>[1]`) become three labels (two cases for the ephemeral DH path
plus the static-only path). This is a multi-label call (see ISSUE I9).

---

### 15. `gkdf` call for `shared_secret_ghost` updated

**Before:**
```owl
let shared_secret_ghost = gkdf<kdfkey;0>(0x,
    lbl_ikm(kem_suite_id(), eae_prk(), dh),
    lbl_info(kem_suite_id(), kdfkey_len(), shared_secret_string(), kem_context)) in
```

**After:**
```owl
// At this point we have a concrete i from choose_idx, so L_kem<i> is appropriate
let shared_secret_ghost = gkdf<HPKE_KDF.L_kem<i>; kdfkey; 0>(0x,
    lbl_ikm(kem_suite_id(), eae_prk(), dh),
    lbl_info(kem_suite_id(), kdfkey_len(), shared_secret_string(), kem_context)) in
```

**Reason:** Ghost gkdf calls must reference a specific group label. We use
`L_kem<i>` since at this point we have a concrete session index from
`choose_idx`. The `kdf_inj_lemma` call that follows is unchanged in form.

---

### 16. `sk` derivation in `KeyScheduleR` uses multi-label call

**Before:**
```owl
let sk = kdf<1;1,2;enckey;0>(shared_secret, dh_secret_kdf_ikm(get(psk)), key_kdf_info()) in
```

**After:**
```owl
// ISSUE (I9): multi-label call — shared_secret may be SS_t (case 1=hpke_key_t)
// or SS_corr_t (case 2=hpke_corr_key_t). Both L_sched_key and L_sched_key_corr
// are listed as witnesses.
let sk = kdf<HPKE_KDF.L_sched_key, HPKE_KDF.L_sched_key_corr; enckey; 0>(shared_secret,
    dh_secret_kdf_ikm(get(HPKE_KDF.psk)), key_kdf_info()) in
```

**Reason:** The receiver does not know at this point whether the shared_secret
has type `SS_t` (correct case, yielding `hpke_key_t`) or `SS_corr_t` (wrong
case, yielding `hpke_corr_key_t`). The old syntax expressed this as two case
indices `1,2`. The new syntax uses two labels. See ISSUE I9.

---

## Summary of rule-name correspondences

| Old declaration | New label(s) in `HPKE_KDF` |
|----------------|----------------------------|
| `odh se<i> : skR, skE<i>` (correct info for session i) | `L_kem<i>` |
| `odh se<i> : skR, skE<i>` (wrong info for session i) | `L_kem_corr<i>` |
| `odh ss : skR, skS` (exists i. correct info) | (merged into `L_kem<i>`) |
| `odh ss : skR, skS` (forall i. wrong info) | `L_kem_ss_corr` |
| `nametype shared_secret_t` (base_nonce branch) | `L_sched_nonce` |
| `nametype shared_secret_t` (key branch) | `L_sched_key` |
| `nametype shared_secret_t` (export branch) | `L_sched_export` |
| `nametype shared_secret_corr_t` (base_nonce branch) | `L_sched_nonce_corr` |
| `nametype shared_secret_corr_t` (key branch) | `L_sched_key_corr` |
| `nametype shared_secret_corr_t` (export branch) | `L_sched_export_corr` |
| `nametype psk_t = dualkdf { ... }` | (replaced by `name psk : kdfkey` + L_sched_* rules) |
