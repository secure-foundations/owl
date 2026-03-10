# Annotated Diff: WireGuard `kdf_group` Conversion

This document explains each significant change made when converting the WireGuard
case study from `tests/wip/wg/` to `tests/wip/kdf_group/wg/`.

---

## `defs.owl`

### 1. DH name declarations moved inside `kdf_group WG_KDF`

**Before (`tests/wip/wg/defs.owl`, lines 30–35):**
```owl
name E_init<i@n> : DH @ Initiator<n>
name E_resp<j@m> : DH @ Responder<m>
name S_init<@n> : DH @ Initiator<n>
name S_resp<@m> : DH @ Responder<m>
```

**After:**
```owl
kdf_group WG_KDF {
    name E_init<i@n> : DH @ Initiator<n>
    name E_resp<j@m> : DH @ Responder<m>
    name S_init<@n>  : DH @ Initiator<n>
    name S_resp<@m>  : DH @ Responder<m>
    ...
}
```

**Reason:** The new `kdf_group` syntax requires all DH names involved in
ODH instances to be declared *inside* the group.  Any use of these names
outside the group must be qualified as `WG_KDF.E_init<i@n>`, etc.  The
group declaration makes the scope of the ODH assumption explicit: only the
DH names listed inside `WG_KDF` participate in the ODH rules of that group.

---

### 2. `name psk<@n,m>` type changed from `C6_dual` to `kdfkey`

**Before:**
```owl
nametype C6_dual<@n,m> = dualkdf {salt info self .
    (exists i:idx,j:idx. salt == honest_c6<...>()) -> strict C7<@n,m> || ...
    (forall i:idx,j:idx. salt != ...)              -> strict C7_corr || ...
}
name psk<@n,m> : C6_dual<@n,m>
```

**After:**
```owl
kdf_group WG_KDF {
    ...
    name psk<@n,m> : kdfkey
    ...
    kdf L6<@n,m>      : C6<@n,m>, psk<@n,m>, 0x -> strict C7<@n,m> || ...
    kdf L6_zeros<@n,m>: C6<@n,m>, 0x00...00,  0x -> strict C7<@n,m> || ...
}
```

**Reason:** The old `dualkdf` nametype encoded two things at once: (a) that
the PSK goes in the *ikm* position of the KDF, and (b) the conditional
security guarantee depending on whether the salt equals `honest_c6<...>()`.
In the new syntax, (a) is captured by placing `psk<@n,m>` in the second
(ikm) argument of the `kdf L6` rule, and (b) is captured type-structurally:
a value of type `C6<@n,m>` can only have been derived via rule `L5`, so
using it as salt in `L6` already implies the honest-derivation condition.
The old `C6_dual` nametype is eliminated entirely; rules `L6`,
`L6_zeros`, `L6_corr`, and `L6_corr_zeros` replace it.

---

### 3. Old `nametype Cx = kdf { ... }` declarations replaced by group nametypes + rules

**Before (example):**
```owl
nametype C7<@n,m> = kdf {ikm info.
    True ->
        strict transp_key_init_send<@n,m>
            ||
        strict transp_key_resp_send<@n,m>
}

nametype C7_corr = kdf {ikm info.
    True ->
        strict transp_key_init_send_corr
        ||
        strict transp_key_resp_send_corr
}
```

**After:**
```owl
kdf_group WG_KDF {
    ...
    nametype C7<@n,m> : kdfkey
    nametype C7_corr  : kdfkey
    ...
    kdf L7<@n,m> : C7<@n,m>, 0x, 0x ->
        strict transp_key_init_send<@n,m> || strict transp_key_resp_send<@n,m>

    kdf L7_corr : C7_corr, 0x, 0x ->
        strict transp_key_init_send_corr || strict transp_key_resp_send_corr
}
```

**Reason:** The old `nametype Cx = kdf { ... }` form bundled the type *and*
the output specification into one declaration.  The new `kdf_group` design
separates these: a `nametype Cx : kdfkey` inside the group declares that
`Cx` is an intermediate kdfkey, while the corresponding `kdf Lx` rule
specifies exactly what salt, ikm, and info values produce a `Cx`-typed
output and what that output's type is.  This separation makes the KDF chain
graph explicit and readable as a sequence of labelled edges.

The same transformation applies to all of C1–C6 and their `_corr` variants.

---

### 4. Old ODH declarations replaced by `odh` rules inside the group

**Before (example):**
```owl
odh L1<i@n,m> :
    E_init<i@n>, S_resp<@m> -> {salt info.
        salt == honest_c1<session i, pid n>() ->
            strict C2<@n,m> || strict st_aead (dhpk(S_init<@n>))
                             aad x. true
                             nonce aead_counter_msg1_C2
}

odh L2<@n,m> :
    S_init<@n>, S_resp<@m> -> {salt info.
        (exists i:idx. salt == honest_c2<...>()) ->
                strict C3<@n,m> || ...
        <n_eph>
        n_eph !=idx n /\ (...) ->
                strict C3_corr || ...
    }
```

**After:**
```owl
kdf_group WG_KDF {
    ...
    odh L1<i@n,m> : C1<@n>, dh_combine(E_init<i@n>, S_resp<@m>), 0x ->
        strict C2<@n,m> ||
        strict st_aead (dhpk(S_init<@n>)) aad x. true nonce aead_counter_msg1_C2

    odh L2<@n,m>          : C2<@n,m>,     dh_combine(S_init<@n>, S_resp<@m>), 0x ->
        strict C3<@n,m> || strict st_aead (Data<adv> |12|) aad x. h3_pred[x] nonce aead_counter_msg1_C3

    odh L2_corr<n_eph@n,m>: C2<@n_eph,m>, dh_combine(S_init<@n>, S_resp<@m>), 0x ->
        strict C3_corr || strict st_aead (Data<adv> |12|) aad x. h3_pred[x] nonce aead_counter_msg1_C3
    ...
}
```

**Reason:** The old `odh` declarations were top-level and encoded the salt
condition (`salt == honest_cx<...>()`) as a runtime predicate.  In the new
syntax, the salt is given as a *typed pattern* (a nametype kdfkey from the
group), which is checked statically.  The multi-case old `odh L2` becomes
two separate rules (`L2` for the correct case, `L2_corr` for the
wrong-index case), making the case split structurally visible.

Note that the `dh_combine(X,Y)` argument now makes the two DH names used in
the ODH assumption explicit at the point of the rule declaration.

---

### 5. New `kdf L3` rule for the C3→C4 step (public-key-in-ikm)

**Before (implicit in `nametype C3<@n,m>`):**
```owl
nametype C3<@n,m> = kdf {ikm info.
    (exists j:idx. ikm == dhpk(get(E_resp<j@m>))) -> strict C4<@n,m> || strict useless_enc,
    (forall j:idx. ikm != dhpk(get(E_resp<j@m>))) -> strict C4_corr || strict useless_enc
}
```

**After:**
```owl
kdf L3<j@n,m>  : C3<@n,m>, dhpk(E_resp<j@m>), 0x -> strict C4<@n,m>  || strict useless_enc
kdf L3_corr<j@m>: C3_corr, dhpk(E_resp<j@m>), 0x -> strict C4_corr || strict useless_enc
```

**Reason:** The C3→C4 step in WireGuard uses `dhpk(E_resp<j@m>)` — the
responder's ephemeral *public key* — as the ikm argument.  This is not a
DH shared secret, so the step is a plain `kdf` rule (not `odh`).  The
condition "ikm is an honest responder ephemeral public key" is now expressed
by the typed pattern `dhpk(E_resp<j@m>)` for the correct case, and the
absence of such a pattern (via a separate `L3_corr` rule using `C3_corr` as
salt) for the incorrect case.  See Issue I2 for the caveat that a DH
public key is not strictly a valid ikm form under the stated syntax rules.

---

### 6. `corr` declarations updated to use `WG_KDF`-qualified names

**Before:**
```owl
corr<i,n,m> [S_init<@n>] /\ [E_init<i@n>] ==> [channel_secret_init_send<@n,m>]
corr<n,m>   [S_resp<@m>]                   ==> [channel_secret_init_send<@n,m>]
corr<j,n,m> [S_resp<@m>] /\ [E_resp<j@m>] ==> [channel_secret_resp_send<@n,m>]
corr<n,m>   [S_init<@n>]                   ==> [channel_secret_resp_send<@n,m>]
```

**After:**
```owl
corr<i,n,m> [WG_KDF.S_init<@n>] /\ [WG_KDF.E_init<i@n>] ==> [channel_secret_init_send<@n,m>]
corr<n,m>   [WG_KDF.S_resp<@m>]                           ==> [channel_secret_init_send<@n,m>]
corr<j,n,m> [WG_KDF.S_resp<@m>] /\ [WG_KDF.E_resp<j@m>] ==> [channel_secret_resp_send<@n,m>]
corr<n,m>   [WG_KDF.S_init<@n>]                           ==> [channel_secret_resp_send<@n,m>]
```

**Reason:** Since the DH key names are now declared inside `kdf_group
WG_KDF`, all external references to them must use the qualified form
`WG_KDF.X`.  The `corr` declarations are the corruption model and must
refer to the same names that appear in the group.

---

### 7. `honest_cx` functions updated to use group labels and qualified names

**Before (example):**
```owl
func honest_c1<i@n_eph>() =
    gkdf<kdfkey;0>(crh(construction()), dhpk(get(E_init<i@n_eph>)), 0x)

func honest_c2<i@n_eph,m>() =
    gkdf<kdfkey||enckey;0>(honest_c1<session i, pid n_eph>(),
        dh_combine(dhpk(get(E_init<i@n_eph>)), get(S_resp<@m>)), 0x)
```

**After:**
```owl
func honest_c1<i@n_eph>() =
    gkdf<WG_KDF.L0<i@n_eph>; kdfkey; 0>(crh(construction()), dhpk(get(WG_KDF.E_init<i@n_eph>)), 0x)

func honest_c2<i@n_eph,m>() =
    gkdf<WG_KDF.L1<i@n_eph,m>; kdfkey||enckey; 0>(honest_c1<session i, pid n_eph>(),
        dh_combine(dhpk(get(WG_KDF.E_init<i@n_eph>)), get(WG_KDF.S_resp<@m>)), 0x)
```

**Reason:** Ghost `gkdf` calls must reference a specific group label in the
new system (analogous to how `kdf` calls reference a label at runtime).
Each `honest_cx` function is updated so that its internal `gkdf` calls
carry the label of the corresponding rule in `WG_KDF`.  Name references
inside these functions also gain the `WG_KDF.` qualifier.

---

### 8. `tk1_of_c6` / `tk2_of_c6` made index-parametric

**Before:**
```owl
func tk1_of_c6(x, psk) = gkdf<enckey||enckey;0>(gkdf<kdfkey||nonce||enckey;0>(x, psk, 0x), 0x, 0x)
func tk2_of_c6(x, psk) = gkdf<enckey||enckey;1>(gkdf<kdfkey||nonce||enckey;0>(x, psk, 0x), 0x, 0x)
```

**After:**
```owl
func tk1_of_c6<@n,m>(x, psk) =
    gkdf<WG_KDF.L7<@n,m>; enckey||enckey; 0>(
        gkdf<WG_KDF.L6<@n,m>; kdfkey||nonce||enckey; 0>(x, psk, 0x),
        0x, 0x)

func tk2_of_c6<@n,m>(x, psk) =
    gkdf<WG_KDF.L7<@n,m>; enckey||enckey; 1>(
        gkdf<WG_KDF.L6<@n,m>; kdfkey||nonce||enckey; 0>(x, psk, 0x),
        0x, 0x)
```

**Reason:** Because the new `gkdf` calls carry group labels with index
parameters (`L6<@n,m>`, `L7<@n,m>`), the functions that call them must
also be parametric in those indices.  See Issue I6 and I7 for the
remaining ambiguity about how these functions are invoked inside the
output-type predicates of the `L6` rules.

---

### 9. `KDF<...>` references in struct field types updated

**Before (in `transp_keys_init`):**
```owl
tki_k_init_send : if init_clean<...> then
    (x:SecName(KDF<enckey||enckey; 0; transp_key_init_send<@n,m>>(tki_c7, 0x, 0x)){...})
    else Data<adv>
```

**After:**
```owl
tki_k_init_send : if init_clean<...> then
    (x:SecName(KDF<WG_KDF.L7<@n,m>; enckey||enckey; 0>(tki_c7, 0x, 0x)){...})
    else Data<adv>
```

**Reason:** The old `KDF<type; index; nametype>(...)` syntax referenced a
nametype to identify which KDF step produced the key.  The new syntax uses
a group label `KDF<group.label; type; index>(...)`.  The label `WG_KDF.L7`
identifies the transport-key derivation step, replacing the old reference
to the `C7<@n,m>` nametype.  A similar change applies to
`transp_keys_resp` and the `transp_key_init_send_corr` / `_corr` variants.

---

### 10. `enum PSKMode` updated to reference group-qualified PSK name

**Before:**
```owl
enum PSKMode<n,m> {
    | HasPSK Name(psk<@n,m>)
    | NoPSK
}
```

**After:**
```owl
enum PSKMode<n,m> {
    | HasPSK Name(WG_KDF.psk<@n,m>)
    | NoPSK
}
```

**Reason:** Since `psk<@n,m>` is now declared inside `WG_KDF`, any
reference to it outside the group uses the qualified name.

---

### 11. `predicate valid_h6` and `predicate h3_pred` updated to use qualified names

**Before:**
```owl
predicate valid_h6(h) =
    exists m:idx,j:idx,...
        h == crh(h6_pre(dhpk(get(S_resp<@m>)), ..., dhpk(get(E_resp<j@m>)), tau))
```

**After:**
```owl
predicate valid_h6(h) =
    exists m:idx,j:idx,...
        h == crh(h6_pre(dhpk(get(WG_KDF.S_resp<@m>)), ..., dhpk(get(WG_KDF.E_resp<j@m>)), tau))
```

**Reason:** These predicates reference the DH names, which are now in the
group.  The predicates themselves remain at top level (not inside the
group) because they are output-type conditions used in AEAD nametypes
(`transp_key_init_send`, etc.) that also remain at top level.

---

## `init.owl`

### 12. All `get(E_init<...>)` etc. qualified to `get(WG_KDF.E_init<...>)`

**Before:** `get(E_init<i@n>)`, `dhpk(S_resp<@m>)`, etc.

**After:** `get(WG_KDF.E_init<i@n>)`, `dhpk(WG_KDF.S_resp<@m>)`, etc.

**Reason:** All DH key names are now in the group scope.

---

### 13. `kdf<;;kdfkey;0>(C0, e_init, 0x)` → `kdf<WG_KDF.L0<i@n>; kdfkey; 0>(...)`

**Before:**
```owl
let C1 = kdf<;;kdfkey;0>(C0, e_init, 0x) in
```

**After:**
```owl
let C1 = kdf<WG_KDF.L0<i@n>; kdfkey; 0>(C0, e_init, 0x) in
```

**Reason:** Every kdf call now references a specific group label.  The
unlabeled form `kdf<;;type;index>` is replaced by `kdf<group.label; type;
index>`.  See Issue I1 for the caveat that this step derives C1 from all
public inputs and may require a special treatment.

---

### 14. ODH kdf calls updated: `kdf<;odh L1<i@n,m>[0]; ...>` → `kdf<WG_KDF.L1<i@n,m>; ...>`

**Before:**
```owl
let C2 = kdf<;odh L1<i@n,m>[0]; kdfkey||enckey; 0>(C1, ss_S_resp_E_init, 0x) in
let k0 = kdf<;odh L1<i@n,m>[0]; kdfkey||enckey; 1>(C1, ss_S_resp_E_init, 0x) in
```

**After:**
```owl
let C2 = kdf<WG_KDF.L1<i@n,m>; kdfkey||enckey; 0>(C1, ss_S_resp_E_init, 0x) in
let k0 = kdf<WG_KDF.L1<i@n,m>; kdfkey||enckey; 1>(C1, ss_S_resp_E_init, 0x) in
```

**Reason:** The old syntax separated the salt-case index (the first
semicolon-delimited field) and the ODH witness (`odh L1<...>[0]`).  The new
syntax unifies these into a single group label `WG_KDF.L1<i@n,m>` that
identifies which rule applies.  The output index (0 or 1 for kdfkey vs.
enckey components) remains the last field after the output type.

---

### 15. Multi-witness kdf calls (C5, C6, C7 derivations)

**Before:**
```owl
let c5 = kdf<0,1; odh L4<i,j@n,m>[0], odh L4<i,j@n,m2>[1]; kdfkey; 0>(c4, ss, 0x) in
```

**After (tentative):**
```owl
let c5 = kdf<WG_KDF.L4<i,j@n,m>, WG_KDF.L4<i,j@n,m2>; kdfkey; 0>(c4, ss, 0x) in
```

**Reason:** Some kdf calls used two ODH witnesses simultaneously because the
salt `c4` could satisfy either of two cases in the old `C4<@n,m>` nametype
(one for `m` and one for `m2`).  In the new syntax, this becomes a
"multi-label" call listing both applicable rules.  The semantics of
multi-label calls is unspecified in the new syntax; see Issue I9.

---

### 16. `kdf<0;; enckey||enckey; 0>(c7, 0x, 0x)` → `kdf<WG_KDF.L7<n,m>; enckey||enckey; 0>(...)`

**Before:**
```owl
let k1 = kdf<0;; enckey || enckey; 0>(c7, 0x, 0x) in
let k2 = kdf<0;; enckey || enckey; 1>(c7, 0x, 0x) in
```

**After:**
```owl
let k1 = kdf<WG_KDF.L7<n,m>; enckey || enckey; 0>(c7, 0x, 0x) in
let k2 = kdf<WG_KDF.L7<n,m>; enckey || enckey; 1>(c7, 0x, 0x) in
```

**Reason:** The final transport-key derivation now uses the group label
`L7<n,m>`, which identifies the rule that maps `C7<@n,m>` to the transport
keys.

---

## `resp.owl`

### 17. All name qualifications (`WG_KDF.X`)

Same as Change 12 for `init.owl`.  All occurrences of `E_init`, `E_resp`,
`S_init`, `S_resp`, and `psk` gain the `WG_KDF.` prefix.

---

### 18. `rrs_c2` ghost field updated to use group label `gkdf` calls

**Before:**
```owl
rrs_c2 : (x:Ghost{
    x ==
    gkdf<kdfkey||enckey;0>(
        gkdf<kdfkey;0>(crh(construction()), rrs_msg1_ephemeral, 0x),
        dh_combine(rrs_msg1_ephemeral, get(S_resp<@m>)), 0x)
  })
```

**After:**
```owl
rrs_c2 : (x:Ghost{
    x ==
    gkdf<WG_KDF.L1<n_eph,m>; kdfkey||enckey; 0>(
        gkdf<WG_KDF.L0<n_eph>; kdfkey; 0>(crh(construction()), rrs_msg1_ephemeral, 0x),
        dh_combine(rrs_msg1_ephemeral, get(WG_KDF.S_resp<@m>)), 0x)
  })
```

**Reason:** Ghost constraints inside struct field types that reference
intermediate kdf values must also use the new label-based `gkdf` syntax.

---

### 19. `rrs_c3` field type updated to use `WG_KDF.L2` / `WG_KDF.L2_corr` labels

**Before:**
```owl
rrs_c3 : if resp_stage1_clean<...> then
    if n_pk =idx n_eph then
        SecName(KDF<kdfkey||enckey;0;C3<@n_eph,m>>(rrs_c2, ..., 0x))
    else
        SecName(KDF<kdfkey||enckey;0;C3_corr>(rrs_c2, ..., 0x))
    else (x:Data<adv>{...})
```

**After:**
```owl
rrs_c3 : if resp_stage1_clean<...> then
    if n_pk =idx n_eph then
        SecName(KDF<WG_KDF.L2<n_eph,m>; kdfkey||enckey; 0>(rrs_c2, ..., 0x))
    else
        SecName(KDF<WG_KDF.L2_corr<n_pk,n_eph,m>; kdfkey||enckey; 0>(rrs_c2, ..., 0x))
    else (x:Data<adv>{...})
```

**Reason:** The old form `KDF<type;index;nametype>(...)` referenced the
output nametype to identify the KDF step.  The new form
`KDF<group.label; type; index>(...)` uses the group label directly.

---

### 20. `resp_stage1` derivation of C2 via `WG_KDF.L1`

**Before:**
```owl
let C2 = kdf<;odh L1<i@n,m>[0]; kdfkey||enckey; 0>(C1, ss_msg1_ephemeral_S_resp, 0x) in
let k0 = kdf<;odh L1<i@n,m>[0]; kdfkey||enckey; 1>(C1, ss_msg1_ephemeral_S_resp, 0x) in
```

**After:**
```owl
let C2 = kdf<WG_KDF.L1<i@n,m>; kdfkey||enckey; 0>(C1, ss_msg1_ephemeral_S_resp, 0x) in
let k0 = kdf<WG_KDF.L1<i@n,m>; kdfkey||enckey; 1>(C1, ss_msg1_ephemeral_S_resp, 0x) in
```

---

### 21. `resp_stage1` derivation of C3 uses multi-label call

**Before:**
```owl
let C3 = kdf<0;odh L2<@n,m>[0], odh L2<@n3,m>[1<n>]; kdfkey || enckey; 0>(C2, ss, 0x) in
let k1 = kdf<0;odh L2<@n,m>[0], odh L2<@n3,m>[1<n>]; kdfkey || enckey; 1>(C2, ss, 0x) in
```

**After:**
```owl
let C3 = kdf<WG_KDF.L2<n,m>, WG_KDF.L2_corr<n3,n,m>; kdfkey || enckey; 0>(C2, ss, 0x) in
let k1 = kdf<WG_KDF.L2<n,m>, WG_KDF.L2_corr<n3,n,m>; kdfkey || enckey; 1>(C2, ss, 0x) in
```

**Reason:** The responder does not know whether `n =idx n3` at this point,
so it must use both the correct rule (`L2`) and the wrong-index rule
(`L2_corr`) as simultaneous witnesses.  This is a multi-label call; see
Issue I9.

---

## `transp.owl`

### 22. `get(E_init<...>)` references qualified

**Before:**
```owl
pcase exists i:idx. eph == dhpk(get(E_init<i@n>)) ...
assume (sec(channel_secret_resp_send<@n,m>) ==> exists i:idx. eph == dhpk(get(E_init<i@npk>)));
```

**After:**
```owl
pcase exists i:idx. eph == dhpk(get(WG_KDF.E_init<i@n>)) ...
assume (sec(channel_secret_resp_send<@n,m>) ==> exists i:idx. eph == dhpk(get(WG_KDF.E_init<i@npk>)));
```

**Reason:** Same as Change 12.  `transp.owl` does not perform any kdf
calls directly but does reference the DH key names in ghost assertions and
`assume` statements.  All such references are qualified.

---

## Summary of rule-name correspondences

| Old declaration | New label(s) in `WG_KDF` |
|-----------------|--------------------------|
| (C0→C1 step, implicit in init code) | `L0<i@n>` |
| `odh L1<i@n,m>` | `L1<i@n,m>` |
| `odh L2<@n,m>` (correct case) | `L2<@n,m>` |
| `odh L2<@n,m>` (wrong-index case) | `L2_corr<n_eph@n,m>` |
| `nametype C3<@n,m>` (C3→C4 correct case) | `L3<j@n,m>` |
| `nametype C3_corr` (C3→C4 wrong case) | `L3_corr<j@m>` |
| `odh L4<i,j@n,m>` | `L4<i,j@n,m>` |
| (L4 corr case, implicit in old C4_corr) | `L4_corr<i,j@n,m>` |
| `odh L5<j@n,m>` (correct case) | `L5<j@n,m>` |
| `odh L5<j@n,m>` (wrong-index case) | `L5_corr<j,n_eph@n,m>` |
| `name psk : C6_dual` (correct C6 + PSK) | `L6<@n,m>` |
| `name psk : C6_dual` (correct C6 + zeros) | `L6_zeros<@n,m>` |
| `nametype C6_corr` (wrong C6 + PSK) | `L6_corr<@n,m>` |
| `nametype C6_corr` (wrong C6 + zeros) | `L6_corr_zeros` |
| `nametype C7<@n,m>` | `L7<@n,m>` |
| `nametype C7_corr` | `L7_corr` |
