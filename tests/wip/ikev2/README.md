# IKEv2 in Owl

A verified Owl model of a minimal IKEv2 handshake (RFC 5996 / RFC 7296):
IKE_SA_INIT and IKE_AUTH with signature authentication, ending in the keys of
the first Child SA. One fixed suite: ChaCha20-Poly1305, HKDF-SHA256 as the
PRF, Curve25519, RSA-PSS signatures.

| File | Contents |
|---|---|
| [defs.owl](defs.owl) | constants, message formats, KDF scope, signature types, result types |
| [init.owl](init.owl) | `init_main<i@n,m>`: the initiator |
| [resp.owl](resp.owl) | `resp_main<j@m>`: the responder |
| [full.owl](full.owl) | both |
| [spec/](spec/README.md) | the Python functional spec, its tests, and the list of deviations from the RFC |
| [interop/](interop) | runs the extracted Rust against the Python spec |
| [mutants.sh](mutants.sh) | checks that the proof is not vacuous |

```
cabal run owl -- tests/wip/ikev2/full.owl                      # verify (about 20 s)
tests/wip/ikev2/mutants.sh                                      # 16 mutants, all must be rejected
python tests/wip/ikev2/interop/run_interop.py /tmp/ikev2-interop  # needs `cryptography`, cargo
```

## What is proved

**Initiator.** `init_main<i@n,m>` is session `i` of initiator `n`, talking to
responder `m`. It returns `init_result<i,j,n,m,m2>`, where `j` and `m2` are
the session and owner of the key share KEr it received.

- *Authentication:* if `skR<@m>` is secret, then `m2 = m` and KEr is
  `dhpk(E_r<j@m>)`. In words, KEr is the ephemeral of an honest session `j`
  of the intended responder (`ir_ke_r`).
- *Secrecy:* if KEr is that honest ephemeral and both `E_i<i@n>` and
  `E_r<j@m2>` are secret, then the two Child SA keys are the secret names
  `KDF<L_child<i,j@n,m2>(...); ...>`. These keys are derived only from this
  pair of sessions (`ir_k_i2r`, `ir_k_r2i`).

**Responder.** This is dual. `resp_main<j@m>` returns
`resp_result<i,j,n,n2,m>`. Here `n` is the initiator whose key the
responder looked up through IDi, and `n2` owns KEi. If `skI<@n>` is secret,
then `n2 = n` and KEi is `dhpk(E_i<i@n>)`. The keys are secret names under
the same conditions.

These are the usual guarantees of a signed Diffie-Hellman (SIGMA-style)
exchange. The proof does not cover nonce freshness, replay, injective
agreement, or properties of the IKE SA keys after the handshake.

## How the proof works

- **Key schedule** (`kdf_scope IKE`). Rule `L_ike<i,j@n,m>(s, inf)` is the
  single kdf call `kdf(Ni ++ Nr, g^ir, Ni ++ Nr ++ SPIi ++ SPIr)`. That call
  is SKEYSEED followed by prf+, and it yields SK_d, SK_ei, SK_er, SK_pi and
  SK_pr. Rule `L_child` derives KEYMAT from SK_d. Salt and info are public
  rule parameters.
- **One case split per party.** The code first runs `pcase` on whether the
  received key share is an honest ephemeral, then picks its owner with
  `choose_idx`. This follows WireGuard's `on_chain`.
  - In the honest branch, each kdf call matches its `L_ike` hint after
    `corr_case` on the two ephemerals.
  - In the other branch, no rule matches, so the keys are public.
    `cross_dh_lemma` and the DH injectivity axioms rule out every `L_ike`
    instance.
- **Signatures.** Each signing key's type says that the key share in the
  signed IKE_SA_INIT message is one of the signer's ephemerals
  (`init_signed`, `resp_signed`). After `vrfy`, concatenation injectivity
  recovers "KEr is honest" from the received message bytes. Two details make
  this work:
  - The signed octets are built with `++`, nested as
    `(fixed prefix) ++ (ke ++ rest)` (`init_msg1`, `init_octets`, ...).
    Struct constructors are uninterpreted in the SMT theory, but `++` has
    injectivity axioms.
  - `vrfy`'s result is not known to equal the message that was passed in, so
    the code checks `eq(x, octets)` after it. At run time this always holds.
- **Wire format.** Every field has a fixed length, so all IKEv2 length fields
  and payload chains are constants. Each message is a flat struct, as in
  WireGuard. [spec/README.md](spec/README.md) has the full argument.

## Testing against the spec

[interop/run_interop.py](interop/run_interop.py) does the following:

1. Extracts `full.owl` in a scratch copy of `extraction/`.
2. Fills in the abstract defs (random SPIs and nonces, and the ID-to-key
   lookup).
3. Builds the code with cargo.
4. Runs all four pairings of {Owl, Python} initiator and {Owl, Python}
   responder, and checks that both sides agree on the Child SA keys, SPIs and
   ESP SPIs.
5. Checks that the Owl parties reject a tampered message.

All pass. This shows that the verified code computes the same bytes as the
spec. The spec is itself checked against the RFC's key schedule and against
scapy's IKEv2 parser. Verus was not run on the extracted code.

## Issues found in the Owl backend

The harness works around these issues in its scratch copy. The repo's
`extraction/` is not changed.

- `owl_dec_st_aead` passes the nonce through unchanged, but
  `owl_enc_st_aead` zero-pads the counter to 12 bytes. A receiver that passes
  the 8-byte counter it received always fails to decrypt. The Owl code
  therefore pads explicitly with `aead_nonce(iv) = iv ++ 0x00000000`.
  WireGuard's transport code, which passes `ctr` directly, may be affected.
- `SecretBuf::secret_eq` is `todo!()` in `execlib.rs`. Every `eq` on a
  secret-typed value compiles to it, including the check after `vrfy`. The
  harness fills it in with a constant-time comparison.
- `SIGNATURE_SIZE` is hardcoded to 64 (in `preamble.rs` and
  `ExtractionBase.hs`), but the backend signs with RSA-2048, whose
  signatures are 256 bytes. The harness sets it to 256.
- The `|crh|` length is not supported by extraction (`CRH_SIZE`), so Ni and
  Nr use a literal `|32|`.
