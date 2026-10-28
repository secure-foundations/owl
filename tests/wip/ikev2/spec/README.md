# IKEv2: Python functional spec

[ikev2.py](ikev2.py) is a functional spec of a minimal IKEv2 handshake
(RFC 5996, as revised by RFC 7296). Every step in it corresponds to an Owl
operation. It is the reference for the verified Owl model in
[../](../README.md), and [../interop](../interop) tests the extracted Owl
code against it.

```
python3 -m venv venv && venv/bin/pip install -r requirements.txt
venv/bin/python test_ikev2.py
```

## What it covers

```
Initiator                                   Responder
HDR(SA_INIT), SAi1, KEi, Ni           -->
                                      <--   HDR(SA_INIT), SAr1, KEr, Nr
HDR(AUTH), SK{IDi, AUTH, SAi2, TSi, TSr} -->
                                      <--   HDR(AUTH), SK{IDr, AUTH, SAr2, TSi, TSr}
```

It uses one fixed suite and does no negotiation:

| Transform | Choice | Owl primitive |
|---|---|---|
| ENCR | ENCR_CHACHA20_POLY1305 (28) | `st_aead` |
| PRF | PRF_HMAC_SHA2_256 (5) | `kdf` (HKDF-SHA256); `mac` is HMAC-SHA512 (deviation 3) |
| D-H | Curve25519 (31) | `DH` |
| Auth method | Digital Signature (14), RSASSA-PSS/SHA-256 | `sign` / `vrfy` |
| Child SA | ESP, ChaCha20-Poly1305, no ESN | (keys only) |

It leaves out cookies, INVALID_KE_PAYLOAD retries, CERT/CERTREQ, NAT-D,
Notify payloads, EAP, PSK auth, CREATE_CHILD_SA, rekeying and INFORMATIONAL.
Identities are fixed-length ID_KEY_ID values. The initiator is configured with
the responder's ID and verification key. The responder looks up the
initiator's key by ID.

## What the tests check

- **Honest run:** both sides end with the same SK_d, SK_ei, SK_er and Child SA
  keys, and each authenticates the other's ID.
- **Key schedule against the RFC:** SKEYSEED and prf+ are computed literally
  from RFC 5996 §2.13–2.14. The Owl-style single `kdf` call gives byte-identical
  {SK_d, SK_ei, SK_er, SK_pi, SK_pr}.
- **Wire format:** scapy's independent IKEv2 parser reads all four messages
  (header, SA/KE/Nonce, and the decrypted ID/AUTH/SA/TS chain) as intended.
  The header length fields equal the actual lengths. The RFC 7427 A.4.3
  AlgorithmIdentifier is copied from the RFC.
- **Tampering:** every single-bit flip in every message (1276 cases) makes the
  initiator reject. The responder rejects too, except in two expected cases:
  flips to msg4, which arrives after the responder has finished, and the
  X25519 high bit of KEr, which X25519 ignores. A substituted KEi, an unknown
  initiator ID, a wrong responder ID and a wrong responder key are all
  rejected.

## Why this is implementable in Owl (executable part)

The design rule is to **fix every length**. In this profile every field has a
fixed size: SPIs are 8 bytes, the key share is `|group|`, nonces are
32 bytes, IDs are 16 bytes, the signature is `|signature|`, and the
SA/TS payloads are constants. So every IKEv2 length field, Next Payload
chain, header tag and AAD prefix is a constant byte string. Each message is
then a flat Owl `struct` of `Const(...)` fields and `Data<adv> |n|` fields,
the same style as WireGuard's `msg1`/`msg2` in
[../../wg/defs.owl](../../wg/defs.owl). Owl needs no integer-to-bytes
encoding, no variable-length TLV parsing, and no computed lengths. The
`Struct` class in `ikev2.py` mirrors this, and its `parse` returning `None`
corresponds to `parse ... otherwise`.

How each step maps to Owl:

| IKEv2 step | Owl | Precedent |
|---|---|---|
| Ephemeral `E_i`, `E_r` | `name E_i<i@n> : DH` | WG ephemerals |
| SPIs, ESP SPIs, `Ni`, `Nr` | `def get_spi_i<@n>() : Data<adv> \|8\|` etc. (adversary-chosen) | WG `get_sender_i` |
| `g^ir` | `dh_combine(KEr, get(E_i))`, with a `guard is_group_elem(KEr)` | WG |
| SKEYSEED + prf+ → SK_d, SK_ei, SK_er, SK_pi, SK_pr | **one** `kdf<L_ike; kdfkey\|\|enckey\|\|enckey\|\|mackey\|\|mackey; j>(Ni++Nr, g^ir, Ni++Nr++SPIi++SPIr)`, an `odh` rule with a public salt and info | WG `L1`, HPKE |
| MACedIDForI = prf(SK_pi, IDi') | `mac(SK_pi, id_type ++ id)` | |
| AUTH = Sign(RealMessage1 \|\| Nr \|\| MACedID) | `sign(get(skI<@n>), init_octets(...))`; the responder uses `vrfy(vk, …, sig)` | [dhke.owl](../../../success/dhke.owl) (signed DH) |
| SK{...} | `st_aead_enc<ctr_ei<i@n>>(SK_ei, inner, aad)`; IV on the wire = `get_counter`; the receiver calls `st_aead_dec(SK_ei, ct, aad, iv ++ 0^4)` | WG transport |
| AAD = IKE header ++ SK header | `spi_i ++ spi_r ++ const` | WG `msg1` (h3 as aad) |
| Look up the initiator's vk by IDi | `def get_pk_info<@m>(id) : Option ...` | WG `get_pk_info` |
| KEYMAT | `kdf<L_child; enckey\|\|enckey; j>(SK_d, 0x, Ni++Nr)`, a `kdf` rule with a kdfkey salt | WG `L7` |
| Staging | one def per party, `init_main` and `resp_main`; the stages here are the points where it outputs | |

Why the key schedule is exact: HKDF-Extract(salt, ikm) is HMAC(salt, ikm),
which is prf(Ni|Nr, g^ir) = SKEYSEED. HKDF-Expand(PRK, info) is
T(i) = HMAC(PRK, T(i-1) | info | i), which is prf+. Owl's `kdf` already
computes one HKDF stream and slices it per output (see `concretifyCryptOp
CKDF`), so one Owl `kdf` call computes the RFC's IKE SA keys exactly.
SKEYSEED itself is never needed: it would only matter for rekeying.

## Deviations from the RFC

None of these affects the protocol flow. They do matter for
interoperability with a real IKEv2 peer.

1. **Child SA KEYMAT.** The RFC defines it as prf+(SK_d, Ni|Nr), which is
   Expand only. Owl's `kdf` always runs Extract first, so we compute
   prf+(prf(SK_d, ""), Ni|Nr). The fix would be an expand-only primitive in
   Owl, or a `kdf` variant that takes a PRK.
2. **AEAD salt and nonce.** RFC 7634 takes a 4-byte salt along with each
   SK_e (36 bytes of KEYMAT) and uses nonce = salt | IV. Owl's `st_aead`
   pads the counter with zeros (`iv ++ 0^4`). Owl has no 4-byte named
   length, so SK_e here is a plain 32-byte `enckey`. This also shifts where
   SK_pi and SK_pr sit in the stream relative to a real implementation. A
   `nonce |salt|` length plus a `pattern i. salt ++ i` nonce pattern would
   close this gap. HPKE already uses `pattern`.
3. **Backend parameters.** The Owl Rust backend fixes `mac` to HMAC-SHA512
   with 64-byte mackeys, so prf(SK_p, ID') here is HMAC-SHA512 and SK_pi,
   SK_pr are 64 bytes. The negotiated PRF would make them HMAC-SHA256 and
   32 bytes. The spec follows the backend so that the two interoperate.
   The backend's RSA-PSS uses the maximum salt length (222 bytes), while the
   RFC 7427 AlgorithmIdentifier in AUTH says 32. The spec signs with 32 and
   accepts any salt length.
   The IV is the counter in little-endian, which the RFC allows: the IV is
   opaque and sent explicitly.

The spec also omits some receiver checks. It does not check the SA payloads
beyond exact constant matching. It does not check the IKE header's Message
ID beyond fixed constants (0 and 1). It sends no error Notify payloads.
