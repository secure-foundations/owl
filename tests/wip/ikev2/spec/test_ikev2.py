"""
Checks for ikev2.py:
  - an honest run succeeds and both sides compute the same keys;
  - the Owl-style key schedule equals RFC 5996's SKEYSEED / prf+ (computed
    here from the RFC text, independently of the kdf helper);
  - the messages are well-formed IKEv2, according to scapy's independent parser;
  - tampering with any byte of any message makes the handshake fail;
  - wrong identities and keys are rejected.

Run: python test_ikev2.py   (needs `cryptography`; `scapy` is optional)
"""

import hashlib
import hmac
import os
import random
import struct

import ikev2 as I


def prf(k, m):
    return hmac.new(k, m, hashlib.sha256).digest()


def rfc_prf_plus(k, s, n):
    """RFC 5996 2.13, written out literally."""
    out, t, i = b"", b"", 1
    while len(out) < n:
        t = prf(k, t + s + bytes([i]))
        out += t
        i += 1
    return out[:n]


def setup():
    sig_i, sig_r = I.SigKey(), I.SigKey()
    id_i, id_r = b"I" * I.ID_LEN, b"R" * I.ID_LEN
    init = I.Initiator(sig_i, id_i, id_r, sig_r.vk)
    resp = I.Responder(sig_r, id_r, {id_i: sig_i.vk})
    return init, resp


def capture(init, resp):
    msgs = {}

    def tap(i, m):
        msgs[i] = m
        return m
    sa_i, sa_r = I.run_handshake(init, resp, tap)
    return sa_i, sa_r, msgs


def test_honest(init, resp):
    sa_i, sa_r, msgs = capture(init, resp)
    assert sa_i is not None and sa_r is not None
    assert sa_i == I.ChildSA(**{**sa_r.__dict__, "peer_id": sa_i.peer_id})
    assert sa_i.peer_id == resp.ident and sa_r.peer_id == init.ident
    for k in ("sk_d", "sk_ei", "sk_er", "esp_key_i2r", "esp_key_r2i"):
        assert len(getattr(sa_i, k)) == 32
    assert len({sa_i.sk_d, sa_i.sk_ei, sa_i.sk_er, sa_i.esp_key_i2r, sa_i.esp_key_r2i}) == 5
    # Length fields in the IKE header match the actual lengths
    for m in msgs.values():
        assert struct.unpack(">I", m[24:28])[0] == len(m)
    print(f"honest run ok; message sizes {[len(msgs[i]) for i in (1, 2, 3, 4)]}")
    return msgs


def test_rfc_key_schedule():
    ni, nr = os.urandom(32), os.urandom(32)
    spi_i, spi_r = os.urandom(8), os.urandom(8)
    e_i, e_r = os.urandom(32), os.urandom(32)
    gir = I.dh_combine(I.dhpk(e_r), e_i)
    assert gir == I.dh_combine(I.dhpk(e_i), e_r)

    skeyseed = prf(ni + nr, gir)
    lens = [I.KIND_LEN[k] for k in I.IKE_KEYS]
    stream = rfc_prf_plus(skeyseed, ni + nr + spi_i + spi_r, sum(lens))
    rfc = [stream[sum(lens[:j]):sum(lens[:j + 1])] for j in range(5)]
    owl = [I.ike_sa_keys(ni, nr, gir, spi_i, spi_r, j) for j in range(5)]
    assert rfc == owl, "IKE SA keys differ from RFC 5996 2.14"
    print("IKE SA key schedule == RFC 5996 SKEYSEED/prf+ (byte-exact)")

    sk_d = owl[I.SK_D]
    keymat_rfc = rfc_prf_plus(sk_d, ni + nr, 64)
    keymat_owl = I.child_keys(sk_d, ni, nr, 0) + I.child_keys(sk_d, ni, nr, 1)
    assert keymat_owl == rfc_prf_plus(prf(sk_d, b""), ni + nr, 64)
    assert keymat_owl != keymat_rfc
    print("Child SA KEYMAT == prf+(prf(SK_d, \"\"), Ni|Nr)  (documented deviation from 2.17)")


def test_algid_der():
    a = I.RSA_PSS_SHA256_ALGID
    assert a[0] == 0x30 and a[1] == len(a) - 2
    # Inner SEQUENCE of parameters
    assert a[13] == 0x30 and a[14] == len(a) - 15
    print(f"RSASSA-PSS AlgorithmIdentifier is well-formed DER ({len(a)} bytes)")


def test_scapy(msgs, sa_i):
    try:
        from scapy.contrib.ikev2 import (IKEv2, IKEv2_AUTH, IKEv2_IDi, IKEv2_IDr,
                                         IKEv2_KE, IKEv2_Nonce, IKEv2_SA, IKEv2_TSi,
                                         IKEv2_TSr)
    except ImportError:
        print("scapy not installed; skipping wire-format check")
        return

    for i in (1, 2):
        p = IKEv2(msgs[i])
        assert p.exch_type == 34 and p.length == len(msgs[i])
        assert p.flags == (0x08 if i == 1 else 0x20)
        sa = p[IKEv2_SA]
        prop = sa.prop
        assert prop.proto == 1 and prop.trans_nb == 3
        ids = []
        t = prop.trans
        while t is not None and hasattr(t, "transform_id"):
            ids.append((t.transform_type, t.transform_id))
            t = t.payload if t.payload.name != "NoPayload" else None
        assert ids == [(1, 28), (2, 5), (4, 31)], ids
        assert p[IKEv2_KE].group == 31 and len(p[IKEv2_KE].ke) == 32
        assert len(p[IKEv2_Nonce].nonce) == 32
        assert p[IKEv2_Nonce].next_payload == 0

    for i, key, idcls in ((3, sa_i.sk_ei, IKEv2_IDi), (4, sa_i.sk_er, IKEv2_IDr)):
        p = IKEv2(msgs[i])
        assert p.exch_type == 35 and p.length == len(msgs[i]) and p.next_payload == 46
        assert struct.unpack(">H", msgs[i][30:32])[0] == len(msgs[i]) - 28
        # Decrypt by hand per RFC 5282/7634 framing, then parse the inner
        # payload chain with scapy
        iv, ct = msgs[i][32:40], msgs[i][40:]
        pt = I.st_aead_dec(key, ct, msgs[i][:32], iv)
        assert pt[-1] == 0  # Pad Length
        first = msgs[i][28]
        inner = idcls(pt[:-1]) if first in (35, 36) else None
        assert inner is not None and inner.IDtype == 11
        assert inner[IKEv2_AUTH].auth_type == 14
        assert inner[IKEv2_SA].prop.proto == 3
        assert inner[IKEv2_TSi].number_of_TSs == 1
        assert inner[IKEv2_TSr].next_payload == 0
    print("scapy parses all four messages as the intended IKEv2 payload chains")


def test_tamper(init, resp, msgs):
    rng = random.Random(0)
    tried = 0
    assert msgs[1][KE_OFFSET:KE_OFFSET + 32] == I.msg1.parse(msgs[1])["ke"]
    for i in (1, 2, 3, 4):
        n = len(msgs[i])
        positions = range(n) if i in (1, 2) else range(n)
        for pos in positions:
            bit = rng.randrange(8)

            def flip(j, m, i=i, pos=pos, bit=bit):
                if j != i:
                    return m
                return m[:pos] + bytes([m[pos] ^ (1 << bit)]) + m[pos + 1:]
            try:
                sa_i, sa_r = I.run_handshake(init, resp, flip)
            except ValueError:  # X25519 rejects a low-order point
                sa_i, sa_r = None, None
            assert sa_i is None, (i, pos)
            # A tampered msg4 only affects the initiator: the responder has
            # already finished. X25519 ignores the top bit of a public key
            # (RFC 7748), so flipping it in KEr leaves g^ir unchanged and the
            # responder completes; the initiator still rejects, since msg2 is
            # covered by the responder's AUTH.
            ke_msb = (i == 2 and pos == KE_OFFSET + 31 and bit == 7)
            if i < 4 and not ke_msb:
                assert sa_r is None, (i, pos)
            tried += 1
    print(f"all {tried} single-bit tamperings rejected")


def test_wrong_keys():
    init, resp = setup()
    # Responder does not know the initiator
    resp.peers = {}
    assert I.run_handshake(init, resp) == (None, None)
    # Initiator expects a different responder key
    init, resp = setup()
    init.peer_vk = I.SigKey().vk
    sa_i, sa_r = I.run_handshake(init, resp)
    assert sa_i is None and sa_r is not None
    # Initiator expects a different responder identity
    init, resp = setup()
    init.peer_id = b"X" * I.ID_LEN
    assert I.run_handshake(init, resp)[0] is None
    # A man-in-the-middle substituting its own KE in msg1 is caught by AUTH
    init, resp = setup()
    evil = I.dhpk(os.urandom(32))

    def mitm(j, m):
        return m[:KE_OFFSET] + evil + m[KE_OFFSET + 32:] if j == 1 else m
    assert I.run_handshake(init, resp, mitm) == (None, None)
    print("wrong identities / keys / substituted KE rejected")


# KE data offset in msg1/msg2: IKE header, SA payload, KE payload header
KE_OFFSET = 28 + len(I.SA1_PAYLOAD) + 8


if __name__ == "__main__":
    init, resp = setup()
    test_algid_der()
    test_rfc_key_schedule()
    msgs = test_honest(init, resp)
    sa_i, _, msgs = capture(init, resp)
    test_scapy(msgs, sa_i)
    test_tamper(init, resp, msgs)
    test_wrong_keys()
    # Several sessions on the same long-term keys and counters
    for _ in range(3):
        a, b = I.run_handshake(init, resp)
        assert a is not None and b is not None and a.esp_key_i2r == b.esp_key_i2r
    print("repeated sessions ok")
    print("ALL TESTS PASSED")
