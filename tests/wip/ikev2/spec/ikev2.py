"""
Functional spec of a minimal IKEv2 (RFC 5996 / RFC 7296) handshake, written so
that every step corresponds to an Owl operation.

Scope: IKE_SA_INIT + IKE_AUTH with a single fixed cipher suite, signature
authentication, and derivation of the first Child SA's keys. No cookies,
no negotiation, no CERT/CERTREQ, no NAT detection, no EAP, no rekeying.

Fixed suite (all of it is one Owl backend configuration):
  ENCR  = ENCR_CHACHA20_POLY1305 (28)      -> Owl st_aead
  PRF   = PRF_HMAC_SHA2_256 (5)            -> Owl kdf (HKDF-SHA256)
          (Owl's `mac`, used for prf(SK_p, ID'), is HMAC-SHA512 with 64-byte
          keys in the Owl backend; this spec does the same so that it
          interoperates with the extracted code)
  DH    = Curve25519 (31)                  -> Owl DH
  AUTH  = Digital Signature (14), RSASSA-PSS/SHA-256 -> Owl sign/vrfy

The code is organised the way an Owl protocol is:
  1. "Owl primitives": Python functions with exactly the semantics of the
     corresponding Owl operations (as implemented in extraction/src).
  2. Constants (Owl `func c() = 0x...`).
  3. Message formats as fixed-layout structs (Owl `struct` with `Const` and
     fixed-length `Data<adv> |n|` fields). Every IKEv2 length field is a
     constant because every field in this profile has a fixed length.
  4. The parties, written as `def`s at a locality, each a straight-line
     function of the form input; parse; guard; crypto; output.
"""

import hashlib
import hmac
import os
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from cryptography.exceptions import InvalidSignature, InvalidTag
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import padding, rsa
from cryptography.hazmat.primitives.asymmetric.x25519 import (
    X25519PrivateKey,
    X25519PublicKey,
)
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305


# =====================================================================
# 1. Owl primitives
# =====================================================================

# Named lengths (Owl's |group|, |kdfkey|, |enckey|, ...)
GROUP_LEN = 32      # |group|: X25519 public key / shared secret
KDFKEY_LEN = 32     # |kdfkey|
ENCKEY_LEN = 32     # |enckey|
MACKEY_LEN = 64     # |mackey| in the Owl backend (HMAC-SHA512)
CRH_LEN = 32        # |crh|; we use `nonce |crh|` for Ni, Nr
COUNTER_LEN = 8     # |counter|
TAG_LEN = 16        # |tag|
AEAD_NONCE_LEN = 12
SIGNATURE_LEN = 256  # |signature| (RSA-2048)

KIND_LEN = {"kdfkey": KDFKEY_LEN, "enckey": ENCKEY_LEN, "mackey": MACKEY_LEN}


def dhpk(sk: bytes) -> bytes:
    return X25519PrivateKey.from_private_bytes(sk).public_key().public_bytes_raw()


def dh_combine(pk: bytes, sk: bytes) -> bytes:
    """Owl dh_combine(pk, sk)."""
    return X25519PrivateKey.from_private_bytes(sk).exchange(
        X25519PublicKey.from_public_bytes(pk))


def is_group_elem(x: bytes) -> bool:
    """Owl is_group_elem: a length check on the X25519 backend."""
    return len(x) == GROUP_LEN


def _hkdf(length: int, salt: bytes, ikm: bytes, info: bytes) -> bytes:
    """HKDF-SHA256 (RFC 5869) extract-then-expand: owl_extract_expand_to_len."""
    prk = hmac.new(salt, ikm, hashlib.sha256).digest()
    out, t, i = b"", b"", 1
    while len(out) < length:
        t = hmac.new(prk, t + info + bytes([i]), hashlib.sha256).digest()
        out += t
        i += 1
    return out[:length]


def kdf(kinds: List[str], j: int, salt: bytes, ikm: bytes, info: bytes) -> bytes:
    """Owl kdf<...; k_0 || ... || k_n; j>(salt, ikm, info).

    Extraction computes one HKDF output of length sum(|k_i|) and returns the
    j'th slice, so all outputs of one call come from a single HKDF stream."""
    lens = [KIND_LEN[k] for k in kinds]
    stream = _hkdf(sum(lens), salt, ikm, info)
    start = sum(lens[:j])
    return stream[start:start + lens[j]]


def mac(k: bytes, m: bytes) -> bytes:
    """Owl mac: HMAC-SHA512 in the Owl backend (owl_hmac, HMAC_MODE)."""
    return hmac.new(k, m, hashlib.sha512).digest()


@dataclass
class SigKey:
    """Owl sigkey name. `vk` is Owl's vk(...) / get_vk(...)."""
    sk: rsa.RSAPrivateKey = field(
        default_factory=lambda: rsa.generate_private_key(65537, 2048))

    @property
    def vk(self) -> rsa.RSAPublicKey:
        return self.sk.public_key()


_PSS = padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=32)
# The Owl backend (rsa crate) signs with the maximum salt length, so accept
# any salt length when verifying
_PSS_VERIFY = padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=padding.PSS.AUTO)


def sign(k: SigKey, m: bytes) -> bytes:
    return k.sk.sign(m, _PSS, hashes.SHA256())


def vrfy(vk: rsa.RSAPublicKey, m: bytes, sig: bytes) -> Optional[bytes]:
    """Owl vrfy(vk, m, sig) : Option t."""
    try:
        vk.verify(sig, m, _PSS_VERIFY, hashes.SHA256())
        return m
    except InvalidSignature:
        return None


class Counter:
    """Owl `counter N @ L`: local, monotonic."""

    def __init__(self):
        self.v = 0

    def get(self) -> bytes:
        """Owl get_counter N: counter_as_bytes is 8 bytes little-endian."""
        return self.v.to_bytes(COUNTER_LEN, "little")


def _pad_nonce(iv: bytes) -> bytes:
    # owl_enc_st_aead zero-pads the counter on the right to the AEAD nonce size
    return iv + bytes(AEAD_NONCE_LEN - len(iv))


def st_aead_enc(ctr: Counter, k: bytes, x: bytes, aad: bytes) -> bytes:
    """Owl st_aead_enc<N>(k, x, aad): nonce = current counter, then increment."""
    nonce = ctr.get()
    ctr.v += 1
    return ChaCha20Poly1305(k).encrypt(_pad_nonce(nonce), x, aad)


def st_aead_dec(k: bytes, c: bytes, aad: bytes, nonce: bytes) -> Optional[bytes]:
    """Owl st_aead_dec(k, c, aad, nonce) : Option t."""
    try:
        return ChaCha20Poly1305(k).decrypt(_pad_nonce(nonce), c, aad)
    except InvalidTag:
        return None


def cipherlen(n: int) -> int:
    return n + TAG_LEN


# =====================================================================
# 2. Constants
# =====================================================================

def u8(x): return x.to_bytes(1, "big")
def u16(x): return x.to_bytes(2, "big")
def u32(x): return x.to_bytes(4, "big")


# Payload types (RFC 5996 3.2)
PT_NONE, PT_SA, PT_KE, PT_IDI, PT_IDR, PT_AUTH, PT_NONCE = 0, 33, 34, 35, 36, 39, 40
PT_TSI, PT_TSR, PT_SK = 44, 45, 46
# Exchange types (3.1)
IKE_SA_INIT, IKE_AUTH = 34, 35
# Flags (3.1)
FLAG_I, FLAG_R = 0x08, 0x20
VERSION = 0x20  # MjVer 2, MnVer 0
# Transforms (3.3.2, RFC 7634, RFC 8031)
TT_ENCR, TT_PRF, TT_DH, TT_ESN = 1, 2, 4, 5
ENCR_CHACHA20_POLY1305 = 28
PRF_HMAC_SHA2_256 = 5
DH_CURVE25519 = 31
ESN_NONE = 0
PROTO_IKE, PROTO_ESP = 1, 3
ID_KEY_ID = 11
AUTH_DIGITAL_SIGNATURE = 14  # RFC 7427
TS_IPV4_ADDR_RANGE = 7

ID_LEN = 16       # fixed-length ID_KEY_ID identities
ESP_SPI_LEN = 4
IKE_SPI_LEN = 8

# RFC 7427 Appendix A.4.3: AlgorithmIdentifier for RSASSA-PSS with SHA-256,
# MGF1-SHA-256, salt length 32, trailer field 1 (72 bytes)
RSA_PSS_SHA256_ALGID = bytes.fromhex(
    "30460609 2a864886 f70d0101 0a3039a0"
    "0f300d06 09608648 01650304 02010500"
    "a11c301a 06092a86 4886f70d 01010830"
    "0d060960 86480165 03040201 0500a203"
    "020120a3 03020101".replace(" ", ""))


def gen_hdr(np: int, length: int) -> bytes:
    """Generic payload header (3.2)."""
    return u8(np) + u8(0) + u16(length)


def transform(last: bool, ttype: int, tid: int) -> bytes:
    return u8(0 if last else 3) + u8(0) + u16(8) + u8(ttype) + u8(0) + u16(tid)


def proposal_hdr(plen: int, proto: int, spi_size: int, ntrans: int) -> bytes:
    return u8(0) + u8(0) + u16(plen) + u8(1) + u8(proto) + u8(spi_size) + u8(ntrans)


# SAi1 / SAr1: the single IKE proposal
_ike_transforms = (transform(False, TT_ENCR, ENCR_CHACHA20_POLY1305)
                   + transform(False, TT_PRF, PRF_HMAC_SHA2_256)
                   + transform(True, TT_DH, DH_CURVE25519))
_ike_proposal = proposal_hdr(8 + len(_ike_transforms), PROTO_IKE, 0, 3) + _ike_transforms
SA1_PAYLOAD = gen_hdr(PT_KE, 4 + len(_ike_proposal)) + _ike_proposal

KE_PAYLOAD_LEN = 8 + GROUP_LEN
KE_HDR = gen_hdr(PT_NONCE, KE_PAYLOAD_LEN) + u16(DH_CURVE25519) + u16(0)
NONCE_HDR = gen_hdr(PT_NONE, 4 + CRH_LEN)

MSG_SA_INIT_LEN = 28 + len(SA1_PAYLOAD) + KE_PAYLOAD_LEN + 4 + CRH_LEN


def ike_hdr_tail(np: int, exch: int, flags: int, msg_id: int, length: int) -> bytes:
    """IKE header (3.1) minus the two SPIs: 12 constant bytes."""
    return u8(np) + u8(VERSION) + u8(exch) + u8(flags) + u32(msg_id) + u32(length)


SA_INIT_REQ_TAG = ike_hdr_tail(PT_SA, IKE_SA_INIT, FLAG_I, 0, MSG_SA_INIT_LEN)
SA_INIT_RESP_TAG = ike_hdr_tail(PT_SA, IKE_SA_INIT, FLAG_R, 0, MSG_SA_INIT_LEN)

# Inner IKE_AUTH payloads
ID_REST_PREFIX = u8(ID_KEY_ID) + bytes(3)     # IDType | RESERVED
AUTH_DATA_PREFIX = (u8(AUTH_DIGITAL_SIGNATURE) + bytes(3)
                    + u8(len(RSA_PSS_SHA256_ALGID)) + RSA_PSS_SHA256_ALGID)
AUTH_PAYLOAD_LEN = 4 + len(AUTH_DATA_PREFIX) + SIGNATURE_LEN
AUTH_HDR = gen_hdr(PT_SA, AUTH_PAYLOAD_LEN)

_esp_transforms = (transform(False, TT_ENCR, ENCR_CHACHA20_POLY1305)
                   + transform(True, TT_ESN, ESN_NONE))
_esp_proposal_len = 8 + ESP_SPI_LEN + len(_esp_transforms)
SA2_PREFIX = (gen_hdr(PT_TSI, 4 + _esp_proposal_len)
              + proposal_hdr(_esp_proposal_len, PROTO_ESP, ESP_SPI_LEN, 2))
SA2_TRANSFORMS = _esp_transforms

# Traffic selectors: everything
_ts = (u8(TS_IPV4_ADDR_RANGE) + u8(0) + u16(16) + u16(0) + u16(65535)
       + bytes(4) + b"\xff" * 4)
TSI_PAYLOAD = gen_hdr(PT_TSR, 8 + len(_ts)) + u8(1) + bytes(3) + _ts
TSR_PAYLOAD = gen_hdr(PT_NONE, 8 + len(_ts)) + u8(1) + bytes(3) + _ts

ID_PAYLOAD_LEN = 4 + len(ID_REST_PREFIX) + ID_LEN
IDI_HDR = gen_hdr(PT_AUTH, ID_PAYLOAD_LEN)
IDR_HDR = gen_hdr(PT_AUTH, ID_PAYLOAD_LEN)
PAD_LEN_BYTE = u8(0)  # AEAD: no padding, just the Pad Length octet

AUTH_INNER_LEN = (ID_PAYLOAD_LEN + AUTH_PAYLOAD_LEN + len(SA2_PREFIX) + ESP_SPI_LEN
                  + len(SA2_TRANSFORMS) + len(TSI_PAYLOAD) + len(TSR_PAYLOAD) + 1)
SK_PAYLOAD_LEN = 4 + COUNTER_LEN + cipherlen(AUTH_INNER_LEN)
MSG_AUTH_LEN = 28 + SK_PAYLOAD_LEN

AUTH_REQ_TAG = ike_hdr_tail(PT_SK, IKE_AUTH, FLAG_I, 1, MSG_AUTH_LEN)
AUTH_RESP_TAG = ike_hdr_tail(PT_SK, IKE_AUTH, FLAG_R, 1, MSG_AUTH_LEN)
SK_HDR_REQ = gen_hdr(PT_IDI, SK_PAYLOAD_LEN)
SK_HDR_RESP = gen_hdr(PT_IDR, SK_PAYLOAD_LEN)

ZERO_SPI = bytes(IKE_SPI_LEN)

# Owl kdf output layouts.
# {SK_d | SK_ai | SK_ar | SK_ei | SK_er | SK_pi | SK_pr}; SK_a* are empty for
# an AEAD transform.
IKE_KEYS = ["kdfkey", "enckey", "enckey", "mackey", "mackey"]
SK_D, SK_EI, SK_ER, SK_PI, SK_PR = range(5)
# KEYMAT: ESP key initiator->responder, then responder->initiator (2.17)
CHILD_KEYS = ["enckey", "enckey"]


# =====================================================================
# 3. Message formats
# =====================================================================

class Const:
    def __init__(self, v: bytes):
        self.v = v


class Struct:
    """Owl struct: fields are Const(bytes) or a fixed length."""

    def __init__(self, name: str, fields: List[Tuple[str, object]]):
        self.name = name
        self.fields = fields

    def __call__(self, *args) -> bytes:
        vals = iter(args)
        out = b""
        for fname, f in self.fields:
            v = next(vals)
            if isinstance(f, Const):
                assert v == f.v, f"{self.name}.{fname}: wrong constant"
            else:
                assert len(v) == f, f"{self.name}.{fname}: wrong length"
            out += v
        return out

    def parse(self, b: bytes) -> Optional[Dict[str, bytes]]:
        """`parse x as s(...) in ... otherwise ...`: None on any mismatch."""
        out, pos = {}, 0
        for fname, f in self.fields:
            n = len(f.v) if isinstance(f, Const) else f
            v = b[pos:pos + n]
            if len(v) != n or (isinstance(f, Const) and v != f.v):
                return None
            out[fname] = v
            pos += n
        return out if pos == len(b) else None


def _sa_init_struct(name, tag):
    return Struct(name, [
        ("spi_i", IKE_SPI_LEN),
        ("spi_r", Const(ZERO_SPI)) if tag == SA_INIT_REQ_TAG else ("spi_r", IKE_SPI_LEN),
        ("tag", Const(tag)),
        ("sa", Const(SA1_PAYLOAD)),
        ("ke_hdr", Const(KE_HDR)),
        ("ke", GROUP_LEN),
        ("nonce_hdr", Const(NONCE_HDR)),
        ("nonce", CRH_LEN),
    ])


msg1 = _sa_init_struct("msg1", SA_INIT_REQ_TAG)   # HDR, SAi1, KEi, Ni
msg2 = _sa_init_struct("msg2", SA_INIT_RESP_TAG)  # HDR, SAr1, KEr, Nr


def _auth_outer_struct(name, tag, sk_hdr):
    return Struct(name, [
        ("spi_i", IKE_SPI_LEN),
        ("spi_r", IKE_SPI_LEN),
        ("tag", Const(tag)),
        ("sk_hdr", Const(sk_hdr)),
        ("iv", COUNTER_LEN),
        ("ct", cipherlen(AUTH_INNER_LEN)),
    ])


msg3 = _auth_outer_struct("msg3", AUTH_REQ_TAG, SK_HDR_REQ)    # HDR, SK{...}
msg4 = _auth_outer_struct("msg4", AUTH_RESP_TAG, SK_HDR_RESP)  # HDR, SK{...}


def _auth_inner_struct(name, id_hdr):
    return Struct(name, [
        ("id_hdr", Const(id_hdr)),
        ("id_type", Const(ID_REST_PREFIX)),
        ("id", ID_LEN),
        ("auth_hdr", Const(AUTH_HDR)),
        ("auth_prefix", Const(AUTH_DATA_PREFIX)),
        ("auth_sig", SIGNATURE_LEN),
        ("sa2_prefix", Const(SA2_PREFIX)),
        ("esp_spi", ESP_SPI_LEN),
        ("sa2_transforms", Const(SA2_TRANSFORMS)),
        ("tsi", Const(TSI_PAYLOAD)),
        ("tsr", Const(TSR_PAYLOAD)),
        ("pad_len", Const(PAD_LEN_BYTE)),
    ])


# {IDi, AUTH, SAi2, TSi, TSr} and {IDr, AUTH, SAr2, TSi, TSr}
auth_inner_i = _auth_inner_struct("auth_inner_i", IDI_HDR)
auth_inner_r = _auth_inner_struct("auth_inner_r", IDR_HDR)


def auth_inner(s: Struct, ident, sig, esp_spi):
    return s(s.fields[0][1].v, ID_REST_PREFIX, ident, AUTH_HDR, AUTH_DATA_PREFIX,
             sig, SA2_PREFIX, esp_spi, SA2_TRANSFORMS, TSI_PAYLOAD, TSR_PAYLOAD,
             PAD_LEN_BYTE)


def sk_aad(spi_i, spi_r, tag, sk_hdr) -> bytes:
    """RFC 5282 5.1: AAD is the IKE header through the SK payload header."""
    return spi_i + spi_r + tag + sk_hdr


# Signed octets (2.15)
def signed_octets(real_msg: bytes, peer_nonce: bytes, sk_p: bytes, ident: bytes) -> bytes:
    """RealMessage | NonceData | prf(SK_p, IDType | RESERVED | IDData)."""
    return real_msg + peer_nonce + mac(sk_p, ID_REST_PREFIX + ident)


# =====================================================================
# 4. The parties
# =====================================================================

@dataclass
class ChildSA:
    """What each side returns: the IKE SA keys and the first Child SA."""
    spi_i: bytes
    spi_r: bytes
    peer_id: bytes
    sk_d: bytes
    sk_ei: bytes
    sk_er: bytes
    esp_spi_i: bytes
    esp_spi_r: bytes
    esp_key_i2r: bytes
    esp_key_r2i: bytes


def ike_sa_keys(ni, nr, gir, spi_i, spi_r, j):
    """SKEYSEED = prf(Ni|Nr, g^ir); {SK_d|...} = prf+(SKEYSEED, Ni|Nr|SPIi|SPIr).

    In Owl this is one call kdf<L_ike; ...; j>(Ni ++ Nr, g^ir, Ni++Nr++SPIi++SPIr):
    HKDF-Extract(salt, ikm) is prf(salt, ikm) and HKDF-Expand is prf+."""
    return kdf(IKE_KEYS, j, ni + nr, gir, ni + nr + spi_i + spi_r)


def child_keys(sk_d, ni, nr, j):
    """KEYMAT = prf+(SK_d, Ni|Nr). Owl has no expand-only call, so this is
    kdf<L_child; enckey||enckey; j>(SK_d, 0x, Ni ++ Nr), which is
    prf+(prf(SK_d, 0x), Ni|Nr). See README: not byte-compatible with the RFC."""
    return kdf(CHILD_KEYS, j, sk_d, b"", ni + nr)


class Initiator:
    """locality Initiator. Long-term state: signing key, its own ID, and the
    responder's ID and verification key (configured out of band)."""

    def __init__(self, sig: SigKey, ident: bytes, peer_id: bytes, peer_vk):
        self.sig, self.ident = sig, ident
        self.peer_id, self.peer_vk = peer_id, peer_vk
        # counter for SK_ei; it is used for the msg3 IV
        self.ctr_sk_ei = Counter()

    # Owl: getters for adversary-chosen public values, like WG's get_sender_i
    def get_spi(self) -> bytes:
        return os.urandom(IKE_SPI_LEN)

    def get_esp_spi(self) -> bytes:
        return os.urandom(ESP_SPI_LEN)

    def stage1(self) -> Tuple[dict, bytes]:
        """IKE_SA_INIT request: HDR, SAi1, KEi, Ni."""
        e_i = os.urandom(32)           # name E_i<i@n> : DH
        ni = os.urandom(CRH_LEN)       # name Ni<i@n> : nonce |crh|
        spi_i = self.get_spi()
        m1 = msg1(spi_i, ZERO_SPI, SA_INIT_REQ_TAG, SA1_PAYLOAD, KE_HDR, dhpk(e_i),
                  NONCE_HDR, ni)
        return dict(e_i=e_i, ni=ni, spi_i=spi_i, msg1=m1), m1

    def stage2(self, st: dict, inp: bytes) -> Optional[Tuple[dict, bytes]]:
        """Receive IKE_SA_INIT response; send IKE_AUTH request."""
        p = msg2.parse(inp)
        if p is None or p["spi_i"] != st["spi_i"]:
            return None
        ker, nr, spi_r = p["ke"], p["nonce"], p["spi_r"]
        if not is_group_elem(ker):
            return None
        gir = dh_combine(ker, st["e_i"])
        ni, spi_i = st["ni"], st["spi_i"]
        sk_ei = ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_EI)
        sk_pi = ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_PI)

        auth = sign(self.sig, signed_octets(st["msg1"], nr, sk_pi, self.ident))
        esp_spi_i = self.get_esp_spi()
        inner = auth_inner(auth_inner_i, self.ident, auth, esp_spi_i)
        aad = sk_aad(spi_i, spi_r, AUTH_REQ_TAG, SK_HDR_REQ)
        iv = self.ctr_sk_ei.get()
        ct = st_aead_enc(self.ctr_sk_ei, sk_ei, inner, aad)
        m3 = msg3(spi_i, spi_r, AUTH_REQ_TAG, SK_HDR_REQ, iv, ct)
        return dict(st, nr=nr, spi_r=spi_r, gir=gir, msg2=inp, esp_spi_i=esp_spi_i), m3

    def stage3(self, st: dict, inp: bytes) -> Optional[ChildSA]:
        """Receive IKE_AUTH response; authenticate the responder."""
        p = msg4.parse(inp)
        if p is None or p["spi_i"] != st["spi_i"] or p["spi_r"] != st["spi_r"]:
            return None
        ni, nr, gir, spi_i, spi_r = st["ni"], st["nr"], st["gir"], st["spi_i"], st["spi_r"]
        sk_er = ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_ER)
        aad = sk_aad(spi_i, spi_r, AUTH_RESP_TAG, SK_HDR_RESP)
        pt = st_aead_dec(sk_er, p["ct"], aad, p["iv"])
        if pt is None:
            return None
        q = auth_inner_r.parse(pt)
        if q is None or q["id"] != self.peer_id:
            return None
        sk_pr = ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_PR)
        if vrfy(self.peer_vk, signed_octets(st["msg2"], ni, sk_pr, q["id"]),
                q["auth_sig"]) is None:
            return None
        sk_d = ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_D)
        return ChildSA(
            spi_i, spi_r, q["id"], sk_d,
            ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_EI), sk_er,
            st["esp_spi_i"], q["esp_spi"],
            child_keys(sk_d, ni, nr, 0), child_keys(sk_d, ni, nr, 1))


class Responder:
    """locality Responder. `peers` maps IDs to verification keys, like WG's
    get_pk_info lookup of the static key."""

    def __init__(self, sig: SigKey, ident: bytes, peers: Dict[bytes, object]):
        self.sig, self.ident, self.peers = sig, ident, peers
        self.ctr_sk_er = Counter()

    def get_spi(self) -> bytes:
        return os.urandom(IKE_SPI_LEN)

    def get_esp_spi(self) -> bytes:
        return os.urandom(ESP_SPI_LEN)

    def get_pk_info(self, ident: bytes):
        return self.peers.get(ident)

    def stage1(self, inp: bytes) -> Optional[Tuple[dict, bytes]]:
        """Receive IKE_SA_INIT request; send IKE_SA_INIT response."""
        p = msg1.parse(inp)
        if p is None or not is_group_elem(p["ke"]):
            return None
        e_r = os.urandom(32)
        nr = os.urandom(CRH_LEN)
        spi_r = self.get_spi()
        gir = dh_combine(p["ke"], e_r)
        m2 = msg2(p["spi_i"], spi_r, SA_INIT_RESP_TAG, SA1_PAYLOAD, KE_HDR, dhpk(e_r),
                  NONCE_HDR, nr)
        return dict(ni=p["nonce"], nr=nr, spi_i=p["spi_i"], spi_r=spi_r, gir=gir,
                    msg1=inp, msg2=m2), m2

    def stage2(self, st: dict, inp: bytes) -> Optional[Tuple[ChildSA, bytes]]:
        """Receive IKE_AUTH request; authenticate the initiator; send IKE_AUTH response."""
        p = msg3.parse(inp)
        if p is None or p["spi_i"] != st["spi_i"] or p["spi_r"] != st["spi_r"]:
            return None
        ni, nr, gir, spi_i, spi_r = st["ni"], st["nr"], st["gir"], st["spi_i"], st["spi_r"]
        sk_ei = ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_EI)
        aad = sk_aad(spi_i, spi_r, AUTH_REQ_TAG, SK_HDR_REQ)
        pt = st_aead_dec(sk_ei, p["ct"], aad, p["iv"])
        if pt is None:
            return None
        q = auth_inner_i.parse(pt)
        if q is None:
            return None
        vk = self.get_pk_info(q["id"])
        if vk is None:
            return None
        sk_pi = ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_PI)
        if vrfy(vk, signed_octets(st["msg1"], nr, sk_pi, q["id"]), q["auth_sig"]) is None:
            return None

        sk_pr = ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_PR)
        sk_er = ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_ER)
        auth = sign(self.sig, signed_octets(st["msg2"], ni, sk_pr, self.ident))
        esp_spi_r = self.get_esp_spi()
        inner = auth_inner(auth_inner_r, self.ident, auth, esp_spi_r)
        aad = sk_aad(spi_i, spi_r, AUTH_RESP_TAG, SK_HDR_RESP)
        iv = self.ctr_sk_er.get()
        ct = st_aead_enc(self.ctr_sk_er, sk_er, inner, aad)
        m4 = msg4(spi_i, spi_r, AUTH_RESP_TAG, SK_HDR_RESP, iv, ct)

        sk_d = ike_sa_keys(ni, nr, gir, spi_i, spi_r, SK_D)
        sa = ChildSA(spi_i, spi_r, q["id"], sk_d, sk_ei, sk_er, q["esp_spi"], esp_spi_r,
                     child_keys(sk_d, ni, nr, 0), child_keys(sk_d, ni, nr, 1))
        return sa, m4


def run_handshake(init: Initiator, resp: Responder, tamper=None):
    """Run the four messages over an (optionally tampering) network."""
    tamper = tamper or (lambda i, m: m)
    st_i, m1 = init.stage1()
    r = resp.stage1(tamper(1, m1))
    if r is None:
        return None, None
    st_r, m2 = r
    r = init.stage2(st_i, tamper(2, m2))
    if r is None:
        return None, None
    st_i, m3 = r
    r = resp.stage2(st_r, tamper(3, m3))
    if r is None:
        return None, None
    sa_r, m4 = r
    sa_i = init.stage3(st_i, tamper(4, m4))
    return sa_i, sa_r
