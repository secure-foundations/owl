"""
Interoperability test between the Owl IKEv2 implementation (extracted from
../full.owl to Rust) and the Python spec (../spec/ikev2.py).

  1. extract ../full.owl in a scratch copy of the repo's extraction/ crate
     (the repo's own extraction/src is not touched);
  2. fill in the abstract defs (patch_stubs.py) and add ikev2_peer.rs;
  3. cargo build (plain cargo: this runs the code, it does not run Verus);
  4. run all four pairings of {Owl, Python} initiator x {Owl, Python}
     responder, and check that both sides finish with the same Child SA keys,
     SPIs and ESP SPIs;
  5. check that the Owl parties reject a tampered message.

Usage, from anywhere:
  python run_interop.py WORKDIR [--reuse]   (needs `cryptography`; cabal, cargo, z3)
--reuse skips steps 1-3 if WORKDIR already has a built binary.
"""

import os
import shutil
import signal
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
IKEV2 = os.path.dirname(HERE)
REPO = os.path.abspath(os.path.join(IKEV2, "..", "..", ".."))
sys.path.insert(0, os.path.join(IKEV2, "spec"))

import ikev2 as I  # noqa: E402
from cryptography.hazmat.primitives import serialization  # noqa: E402

ID_I, ID_R = b"I" * I.ID_LEN, b"R" * I.ID_LEN


def build(work):
    ext = os.path.join(work, "extraction")
    if os.path.exists(work):
        shutil.rmtree(work)
    os.makedirs(work)
    shutil.copy(os.path.join(REPO, "prelude.smt2"), work)
    shutil.copytree(os.path.join(REPO, "extraction"), ext,
                    ignore=shutil.ignore_patterns("target"))
    shutil.copytree(IKEV2, os.path.join(work, "ikev2"),
                    ignore=shutil.ignore_patterns("interop", "spec", "*.smtcache"))
    owl = subprocess.check_output(["cabal", "list-bin", "owl"], cwd=REPO, text=True).strip()
    subprocess.run([owl, "--extract", "ikev2/full.owl"], cwd=work, check=True)
    subprocess.run([sys.executable, os.path.join(HERE, "patch_stubs.py"),
                    os.path.join(ext, "src", "lib.rs")], check=True)
    os.makedirs(os.path.join(ext, "src", "bin"))
    shutil.copy(os.path.join(HERE, "ikev2_peer.rs"), os.path.join(ext, "src", "bin"))
    subprocess.run(["cargo", "build", "--bin", "ikev2_peer"], cwd=ext, check=True)
    return os.path.join(ext, "target", "debug", "ikev2_peer")


def der(k: I.SigKey):
    sk = k.sk.private_bytes(serialization.Encoding.DER, serialization.PrivateFormat.PKCS8,
                            serialization.NoEncryption())
    vk = k.vk.public_bytes(serialization.Encoding.DER,
                           serialization.PublicFormat.SubjectPublicKeyInfo)
    return sk, vk


class OwlParty:
    """An extracted Owl party, as a subprocess."""

    def __init__(self, binary, role, me: I.SigKey, peer: I.SigKey, my_id, peer_id):
        sk, vk = der(me)
        _, peer_vk = der(peer)
        self.p = subprocess.Popen(
            [binary, role, sk.hex(), vk.hex(), peer_vk.hex(), my_id.hex(), peer_id.hex()],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def recv(self):
        """Next message the party sends, or its RESULT/FAIL line."""
        line = self.p.stdout.readline().strip()
        if line.startswith("OUT "):
            return bytes.fromhex(line[4:])
        return line

    def send(self, m: bytes):
        self.p.stdin.write(m.hex() + "\n")
        self.p.stdin.flush()

    def result(self):
        line = self.recv()
        self.p.wait(timeout=30)
        if not isinstance(line, str) or not line.startswith("RESULT "):
            return None
        return tuple(bytes.fromhex(x) for x in line.split()[1:])


def py_result(sa: I.ChildSA):
    if sa is None:
        return None
    return (sa.spi_i, sa.spi_r, sa.esp_spi_i, sa.esp_spi_r, sa.esp_key_i2r, sa.esp_key_r2i)


def run(binary, owl_init: bool, owl_resp: bool, tamper=None):
    """One handshake. Messages pass through `tamper(i, m)`."""
    tamper = tamper or (lambda i, m: m)
    signal.alarm(60)  # a party waiting on a message that never comes
    ki, kr = I.SigKey(), I.SigKey()
    pi = I.Initiator(ki, ID_I, ID_R, kr.vk)
    pr = I.Responder(kr, ID_R, {ID_I: ki.vk})
    oi = OwlParty(binary, "init", ki, kr, ID_I, ID_R) if owl_init else None
    orr = OwlParty(binary, "resp", kr, ki, ID_R, ID_I) if owl_resp else None
    res_i = res_r = None
    try:
        # msg1
        if oi:
            m1 = oi.recv()
        else:
            st_i, m1 = pi.stage1()
        m1 = tamper(1, m1)
        # msg2
        if orr:
            orr.send(m1)
            m2 = orr.recv()
        else:
            r = pr.stage1(m1)
            if r is None:
                return None, None
            st_r, m2 = r
        m2 = tamper(2, m2)
        # msg3
        if oi:
            oi.send(m2)
            m3 = oi.recv()
        else:
            r = pi.stage2(st_i, m2)
            if r is None:  # an Owl responder is left waiting for msg3
                return None, None
            st_i, m3 = r
        if isinstance(m3, str):  # the Owl initiator stopped
            return None, None
        m3 = tamper(3, m3)
        # msg4
        if orr:
            orr.send(m3)
            m4 = orr.recv()
            if isinstance(m4, str):
                return (oi.result() if oi else None), None
            res_r = orr.result()
        else:
            r = pr.stage2(st_r, m3)
            if r is None:
                return None, None
            sa_r, m4 = r
            res_r = py_result(sa_r)
        m4 = tamper(4, m4)
        if oi:
            oi.send(m4)
            res_i = oi.result()
        else:
            res_i = py_result(pi.stage3(st_i, m4))
        return res_i, res_r
    finally:
        signal.alarm(0)
        for o in (oi, orr):
            if o and o.p.poll() is None:
                o.p.kill()


def main(work, reuse):
    binary = os.path.join(work, "extraction", "target", "debug", "ikev2_peer")
    if not (reuse and os.path.exists(binary)):
        binary = build(work)
    names = {False: "Python", True: "Owl"}
    for owl_init in (True, False):
        for owl_resp in (True, False):
            res_i, res_r = run(binary, owl_init, owl_resp)
            label = f"{names[owl_init]} initiator <-> {names[owl_resp]} responder"
            assert res_i is not None and res_r is not None, f"{label}: handshake failed"
            assert res_i == res_r, f"{label}: results differ\n{res_i}\n{res_r}"
            assert len(res_i[4]) == 32 and res_i[4] != res_i[5]
            print(f"ok: {label}; k_i2r = {res_i[4].hex()[:16]}...")

    # Tampering: flip one bit of each message in turn; the Owl parties must
    # not complete with a Python peer (msg4 is only seen by the initiator)
    for owl_init, owl_resp in ((True, False), (False, True)):
        for target in (1, 2, 3, 4):
            if target == 4 and not owl_init:
                continue

            def flip(i, m, target=target):
                if i != target:
                    return m
                pos = len(m) // 2
                return m[:pos] + bytes([m[pos] ^ 1]) + m[pos + 1:]
            res_i, res_r = run(binary, owl_init, owl_resp, flip)
            owl_res = res_i if owl_init else res_r
            assert owl_res is None, f"Owl {'initiator' if owl_init else 'responder'} accepted tampered msg{target}"
    print("ok: Owl parties reject tampered messages")
    print("INTEROP PASSED")


if __name__ == "__main__":
    main(os.path.abspath(sys.argv[1]), "--reuse" in sys.argv[2:])
