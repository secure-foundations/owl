"""
Fill in the hand-written parts of the extracted code: the bodies of the
abstract defs in defs.owl (get_spi_i, get_ni, ..., get_pk_info), which Owl
extracts as `unimplemented!(/* implement owl_X by hand */)`.

Also sets the signature length to 256 bytes: the extraction preamble
hardcodes SIGNATURE_SIZE = 64, but the backend's signatures are RSA-2048
(owl_pke.rs), which are 256 bytes.

And it implements SecretBuf::secret_eq in execlib.rs, which the runtime
leaves as todo!(); the `eq` after each vrfy compiles to it.

Usage: python patch_stubs.py path/to/extraction/src/lib.rs
"""

import os
import re
import sys

RANDOM = {
    "get_spi_i": 8, "get_spi_r": 8,
    "get_ni": 32, "get_nr": 32,
    "get_esp_spi_i": 4, "get_esp_spi_r": 4,
}


def body(name, sig):
    if name in RANDOM:
        return f"(OwlBuf::from_vec(crate::owl_util::gen_rand_bytes({RANDOM[name]})), Tracked(itree))"
    if name == "get_pk_info":
        # The responder's database holds one initiator: the ID in
        # IKEV2_PEER_ID, with verification key pk_owl_skI
        arg = re.search(r"mut_state: &mut state_Responder, (owl_id\d+): OwlBuf", sig).group(1)
        return (
            "{ let want: Vec<u8> = { let s = std::env::var(\"IKEV2_PEER_ID\").unwrap(); "
            "(0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect() }; "
            f"if {arg}.as_slice() == &want[..] {{ (Some(OwlBuf::another_ref(&self.pk_owl_skI)), Tracked(itree)) }} "
            "else { (None, Tracked(itree)) } }"
        )
    raise SystemExit(f"no implementation for {name}")


def main(path):
    src = open(path).read()
    pat = re.compile(r"(pub fn owl_(\w+)<[^\n]*\n(?:.*\n)*?)(\s*)unimplemented!\(/\* implement owl_\2 by hand \*/\)")
    n = 0

    def repl(m):
        nonlocal n
        n += 1
        return m.group(1) + m.group(3) + body(m.group(2), m.group(1).split("\n")[0])
    src = pat.sub(repl, src)
    # The constants, and the signature field (field 6) of the auth_inner
    # spec and exec combinators, where the length is inlined
    for old, new, count in (
            ("SPEC_SIGNATURE_SIZE: usize = 64usize", "SPEC_SIGNATURE_SIZE: usize = 256usize", 1),
            ("{ 64usize }", "{ 256usize }", 1),
            ("let field_6 = Varied(64usize);", "let field_6 = Varied(256usize);", 2)):
        assert src.count(old) == count, old
        src = src.replace(old, new)
    if "implement owl_" in src:
        raise SystemExit("some stubs were not patched")
    open(path, "w").write(src)

    execlib = os.path.join(os.path.dirname(path), "execlib.rs")
    ex = open(execlib).read()
    old = 'todo!("implement secret_eq")'
    assert ex.count(old) == 1
    ex = ex.replace(old, "{ let (a, b) = (self.buf.as_slice(), other.buf.as_slice()); "
                         "a.len() == b.len() && a.iter().zip(b.iter()).fold(0u8, |acc, (x, y)| acc | (x ^ y)) == 0 }")
    open(execlib, "w").write(ex)
    print(f"patched {n} stubs, SIGNATURE_SIZE, and secret_eq")


if __name__ == "__main__":
    main(sys.argv[1])
