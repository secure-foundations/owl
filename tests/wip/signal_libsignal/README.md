# Signal models for the libsignal integration

Two extractable variants of the Signal model (X3DH or PQXDH, then the double ratchet), with
def boundaries that follow libsignal's API and libsignal's concrete formats. They are
derived from `tests/wip/signal/{pqxdh,x3dh}_double_ratchet`; the header of each `defs.owl`
lists the differences.

| directory | handshake | used by the libsignal fork as |
|---|---|---|
| `pqxdh/` | PQXDH (Kyber1024 prekey) | `rust/protocol/owl` (crate `libsignal-protocol-owl`) |
| `x3dh/`  | X3DH (no KEM)            | `rust/protocol/owl-x3dh` (crate `libsignal-protocol-owl-x3dh`) |

Files shared by both variants:

- `owl_wire.rs`: the wire formats (libsignal's protobuf messages) for `--no-vest`. It becomes
  `extraction/src/owl_wire.rs`. Both variants have the same wire structs.
- `signal_message_aead.rs`: Signal's message encryption, the AEAD of the models' cipher
  suite. The support library loads it from `owl_aead.rs` only under the `libsignal-crypto`
  feature, which builds only inside the libsignal fork.

Both files are trusted (not checked by Verus); see their headers.

## Commands

Run from the repository root (owl reads `prelude.smt2` from the working directory).

Typecheck:

```sh
cabal run owl -- --no-color-output --parallelize-splits 8 --reuse-z3 tests/wip/signal_libsignal/pqxdh/full.owl
cabal run owl -- --no-color-output --parallelize-splits 8 --reuse-z3 tests/wip/signal_libsignal/x3dh/full.owl
```

Extract (the typecheck above already checked the def bodies, so `--only-check __none__`
skips them) and verify with Verus, for `<v>` = `pqxdh` or `x3dh`:

```sh
cabal run owl -- --no-color-output --extract --no-vest --only-check __none__ tests/wip/signal_libsignal/<v>/full.owl
cp tests/wip/signal_libsignal/owl_wire.rs extraction/src/
cd extraction && ./run_verus.sh -n $PWD
```

`run_verus.sh -n` skips verusfmt, which is slow on these files. The generated
`extraction/src/lib.rs` and the copied `owl_wire.rs` are build outputs; do not commit them.
The libsignal fork's `owl-sync.sh` runs these steps and copies the results into its crates.
