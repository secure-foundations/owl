# Owl

Owl is a tool for developing cryptographic protocols with formal, machine-checked guarantees of security. Cryptographic protocols, such as WireGuard and TLS, form the foundation of secure digital infrastructure, but vulnerabilities are discovered in them with alarming frequency. To ameliorate this situation, Owl allows developers to _prove_ that their protocols are secure, providing a high degree of assurance that many common classes of vulnerabilities will not arise.

Owl consists of an automated verifier and secure compiler for cryptographic protocols. Owl's verifier enables developers to prove security against a strong adversary model, analogous to models used by pen-and-paper cryptographers[^1]; unlike pen-and-paper proofs, however, Owl provides powerful proof automation to aid with scaling proofs to realistic protocols. The verifier is based on a novel _type system_ for secure protocol code, which guarantees that any well-typed protocol is secure. Owl's secure compiler translates verified protocol designs into performant, interoperable Rust libraries, ready for deployment. The libraries are automatically formally verified to be correct implementations of the verified protocol design, using [Verus](https://github.com/verus-lang/verus/), a deductive program verifier for Rust; they also use Rust's type system to guarantee the absence of certain digital side-channel attacks. 

[^1]: Owl's verifier works in the _computational model_, in which adversaries are modeled as probabilistic Turing machines operating over bytestrings; this is in contrast to the _symbolic model_, which abstracts away some details of cryptography to simplify analysis. For more details, see [this survey](https://bblanche.gitlabpages.inria.fr/publications/BlanchetETAPS12.pdf) or our [S&P 2023 paper](https://eprint.iacr.org/2023/473.pdf).

## Owl developer workflow

Developers first describe their protocol in the Owl language, a high-level, functional domain-specific language with built-in cryptographic primitives. They then prove computational security for their protocol using Owl's information-flow and refinement types. Finally, they use Owl's secure compiler to generate a verified Rust library of protocol routines, which they can then integrate into a larger application or codebase.

## Status

Owl is still under active development, and the language, verifier, and compiler are all subject to change. Please report bugs and problems via GitHub issues. We also welcome contributions from the community via pull requests!

### Supported Cryptographic Operations

Owl currently supports the following cryptographic primitives:
* Authenticated Symmetric Encryption (e.g., ChaCha20-Poly1305, or AES-GCM)
* CCA-secure PKE (e.g., RSA with OAEP)
* Message Authentication Codes (e.g., HMAC)
* Digital Signatures (e.g., RSA signatures)
* Diffie-Hellman Key Exchange
* HKDF for key derivations
* Unique Nonces for checking equality

## Documentation 

Reference documentation for the Owl language is [here](gancher.dev/owl-docs). 

For the compiler, we have a 
[compiler guide](/docs/compiler-guide.md) 
 with information on how to produce bit-precise protocol models using Owl's compiler pipeline. A number of example Owl protocols are in the [tests/success](/tests/success/) directory, illustrating various features of the Owl language and type system.

## Relevant branches

The `main` branch tracks recent developments, so the Owl syntax and language features are subject to change. 
Our release [here](https://github.com/secure-foundations/owl/releases/tag/ieee-sp-2023) corresponds to our [S&P 2023 publication](https://www.computer.org/csdl/proceedings-article/sp/2023/933600b130/1NrbYvgcB4Q).
The artifact attached to our [USENIX Security 2025 publication](https://www.usenix.org/conference/usenixsecurity25/presentation/singh) is available in archival form [here](https://doi.org/10.5281/zenodo.15605318).

## Setup

To build and run Owl, you need `cabal` and `ghc` in your `PATH`. You can use [ghcup](https://www.haskell.org/ghcup/) to install them. 
Additionally, you need the [Z3 Prover](https://github.com/Z3Prover/z3) installed
and in your `PATH`; binary releases are [here](https://github.com/Z3Prover/z3/releases). Owl has been tested with Z3 version `4.12.5`.

To build and run, type `cabal run owl -- path/to/protocol.owl`. For more options, type `cabal run owl -- --help`.

To compile a protocol to Verus using Owl's secure compiler, use the `--extract` argument: `cabal run owl -- --extract path/to/protocol.owl`.
Then, in the `extraction/` directory, run `./run_verus.sh $PWD` to verify the generated code with Verus. 
The `run_verus` script assumes you have [`verus`](https://github.com/verus-lang/verus/) and [`verusfmt`](https://github.com/verus-lang/verusfmt/)
in your `PATH`.

## Syntax highlighting

### Vim

Add the following to your vimrc:

```
set runtimepath+=$OWL_HOME/vim
```

where `$OWL_HOME` is set accordingly.

### VSCode

See `vscode/README.md` for details.

## Related Publications

Joshua Gancher, Sydney Gibson, Pratap Singh, Samvid Dharanikota, & Bryan Parno. (2023). [Owl: Compositional Verification of Security Protocols via an Information-Flow Type System](https://eprint.iacr.org/2023/473.pdf). 

Pratap Singh, Joshua Gancher, & Bryan Parno. (2025). [OwlC: Compiling Security Protocols to Verified, Secure, High-Performance Libraries](https://eprint.iacr.org/2025/1092.pdf).
