# Owl

## Extraction

Owl currently features a prototype extraction mechanism generating safe Rust code. To use it, you will need Rust (including `cargo` and `rustfmt`) installed and in your `PATH`. 

Suppose you want to extract the protocol in `protocol.owl`, which contains localities `alice`, `bob`, and `charlie`. The steps are as follows:

1. `cabal run owl -- -e path/to/protocol.owl`  
    This should print `Successfully extracted to file extraction/src/main.rs`
2. `cd extraction`
3. `cargo run -- config .`  
    This should output one `.owl_config` file for each of the localities in the protocol (in this example, `loc_alice.owl_config`, `loc_bob.owl_config`, `loc_charlie.owl_config`). These files contain all the pre-initialized names for the protocol (such as pre-shared symmetric keys, public keys for other localities, shared salt for the KDF, etc).
4.  Open one shell for each of the localities in the protocol (in this example, three shells). In all of them, `cd` to the `extraction` subdirectory.
5.  In each of the shells, run `cargo run -- run LOCALITY PATH-TO-LOCALITY-CONFIG`. In this example, you would run:  
    - Shell 1: `cargo run -- run alice loc_alice.owl_config`  
    - Shell 2: `cargo run -- run bob loc_bob.owl_config`  
    - Shell 3: `cargo run -- run charlie loc_charlie.owl_config`  
    These should all be started within 5 seconds of each other. The extraction harness waits 5 seconds before beginning execution of the locality; this is to ensure that the user has time to start the other localities. Otherwise, the protocol code may fail because another locality's TCP socket is not ready to receive yet.
6.  You should see the return values of each of the localities printed in their corresponding shells.

## Syntax highlighting

For vim: add the following to your vimrc:

    set runtimepath+=$OWL_HOME/vim

where `$OWL_HOME` is set accordingly.


## Supported Cryptographic Operations

Owl currently supports the following cryptographic primitives:
* Authenticated Symmetric Encryption (e.g., ChaCha20-Poly1305, or AES-GCM)
* CCA-secure PKE (e.g., RSA with OAEP)
* Message Authentication Codes (e.g., HMAC)
* Digital Signatures (e.g., RSA siagnatures)
* Diffie-Hellman Key Exchange
* HKDF for key derivations
* Unique Nonces for checking equality
