# Owl Compiler Pipeline Guide

Owl features a compiler pipeline that translates well-typed Owl programs into efficient Rust code that is machine verified (using Verus) to be correct and secure. Using Owl, you can produce bit-precise models of protocols that adhere to specified ciphersuite choices and binary network formats, in addition to the strong security guarantees provided by our typechecker.

The Owl compiler (also known as "OwlC" or "Owl extraction") is described in detail in our [USENIX Security 2025 publication](https://eprint.iacr.org/2025/1092.pdf); this document provides guidance on how to use the Owl compiler and its generated output, and how to model implementation-level details such as ciphersuite choices and message formats.

## Running the compiler

The artifact for our USENIX Security 2025 publication, available [here](https://doi.org/10.5281/zenodo.15605318), provides a Docker image containing all the dependencies required to run the Owl compiler and verify its output. The artifact evaluation appendix in that archive provides instructions on how to set up and use the Docker image. For those using this repository from source, you'll need to use the following instructions.

- **Prerequisites.** Follow the setup in `README.md` to install `cabal`, `ghc`, and `z3`. Rust's `cargo` tool, the `verus` binary, and `verusfmt` must also be available in `PATH` when you run the verification script. 
- **Compilation command.** From the repository root run:

  ```
  cabal run owl -- --extract path/to/protocol.owl
  ```

  The verifier type-checks your protocol first. On success, the compiler emits a Rust crate under `extraction/<protocol-stem>/`.
- **Output layout.** The compiled Rust crate is in the `extraction/` subdirectory. The Owl compiler will generate `extraction/src/lib.rs`, while all other files in `extraction/src/` contain libraries of helper routines (e.g., code for cryptographic primitives). We also provide `run_verus.sh`, a script that orchestrates running Verus and `verusfmt` to verify the generated Rust crate. A full representative example crate in `client_example/extraction/`.

## Verifying the output with Verus

- **Entering the crate.** Change into the extraction directory:

  ```
  cd extraction
  ```

- **Running Verus.** Execute the provided script, passing the workspace root:

  ```
  ./run_verus.sh $PWD
  ```

  The script orchestrates the Verus proof obligations for every generated Rust module. Ensure `verus`, `verusfmt`, and required Rust targets are installed; the script exits with a non-zero status if verification fails.

- **Iterating.** When you re-run the compiler, it overwrites the crate root `extraction/src/lib.rs`. Re-run Verus after every change to the Owl source to re-verify the generated output.

## Owl length constants

Owl's source language lets you specify the length of byte buffers: the `Data` type for byte buffers may optionally carry a length refinement. As well as non-negative integers, Owl provides built-in length constants that you can use in type annotations and length expressions. These constants represent the sizes of cryptographic keys or data, and are automatically resolved to concrete byte values during compilation. The following constants are available:

- **`|group|`**: Length of a Diffie-Hellman group element. Used for DH private/public keys and shared secrets.
- **`|enckey|`**: Length of an authenticated encryption key. Used for symmetric encryption keys.
- **`|kdfkey|`**: Length of a key derivation function output. Used for KDF-derived keys.
- **`|mackey|`**: Length of a MAC key. Used for message authentication code keys.
- **`|nonce|`**: Length of a nonce. Used for IVs for symmetric encryption. The `nonce` name type in Owl can also carry a customized length, e.g., `nonce |8|`.
- **`|tag|`**: Length of an AEAD authentication tag.
- **`|maclen|`**: Length of a MAC output. Used for MAC values.
- **`|counter|`**: Length of a counter value (8 bytes little-endian, by default). Used for stateful AEAD counters.
- **`|sigkey|`**: Length of a digital signature private key. Used for digital signature keys.
- **`|pkekey|`**: Length of a public-key encryption private key. Used for PKE keys.

These constants can be used in length annotations like `Data<adv> | |group| |` or in length expressions like `cipherlen(|group|)`. The compiler resolves them to concrete numerical values based on the configured cipher suites. 

The `cipherlen(n)` function computes the length of an AEAD ciphertext given a plaintext length `n`, adding the authentication tag size (typically 16 bytes for ChaCha20Poly1305): `cipherlen(n) = n + TAG_SIZE`.

## Customising cipher suites

Owl’s runtime library currently hosts implementations of cryptographic in `extraction/src/execlib.rs`. The compiler must assume specific parameter sizes when setting struct layouts, so changing cipher suites requires updates in two locations:

1. **Runtime crypto module (`extraction/src/execlib.rs`).**
   - Update `CIPHER`, `HMAC_MODE`, and related constructors to select the desired primitives (for example, switch from `Chacha20Poly1305` to `Aes256Gcm`).
   - Ensure helper functions (`owl_aead::*`, `owl_hmac::*`, HKDF glue, etc.) route into implementations that match your choice. If you replace or extend the crypto back-end, maintain the same function signatures used by the generated code (`owl_enc`, `owl_dec`, `owl_mac`, ...). You can add additional Rust libraries by modifying `Cargo.toml`.

2. **Hard-coded length table (`src/Extraction/ExtractionBase.hs`).**
   - Update `concreteLength` so that constants such as `ENCKEY_SIZE`, `NONCE_SIZE`, `MACKEY_SIZE`, and `TAG_SIZE` reflect the new primitive. This mapping controls the combinator sizes the compiler bakes into the generated proofs. A mismatch between the runtime library and these constants will cause Verus verification to fail or, worse, produce unsound assumptions.

After both changes, re-run the compiler and Verus to confirm the pipeline remains consistent.

## Binary message formats and Vest

Owl protocols communicate over the network by exchanging binary messages. The compiler translates Owl `struct` and `enum` definitions into **Vest** format descriptions, which provide verified parsing and serialization for these messages.

### What is Vest?

[**Vest**](https://github.com/secure-foundations/vest) is a verified parsing and serialization library for Verus. It uses a combinator-based approach, where complex formats are built by combining primitive formats. Each combinator describes how to parse a portion of a byte sequence and how to serialize structured data back into bytes.

Among other properties, Vest proves **roundtrip correctness**, i.e., that parsing and serializing are mutual inverses. This rules out parser malleability and format confusion attacks, providing strong security guarantees about the format. For more details, see our [USENIX Security 2025 publication on Vest](https://www.usenix.org/conference/usenixsecurity25/presentation/cai-yi).

Vest provides a front-end, VestDSL, that translates human-readable format descriptions in an RFC-like language into Vest combinators. Owl's compiler pipeline does not use this front-end; instead, it directly translates Owl `struct`s and `enum`s into Vest combinators.

### Combinator primitives

Owl uses the following Vest combinators. 

- **`Variable(n)`**: Parses exactly `n` bytes. Used for fixed-size fields like `Data<adv> |4|`.
- **`Tail`**: Parses all remaining bytes until the end of the input. Used for variable-length trailing fields like `Data<adv>` (without a length annotation).
- **`Tag<U8, u8>(value)`**: Parses a single byte tag that must equal `value`. Used for enum discriminants and constant markers.
- **`OwlConstBytes<N>(bytes)`**: Parses exactly `N` bytes that must match the constant `bytes`. Used for fixed constants like `Const(0x01000000)`. This is an Owl-specific combinator implemented in `extraction/src/owl_const_bytes.rs`.

Complex formats are built by nesting these combinators into tuples, representing sequential fields, and tagged unions, representing enums.

### How Owl translates structs

When you define a struct in Owl, the compiler generates:

1. **A spec-level struct** (`owlSpec_*`) representing the logical structure.
2. **An exec-level struct** (`owl_*`) with runtime buffer types (`OwlBuf`, `SecretBuf`).
3. **Combinator functions** (`spec_combinator_*`, `exec_combinator_*`) that describe the binary format.
4. **Parse and serialize functions** that use the combinators.

The translation maps each field type to a combinator:
- `Const(0x...)` → `OwlConstBytes<N>(constant_bytes)`
- `Data<adv> |n|` → `Variable(n)` where `n` is a concrete length
- `Data<adv>` (no length) → `Tail`
- Nested structs → nested combinator tuples

### How Owl translates enums

Enums are translated using `ord_choice!`, a Vest macro which generates a tagged union:
- Each variant gets a `Tag<U8, u8>(discriminant)` followed by its payload combinator.
- The discriminant is assigned sequentially (1, 2, 3, ...) based on the order in the enum definition.
- Variants with data use their payload combinator; variants without data use `Variable(0)` (the empty byte sequence).

### Worked example: WireGuard message formats

The WireGuard protocol defines three message types for its handshake and data transport. The [WireGuard protocol specification](https://www.wireguard.com/protocol/) describes these formats in detail. Our WireGuard case study models these message types as Owl structs in `tests/wip/wg/defs.owl`. Here, we explain how the protocol format descriptions translate into Owl struct definitions and then into Vest combinators:

#### Message 1 (Handshake initiation)

**Protocol format** (from [WireGuard protocol specification](https://www.wireguard.com/protocol/)):
```
msg = handshake_initiation {
    u8 message_type
    u8 reserved_zero[3]
    u32 sender_index
    u8 unencrypted_ephemeral[32]
    u8 encrypted_static[AEAD_LEN(32)]
    u8 encrypted_timestamp[AEAD_LEN(12)]
    u8 mac1[16]
    u8 mac2[16]
}
```
Here, `message_type = 1`, `reserved_zero = {0, 0, 0}`, and `AEAD_LEN(n) = n + 16` (plaintext length plus authentication tag).

**Owl definition** (`tests/wip/wg/defs.owl`):
```owl
struct msg1 {
      _msg1_tag : Const(0x01000000)
    , _msg1_sender : Data<adv> |4|
    , _msg1_ephemeral : Data<adv> | |group| |
    , _msg1_static : Data<adv> | cipherlen(|group|) | 
    , _msg1_timestamp: Data<adv> | cipherlen(12) |
    , _msg1_mac1: Data<adv> | |maclen| |
    , _msg1_mac2: Const(0x00000000000000000000000000000000)
}
```
We combine the constant `message_type` and `reserved_zero` fields into a single constant `msg1_tag` field.

**Translation to Vest combinator**:
```rust
spec fn spec_combinator_owlSpec_msg1() -> (
    OwlConstBytes<4>,      // _msg1_tag: 0x01000000
    Variable(4),           // _msg1_sender: 4 bytes
    Variable(32),          // _msg1_ephemeral: |group| = 32 bytes
    Variable(48),          // _msg1_static: cipherlen(32) = 32 + 16 tag = 48
    Variable(28),          // _msg1_timestamp: cipherlen(12) = 12 + 16 tag = 28
    Variable(16),          // _msg1_mac1: |maclen| = 16 bytes
    OwlConstBytes<16>      // _msg1_mac2: 16 zero bytes
) {
    let field_1 = OwlConstBytes::<4>(SPEC_BYTES_CONST_01000000_MSG1);
    let field_2 = Variable(4);
    let field_3 = Variable(32);
    let field_4 = Variable(48);
    let field_5 = Variable(28);
    let field_6 = Variable(16);
    let field_7 = OwlConstBytes::<16>(SPEC_BYTES_CONST_0000..._MSG1);
    (field_1, field_2, field_3, field_4, field_5, field_6, field_7)
}
```

The combinator is a 7-tuple where each element corresponds to one field. Constants become `OwlConstBytes` with the constant value baked in; fixed-length fields become `Variable(n)` with the concrete length.

**Translation mapping**: The protocol's `message_type` (1 byte) and `reserved_zero[3]` combine into a single 4-byte constant `0x01000000`. The `u32 sender_index` becomes a 4-byte field. The `unencrypted_ephemeral[32]` maps to `|group|` (32 bytes for Curve25519). The encrypted fields use `cipherlen(n)` which accounts for the AEAD tag: `cipherlen(32) = 48` and `cipherlen(12) = 28`.

#### Message 2 (Handshake response)

**Protocol format** (from [WireGuard protocol specification](https://www.wireguard.com/protocol/)):
```
msg = handshake_response {
    u8 message_type
    u8 reserved_zero[3]
    u32 sender_index
    u32 receiver_index
    u8 unencrypted_ephemeral[32]
    u8 encrypted_nothing[AEAD_LEN(0)]
    u8 mac1[16]
    u8 mac2[16]
}
```

Where `message_type = 2` and `encrypted_nothing` is an encryption of an empty plaintext (just the 16-byte authentication tag).

**Owl definition**:
```owl
struct msg2 {
      _msg2_tag : Const(0x02000000)
    , _msg2_sender: Data<adv> |4|
    , _msg2_receiver: Data<adv> |4|
    , _msg2_ephemeral: Data<adv> | |group| |
    , _msg2_empty: Data<adv> | cipherlen(0) |
    , _msg2_mac1: Data<adv> | |maclen| |
    , _msg2_mac2: Const(0x00000000000000000000000000000000)
}
```

#### Transport message (Data packet)

**Protocol format** (from [WireGuard protocol specification](https://www.wireguard.com/protocol/)):
```
msg = packet_data {
    u8 message_type
    u8 reserved_zero[3]
    u32 receiver_index
    u64 counter
    u8 encrypted_encapsulated_packet[]
}
```

Where `message_type = 4` and `encrypted_encapsulated_packet[]` is a variable-length field containing the encrypted payload (whose length is determined by the ciphertext).

**Owl definition**:
```owl
struct transp {
      _transp_tag : Const(0x04000000)
    , _transp_receiver : Data<adv> |4|
    , _transp_counter  : Data<adv> | |counter| | 
    , _transp_packet   : Data<adv> 
}
```

**Translation**:
```rust
spec fn spec_combinator_owlSpec_transp() -> (
    OwlConstBytes<4>,      // _transp_tag: 0x04000000
    Variable(4),           // _transp_receiver: 4 bytes
    Variable(8),           // _transp_counter: |counter| = 8 bytes
    Tail                  // _transp_packet: variable-length remainder
) { ... }
```

Note that `_transp_packet` has no length annotation, so it becomes `Tail`, consuming all remaining bytes. This is appropriate for encrypted payloads whose length is determined by the ciphertext.

### Using generated parsers and serializers

The compiler generates `parse_owl_*` and `serialize_owl_*` functions that use these combinators.
The parse function uses the exec combinator to parse the buffer, then constructs the struct from the parsed tuple. The spec-level parse function (`parse_owlSpec_*`) provides the specification that the exec function must match, wrapping the Vest combinator calls.

### Design guidelines

When defining message formats in Owl:

1. **Use `Const(...)` for fixed tags and markers** that identify message types or protocol versions.
2. **Use `Data<...> |n|` for fixed-length fields** where `n` is a concrete length or length expression (e.g., `|group|`, `cipherlen(12)`).
3. **Use `Data<...>` (no length) for variable-length trailing fields** like encrypted payloads. Owl will only accept a type without a length annotation as the last field in a struct or as an enum payload, since otherwise there could be ambiguity in parsing.
5. **Use enums for tagged unions** where the tag identifies which variant follows. Enum tags are assigned in ascending order starting from `1`.

The compiler automatically handles length calculations (e.g., `cipherlen(n) = n + TAG_SIZE`) and generates both spec and exec combinators that Verus verifies are equivalent.

## Generated interface overview

The compiler emits a high-level Rust API that mirrors your Owl protocol.

- **Module structure.** `lib.rs` re-exports:
  - The Owl-specific support code (e.g., `execlib`, `speclib`, crypto modules).
  - Generated structs, enums, and combinators that correspond to Owl datatypes.
  - Protocol entry points specialised for each locality.

- **Effect handlers.** The trait `OwlEffects` defines the operations the runtime must supply: sampling randomness (`owl_sample`), interacting with the network (`owl_output`, `owl_input`), and fused serialization, an optimization that allows the output primitive to serialize structured data directly onto the network. To integrate the code, implement `OwlEffects` for your IO environment. The generated procedures require an `OwlEffects` implementation to execute.

- **Configurations and state.** For each locality, the compiler creates:
  - `cfg_<Role>` structs holding immutable parameters (pre-configured crypto keys).
  - `state_<Role>` structs representing mutable session state (stateful AEAD counters).

- **Session APIs.** Functions such as `cfg_Server::owl_server_send` and `cfg_Server::owl_server_recv` correspond to Owl `def` blocks. They accept a tracked `ITreeToken` (synchronising with the specification), mutate the role state, and produce either results or errors (`OwlError`).

- **Constants and specifications.** The module exports both spec- and exec-level constants describing crypto parameters (`SPEC_CIPHER`, `CIPHER`, etc.) and message formats (`SPEC_BYTES_CONST_*`). Generated proofs rely on these constants matching the runtime behaviour.

- **Public and secret buffers.** The generated code uses `OwlBuf` for public data (corresponding to `Data<adv>` in Owl) and `SecretBuf` for secret data (corresponding to secret names and values with secret labels).

### Client example
The `client_example` directory contains a small example of a verified application using a cryptographic protocol. It provides a simple echo server that receives an encrypted message, decrypts it, encrypts the same plaintext under a different key, and sends it back to the client.
The file `server.rs` contains a simple harness that shows how to implement the `OwlEffects` trait and wire the generated API into an application.

## Interaction trees and specifications

Owl embeds protocol specifications using **interaction trees** (ITrees), which provide a structured representation of protocol behavior as sequences of effectful operations (I/O, random sampling, and declassification). The generated Verus code includes specification functions that construct ITree values representing the protocol's control flow and I/O behavior.

### What are interaction trees?

An `ITree<A>` is a recursive data structure that represents an effectful computation returning a value of type `A`. ITrees have the following variants:

- **`Input`**: Represents receiving data from the network, containing a continuation that specifies how to proceed with the received data.
- **`Output`**: Represents sending data to the network, containing the data to send, an optional endpoint to send to, and a continuation.
- **`Sample`**: Represents sampling randomness (e.g., generating nonces or keys), containing the length to sample and a continuation.
- **`Declassify`**: Represents operations that declassify secret information (e.g., decryption, MAC verification), containing a declassifying operation and a continuation.
- **`Ret`**: Represents the final return value of the protocol operation.

These variants compose to form tree structures that capture the complete I/O behavior of a protocol, enabling Verus to reason about information flow and correctness properties.

### The `owl_spec!` macro

The compiler generates specifications using the `owl_spec!` macro, which provides a domain-specific language for constructing ITrees from Owl source code. The macro translates Owl protocol definitions into ITree specifications that Verus can verify.

For each `def` block in your Owl source code, the compiler generates a corresponding `*_spec` function. For example, if your Owl code defines:

```owl
def server_send(m: Data<adv>):
    ...
```

The compiler generates a Verus specification function:

```rust
pub open spec fn server_send_spec(
    cfg: cfg_Server,
    mut_state: state_Server,
    m: Seq<u8>
) -> (res: ITree<(owlSpec_ServerResult, state_Server), Endpoint>) {
    owl_spec!(mut_state, state_Server,
        // ... translated Owl code ...
    )
}
```

The `owl_spec!` macro accepts two type parameters (the mutable state variable name and its type) followed by an expression written in a syntax that mirrors Owl's language constructs. The macro is defined in `extraction/src/speclib.rs`.

For more details on the theoretical foundations of our verification strategy, and how our ITrees connect to the executable code, see Section 4 of [our USENIX Security 2025 paper](https://eprint.iacr.org/2025/1092.pdf).

## Notes on reusability

The following section is based on the [artifact appendix](https://doi.org/10.5281/zenodo.15605318) that accompanies our USENIX Security 2025 paper. It discusses important security considerations related to incorporating code generated by Owl into larger codebases, whether verified or unverified.

> The echo server illustrates how to connect a library generated by OwlC
> to a larger verified codebase. Verus will verify that the application
> logic follows its specifications. However, as
> discussed in our USENIX Security 2025 paper, Verus does not presently feature
> information-flow control or cryptographic reasoning, so it cannot
> prove cryptographic security properties about handwritten
> specifications. Developers must therefore take care that any handwritten
> specifications do not leak protocol secrets or otherwise compromise the
> security properties of the code proven in Owl. The best practice for
> developing verified applications using OwlC is to write as much of the
> application logic as possible in Owl, with handwritten specifications only for
> simple interfaces and functionality that does not directly interact
> with secrets.
>
> ### Incorporating code generated by OwlC into larger Rust projects
>
> OwlC generates a library crate that can straightforwardly be integrated into
> verified code in Verus. Examples of this are in the `echo_server_example`
> directory, as we discuss below. Our WireGuard and HPKE case studies
> illustrate how to integrate the generated libraries into pre-existing Rust codebases.
> We discuss some high-level considerations here.
>
> Integrating a library generated by OwlC into a pre-existing Rust
> codebase requires building an interface between verified and
> unverified code. As with any such interface, the developer must make
> sure that the unverified calling context satisfies the preconditions
> of the verified routine. For OwlC, this means that all arguments to
> generated protocol routines must match the Owl types of the
> corresponding Owl protocol routine. That is, if an Owl routine takes
> as argument a key `k`, then the generated Verus routine must only be
> called with the runtime value of the key `k`.
>
> OwlC relies on Rust abstract types and Verus verification conditions
> to maintain important soundness and correctness properties. Our `SecretBuf`
> wrapper types are opaque, so that implementation code cannot leak secrets via side
> channels. However, connecting to unverified Rust code may necessitate
> breaking some of these abstraction barriers. For instance, an
> application may need to reveal a `SecretBuf` to display a
> decrypted plaintext message to the user.
>
> When connecting to unverified code, developers may therefore need to
> add "escape hatches" that enable such functionality. This must be
> done with extreme care. We recommend that any such escape hatches be
> annotated with a Verus precondition of `requires false`, so
> that verified code cannot use them, and the generated libraries
> remain sound.


