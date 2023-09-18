# Intro to Owl

Owl is a new language for _security by typing_ for cryptographic
communication protocols (e.g., Kerberos, WireGuard, and TLS).

### Example: Encrypted Key

We begin with an example: suppose Alice and Bob already have a 
pre-shared key, `psk`, and want to use it to exchange a data key, `k_data`. so that later on, they can use `k_data` to exhange a secret nonce `x`:

    A, B already have key psk 

    A -> B : {k_data}_psk 

    B -> A : {x}_(k_data)

    A : retrieve x

First, Alice sends Bob an encryption of `k_data` under `psk`. In return, Bob sends Alice an encryption of `x` under `k_data`. After recieving Bob's message, 
Alice can obtain the value of `x` by decrypting Bob's message using `k_data`.  
While this protocol is simple, it naturally scales 
to real-world use cases, such as the protocol underlying Kerberos.

We will describe the Owl version of the protocol in sections. The full protocol is given [here](encrypted_key_basic.owl).
We can run and typecheck this protocol via `cabal run owl -- docs/encrypted_key_basic.owl`. 


To encode this protocol in Owl, we first specify the _localities_, which comprise the parties of the protocol:

    locality alice
    locality bob

Next, we specify the _names_ for the protocol. Names correspond to cryptographic secrets, such as keys and nonces. There are three names for our protocol: `psk`, `k_data`, and `x`. The corresponding name declarations are given below:

    name x : nonce @ bob
    name k_data : enckey Name(x) @ alice 
    name psk : enckey Name(k_data) @ alice, bob 

#### Name Declarations

Name declarations are of the form `name N : nt @ L`, where `N` is the identifier for the name, `nt` is a _name type_, and `L` is a set of localities. The localities constrain where the name is randomly sampled and stored. Names which are stored at two localities, such as `psk`, correspond to a trusted joint setup, while names stored at one locality, such as `k_data`, may be sampled lazily whenever they are needed. 

#### Name Types

Name types constrain how the name is sampled and how it may be used. We see two name types above: `nonce`, which corresponds to opaque, random data; and
`enckey t`, which corresponds to an authenticated symmetric encryption key (e.g., AES-GCM) for data of type `t`. Additional name types include `sigkey t` for signing keys, `mackey t` for message authentication codes (MACs), and `DH`, for Diffie-Hellman keys. 

#### Encryption Keys in Owl

The name type `enckey t` contains a type, `t`, for the underlying data the key is meant to encrypt. In our example, `psk` encrypts data of type `Name(k_data)`. Here, `Name(n)` is a _singleton_ type for the value of name `n`; thus, our protocol will maintain and enforce that (unless `psk` is corrupt) that valid ciphertexts under `psk` only contain `k_data`, and nothing else. Similarly, 
`k_data` only may encrypt the value of `x`. 

### Structs and Enums 

Data types in Owl, in addition to the `Name(n)` type, can express arbitrary structs and enums. Our protocol uses a `Result` enum, defined below:

    enum Result {
        | SomeResult Name(x)
        | NoResult
    }

Currently, enums may have either zero or one pieces of data attached to constructors. 

### The Protocol: Alice

One of the main novel features of Owl is that procedures for different parties may be type checked _independently_. As long as Alice's code satsifies the key constraints given by the name declarations, we are guaranteed that Alice is secure. 
So, let's begin the protocol with the code for Alice:

    1: def alice_main () @ alice : if sec(k_data) then Result else Data<adv> = 
    2:    let c = samp enc(get(psk), get(k_data)) in
    3:    output c;
    4:    input i in // i : Data<adv> 
    5:    corr_case k_data in
    6:    let res = dec(get(k_data), i) in 
    7:    case res {
    8:        | Some j => SomeResult(j)
    9:        | None => NoResult()
    10:   }

Line 1 defines `alice_main`, the main procedure for Alice. Other than the name, we know it's Alice's procedure since it's annotated with the locality `alice`. We'll get back to the type annotation for `alice_main` in a little bit.

First, Alice needs to encrypt `k_data` under `psk`; this is done in Line 2. 
The expression `samp enc(x, y)` performs an encryption of plaintext `y` under key `x`. 
The key and plaintext are given by `get(psk)` and `get(k_data)`; here, `get(N)` retrieves the locally known value of name `N`. The `get(N)` operation requires that we are currently in a valid locality for `N`. (Thus, since `x` is stored only at `bob`, perfoming `get(x)` in Alice's code would raise an error).

#### Input and Output

Next, Line 3 performs an output, which sends the value `c` to the network. In Owl, we protect security against an attacker who we assume controls the entire network. Indeed, Alice and Bob cannot talk to each other directly, but only through the attacker-controlled network. 

After outputting the ciphertext, Alice moves to the second stage, where she gets a message from Bob and attempts to decrypt it. Line 4 performs an `input` expression, retrieving a message from the network and binding it to `i`. 
Since the attacker controls the network, we don't have any guarantee about the value of `i`, other than it came from the attacker; thus, `i` has type `Data<adv>`, which stands for arbitrary public data, possibly controlled by the attacker. Here, `adv` is a _label_, which is used to specify information flow properties. We'll explain labels below.

The central invariant of Owl is that all data flowing in an out of the attacker has label `Data<adv>`. Thus, Owl checks in Line 3 that `c` has type `Data<adv>` as well.

#### Labels, Decryption and `corr_case`

Now, Alice needs to perform the decryption using `k_data`. Since all cryptography in Owl is strongly typed, we expect that the result of decryption will have the type corresponding to `k_data`'s name type, `Name(x)`. 

However, this is _not_ the case if `k_data` is obtained by the attacker (e.g., the attacker gains access to Alice's local disk to read `k_data`). We model this capability of the attacker by allowing it to _corrupt_ a set of names before protocol execution. This set of names is given by the information flow label, `adv`. Labels are intuitively sets of names, along with the symbolic label `adv` for the adversary:
``` L ::= 0 | [n] (where n is a name) | L /\ L | adv ```
Labels support a _flows-to_ partial order, `L1 <= L2`, which says if the set of dependencies in `L1` is captured by `L2`. 

If the name `k_data` is corrupt, then when Alice decrypts `i` under `k_data`, we shouldn't expect the result to be `x`; for example, the attacker could encrypt its own nonce under `k_data` instead! This is reflected in the type we compute for `res`, in Line 6:
`res : if sec(k_data) then Option (Name(x)) else Option(Data<adv>)`. 

This type means that either `k_data` is secret (meaning that `[k_data] !<= adv`) and `res : Option(Name(x))`, or `k_data` is corrupt (i.e., `[k_data] <= adv`) and `res : Option(Data<adv>)`. 

To reason about the protocol, we split the type checking into two cases, depending on whether `k_data` is corrupt. This is done in Line 5: `corr_case k_data`. The `corr_case` command is often needed when performing decryptions, signature verifications, etc. (If you don't perform a needed `corr_case`, you'll get an error message about the query `[k_data] <= adv` being inconclusive.)

Finally, we perform a pattern match on `res` in Lines 7-9. 
Because of the previous `corr_case`, this pattern match is checked twice -- once for when `k_data` is secret, and once for when it's corrupt. 

In the secret case, we have that `res : Option(Name(x))`. Thus, when `res` is `Some j`, we have that `j : Name(x)`, and thus `SomeResult(j)` has type `Result`. 

The corrupt case is more subtle. We have that `res : Option(Data<adv>)`, under the assumption that `[k_data] <= adv`; thus, when we match `res` against `Some j`, we have that `j : Data<adv>`. 
In this case, the constructor `SomeResult(j)` _also_ has type `Data<adv>`.
Essentially, all function symbols in Owl can be thought of having two typing rules: a strongly typed one, where the types match up as expected:

    j : Name(x)
    -----------
    SomeResult(j) : Result

and an overapproximating one, where we instead overapproximate all types with `Data<L>`, the type of _arbitrary data with label `L`_: 

    j : Data<L>
    -----------
    SomeResult(j) : Data<L>

The second branch is well-typed when `k_data` is corrupt, since `NoResult()` is a constant, and hence has type `Data<L>` for any `L`.

At the end of the procedure, we have that Alice returns one of two possible types, depending on `adv`:
- If `[k_data] !<= adv`, then we return a value of type `Result`;
- If `[k_data] <= adv`, then we return a value of type `Data<adv>`. 

These two return types unify with the annotated return type of `alice_main`, `if sec(k_data) then Result else Data<adv>`, since this return type _normalizes_ to the corresponding side under one of the two assumptions above on the adversary.

The code for Bob is similar, and can be seen in the source file [here](encrypted_key_basic.owl).

### Hierarchical Label Model

Labels in Owl represent per-name dataflow dependencies. Since `psk` encrypts `k_data`, and `k_data` encrypts `x`, our name declarations induce the following flows:

    [x] <= [k_data]
    [k_data] <= [psk]

Two labels `L1` and `L2` are considered equivalent whenever `L1 <= L2` and `L2 <= L1`. Thus, we have that `[x] /\ [k_data] = [k_data]`. 

#### Hierarchical Corruption
Since labels form a partial order, and corruption is defined via the flows-to relation, we have that corruption is hierarchical as well. For example, if `psk` is corrupt, then we have that `x` is as well, since `[x] <= [k_data] <= [psk] <= adv`. 

### Additional Types

Owl supports the following types:

    t ::=
        | Data<L, |L'|> // arbitrary data with label L, with length label L'
        | Data<L> |a|   // arbitrary data with label L, with length equal to expression a
        | Option(t)
        | if P then t1 else t2 // where P is a proposition
        | s<i> // where s is a struct or enum, and i are index parameters (indices to be explained )
        | Bool<L> // booleans with label L
        | Union<t1, t2> // Union types. Either has type t1 or t2 
        | Unit
        | Name(n) // singleton name type
        | vk(n) // signature verification keys for name n : sigkey t
        | dhpk(n) // diffie-hellman public key for name n : DH
        | encpk(n) // public encryption key for name n : pkekey t
        | shared_secret(n, m) // diffie-hellman shared secret for n : DH, m : DH
        | exists i. t // existential type for indices (to be explained)
