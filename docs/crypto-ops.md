# Overview of cryptographic typing rules

Each cryptographic primitive in Owl is modeled in the following way:
- First, we have a name type `nt` that corresponds to the primitive;
- Next, for each name type, we have a collection of typed cryptographic
operations. Each operation has two typing rules: a _well-typed_ rule,
which captures the security guarantees of the operation, and an
_overapproximating_ rule, which applies when the well-typed rule does not. 

## Secrecy and corruption

Owl encodes static corruption by modeling the adversary via a label, `adv`,
that remains constant throughout typechecking. Many cryptographic operations
rely on secrecy hypotheses of the form `sec(n)`, where `n` is a name; the
proposition `sec(n)` is an abbreviation for `[n] <= adv`. Similarly, `corr(n)`
is an abbreviatino for `[n] !<= adv`. 

Whenever a rule requires that `sec(n)` holds, then we need to perform a
`corr_case` if one has not already been performed for `n`. For example:

    corr_case k in
    input i in 
    case adec(get(k), i) {
        | Some m => ..
        | None => ..
    }

## Overapproximating rule

For every cryptographic operation, if the type constraints for that operation
are not met, then we overapproximate the type with IFC labels. For example, 
`adec(x, y)`  requires that `x : Name(n)` where `n : enckey t`, `y : Data<adv>`, and
`sec(x)`. 
If any of the three hypotheses are not met, we use the following rule:

    x : Data<L1>
    y : Data<L2>
    ------------
    adec(x, y) : Data<L1 /\ L2>

## Authenticated encryption

Given a type `t`, the name type `enckey t` corresponds to an authenticated
encryption scheme for encrypting values of type `t`. 
Because encryption leaks the lengths of plaintexts, we require that the type `t`
has _public lengths_. This requirement is usually easily met. 
Let `n` be a name with type `enckey t`. There are two operations for `n`: 
- Encryption, `aenc(x,y)`: If `x : Name(n)` and `y : t`, then `aenc(x, y) : Data<adv>`. 
- Decryption `adec(x, y):` If `x : Name(n)`, `y : Data<adv>`, and `sec(x)`, then `adec(x, y) : Option t`.
Decryption returns an option type, as decryption will fail if the tag fails to verify.

## Signatures, MACs

TODO

## PKE

TODO

## Nonces

Nonces model opaque random bytes, and have no additional cryptographic typing
rules.



