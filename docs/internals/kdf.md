KDFs in Owl
===========


## Concrete syntax

In code, we call `kdf` with the following syntax.
```
kdf<salt selector, ikm selector, output pattern, output selector>(salt, ikm, info)
```

When defining names, we have: `kdf` becomes `KDF_SaltPos`, `dualkdf` becomes `KDF_IKMPos`; `odh` becomes `KDF_IKMPos`.



## Terminology

**Key position**: the position of the key argument to the kdf (i.e., `salt` or `ikm`).



Rules
=====

The rules below ignore the functionality of `findGoodKDFSplits` in the typechecker. That function essentially considers 
a bunch of corruption scenarios for the names that may appear in the KDF expression and attempts to 
derive a type for the KDF for each, joining the results together with `if ... then ... else ...` types.

Currently I'm ignoring indices (they seem to just get substituted at the "right" places). _TODO_ go back and add them in,
hopefully without muddying the waters too much.

### Notation
Each premise of the rule is written on a new line (except where otherwise marked).
Rule conclusions may span multiple lines (just to make it easier to read).

`G` represents the overall typing context. `G[k]`, where `k` is a name, means look up `k` in `G` as a name definition.
Elsewhere, `x[i]` means list indexing, where `x` is a list of some kind and `i` is a numeric index.
`p[x := y]` means capture-avoiding substitution of term `y` for variable `x` in `p`.

`dhpk()` is not written explicitly.


## `CKDF` case in `checkCryptoOp`:

**Good case**
```
G |- c <= adv
G |- validKDFKey((ann1,ann2,a,b,c), kdfkey, kdfCasePat, kdfCaseStrictness)
G |- kdfkey !<= adv
kdfCasePat conforms with nks
kdfCasePat[j] = N
---------------------------------------------------------------------------
G |- kdf<ann1,ann2,nks,j>(a,b,c) : 
    x:Name(KDFName(a,b,c,nks,j,N,True)){ 
        strictnessOf(N, kdfCaseStrictness)
        /\ |x| = |nks[j]| 
        /\ x = gkdf<nks,j>(a,b,c)
    }
```
Here, "`kdfCasePat` conforms with `nks`" means that the row of name kinds in `nks` is 
compatible with the row of name types defined by the `kdfCasePat`.

**Well-typed, key corrupt case**
_TODO_ can only use this rule if the "good case" rule does not apply.
_TODO_ do we add more IFC annotations based on the arguments that are secret
```
G |- c <= adv
G |- validIKM_ODHKey((ann1,ann2,a,b,c), kdfkey, kdfCasePat, kdfCaseStrictness)
G |- pubIKM(kdfkey)
kdfCasePat conforms with nks
---------------------------------------------------------------------------
G |- kdf<ann1,ann2,nks,j>(a,b,c) : 
    x:Data<adv>{ 
        /\ |x| = |nks[j]| 
        /\ x = gkdf<nks,j>(a,b,c)
    }
```

**Ill-typed case**
```
G |- a <= adv
G |- b <= adv
G |- c <= adv
---------------------------------------------------------------------------
G |- kdf<ann1,ann2,nks,j>(a,b,c) : 
    x:Data<adv>{ 
        /\ |x| = |nks[j]| 
        /\ x = gkdf<nks,j>(a,b,c)
    }
```


## `validKDFKey(kdfArgs, kdfkey, kdfCasePat, kdfCaseStrictness)`
Given some arguments from the function call, figure out which kdf key to use and which case of the pattern we are in.
The rules are ignoring the consistency check and unification in `unifyKDFKCallResult`, `findBestKDFCallResult`, `unifyValidKDFResults`
(see comments in `Typing.hs` for how those work).
- `kdfArgs`: `(ann1, ann2, a, b, c)` from the kdf call

There are three cases to consider: salt position keys, IKM position keys, and ODH keys (must be in IKM position).

```
G |- validSaltKey((ann1,a,b,c), kdfkey, kdfCasePat, kdfCaseStrictness)
---------------------------------------------------------------------------
G |- validKDFKey((ann1,ann2,a,b,c), kdfkey, kdfCasePat, kdfCaseStrictness)
```

```
G |- validIKMKey((ann2,a,b,c), kdfkey, kdfCasePat, kdfCaseStrictness)
---------------------------------------------------------------------------
G |- validKDFKey((ann1,ann2,a,b,c), kdfkey, kdfCasePat, kdfCaseStrictness)
```

```
G |- validODHKey((ann2,a,b,c), kdfkey, kdfCasePat, kdfCaseStrictness)
---------------------------------------------------------------------------
G |- validKDFKey((ann1,ann2,a,b,c), kdfkey, kdfCasePat, kdfCaseStrictness)
```


## `validSaltKey((saltAnn,salt,b,c), kdfkey, kdfCasePat, kdfCaseStrictness)`
See `findValidSaltCalls` and `matchKDF` in the code.

```
i ∈ saltAnn
G |- salt : Name(kdfkey) // modulo refinements, etc
G[kdfkey] = kdf {ikm info self. ..., i: p -> kdfCaseStrictness kdfCasePat, ... }
G |- p[ikm := b, info := c, self := salt] is true
--------------------------------------------------------------------------------
G |- validSaltKey((saltAnn,salt,b,c), kdfkey, kdfCasePat, kdfCaseStrictness)
```


## `validIKMKey((ikmAnn,a,ikm,c), kdfkey, kdfCasePat, kdfCaseStrictness)`
See `findValidIKMCalls`, `unconcatIKM`, and `matchKDF` in the code. _TODO_ confirm the concat handling, but
it seems like we enforce that the `ikm'` must be an honest name sandwiched between only public stuff
(since we use `unifyKDFCallResult` across all the splits of the IKM).

```
i ∈ ikmAnn
ikm = preIkm ++ ikm' ++ postIkm
G |- pubIKM(a, preIkm, c)
G |- pubIKM(a, postIkm, c)
G |- ikm' : Name(kdfkey) // modulo refinements, etc
G[kdfkey] = kdf {salt info self. ..., p -> kdfCaseStrictness kdfCasePat, ... }
G |- p[salt := a, info := c, self := ikm] is true
--------------------------------------------------------------------------------
G |- validIKMKey((ikmAnn,a,ikm,c), kdfkey, kdfCasePat, kdfCaseStrictness)
```


## `validODHKey((ikmAnn,a,ikm,c), kdfkey, kdfCasePat, kdfCaseStrictness)`
See `findValidIKMCalls`, `unconcatIKM`, and `matchODH` in the code. _TODO_ confirm the concat handling, but
it seems like we enforce that the `ikm'` must be an honest name sandwiched between only public stuff
(since we use `unifyKDFCallResult` across all the splits of the IKM).

```
(odhName, ips, i) ∈ ikmAnn // `ips` are indices, _TODO_ handle explicitly
G[odhName] = odh X, Y {salt info self. ..., p -> kdfCaseStrictness kdfCasePat, ... }
ikm = preIkm ++ ikm' ++ postIkm
G |- pubIKM(a, preIkm, c)
G |- pubIKM(a, postIkm. c)
G |- ikm' = dh_combine(X, Y)
G |- X !<= adv
G |- Y !<= adv
G |- p[salt := a, info := c, self := ikm] is true
--------------------------------------------------------------------------------
G |- validODHKey((ikmAnn,a,ikm,c), [X,Y], kdfCasePat, kdfCaseStrictness)
```
_NOTE_: in the typechecker, we don't exactly return `[X,Y]` as `kdfkey`; but I think this suffices because the rules check if
`kdfkey` is public to see if we are in the good case or the well-typed but corrupt case. We need to check that `X` and `Y` are both secret.


## `pubIKM(a, b, c)`
A value in IKM position is public if it is either actually public (flows to adv), or if it is a DH shared secret that
is not declared as part of any `odh` declaration (via PRF-ODH), or if it is a DH shared secret that does match an existing
ODH declaration, but one of the keys in the pair is public. 
See `kdfOOB` in the code.

```
G |- b <= adv
-----------------------------
G |- pubIKM(a,b,c)
```

```
G |- !in_odh(a,b,c)
-----------------------------
G |- pubIKM(a,b,c)
```

```
G |- in_odh(a,b,c)
G |- b = dh_combine(X, Y)
G |- X <= adv
-----------------------------
G |- pubIKM(a,b,c)
```

```
G |- in_odh(a,b,c)
G |- b = dh_combine(X, Y)
G |- Y <= adv
-----------------------------
G |- pubIKM(a,b,c)
```



## Ancillary definitions:

### `in_odh(a,b,c)`:
_TODO_ fill this in formally. Checks whether `kdf(a,b,c)` corresponds to any valid ODH call, i.e.,
`b = dh_combine(X, Y)` for some `X` and `Y` that appear as `odh X, Y -> {...}` somewhere in scope.

Owl restricts `odh` declarations to only have pairs of keys that appear in the local module 
(so we can iterate through all of them). All names must be defined before any `def`s appear, so
that we can't add a later `odh` call that invalidates the `in_odh` assumption. See `ensureNoConcreteDefs`


### `strictnessOf(N, strictness)`:
So as to not have three copies of the good-case typing rule, we separate out the 
result of the strictness annotation.
```
strictnessOf(N, KDFStrict) := N !<= adv
strictnessOf(N, KDFPub) := N <= adv
strictnessOf(N, KDFUnstrict) := True (doesn't add any refinement)
```


# High-level differences between the rules and the code
- The rules only focus on the "good" path of finding a key that works, and don't show consistency/unification of multiple possible hints; this is fine since the three top-level rules cover all the cases.





