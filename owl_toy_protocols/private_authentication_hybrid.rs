// Extracted verus code from file owl_toy_protocols/private_authentication_hybrid.owl:
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#[cfg_attr(verus_keep_ghost, forbid(unsafe_code))]
pub use vstd::{modes::*, prelude::*, seq::*, view::*};
pub mod speclib;
pub use crate::speclib::{itree::*, *};
pub mod execlib;
pub use crate::execlib::*;
pub mod owl_const_bytes;
pub use crate::owl_const_bytes::*;
pub mod owl_aead;
pub mod owl_dhke;
pub mod owl_hkdf;
pub mod owl_hmac;
pub mod owl_pke;
pub mod owl_util;
pub use vest::{
    properties::*, regular::builder::*, regular::bytes::*, regular::repetition::*,
    regular::sequence::*, regular::tag::*, regular::uints::*, regular::variant::*, regular::*,
    utils::*,
};

pub use std::collections::HashMap;
pub use std::env;
pub use std::fs;
pub use std::io::{self, BufRead, Write};
pub use std::net::{SocketAddr, TcpListener, TcpStream, ToSocketAddrs};
pub use std::str;
pub use std::sync::Arc;
pub use std::thread;
pub use std::time::Duration;
pub use std::time::Instant;

verus! {

pub spec const SPEC_CIPHER: owl_aead::Mode = crate::owl_aead::Mode::Chacha20Poly1305;

pub spec const SPEC_ENCKEY_SIZE: usize = owl_aead::spec_key_size(CIPHER);

pub spec const SPEC_TAG_SIZE: usize = owl_aead::spec_tag_size(CIPHER);

pub spec const SPEC_NONCE_SIZE: usize = owl_aead::spec_nonce_size(CIPHER);

pub spec const SPEC_HMAC_MODE: owl_hmac::Mode = crate::owl_hmac::Mode::Sha512;

pub spec const SPEC_MACKEY_SIZE: usize = owl_hmac::spec_key_size(HMAC_MODE);

pub spec const SPEC_KDFKEY_SIZE: usize = owl_hkdf::spec_kdfkey_size();

pub spec const SPEC_COUNTER_SIZE: usize = 8usize;

pub spec const SPEC_SIGNATURE_SIZE: usize = 64usize;

pub spec const SPEC_MACLEN_SIZE: usize = 16usize;

#[verifier::when_used_as_spec(SPEC_CIPHER)]
pub exec const CIPHER: owl_aead::Mode
    ensures
        CIPHER == SPEC_CIPHER,
{
    crate::owl_aead::Mode::Chacha20Poly1305
}

#[verifier::when_used_as_spec(SPEC_ENCKEY_SIZE)]
pub exec const ENCKEY_SIZE: usize
    ensures
        ENCKEY_SIZE == SPEC_ENCKEY_SIZE,
{
    owl_aead::key_size(CIPHER)
}

#[verifier::when_used_as_spec(SPEC_TAG_SIZE)]
pub exec const TAG_SIZE: usize
    ensures
        TAG_SIZE == SPEC_TAG_SIZE,
{
    owl_aead::tag_size(CIPHER)
}

#[verifier::when_used_as_spec(SPEC_NONCE_SIZE)]
pub exec const NONCE_SIZE: usize
    ensures
        NONCE_SIZE == SPEC_NONCE_SIZE,
{
    owl_aead::nonce_size(CIPHER)
}

#[verifier::when_used_as_spec(SPEC_HMAC_MODE)]
pub exec const HMAC_MODE: owl_hmac::Mode
    ensures
        HMAC_MODE == SPEC_HMAC_MODE,
{
    crate::owl_hmac::Mode::Sha512
}

#[verifier::when_used_as_spec(SPEC_MACKEY_SIZE)]
pub exec const MACKEY_SIZE: usize
    ensures
        MACKEY_SIZE == SPEC_MACKEY_SIZE,
{
    owl_hmac::key_size(HMAC_MODE)
}

#[verifier::when_used_as_spec(SPEC_KDFKEY_SIZE)]
pub exec const KDFKEY_SIZE: usize
    ensures
        KDFKEY_SIZE == SPEC_KDFKEY_SIZE,
{
    owl_hkdf::kdfkey_size()
}

#[verifier::when_used_as_spec(SPEC_COUNTER_SIZE)]
pub exec const COUNTER_SIZE: usize
    ensures
        COUNTER_SIZE == SPEC_COUNTER_SIZE,
{
    8usize
}

#[verifier::when_used_as_spec(SPEC_SIGNATURE_SIZE)]
pub exec const SIGNATURE_SIZE: usize
    ensures
        SIGNATURE_SIZE == SPEC_SIGNATURE_SIZE,
{
    64usize
}

#[verifier::when_used_as_spec(SPEC_MACLEN_SIZE)]
pub exec const MACLEN_SIZE: usize
    ensures
        MACLEN_SIZE == SPEC_MACLEN_SIZE,
{
    16usize
}

pub trait OwlEffects {
    fn owl_output<A>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
        x: &[u8],
        dest_addr: Option<&str>,
        ret_addr: &str,
    )
        requires
            old(t).view().is_output(
                x.view(),
                option_map(view_option(dest_addr), |a| endpoint_of_addr(a)),
            ),
        ensures
            t.view() == old(t).view().give_output(),
    ;

    fn owl_input<A>(&mut self, Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>) -> (ie: (
        Vec<u8>,
        String,
    ))
        requires
            old(t).view().is_input(),
        ensures
            t.view() == old(t).view().take_input(ie.0.view(), endpoint_of_addr(ie.1.view())),
    ;

    fn owl_sample<A, 'a>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
        n: usize,
    ) -> (res: SecretBuf<'a>)
        requires
            old(t).view().is_sample(n),
        ensures
            t.view() == old(t).view().get_sample(res.view()),
            res.len_valid(),
    ;

    fn owl_output_serialize_fused<A, I: VestPublicInput, C: View + Combinator<I, Vec<u8>>>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
        comb: C,
        val: C::Type,
        dest_addr: Option<&str>,
        ret_addr: &str,
    ) where <C as View>::V: SecureSpecCombinator<Type = <C::Type as View>::V>
        requires
            comb@.spec_serialize(val.view()) matches Ok(b) ==> old(t).view().is_output(
                b,
                option_map(view_option(dest_addr), |a| endpoint_of_addr(a)),
            ),
        ensures
            t.view() == old(t).view().give_output(),
    ;
}

// for debugging purposes, not used by the compiler
#[verifier(external_body)]
pub fn debug_print_bytes(x: &[u8]) {
    println!("debug_print_bytes: {:?}", x);
}

#[derive(Debug)]
pub enum OwlError {
    IntegerOverflow,
}

} // verus!
verus! {

// ------------------------------------
// ---------- SPECIFICATIONS ----------
// ------------------------------------
spec fn spec_combinator_owlSpec_m1() -> (((Variable, Variable), Variable), Tail) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(1);
    let field_4 = Tail;
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_m1() -> (res: (((Variable, Variable), Variable), Tail))
    ensures
        res.view() == spec_combinator_owlSpec_m1(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(1);
    let field_4 = Tail;
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_m1 {
    pub owlSpec_m1_n0: Seq<u8>,
    pub owlSpec_m1_r0: Seq<u8>,
    pub owlSpec_m1_pka_tag: Seq<u8>,
    pub owlSpec_m1_pkA_tag: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_m1(x: Seq<u8>) -> Option<owlSpec_m1> {
    let spec_comb = spec_combinator_owlSpec_m1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec_m1_n0, owlSpec_m1_r0), owlSpec_m1_pka_tag), owlSpec_m1_pkA_tag)) = parsed;
        Some(owlSpec_m1 { owlSpec_m1_n0, owlSpec_m1_r0, owlSpec_m1_pka_tag, owlSpec_m1_pkA_tag })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_m1_inner(x: owlSpec_m1) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_m1_n0.len(), x.owlSpec_m1_r0.len(), x.owlSpec_m1_pka_tag.len(), x.owlSpec_m1_pkA_tag.len() ] {
        let spec_comb = spec_combinator_owlSpec_m1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec_m1_n0, x.owlSpec_m1_r0), x.owlSpec_m1_pka_tag), x.owlSpec_m1_pkA_tag)),
        ) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_m1(x: owlSpec_m1) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_m1_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_m1 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_m1(self)
    }
}

pub open spec fn m1(
    arg_owlSpec_m1_n0: Seq<u8>,
    arg_owlSpec_m1_r0: Seq<u8>,
    arg_owlSpec_m1_pka_tag: Seq<u8>,
    arg_owlSpec_m1_pkA_tag: Seq<u8>,
) -> owlSpec_m1 {
    owlSpec_m1 {
        owlSpec_m1_n0: arg_owlSpec_m1_n0,
        owlSpec_m1_r0: arg_owlSpec_m1_r0,
        owlSpec_m1_pka_tag: arg_owlSpec_m1_pka_tag,
        owlSpec_m1_pkA_tag: arg_owlSpec_m1_pkA_tag,
    }
}

spec fn spec_combinator_owlSpec_secret_m1() -> (((Variable, Variable), Variable), Tail) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(1);
    let field_4 = Tail;
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_secret_m1() -> (res: (((Variable, Variable), Variable), Tail))
    ensures
        res.view() == spec_combinator_owlSpec_secret_m1(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(1);
    let field_4 = Tail;
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_secret_m1 {
    pub owlSpec_m1_n0: Seq<u8>,
    pub owlSpec_m1_r0: Seq<u8>,
    pub owlSpec_m1_pka_tag: Seq<u8>,
    pub owlSpec_m1_pkA_tag: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_m1(x: Seq<u8>) -> Option<owlSpec_secret_m1> {
    let spec_comb = spec_combinator_owlSpec_secret_m1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec_m1_n0, owlSpec_m1_r0), owlSpec_m1_pka_tag), owlSpec_m1_pkA_tag)) = parsed;
        Some(
            owlSpec_secret_m1 {
                owlSpec_m1_n0,
                owlSpec_m1_r0,
                owlSpec_m1_pka_tag,
                owlSpec_m1_pkA_tag,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_m1_inner(x: owlSpec_secret_m1) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_m1_n0.len(), x.owlSpec_m1_r0.len(), x.owlSpec_m1_pka_tag.len(), x.owlSpec_m1_pkA_tag.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_m1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec_m1_n0, x.owlSpec_m1_r0), x.owlSpec_m1_pka_tag), x.owlSpec_m1_pkA_tag)),
        ) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_m1(x: owlSpec_secret_m1) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_secret_m1_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_m1 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_m1(self)
    }
}

pub open spec fn secret_m1(
    arg_owlSpec_m1_n0: Seq<u8>,
    arg_owlSpec_m1_r0: Seq<u8>,
    arg_owlSpec_m1_pka_tag: Seq<u8>,
    arg_owlSpec_m1_pkA_tag: Seq<u8>,
) -> owlSpec_secret_m1 {
    owlSpec_secret_m1 {
        owlSpec_m1_n0: arg_owlSpec_m1_n0,
        owlSpec_m1_r0: arg_owlSpec_m1_r0,
        owlSpec_m1_pka_tag: arg_owlSpec_m1_pka_tag,
        owlSpec_m1_pkA_tag: arg_owlSpec_m1_pkA_tag,
    }
}

spec fn spec_combinator_owlSpec_m2() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_m2() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_m2(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_m2 {
    pub owlSpec_m2_n0: Seq<u8>,
    pub owlSpec_m2_n: Seq<u8>,
    pub owlSpec_m2_r: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_m2(x: Seq<u8>) -> Option<owlSpec_m2> {
    let spec_comb = spec_combinator_owlSpec_m2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec_m2_n0, owlSpec_m2_n), owlSpec_m2_r)) = parsed;
        Some(owlSpec_m2 { owlSpec_m2_n0, owlSpec_m2_n, owlSpec_m2_r })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_m2_inner(x: owlSpec_m2) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_m2_n0.len(), x.owlSpec_m2_n.len(), x.owlSpec_m2_r.len() ] {
        let spec_comb = spec_combinator_owlSpec_m2();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec_m2_n0, x.owlSpec_m2_n), x.owlSpec_m2_r)),
        ) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_m2(x: owlSpec_m2) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_m2_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_m2 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_m2(self)
    }
}

pub open spec fn m2(
    arg_owlSpec_m2_n0: Seq<u8>,
    arg_owlSpec_m2_n: Seq<u8>,
    arg_owlSpec_m2_r: Seq<u8>,
) -> owlSpec_m2 {
    owlSpec_m2 {
        owlSpec_m2_n0: arg_owlSpec_m2_n0,
        owlSpec_m2_n: arg_owlSpec_m2_n,
        owlSpec_m2_r: arg_owlSpec_m2_r,
    }
}

spec fn spec_combinator_owlSpec_secret_m2() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_secret_m2() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_m2(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_secret_m2 {
    pub owlSpec_m2_n0: Seq<u8>,
    pub owlSpec_m2_n: Seq<u8>,
    pub owlSpec_m2_r: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_m2(x: Seq<u8>) -> Option<owlSpec_secret_m2> {
    let spec_comb = spec_combinator_owlSpec_secret_m2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec_m2_n0, owlSpec_m2_n), owlSpec_m2_r)) = parsed;
        Some(owlSpec_secret_m2 { owlSpec_m2_n0, owlSpec_m2_n, owlSpec_m2_r })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_m2_inner(x: owlSpec_secret_m2) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_m2_n0.len(), x.owlSpec_m2_n.len(), x.owlSpec_m2_r.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_m2();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec_m2_n0, x.owlSpec_m2_n), x.owlSpec_m2_r)),
        ) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_m2(x: owlSpec_secret_m2) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_secret_m2_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_m2 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_m2(self)
    }
}

pub open spec fn secret_m2(
    arg_owlSpec_m2_n0: Seq<u8>,
    arg_owlSpec_m2_n: Seq<u8>,
    arg_owlSpec_m2_r: Seq<u8>,
) -> owlSpec_secret_m2 {
    owlSpec_secret_m2 {
        owlSpec_m2_n0: arg_owlSpec_m2_n0,
        owlSpec_m2_n: arg_owlSpec_m2_n,
        owlSpec_m2_r: arg_owlSpec_m2_r,
    }
}

#[verifier::opaque]
pub open spec fn A_main_spec(cfg: cfg_A, mut_state: state_A) -> (res: ITree<
    ((), state_A),
    Endpoint,
>) {
    owl_spec!(mut_state, state_A,
        let hybridKA = ((ret(cfg.owl_hybrid_skA.view()))) in
let enc_hybridKA = ((ret(pkenc(cfg.pk_owl_pkB.view(), hybridKA)))) in
(output (enc_hybridKA) to (Some(Endpoint::Loc_B))) in
let m = ((ret(m1(cfg.owl_n0.view(), cfg.owl_r0.view(), seq![0x01u8 ], cfg.pk_owl_pkA.view())))) in
let encm = ((sample(NONCE_SIZE, enc(hybridKA, serialize_owlSpec_m1(m))))) in
(output (encm) to (Some(Endpoint::Loc_B))) in
(input(enc_hybridKB,_16)) in
(input(inp,_18)) in
let caseval = ((declassify(DeclassifyingOp::PkDec(cfg.owl_pkA.view(), enc_hybridKB))) in
(ret(pkdec(cfg.owl_pkA.view(), enc_hybridKB)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(hybridKB) => {
let caseval = ((declassify(DeclassifyingOp::ADec(hybridKB, inp))) in
(ret(dec(hybridKB, inp)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(_unused74) => {
(ret(()))
},
}
)
},
}
)
    )
}

#[verifier::opaque]
pub open spec fn B_main_spec(cfg: cfg_B, mut_state: state_B) -> (res: ITree<
    ((), state_B),
    Endpoint,
>) {
    owl_spec!(mut_state, state_B,
        let privKey = ((ret(cfg.owl_pkB.view()))) in
(input(enc_hybridKA,_27)) in
(input(inp,_29)) in
let caseval = ((declassify(DeclassifyingOp::PkDec(privKey, enc_hybridKA))) in
(ret(pkdec(privKey, enc_hybridKA)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(hybridKA) => {
let caseval = ((declassify(DeclassifyingOp::ADec(hybridKA, inp))) in
(ret(dec(hybridKA, inp)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(m) => {
let m_ = ((ret(m))) in
(parse (parse_owlSpec_secret_m1(m_)) as (owlSpec_secret_m1{owlSpec_m1_n0 : n0_, owlSpec_m1_r0 : foo, owlSpec_m1_pka_tag : bar, owlSpec_m1_pkA_tag : m1_pkA}) in {
let declassified_buf48 = ((declassify(DeclassifyingOp::ControlFlow(bar))) in
(ret((bar)))) in
let declassified_buf51 = ((declassify(DeclassifyingOp::ControlFlow(m1_pkA))) in
(ret((m1_pkA)))) in
let eq_bool54 = ((declassify(DeclassifyingOp::EqCheck(n0_, cfg.owl_n0.view()))) in
(ret(n0_ == cfg.owl_n0.view()))) in
(if (andb(declassified_buf51 == cfg.pk_owl_pkA.view(), eq_bool54)) then
(let hybridKB = ((ret(cfg.owl_hybrid_skB.view()))) in
let enc_hybridKB = ((ret(pkenc(cfg.pk_owl_pkA.view(), hybridKB)))) in
(output (enc_hybridKB) to (Some(Endpoint::Loc_A))) in
let pubKeyA = ((ret(cfg.pk_owl_pkA.view()))) in
let m = ((ret(m2(cfg.owl_n0.view(), cfg.owl_n.view(), cfg.owl_r.view())))) in
let encm = ((sample(NONCE_SIZE, enc(hybridKB, serialize_owlSpec_m2(m))))) in
(output (encm) to (Some(Endpoint::Loc_A))) in
(ret(())))
else
((ret(()))))
} otherwise ((ret(()))))
},
}
)
},
}
)
    )
}

// ------------------------------------
// ---------- IMPLEMENTATIONS ---------
// ------------------------------------
#[derive(Clone,Copy)]
pub enum Endpoint {
    Loc_A,
    Loc_B,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier(external_body)]
pub const fn A_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_A,
{
    "127.0.0.1:9001"
}

#[verifier(external_body)]
pub const fn B_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_B,
{
    "127.0.0.1:9002"
}

pub struct owl_m1<'a> {
    pub owl_m1_n0: SecretBuf<'a>,
    pub owl_m1_r0: SecretBuf<'a>,
    pub owl_m1_pka_tag: OwlBuf<'a>,
    pub owl_m1_pkA_tag: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_m1<'a>(
    arg_owl_m1_n0: SecretBuf<'a>,
    arg_owl_m1_r0: SecretBuf<'a>,
    arg_owl_m1_pka_tag: OwlBuf<'a>,
    arg_owl_m1_pkA_tag: OwlBuf<'a>,
) -> (res: owl_m1<'a>)
    ensures
        res.owl_m1_n0.view() == arg_owl_m1_n0.view(),
        res.owl_m1_r0.view() == arg_owl_m1_r0.view(),
        res.owl_m1_pka_tag.view() == arg_owl_m1_pka_tag.view(),
        res.owl_m1_pkA_tag.view() == arg_owl_m1_pkA_tag.view(),
{
    owl_m1 {
        owl_m1_n0: arg_owl_m1_n0,
        owl_m1_r0: arg_owl_m1_r0,
        owl_m1_pka_tag: arg_owl_m1_pka_tag,
        owl_m1_pkA_tag: arg_owl_m1_pkA_tag,
    }
}

impl<'a> owl_m1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_m1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_m1 {
            owl_m1_n0: SecretBuf::another_ref(&self.owl_m1_n0),
            owl_m1_r0: SecretBuf::another_ref(&self.owl_m1_r0),
            owl_m1_pka_tag: OwlBuf::another_ref(&self.owl_m1_pka_tag),
            owl_m1_pkA_tag: OwlBuf::another_ref(&self.owl_m1_pkA_tag),
        }
    }
}

impl View for owl_m1<'_> {
    type V = owlSpec_m1;

    open spec fn view(&self) -> owlSpec_m1 {
        owlSpec_m1 {
            owlSpec_m1_n0: self.owl_m1_n0.view(),
            owlSpec_m1_r0: self.owl_m1_r0.view(),
            owlSpec_m1_pka_tag: self.owl_m1_pka_tag.view(),
            owlSpec_m1_pkA_tag: self.owl_m1_pkA_tag.view(),
        }
    }
}

pub exec fn parse_owl_m1<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_m1<'a>>)
    ensures
        res is Some ==> parse_owlSpec_m1(arg.view()) is Some,
        res is None ==> parse_owlSpec_m1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_m1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_m1);
    let exec_comb = exec_combinator_owl_m1();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (((owl_m1_n0, owl_m1_r0), owl_m1_pka_tag), owl_m1_pkA_tag) = parsed;
        Some(
            owl_m1 {
                owl_m1_n0: SecretBuf::from_buf(owl_m1_n0.another_ref()),
                owl_m1_r0: SecretBuf::from_buf(owl_m1_r0.another_ref()),
                owl_m1_pka_tag: OwlBuf::another_ref(&owl_m1_pka_tag),
                owl_m1_pkA_tag: OwlBuf::another_ref(&owl_m1_pkA_tag),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_m1_inner<'a>(arg: &owl_m1<'a>) -> (res: Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_m1_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_m1_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_m1_inner);
    if no_usize_overflows![ arg.owl_m1_n0.len(), arg.owl_m1_r0.len(), arg.owl_m1_pka_tag.len(), arg.owl_m1_pkA_tag.len(), 0 ] {
        let exec_comb = exec_combinator_owl_m1();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl_m1_n0.len() + arg.owl_m1_r0.len() + arg.owl_m1_pka_tag.len()
                + arg.owl_m1_pkA_tag.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        SecretBuf::another_ref(&arg.owl_m1_n0),
                        SecretBuf::another_ref(&arg.owl_m1_r0),
                    ),
                    SecretBuf::from_buf(arg.owl_m1_pka_tag.another_ref()),
                ),
                SecretBuf::from_buf(arg.owl_m1_pkA_tag.another_ref()),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_m1_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_m1<'a>(arg: &owl_m1<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_m1(arg.view()),
{
    reveal(serialize_owlSpec_m1);
    let res = serialize_owl_m1_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_m1<'a> {
    pub owl_m1_n0: SecretBuf<'a>,
    pub owl_m1_r0: SecretBuf<'a>,
    pub owl_m1_pka_tag: SecretBuf<'a>,
    pub owl_m1_pkA_tag: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_m1<'a>(
    arg_owl_m1_n0: SecretBuf<'a>,
    arg_owl_m1_r0: SecretBuf<'a>,
    arg_owl_m1_pka_tag: SecretBuf<'a>,
    arg_owl_m1_pkA_tag: SecretBuf<'a>,
) -> (res: owl_secret_m1<'a>)
    ensures
        res.owl_m1_n0.view() == arg_owl_m1_n0.view(),
        res.owl_m1_r0.view() == arg_owl_m1_r0.view(),
        res.owl_m1_pka_tag.view() == arg_owl_m1_pka_tag.view(),
        res.owl_m1_pkA_tag.view() == arg_owl_m1_pkA_tag.view(),
{
    owl_secret_m1 {
        owl_m1_n0: arg_owl_m1_n0,
        owl_m1_r0: arg_owl_m1_r0,
        owl_m1_pka_tag: arg_owl_m1_pka_tag,
        owl_m1_pkA_tag: arg_owl_m1_pkA_tag,
    }
}

impl<'a> owl_secret_m1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_m1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_m1 {
            owl_m1_n0: SecretBuf::another_ref(&self.owl_m1_n0),
            owl_m1_r0: SecretBuf::another_ref(&self.owl_m1_r0),
            owl_m1_pka_tag: SecretBuf::another_ref(&self.owl_m1_pka_tag),
            owl_m1_pkA_tag: SecretBuf::another_ref(&self.owl_m1_pkA_tag),
        }
    }
}

impl View for owl_secret_m1<'_> {
    type V = owlSpec_secret_m1;

    open spec fn view(&self) -> owlSpec_secret_m1 {
        owlSpec_secret_m1 {
            owlSpec_m1_n0: self.owl_m1_n0.view(),
            owlSpec_m1_r0: self.owl_m1_r0.view(),
            owlSpec_m1_pka_tag: self.owl_m1_pka_tag.view(),
            owlSpec_m1_pkA_tag: self.owl_m1_pkA_tag.view(),
        }
    }
}

pub exec fn parse_owl_secret_m1<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_secret_m1<'a>>)
    ensures
        res is Some ==> parse_owlSpec_secret_m1(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_m1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_m1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_m1);
    let exec_comb = exec_combinator_owl_secret_m1();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (((owl_m1_n0, owl_m1_r0), owl_m1_pka_tag), owl_m1_pkA_tag) = parsed;
        Some(
            owl_secret_m1 {
                owl_m1_n0: SecretBuf::from_buf(owl_m1_n0.another_ref()),
                owl_m1_r0: SecretBuf::from_buf(owl_m1_r0.another_ref()),
                owl_m1_pka_tag: SecretBuf::from_buf(owl_m1_pka_tag.another_ref()),
                owl_m1_pkA_tag: SecretBuf::from_buf(owl_m1_pkA_tag.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_m1<'a>(arg: SecretBuf<'a>) -> (res: Option<owl_secret_m1<'a>>)
    ensures
        res is Some ==> parse_owlSpec_secret_m1(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_m1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_m1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_m1);
    let exec_comb = exec_combinator_owl_secret_m1();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (((owl_m1_n0, owl_m1_r0), owl_m1_pka_tag), owl_m1_pkA_tag) = parsed;
        Some(
            owl_secret_m1 {
                owl_m1_n0: SecretBuf::another_ref(&owl_m1_n0),
                owl_m1_r0: SecretBuf::another_ref(&owl_m1_r0),
                owl_m1_pka_tag: SecretBuf::another_ref(&owl_m1_pka_tag),
                owl_m1_pkA_tag: SecretBuf::another_ref(&owl_m1_pkA_tag),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_m1_inner<'a>(arg: &owl_secret_m1<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_secret_m1_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_m1_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_secret_m1_inner);
    if no_usize_overflows![ arg.owl_m1_n0.len(), arg.owl_m1_r0.len(), arg.owl_m1_pka_tag.len(), arg.owl_m1_pkA_tag.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_m1();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl_m1_n0.len() + arg.owl_m1_r0.len() + arg.owl_m1_pka_tag.len()
                + arg.owl_m1_pkA_tag.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        SecretBuf::another_ref(&arg.owl_m1_n0),
                        SecretBuf::another_ref(&arg.owl_m1_r0),
                    ),
                    SecretBuf::another_ref(&arg.owl_m1_pka_tag),
                ),
                SecretBuf::another_ref(&arg.owl_m1_pkA_tag),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_m1_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_m1<'a>(arg: &owl_secret_m1<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_m1(arg.view()),
{
    reveal(serialize_owlSpec_secret_m1);
    let res = serialize_owl_secret_m1_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_m2<'a> {
    pub owl_m2_n0: SecretBuf<'a>,
    pub owl_m2_n: SecretBuf<'a>,
    pub owl_m2_r: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_m2<'a>(
    arg_owl_m2_n0: SecretBuf<'a>,
    arg_owl_m2_n: SecretBuf<'a>,
    arg_owl_m2_r: SecretBuf<'a>,
) -> (res: owl_m2<'a>)
    ensures
        res.owl_m2_n0.view() == arg_owl_m2_n0.view(),
        res.owl_m2_n.view() == arg_owl_m2_n.view(),
        res.owl_m2_r.view() == arg_owl_m2_r.view(),
{
    owl_m2 { owl_m2_n0: arg_owl_m2_n0, owl_m2_n: arg_owl_m2_n, owl_m2_r: arg_owl_m2_r }
}

impl<'a> owl_m2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_m2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_m2 {
            owl_m2_n0: SecretBuf::another_ref(&self.owl_m2_n0),
            owl_m2_n: SecretBuf::another_ref(&self.owl_m2_n),
            owl_m2_r: SecretBuf::another_ref(&self.owl_m2_r),
        }
    }
}

impl View for owl_m2<'_> {
    type V = owlSpec_m2;

    open spec fn view(&self) -> owlSpec_m2 {
        owlSpec_m2 {
            owlSpec_m2_n0: self.owl_m2_n0.view(),
            owlSpec_m2_n: self.owl_m2_n.view(),
            owlSpec_m2_r: self.owl_m2_r.view(),
        }
    }
}

pub exec fn parse_owl_m2<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_m2<'a>>)
    ensures
        res is Some ==> parse_owlSpec_m2(arg.view()) is Some,
        res is None ==> parse_owlSpec_m2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_m2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_m2);
    let exec_comb = exec_combinator_owl_m2();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl_m2_n0, owl_m2_n), owl_m2_r) = parsed;
        Some(
            owl_m2 {
                owl_m2_n0: SecretBuf::from_buf(owl_m2_n0.another_ref()),
                owl_m2_n: SecretBuf::from_buf(owl_m2_n.another_ref()),
                owl_m2_r: SecretBuf::from_buf(owl_m2_r.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_m2<'a>(arg: SecretBuf<'a>) -> (res: Option<owl_m2<'a>>)
    ensures
        res is Some ==> parse_owlSpec_m2(arg.view()) is Some,
        res is None ==> parse_owlSpec_m2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_m2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_m2);
    let exec_comb = exec_combinator_owl_m2();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let ((owl_m2_n0, owl_m2_n), owl_m2_r) = parsed;
        Some(
            owl_m2 {
                owl_m2_n0: SecretBuf::another_ref(&owl_m2_n0),
                owl_m2_n: SecretBuf::another_ref(&owl_m2_n),
                owl_m2_r: SecretBuf::another_ref(&owl_m2_r),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_m2_inner<'a>(arg: &owl_m2<'a>) -> (res: Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_m2_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_m2_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_m2_inner);
    if no_usize_overflows![ arg.owl_m2_n0.len(), arg.owl_m2_n.len(), arg.owl_m2_r.len(), 0 ] {
        let exec_comb = exec_combinator_owl_m2();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl_m2_n0.len() + arg.owl_m2_n.len() + arg.owl_m2_r.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (SecretBuf::another_ref(&arg.owl_m2_n0), SecretBuf::another_ref(&arg.owl_m2_n)),
                SecretBuf::another_ref(&arg.owl_m2_r),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_m2_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_m2<'a>(arg: &owl_m2<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_m2(arg.view()),
{
    reveal(serialize_owlSpec_m2);
    let res = serialize_owl_m2_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_m2<'a> {
    pub owl_m2_n0: SecretBuf<'a>,
    pub owl_m2_n: SecretBuf<'a>,
    pub owl_m2_r: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_m2<'a>(
    arg_owl_m2_n0: SecretBuf<'a>,
    arg_owl_m2_n: SecretBuf<'a>,
    arg_owl_m2_r: SecretBuf<'a>,
) -> (res: owl_secret_m2<'a>)
    ensures
        res.owl_m2_n0.view() == arg_owl_m2_n0.view(),
        res.owl_m2_n.view() == arg_owl_m2_n.view(),
        res.owl_m2_r.view() == arg_owl_m2_r.view(),
{
    owl_secret_m2 { owl_m2_n0: arg_owl_m2_n0, owl_m2_n: arg_owl_m2_n, owl_m2_r: arg_owl_m2_r }
}

impl<'a> owl_secret_m2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_m2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_m2 {
            owl_m2_n0: SecretBuf::another_ref(&self.owl_m2_n0),
            owl_m2_n: SecretBuf::another_ref(&self.owl_m2_n),
            owl_m2_r: SecretBuf::another_ref(&self.owl_m2_r),
        }
    }
}

impl View for owl_secret_m2<'_> {
    type V = owlSpec_secret_m2;

    open spec fn view(&self) -> owlSpec_secret_m2 {
        owlSpec_secret_m2 {
            owlSpec_m2_n0: self.owl_m2_n0.view(),
            owlSpec_m2_n: self.owl_m2_n.view(),
            owlSpec_m2_r: self.owl_m2_r.view(),
        }
    }
}

pub exec fn parse_owl_secret_m2<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_secret_m2<'a>>)
    ensures
        res is Some ==> parse_owlSpec_secret_m2(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_m2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_m2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_m2);
    let exec_comb = exec_combinator_owl_secret_m2();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl_m2_n0, owl_m2_n), owl_m2_r) = parsed;
        Some(
            owl_secret_m2 {
                owl_m2_n0: SecretBuf::from_buf(owl_m2_n0.another_ref()),
                owl_m2_n: SecretBuf::from_buf(owl_m2_n.another_ref()),
                owl_m2_r: SecretBuf::from_buf(owl_m2_r.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_m2<'a>(arg: SecretBuf<'a>) -> (res: Option<owl_secret_m2<'a>>)
    ensures
        res is Some ==> parse_owlSpec_secret_m2(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_m2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_m2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_m2);
    let exec_comb = exec_combinator_owl_secret_m2();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let ((owl_m2_n0, owl_m2_n), owl_m2_r) = parsed;
        Some(
            owl_secret_m2 {
                owl_m2_n0: SecretBuf::another_ref(&owl_m2_n0),
                owl_m2_n: SecretBuf::another_ref(&owl_m2_n),
                owl_m2_r: SecretBuf::another_ref(&owl_m2_r),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_m2_inner<'a>(arg: &owl_secret_m2<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_secret_m2_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_m2_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_secret_m2_inner);
    if no_usize_overflows![ arg.owl_m2_n0.len(), arg.owl_m2_n.len(), arg.owl_m2_r.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_m2();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl_m2_n0.len() + arg.owl_m2_n.len() + arg.owl_m2_r.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (SecretBuf::another_ref(&arg.owl_m2_n0), SecretBuf::another_ref(&arg.owl_m2_n)),
                SecretBuf::another_ref(&arg.owl_m2_r),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_m2_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_m2<'a>(arg: &owl_secret_m2<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_m2(arg.view()),
{
    reveal(serialize_owlSpec_secret_m2);
    let res = serialize_owl_secret_m2_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct state_A {}

impl state_A {
    #[verifier::external_body]
    pub fn init_state_A() -> Self {
        state_A {  }
    }
}

pub struct cfg_A<'A> {
    pub owl_hybrid_skA: SecretBuf<'A>,
    pub owl_r0: SecretBuf<'A>,
    pub owl_pkA: SecretBuf<'A>,
    pub owl_n0: SecretBuf<'A>,
    pub pk_owl_pkB: OwlBuf<'A>,
    pub pk_owl_pkA: OwlBuf<'A>,
}

impl cfg_A<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_A_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_A), Endpoint>>,
        mut_state: &mut state_A,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_A), Endpoint>>), OwlError>)
        requires
            itree.view() == A_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_A), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(A_main_spec);
            let tmp_owl_hybridKA75 = { SecretBuf::another_ref(&self.owl_hybrid_skA) };
            let owl_hybridKA75 = SecretBuf::another_ref(&tmp_owl_hybridKA75);
            let tmp_owl_enc_hybridKA76 = {
                owl_pkenc(
                    OwlBuf::another_ref(&OwlBuf::another_ref(&self.pk_owl_pkB)),
                    SecretBuf::another_ref(&owl_hybridKA75),
                )
            };
            let owl_enc_hybridKA76 = OwlBuf::from_vec(tmp_owl_enc_hybridKA76);
            let owl__77 = {
                effects.owl_output::<((), state_A)>(
                    Tracked(&mut itree),
                    owl_enc_hybridKA76.as_slice(),
                    Some(&B_addr()),
                    &A_addr(),
                );
            };
            let tmp_owl_m78 = {
                owl_m1(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_n0)),
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_r0)),
                    OwlBuf::another_ref(
                        &{
                            let x = mk_vec_u8![0x01u8 ];
                            OwlBuf::from_vec(x)
                        },
                    ),
                    OwlBuf::another_ref(&OwlBuf::another_ref(&self.pk_owl_pkA)),
                )
            };
            let owl_m78 = owl_m1::another_ref(&tmp_owl_m78);
            let tmp_owl_encm79 = {
                let tmp_owl_coins80 = effects.owl_sample::<((), state_A)>(
                    Tracked(&mut itree),
                    NONCE_SIZE,
                );
                let owl_coins80 = SecretBuf::another_ref(&tmp_owl_coins80);
                owl_enc(
                    SecretBuf::another_ref(&owl_hybridKA75),
                    SecretBuf::another_ref(&serialize_owl_m1(&owl_m78)),
                    SecretBuf::another_ref(&owl_coins80),
                )
            };
            let owl_encm79 = OwlBuf::from_vec(tmp_owl_encm79);
            let owl__81 = {
                effects.owl_output::<((), state_A)>(
                    Tracked(&mut itree),
                    owl_encm79.as_slice(),
                    Some(&B_addr()),
                    &A_addr(),
                );
            };
            let (tmp_owl_enc_hybridKB83, owl__82) = {
                effects.owl_input::<((), state_A)>(Tracked(&mut itree))
            };
            let owl_enc_hybridKB83 = OwlBuf::from_vec(tmp_owl_enc_hybridKB83);
            let (tmp_owl_inp85, owl__84) = { effects.owl_input::<((), state_A)>(Tracked(&mut itree))
            };
            let owl_inp85 = OwlBuf::from_vec(tmp_owl_inp85);
            let tmp_owl_caseval86 = {
                let tracked owl_declassify_tok87 = consume_itree_declassify::<
                    ((), state_A),
                    Endpoint,
                >(&mut itree);
                owl_pkdec(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_pkA)),
                    OwlBuf::another_ref(&owl_enc_hybridKB83),
                    Tracked(owl_declassify_tok87),
                )
            };
            let owl_caseval86 = SecretBuf::another_ref_option(&tmp_owl_caseval86);
            match SecretBuf::another_ref_option(&owl_caseval86) {
                Option::None => { (owl_unit(), Tracked(itree)) },
                Option::Some(tmp_owl_hybridKB88) => {
                    let owl_hybridKB88 = SecretBuf::another_ref(&tmp_owl_hybridKB88);
                    let tmp_owl_caseval89 = {
                        let tracked owl_declassify_tok90 = consume_itree_declassify::<
                            ((), state_A),
                            Endpoint,
                        >(&mut itree);
                        owl_dec(
                            SecretBuf::another_ref(&owl_hybridKB88),
                            OwlBuf::another_ref(&owl_inp85),
                            Tracked(owl_declassify_tok90),
                        )
                    };
                    let owl_caseval89 = SecretBuf::another_ref_option(&tmp_owl_caseval89);
                    match SecretBuf::another_ref_option(&owl_caseval89) {
                        Option::None => { (owl_unit(), Tracked(itree)) },
                        Option::Some(tmp_owl__91) => {
                            let owl__91 = SecretBuf::another_ref(&tmp_owl__91);
                            (owl_unit(), Tracked(itree))
                        },
                    }
                },
            }
        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub struct state_B {}

impl state_B {
    #[verifier::external_body]
    pub fn init_state_B() -> Self {
        state_B {  }
    }
}

pub struct cfg_B<'B> {
    pub owl_hybrid_skB: SecretBuf<'B>,
    pub owl_r: SecretBuf<'B>,
    pub owl_n: SecretBuf<'B>,
    pub owl_pkB: SecretBuf<'B>,
    pub owl_n0: SecretBuf<'B>,
    pub pk_owl_pkB: OwlBuf<'B>,
    pub pk_owl_pkA: OwlBuf<'B>,
}

impl cfg_B<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_B_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_B), Endpoint>>,
        mut_state: &mut state_B,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_B), Endpoint>>), OwlError>)
        requires
            itree.view() == B_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_B), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(B_main_spec);
            let tmp_owl_privKey92 = { SecretBuf::another_ref(&self.owl_pkB) };
            let owl_privKey92 = SecretBuf::another_ref(&tmp_owl_privKey92);
            let (tmp_owl_enc_hybridKA94, owl__93) = {
                effects.owl_input::<((), state_B)>(Tracked(&mut itree))
            };
            let owl_enc_hybridKA94 = OwlBuf::from_vec(tmp_owl_enc_hybridKA94);
            let (tmp_owl_inp96, owl__95) = { effects.owl_input::<((), state_B)>(Tracked(&mut itree))
            };
            let owl_inp96 = OwlBuf::from_vec(tmp_owl_inp96);
            let tmp_owl_caseval97 = {
                let tracked owl_declassify_tok98 = consume_itree_declassify::<
                    ((), state_B),
                    Endpoint,
                >(&mut itree);
                owl_pkdec(
                    SecretBuf::another_ref(&owl_privKey92),
                    OwlBuf::another_ref(&owl_enc_hybridKA94),
                    Tracked(owl_declassify_tok98),
                )
            };
            let owl_caseval97 = SecretBuf::another_ref_option(&tmp_owl_caseval97);
            match SecretBuf::another_ref_option(&owl_caseval97) {
                Option::None => { (owl_unit(), Tracked(itree)) },
                Option::Some(tmp_owl_hybridKA99) => {
                    let owl_hybridKA99 = SecretBuf::another_ref(&tmp_owl_hybridKA99);
                    let tmp_owl_caseval100 = {
                        let tracked owl_declassify_tok101 = consume_itree_declassify::<
                            ((), state_B),
                            Endpoint,
                        >(&mut itree);
                        owl_dec(
                            SecretBuf::another_ref(&owl_hybridKA99),
                            OwlBuf::another_ref(&owl_inp96),
                            Tracked(owl_declassify_tok101),
                        )
                    };
                    let owl_caseval100 = SecretBuf::another_ref_option(&tmp_owl_caseval100);
                    match SecretBuf::another_ref_option(&owl_caseval100) {
                        Option::None => { (owl_unit(), Tracked(itree)) },
                        Option::Some(tmp_owl_m102) => {
                            let owl_m102 = SecretBuf::another_ref(&tmp_owl_m102);
                            {
                                let tmp_owl_m_103 = { SecretBuf::another_ref(&owl_m102) };
                                let owl_m_103 = SecretBuf::another_ref(&tmp_owl_m_103);
                                let parseval_tmp = SecretBuf::another_ref(&owl_m_103);
                                if let Some(parseval) = secret_parse_owl_secret_m1(
                                    SecretBuf::another_ref(&parseval_tmp),
                                ) {
                                    let owl_n0_107 = SecretBuf::another_ref(&parseval.owl_m1_n0);
                                    let owl_foo106 = SecretBuf::another_ref(&parseval.owl_m1_r0);
                                    let owl_bar105 = SecretBuf::another_ref(
                                        &parseval.owl_m1_pka_tag,
                                    );
                                    let owl_m1_pkA104 = SecretBuf::another_ref(
                                        &parseval.owl_m1_pkA_tag,
                                    );
                                    let tmp_owl_declassified_buf48108 = {
                                        let tracked owl_declassify_tok109 =
                                            consume_itree_declassify::<((), state_B), Endpoint>(
                                            &mut itree,
                                        );
                                        {
                                            SecretBuf::another_ref(&owl_bar105).declassify(
                                                Tracked(owl_declassify_tok109),
                                            )
                                        }
                                    };
                                    let owl_declassified_buf48108 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf48108,
                                    );
                                    let tmp_owl_declassified_buf51110 = {
                                        let tracked owl_declassify_tok111 =
                                            consume_itree_declassify::<((), state_B), Endpoint>(
                                            &mut itree,
                                        );
                                        {
                                            SecretBuf::another_ref(&owl_m1_pkA104).declassify(
                                                Tracked(owl_declassify_tok111),
                                            )
                                        }
                                    };
                                    let owl_declassified_buf51110 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf51110,
                                    );
                                    let owl_eq_bool54112 = {
                                        let tracked owl_declassify_tok113 =
                                            consume_itree_declassify::<((), state_B), Endpoint>(
                                            &mut itree,
                                        );
                                        {
                                            SecretBuf::secret_eq(
                                                &owl_n0_107,
                                                &SecretBuf::another_ref(&self.owl_n0),
                                                Tracked(owl_declassify_tok113),
                                            )
                                        }
                                    };
                                    {
                                        if {
                                            slice_eq(
                                                owl_declassified_buf51110.as_slice(),
                                                OwlBuf::another_ref(&self.pk_owl_pkA).as_slice(),
                                            )
                                        } && owl_eq_bool54112 {
                                            let tmp_owl_hybridKB114 = {
                                                SecretBuf::another_ref(&self.owl_hybrid_skB)
                                            };
                                            let owl_hybridKB114 = SecretBuf::another_ref(
                                                &tmp_owl_hybridKB114,
                                            );
                                            let tmp_owl_enc_hybridKB115 = {
                                                owl_pkenc(
                                                    OwlBuf::another_ref(
                                                        &OwlBuf::another_ref(&self.pk_owl_pkA),
                                                    ),
                                                    SecretBuf::another_ref(&owl_hybridKB114),
                                                )
                                            };
                                            let owl_enc_hybridKB115 = OwlBuf::from_vec(
                                                tmp_owl_enc_hybridKB115,
                                            );
                                            let owl__116 = {
                                                effects.owl_output::<((), state_B)>(
                                                    Tracked(&mut itree),
                                                    owl_enc_hybridKB115.as_slice(),
                                                    Some(&A_addr()),
                                                    &B_addr(),
                                                );
                                            };
                                            let tmp_owl_pubKeyA117 = {
                                                OwlBuf::another_ref(&self.pk_owl_pkA)
                                            };
                                            let owl_pubKeyA117 = OwlBuf::another_ref(
                                                &tmp_owl_pubKeyA117,
                                            );
                                            let tmp_owl_m118 = {
                                                owl_m2(
                                                    SecretBuf::another_ref(
                                                        &SecretBuf::another_ref(&self.owl_n0),
                                                    ),
                                                    SecretBuf::another_ref(
                                                        &SecretBuf::another_ref(&self.owl_n),
                                                    ),
                                                    SecretBuf::another_ref(
                                                        &SecretBuf::another_ref(&self.owl_r),
                                                    ),
                                                )
                                            };
                                            let owl_m118 = owl_m2::another_ref(&tmp_owl_m118);
                                            let tmp_owl_encm119 = {
                                                let tmp_owl_coins120 = effects.owl_sample::<
                                                    ((), state_B),
                                                >(Tracked(&mut itree), NONCE_SIZE);
                                                let owl_coins120 = SecretBuf::another_ref(
                                                    &tmp_owl_coins120,
                                                );
                                                owl_enc(
                                                    SecretBuf::another_ref(&owl_hybridKB114),
                                                    SecretBuf::another_ref(
                                                        &serialize_owl_m2(&owl_m118),
                                                    ),
                                                    SecretBuf::another_ref(&owl_coins120),
                                                )
                                            };
                                            let owl_encm119 = OwlBuf::from_vec(tmp_owl_encm119);
                                            let owl__121 = {
                                                effects.owl_output::<((), state_B)>(
                                                    Tracked(&mut itree),
                                                    owl_encm119.as_slice(),
                                                    Some(&A_addr()),
                                                    &B_addr(),
                                                );
                                            };
                                            (owl_unit(), Tracked(itree))
                                        } else {
                                            (owl_unit(), Tracked(itree))
                                        }

                                    }
                                } else {
                                    (owl_unit(), Tracked(itree))
                                }
                            }
                        },
                    }
                },
            }
        };
        Ok((res_inner, Tracked(itree)))
    }
}

} // verus!
