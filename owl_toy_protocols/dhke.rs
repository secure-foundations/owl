// Extracted verus code from file owl_toy_protocols/dhke.owl:
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
spec fn spec_combinator_owlSpec_alice_msg() -> (Variable, Variable) {
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

exec fn exec_combinator_owl_alice_msg() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_alice_msg(),
{
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

pub struct owlSpec_alice_msg {
    pub owlSpec__a1: Seq<u8>,
    pub owlSpec__a2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_alice_msg(x: Seq<u8>) -> Option<owlSpec_alice_msg> {
    let spec_comb = spec_combinator_owlSpec_alice_msg();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__a1, owlSpec__a2)) = parsed;
        Some(owlSpec_alice_msg { owlSpec__a1, owlSpec__a2 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_alice_msg_inner(x: owlSpec_alice_msg) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__a1.len(), x.owlSpec__a2.len() ] {
        let spec_comb = spec_combinator_owlSpec_alice_msg();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__a1, x.owlSpec__a2))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_alice_msg(x: owlSpec_alice_msg) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_alice_msg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_alice_msg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_alice_msg(self)
    }
}

pub open spec fn alice_msg(
    arg_owlSpec__a1: Seq<u8>,
    arg_owlSpec__a2: Seq<u8>,
) -> owlSpec_alice_msg {
    owlSpec_alice_msg { owlSpec__a1: arg_owlSpec__a1, owlSpec__a2: arg_owlSpec__a2 }
}

spec fn spec_combinator_owlSpec_bob_msg() -> (Variable, Variable) {
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

exec fn exec_combinator_owl_bob_msg() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_bob_msg(),
{
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

pub struct owlSpec_bob_msg {
    pub owlSpec__b1: Seq<u8>,
    pub owlSpec__b2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_bob_msg(x: Seq<u8>) -> Option<owlSpec_bob_msg> {
    let spec_comb = spec_combinator_owlSpec_bob_msg();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__b1, owlSpec__b2)) = parsed;
        Some(owlSpec_bob_msg { owlSpec__b1, owlSpec__b2 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_bob_msg_inner(x: owlSpec_bob_msg) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__b1.len(), x.owlSpec__b2.len() ] {
        let spec_comb = spec_combinator_owlSpec_bob_msg();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__b1, x.owlSpec__b2))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_bob_msg(x: owlSpec_bob_msg) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_bob_msg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_bob_msg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_bob_msg(self)
    }
}

pub open spec fn bob_msg(arg_owlSpec__b1: Seq<u8>, arg_owlSpec__b2: Seq<u8>) -> owlSpec_bob_msg {
    owlSpec_bob_msg { owlSpec__b1: arg_owlSpec__b1, owlSpec__b2: arg_owlSpec__b2 }
}

pub enum owlSpec_DHKEResult {
    owlSpec_NoData(),
    owlSpec_SomeData(Seq<u8>),
}

use owlSpec_DHKEResult::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_DHKEResult(x: Seq<u8>) -> Option<owlSpec_DHKEResult> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(12)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owlSpec_DHKEResult::owlSpec_NoData(),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_DHKEResult::owlSpec_SomeData(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_DHKEResult_inner(x: owlSpec_DHKEResult) -> Option<Seq<u8>> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(12)));
    match x {
        owlSpec_DHKEResult::owlSpec_NoData() => {
            if no_usize_overflows_spec![ 1, 0 ] {
                if let Ok(serialized) = spec_comb.spec_serialize(
                    inj_ord_choice_result!(((), seq![]), *),
                ) {
                    Some(serialized)
                } else {
                    None
                }
            } else {
                None
            }
        },
        owlSpec_DHKEResult::owlSpec_SomeData(x) => {
            if no_usize_overflows_spec![ 1, x.len() ] {
                if let Ok(serialized) = spec_comb.spec_serialize(
                    inj_ord_choice_result!(*, ((), x)),
                ) {
                    Some(serialized)
                } else {
                    None
                }
            } else {
                None
            }
        },
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_DHKEResult(x: owlSpec_DHKEResult) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_DHKEResult_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_DHKEResult {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_DHKEResult(self)
    }
}

pub open spec fn NoData() -> owlSpec_DHKEResult {
    crate::owlSpec_DHKEResult::owlSpec_NoData()
}

pub open spec fn SomeData(x: Seq<u8>) -> owlSpec_DHKEResult {
    crate::owlSpec_DHKEResult::owlSpec_SomeData(x)
}

pub open spec fn NoData_enumtest(x: owlSpec_DHKEResult) -> bool {
    match x {
        owlSpec_DHKEResult::owlSpec_NoData() => true,
        _ => false,
    }
}

pub open spec fn SomeData_enumtest(x: owlSpec_DHKEResult) -> bool {
    match x {
        owlSpec_DHKEResult::owlSpec_SomeData(_) => true,
        _ => false,
    }
}

#[verifier::opaque]
pub open spec fn alice_main_spec(cfg: cfg_alice, mut_state: state_alice) -> (res: ITree<
    ((), state_alice),
    Endpoint,
>) {
    owl_spec!(mut_state, state_alice,
        let vkB = ((ret(cfg.pk_owl_skB.view()))) in
let signed_x = ((ret(sign(cfg.owl_skA.view(), dhpk(cfg.owl_X.view()))))) in
let a = ((ret(alice_msg(dhpk(cfg.owl_X.view()), signed_x)))) in
(output (serialize_owlSpec_alice_msg(a)) to (Some(Endpoint::Loc_bob))) in
(input(i,_8)) in
(parse (parse_owlSpec_bob_msg(i)) as (owlSpec_bob_msg{owlSpec__b1 : b1, owlSpec__b2 : b2}) in {
let caseval = ((declassify(DeclassifyingOp::SigVrfy(vkB, b1, b2))) in
(ret(vrfy(vkB, b1, b2)))) in
(case (caseval) {
| Some(bobs_pk) => {
let ss = ((ret(dh_combine(bobs_pk, cfg.owl_X.view())))) in
let kdfval18 = ((ret(kdf((0 + ENCKEY_SIZE) as usize, empty_seq_u8(), ss, empty_seq_u8())))) in
let k = ((ret(Seq::subrange(kdfval18, 0, 0 + ENCKEY_SIZE)))) in
let c = ((sample(NONCE_SIZE, enc(k, cfg.owl_d.view())))) in
(output (c) to (Some(Endpoint::Loc_bob))) in
(ret(()))
},
| None => {
(ret(()))
},
}
)
} otherwise ((ret(()))))
    )
}

#[verifier::opaque]
pub open spec fn bob_main_spec(cfg: cfg_bob, mut_state: state_bob) -> (res: ITree<
    ((), state_bob),
    Endpoint,
>) {
    owl_spec!(mut_state, state_bob,
        let vkA = ((ret(cfg.pk_owl_skA.view()))) in
let signed_y = ((ret(sign(cfg.owl_skB.view(), dhpk(cfg.owl_Y.view()))))) in
let b = ((ret(bob_msg(dhpk(cfg.owl_Y.view()), signed_y)))) in
(output (serialize_owlSpec_bob_msg(b)) to (Some(Endpoint::Loc_alice))) in
(input(i,_28)) in
(parse (parse_owlSpec_alice_msg(i)) as (owlSpec_alice_msg{owlSpec__a1 : a1, owlSpec__a2 : a2}) in {
let caseval = ((declassify(DeclassifyingOp::SigVrfy(vkA, a1, a2))) in
(ret(vrfy(vkA, a1, a2)))) in
(case (caseval) {
| Some(pkX) => {
let ss = ((ret(dh_combine(pkX, cfg.owl_Y.view())))) in
let kdfval38 = ((ret(kdf((0 + ENCKEY_SIZE) as usize, empty_seq_u8(), ss, empty_seq_u8())))) in
let k = ((ret(Seq::subrange(kdfval38, 0, 0 + ENCKEY_SIZE)))) in
(input(ii,_41)) in
let caseval = ((declassify(DeclassifyingOp::ADec(k, ii))) in
(ret(dec(k, ii)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(dd) => {
let ddd = ((ret(dd))) in
(ret(()))
},
}
)
},
| None => {
(ret(()))
},
}
)
} otherwise ((ret(()))))
    )
}

// ------------------------------------
// ---------- IMPLEMENTATIONS ---------
// ------------------------------------
#[derive(Clone,Copy)]
pub enum Endpoint {
    Loc_alice,
    Loc_bob,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier(external_body)]
pub const fn alice_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_alice,
{
    "127.0.0.1:9001"
}

#[verifier(external_body)]
pub const fn bob_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_bob,
{
    "127.0.0.1:9002"
}

pub struct owl_alice_msg<'a> {
    pub owl__a1: OwlBuf<'a>,
    pub owl__a2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_alice_msg<'a>(arg_owl__a1: OwlBuf<'a>, arg_owl__a2: OwlBuf<'a>) -> (res: owl_alice_msg<
    'a,
>)
    ensures
        res.owl__a1.view() == arg_owl__a1.view(),
        res.owl__a2.view() == arg_owl__a2.view(),
{
    owl_alice_msg { owl__a1: arg_owl__a1, owl__a2: arg_owl__a2 }
}

impl<'a> owl_alice_msg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_alice_msg<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_alice_msg {
            owl__a1: OwlBuf::another_ref(&self.owl__a1),
            owl__a2: OwlBuf::another_ref(&self.owl__a2),
        }
    }
}

impl View for owl_alice_msg<'_> {
    type V = owlSpec_alice_msg;

    open spec fn view(&self) -> owlSpec_alice_msg {
        owlSpec_alice_msg { owlSpec__a1: self.owl__a1.view(), owlSpec__a2: self.owl__a2.view() }
    }
}

pub exec fn parse_owl_alice_msg<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_alice_msg<'a>>)
    ensures
        res is Some ==> parse_owlSpec_alice_msg(arg.view()) is Some,
        res is None ==> parse_owlSpec_alice_msg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_alice_msg(arg.view())->Some_0,
{
    reveal(parse_owlSpec_alice_msg);
    let exec_comb = exec_combinator_owl_alice_msg();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__a1, owl__a2) = parsed;
        Some(
            owl_alice_msg {
                owl__a1: OwlBuf::another_ref(&owl__a1),
                owl__a2: OwlBuf::another_ref(&owl__a2),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_alice_msg_inner<'a>(arg: &owl_alice_msg<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_alice_msg_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_alice_msg_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_alice_msg_inner);
    if no_usize_overflows![ arg.owl__a1.len(), arg.owl__a2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_alice_msg();
        let mut obuf = vec_u8_of_len(arg.owl__a1.len() + arg.owl__a2.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl__a1), OwlBuf::another_ref(&arg.owl__a2)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_alice_msg_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_alice_msg<'a>(arg: &owl_alice_msg<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_alice_msg(arg.view()),
{
    reveal(serialize_owlSpec_alice_msg);
    let res = serialize_owl_alice_msg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_bob_msg<'a> {
    pub owl__b1: OwlBuf<'a>,
    pub owl__b2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_bob_msg<'a>(arg_owl__b1: OwlBuf<'a>, arg_owl__b2: OwlBuf<'a>) -> (res: owl_bob_msg<'a>)
    ensures
        res.owl__b1.view() == arg_owl__b1.view(),
        res.owl__b2.view() == arg_owl__b2.view(),
{
    owl_bob_msg { owl__b1: arg_owl__b1, owl__b2: arg_owl__b2 }
}

impl<'a> owl_bob_msg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_bob_msg<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_bob_msg {
            owl__b1: OwlBuf::another_ref(&self.owl__b1),
            owl__b2: OwlBuf::another_ref(&self.owl__b2),
        }
    }
}

impl View for owl_bob_msg<'_> {
    type V = owlSpec_bob_msg;

    open spec fn view(&self) -> owlSpec_bob_msg {
        owlSpec_bob_msg { owlSpec__b1: self.owl__b1.view(), owlSpec__b2: self.owl__b2.view() }
    }
}

pub exec fn parse_owl_bob_msg<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_bob_msg<'a>>)
    ensures
        res is Some ==> parse_owlSpec_bob_msg(arg.view()) is Some,
        res is None ==> parse_owlSpec_bob_msg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_bob_msg(arg.view())->Some_0,
{
    reveal(parse_owlSpec_bob_msg);
    let exec_comb = exec_combinator_owl_bob_msg();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__b1, owl__b2) = parsed;
        Some(
            owl_bob_msg {
                owl__b1: OwlBuf::another_ref(&owl__b1),
                owl__b2: OwlBuf::another_ref(&owl__b2),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_bob_msg_inner<'a>(arg: &owl_bob_msg<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_bob_msg_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_bob_msg_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_bob_msg_inner);
    if no_usize_overflows![ arg.owl__b1.len(), arg.owl__b2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_bob_msg();
        let mut obuf = vec_u8_of_len(arg.owl__b1.len() + arg.owl__b2.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl__b1), OwlBuf::another_ref(&arg.owl__b2)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_bob_msg_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_bob_msg<'a>(arg: &owl_bob_msg<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_bob_msg(arg.view()),
{
    reveal(serialize_owlSpec_bob_msg);
    let res = serialize_owl_bob_msg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_DHKEResult<'a> {
    owl_NoData(),
    owl_SomeData(SecretBuf<'a>),
}

use owl_DHKEResult::*;

impl<'a> owl_DHKEResult<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_DHKEResult<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_NoData() => owl_NoData(),
            owl_SomeData(x) => owl_SomeData(SecretBuf::another_ref(x)),
        }
    }
}

impl View for owl_DHKEResult<'_> {
    type V = owlSpec_DHKEResult;

    open spec fn view(&self) -> owlSpec_DHKEResult {
        match self {
            owl_NoData() => owlSpec_DHKEResult::owlSpec_NoData(),
            owl_SomeData(v) => owlSpec_DHKEResult::owlSpec_SomeData(v.view()),
        }
    }
}

#[inline]
pub fn owl_NoData_enumtest(x: &owl_DHKEResult<'_>) -> (res: bool)
    ensures
        res == NoData_enumtest(x.view()),
{
    match x {
        owl_DHKEResult::owl_NoData() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_SomeData_enumtest(x: &owl_DHKEResult<'_>) -> (res: bool)
    ensures
        res == SomeData_enumtest(x.view()),
{
    match x {
        owl_DHKEResult::owl_SomeData(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_DHKEResult<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_DHKEResult<'a>>)
    ensures
        res is Some ==> parse_owlSpec_DHKEResult(arg.view()) is Some,
        res is None ==> parse_owlSpec_DHKEResult(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_DHKEResult(arg.view())->Some_0,
{
    reveal(parse_owlSpec_DHKEResult);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(0)), (Tag::new(U8, 2), Variable(12)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owl_DHKEResult::owl_NoData(),
            inj_ord_choice_pat!(*, (_,x)) => owl_DHKEResult::owl_SomeData(
                SecretBuf::from_buf(x.another_ref()),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_DHKEResult<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_DHKEResult<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_DHKEResult(arg.view()) is Some,
        res is None ==> parse_owlSpec_DHKEResult(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_DHKEResult(arg.view())->Some_0,
{
    reveal(parse_owlSpec_DHKEResult);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_DHKEResult_inner(arg: &owl_DHKEResult) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_DHKEResult_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_DHKEResult_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_DHKEResult_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_DHKEResult(arg: &owl_DHKEResult) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_DHKEResult(arg.view()),
{
    reveal(serialize_owlSpec_DHKEResult);
    let res = serialize_owl_DHKEResult_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct state_alice {}

impl state_alice {
    #[verifier::external_body]
    pub fn init_state_alice() -> Self {
        state_alice {  }
    }
}

pub struct cfg_alice<'alice> {
    pub owl_d: SecretBuf<'alice>,
    pub owl_skA: SecretBuf<'alice>,
    pub owl_X: SecretBuf<'alice>,
    pub pk_owl_skB: OwlBuf<'alice>,
    pub pk_owl_skA: OwlBuf<'alice>,
    pub pk_owl_Y: OwlBuf<'alice>,
    pub pk_owl_X: OwlBuf<'alice>,
}

impl cfg_alice<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_alice_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_alice), Endpoint>>,
        mut_state: &mut state_alice,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_alice), Endpoint>>), OwlError>)
        requires
            itree.view() == alice_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_alice), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(alice_main_spec);
            let tmp_owl_vkB51 = { OwlBuf::another_ref(&self.pk_owl_skB) };
            let owl_vkB51 = OwlBuf::another_ref(&tmp_owl_vkB51);
            let tmp_owl_signed_x52 = {
                owl_sign(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skA)),
                    OwlBuf::from_vec(
                        owl_dhpk(SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_X))),
                    ),
                )
            };
            let owl_signed_x52 = OwlBuf::from_vec(tmp_owl_signed_x52);
            let tmp_owl_a53 = {
                owl_alice_msg(
                    OwlBuf::from_vec(
                        owl_dhpk(SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_X))),
                    ),
                    OwlBuf::another_ref(&owl_signed_x52),
                )
            };
            let owl_a53 = owl_alice_msg::another_ref(&tmp_owl_a53);
            let owl__54 = {
                effects.owl_output::<((), state_alice)>(
                    Tracked(&mut itree),
                    serialize_owl_alice_msg(&owl_a53).as_slice(),
                    Some(&bob_addr()),
                    &alice_addr(),
                );
            };
            let (tmp_owl_i56, owl__55) = {
                effects.owl_input::<((), state_alice)>(Tracked(&mut itree))
            };
            let owl_i56 = OwlBuf::from_vec(tmp_owl_i56);
            let parseval_tmp = OwlBuf::another_ref(&owl_i56);
            if let Some(parseval) = parse_owl_bob_msg(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_b158 = OwlBuf::another_ref(&parseval.owl__b1);
                let owl_b257 = OwlBuf::another_ref(&parseval.owl__b2);
                let tmp_owl_caseval59 = {
                    let tracked owl_declassify_tok60 = consume_itree_declassify::<
                        ((), state_alice),
                        Endpoint,
                    >(&mut itree);
                    owl_vrfy(
                        OwlBuf::another_ref(&owl_vkB51),
                        SecretBuf::another_ref(&SecretBuf::from_buf(owl_b158.another_ref())),
                        OwlBuf::another_ref(&owl_b257),
                        Tracked(owl_declassify_tok60),
                    )
                };
                let owl_caseval59 = SecretBuf::another_ref_option(&tmp_owl_caseval59);
                match SecretBuf::another_ref_option(&owl_caseval59) {
                    Option::Some(tmp_owl_bobs_pk61) => {
                        let owl_bobs_pk61 = SecretBuf::another_ref(&tmp_owl_bobs_pk61);
                        let tmp_owl_ss62 = {
                            owl_dh_combine(
                                SecretBuf::another_ref(&owl_bobs_pk61),
                                SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_X)),
                            )
                        };
                        let owl_ss62 = SecretBuf::another_ref(&tmp_owl_ss62);
                        let tmp_owl_kdfval1863 = {
                            owl_extract_expand_to_len(
                                0 + ENCKEY_SIZE,
                                SecretBuf::another_ref(
                                    &SecretBuf::from_buf(
                                        {
                                            let x = mk_vec_u8![];
                                            OwlBuf::from_vec(x)
                                        }.another_ref(),
                                    ),
                                ),
                                SecretBuf::another_ref(&owl_ss62),
                                OwlBuf::another_ref(
                                    &{
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    },
                                ),
                            )
                        };
                        let owl_kdfval1863 = SecretBuf::another_ref(&tmp_owl_kdfval1863);
                        let tmp_owl_k64 = {
                            { SecretBuf::another_ref(&owl_kdfval1863).subrange(0, 0 + ENCKEY_SIZE) }
                        };
                        let owl_k64 = SecretBuf::another_ref(&tmp_owl_k64);
                        let tmp_owl_c65 = {
                            let tmp_owl_coins66 = effects.owl_sample::<((), state_alice)>(
                                Tracked(&mut itree),
                                NONCE_SIZE,
                            );
                            let owl_coins66 = SecretBuf::another_ref(&tmp_owl_coins66);
                            owl_enc(
                                SecretBuf::another_ref(&owl_k64),
                                SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_d)),
                                SecretBuf::another_ref(&owl_coins66),
                            )
                        };
                        let owl_c65 = OwlBuf::from_vec(tmp_owl_c65);
                        let owl__67 = {
                            effects.owl_output::<((), state_alice)>(
                                Tracked(&mut itree),
                                owl_c65.as_slice(),
                                Some(&bob_addr()),
                                &alice_addr(),
                            );
                        };
                        (owl_unit(), Tracked(itree))
                    },
                    Option::None => { (owl_unit(), Tracked(itree)) },
                }
            } else {
                (owl_unit(), Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub struct state_bob {}

impl state_bob {
    #[verifier::external_body]
    pub fn init_state_bob() -> Self {
        state_bob {  }
    }
}

pub struct cfg_bob<'bob> {
    pub owl_skB: SecretBuf<'bob>,
    pub owl_Y: SecretBuf<'bob>,
    pub pk_owl_skB: OwlBuf<'bob>,
    pub pk_owl_skA: OwlBuf<'bob>,
    pub pk_owl_Y: OwlBuf<'bob>,
    pub pk_owl_X: OwlBuf<'bob>,
}

impl cfg_bob<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_bob_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_bob), Endpoint>>,
        mut_state: &mut state_bob,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_bob), Endpoint>>), OwlError>)
        requires
            itree.view() == bob_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_bob), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(bob_main_spec);
            let tmp_owl_vkA68 = { OwlBuf::another_ref(&self.pk_owl_skA) };
            let owl_vkA68 = OwlBuf::another_ref(&tmp_owl_vkA68);
            let tmp_owl_signed_y69 = {
                owl_sign(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skB)),
                    OwlBuf::from_vec(
                        owl_dhpk(SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_Y))),
                    ),
                )
            };
            let owl_signed_y69 = OwlBuf::from_vec(tmp_owl_signed_y69);
            let tmp_owl_b70 = {
                owl_bob_msg(
                    OwlBuf::from_vec(
                        owl_dhpk(SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_Y))),
                    ),
                    OwlBuf::another_ref(&owl_signed_y69),
                )
            };
            let owl_b70 = owl_bob_msg::another_ref(&tmp_owl_b70);
            let owl__71 = {
                effects.owl_output::<((), state_bob)>(
                    Tracked(&mut itree),
                    serialize_owl_bob_msg(&owl_b70).as_slice(),
                    Some(&alice_addr()),
                    &bob_addr(),
                );
            };
            let (tmp_owl_i73, owl__72) = { effects.owl_input::<((), state_bob)>(Tracked(&mut itree))
            };
            let owl_i73 = OwlBuf::from_vec(tmp_owl_i73);
            let parseval_tmp = OwlBuf::another_ref(&owl_i73);
            if let Some(parseval) = parse_owl_alice_msg(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_a175 = OwlBuf::another_ref(&parseval.owl__a1);
                let owl_a274 = OwlBuf::another_ref(&parseval.owl__a2);
                let tmp_owl_caseval76 = {
                    let tracked owl_declassify_tok77 = consume_itree_declassify::<
                        ((), state_bob),
                        Endpoint,
                    >(&mut itree);
                    owl_vrfy(
                        OwlBuf::another_ref(&owl_vkA68),
                        SecretBuf::another_ref(&SecretBuf::from_buf(owl_a175.another_ref())),
                        OwlBuf::another_ref(&owl_a274),
                        Tracked(owl_declassify_tok77),
                    )
                };
                let owl_caseval76 = SecretBuf::another_ref_option(&tmp_owl_caseval76);
                match SecretBuf::another_ref_option(&owl_caseval76) {
                    Option::Some(tmp_owl_pkX78) => {
                        let owl_pkX78 = SecretBuf::another_ref(&tmp_owl_pkX78);
                        let tmp_owl_ss79 = {
                            owl_dh_combine(
                                SecretBuf::another_ref(&owl_pkX78),
                                SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_Y)),
                            )
                        };
                        let owl_ss79 = SecretBuf::another_ref(&tmp_owl_ss79);
                        let tmp_owl_kdfval3880 = {
                            owl_extract_expand_to_len(
                                0 + ENCKEY_SIZE,
                                SecretBuf::another_ref(
                                    &SecretBuf::from_buf(
                                        {
                                            let x = mk_vec_u8![];
                                            OwlBuf::from_vec(x)
                                        }.another_ref(),
                                    ),
                                ),
                                SecretBuf::another_ref(&owl_ss79),
                                OwlBuf::another_ref(
                                    &{
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    },
                                ),
                            )
                        };
                        let owl_kdfval3880 = SecretBuf::another_ref(&tmp_owl_kdfval3880);
                        let tmp_owl_k81 = {
                            { SecretBuf::another_ref(&owl_kdfval3880).subrange(0, 0 + ENCKEY_SIZE) }
                        };
                        let owl_k81 = SecretBuf::another_ref(&tmp_owl_k81);
                        let (tmp_owl_ii83, owl__82) = {
                            effects.owl_input::<((), state_bob)>(Tracked(&mut itree))
                        };
                        let owl_ii83 = OwlBuf::from_vec(tmp_owl_ii83);
                        let tmp_owl_caseval84 = {
                            let tracked owl_declassify_tok85 = consume_itree_declassify::<
                                ((), state_bob),
                                Endpoint,
                            >(&mut itree);
                            owl_dec(
                                SecretBuf::another_ref(&owl_k81),
                                OwlBuf::another_ref(&owl_ii83),
                                Tracked(owl_declassify_tok85),
                            )
                        };
                        let owl_caseval84 = SecretBuf::another_ref_option(&tmp_owl_caseval84);
                        match SecretBuf::another_ref_option(&owl_caseval84) {
                            Option::None => { (owl_unit(), Tracked(itree)) },
                            Option::Some(tmp_owl_dd86) => {
                                let owl_dd86 = SecretBuf::another_ref(&tmp_owl_dd86);
                                let tmp_owl_ddd87 = { SecretBuf::another_ref(&owl_dd86) };
                                let owl_ddd87 = SecretBuf::another_ref(&tmp_owl_ddd87);
                                (owl_unit(), Tracked(itree))
                            },
                        }
                    },
                    Option::None => { (owl_unit(), Tracked(itree)) },
                }
            } else {
                (owl_unit(), Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }
}

} // verus!
