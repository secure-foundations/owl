// Extracted verus code from file owl_toy_protocols/hash-lock.owl:
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
spec fn spec_combinator_owlSpec_nonces() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_nonces() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_nonces(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_nonces {
    pub owlSpec__nR: Seq<u8>,
    pub owlSpec__nT1: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_nonces(x: Seq<u8>) -> Option<owlSpec_nonces> {
    let spec_comb = spec_combinator_owlSpec_nonces();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__nR, owlSpec__nT1)) = parsed;
        Some(owlSpec_nonces { owlSpec__nR, owlSpec__nT1 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_nonces_inner(x: owlSpec_nonces) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__nR.len(), x.owlSpec__nT1.len() ] {
        let spec_comb = spec_combinator_owlSpec_nonces();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__nR, x.owlSpec__nT1))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_nonces(x: owlSpec_nonces) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_nonces_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_nonces {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_nonces(self)
    }
}

pub open spec fn nonces(arg_owlSpec__nR: Seq<u8>, arg_owlSpec__nT1: Seq<u8>) -> owlSpec_nonces {
    owlSpec_nonces { owlSpec__nR: arg_owlSpec__nR, owlSpec__nT1: arg_owlSpec__nT1 }
}

spec fn spec_combinator_owlSpec_secret_nonces() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_secret_nonces() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_nonces(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_secret_nonces {
    pub owlSpec__nR: Seq<u8>,
    pub owlSpec__nT1: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_nonces(x: Seq<u8>) -> Option<owlSpec_secret_nonces> {
    let spec_comb = spec_combinator_owlSpec_secret_nonces();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__nR, owlSpec__nT1)) = parsed;
        Some(owlSpec_secret_nonces { owlSpec__nR, owlSpec__nT1 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_nonces_inner(x: owlSpec_secret_nonces) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__nR.len(), x.owlSpec__nT1.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_nonces();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__nR, x.owlSpec__nT1))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_nonces(x: owlSpec_secret_nonces) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_secret_nonces_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_nonces {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_nonces(self)
    }
}

pub open spec fn secret_nonces(
    arg_owlSpec__nR: Seq<u8>,
    arg_owlSpec__nT1: Seq<u8>,
) -> owlSpec_secret_nonces {
    owlSpec_secret_nonces { owlSpec__nR: arg_owlSpec__nR, owlSpec__nT1: arg_owlSpec__nT1 }
}

spec fn spec_combinator_owlSpec_s() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(16);
    (field_1, field_2)
}

exec fn exec_combinator_owl_s() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_s(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(16);
    (field_1, field_2)
}

pub struct owlSpec_s {
    pub owlSpec__nT2: Seq<u8>,
    pub owlSpec__m: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_s(x: Seq<u8>) -> Option<owlSpec_s> {
    let spec_comb = spec_combinator_owlSpec_s();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__nT2, owlSpec__m)) = parsed;
        Some(owlSpec_s { owlSpec__nT2, owlSpec__m })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_s_inner(x: owlSpec_s) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__nT2.len(), x.owlSpec__m.len() ] {
        let spec_comb = spec_combinator_owlSpec_s();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__nT2, x.owlSpec__m))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_s(x: owlSpec_s) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_s_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_s {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_s(self)
    }
}

pub open spec fn s(arg_owlSpec__nT2: Seq<u8>, arg_owlSpec__m: Seq<u8>) -> owlSpec_s {
    owlSpec_s { owlSpec__nT2: arg_owlSpec__nT2, owlSpec__m: arg_owlSpec__m }
}

pub enum owlSpec_reader_response {
    owlSpec_No(),
    owlSpec_Yes(Seq<u8>),
}

use owlSpec_reader_response::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_reader_response(x: Seq<u8>) -> Option<owlSpec_reader_response> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(12)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owlSpec_reader_response::owlSpec_No(),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_reader_response::owlSpec_Yes(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_reader_response_inner(x: owlSpec_reader_response) -> Option<
    Seq<u8>,
> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(12)));
    match x {
        owlSpec_reader_response::owlSpec_No() => {
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
        owlSpec_reader_response::owlSpec_Yes(x) => {
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
pub closed spec fn serialize_owlSpec_reader_response(x: owlSpec_reader_response) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_reader_response_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_reader_response {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_reader_response(self)
    }
}

pub open spec fn No() -> owlSpec_reader_response {
    crate::owlSpec_reader_response::owlSpec_No()
}

pub open spec fn Yes(x: Seq<u8>) -> owlSpec_reader_response {
    crate::owlSpec_reader_response::owlSpec_Yes(x)
}

pub open spec fn No_enumtest(x: owlSpec_reader_response) -> bool {
    match x {
        owlSpec_reader_response::owlSpec_No() => true,
        _ => false,
    }
}

pub open spec fn Yes_enumtest(x: owlSpec_reader_response) -> bool {
    match x {
        owlSpec_reader_response::owlSpec_Yes(_) => true,
        _ => false,
    }
}

#[verifier::opaque]
pub open spec fn R_main_spec(cfg: cfg_R, mut_state: state_R) -> (res: ITree<
    (owlSpec_reader_response, state_R),
    Endpoint,
>) {
    owl_spec!(mut_state, state_R,
        let nR = ((ret(cfg.owl_NR.view()))) in
(input(_unused67,ev_t7)) in
let declassified_buf9 = ((declassify(DeclassifyingOp::ControlFlow(nR))) in
(ret((nR)))) in
(output (declassified_buf9) to (Some(ev_t7))) in
(input(inp,_13)) in
(parse (parse_owlSpec_s(inp)) as (owlSpec_s{owlSpec__nT2 : nT, owlSpec__m : mc}) in {
let x = (call(lookupKeys_spec(cfg, mut_state, nT))) in
(case (x) {
| None => {
(ret(No()))
},
| Some(k_packed) => {
let k = ((ret(k_packed))) in
let declassified_buf25 = ((declassify(DeclassifyingOp::ControlFlow(nR))) in
(ret((nR)))) in
let msg_to_verify = ((ret(nonces(declassified_buf25, nT)))) in
let caseval = ((declassify(DeclassifyingOp::MacVrfy(k, serialize_owlSpec_nonces(msg_to_verify), mc))) in
(ret(mac_vrfy(k, serialize_owlSpec_nonces(msg_to_verify), mc)))) in
(case (caseval) {
| None => {
(ret(No()))
},
| Some(m) => {
(parse (parse_owlSpec_secret_nonces(m)) as (owlSpec_secret_nonces{owlSpec__nR : nR, owlSpec__nT1 : mm}) in {
let declassified_buf37 = ((declassify(DeclassifyingOp::ControlFlow(nR))) in
(ret((nR)))) in
let mmm = ((ret(mm))) in
let m_ = ((ret(mmm))) in
let res = ((ret(m_))) in
let declassified_buf43 = ((declassify(DeclassifyingOp::ControlFlow(res))) in
(ret((res)))) in
(ret(Yes(declassified_buf43)))
} otherwise ((ret(No()))))
},
}
)
},
}
)
} otherwise ((ret(No()))))
    )
}

#[verifier::opaque]
pub open spec fn lookupKeys_spec(cfg: cfg_R, mut_state: state_R, x: Seq<u8>) -> (res: ITree<
    (Option<Seq<u8>>, state_R),
    Endpoint,
>) {
    owl_spec!(mut_state, state_R,
        (ret(lookupKeys_pure(x)))
    )
}

#[verifier(external_body)]
pub closed spec fn lookupKeys_pure(x: Seq<u8>) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::opaque]
pub open spec fn T_main_spec(cfg: cfg_T, mut_state: state_T) -> (res: ITree<
    ((), state_T),
    Endpoint,
>) {
    owl_spec!(mut_state, state_T,
        (output (empty_seq_u8()) to (Some(Endpoint::Loc_R))) in
(input(inp,_49)) in
(if (length(inp) == NONCE_SIZE) then
(let inp_ = ((ret(inp))) in
let nT = ((ret(cfg.owl_NT.view()))) in
let msg_to_mac = ((ret(nonces(inp_, nT)))) in
let declassified_buf54 = ((declassify(DeclassifyingOp::ControlFlow(serialize_owlSpec_nonces(msg_to_mac)))) in
(ret((serialize_owlSpec_nonces(msg_to_mac))))) in
let m = ((ret(mac(cfg.owl_K.view(), declassified_buf54)))) in
let declassified_buf58 = ((declassify(DeclassifyingOp::ControlFlow(cfg.owl_NT.view()))) in
(ret((cfg.owl_NT.view())))) in
(output (serialize_owlSpec_s(s(declassified_buf58, m))) to (Some(Endpoint::Loc_R))))
else
((ret(()))))
    )
}

// ------------------------------------
// ---------- IMPLEMENTATIONS ---------
// ------------------------------------
#[derive(Clone,Copy)]
pub enum Endpoint {
    Loc_R,
    Loc_T,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier(external_body)]
pub const fn R_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_R,
{
    "127.0.0.1:9001"
}

#[verifier(external_body)]
pub const fn T_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_T,
{
    "127.0.0.1:9002"
}

pub struct owl_nonces<'a> {
    pub owl__nR: OwlBuf<'a>,
    pub owl__nT1: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_nonces<'a>(arg_owl__nR: OwlBuf<'a>, arg_owl__nT1: SecretBuf<'a>) -> (res: owl_nonces<'a>)
    ensures
        res.owl__nR.view() == arg_owl__nR.view(),
        res.owl__nT1.view() == arg_owl__nT1.view(),
{
    owl_nonces { owl__nR: arg_owl__nR, owl__nT1: arg_owl__nT1 }
}

impl<'a> owl_nonces<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_nonces<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_nonces {
            owl__nR: OwlBuf::another_ref(&self.owl__nR),
            owl__nT1: SecretBuf::another_ref(&self.owl__nT1),
        }
    }
}

impl View for owl_nonces<'_> {
    type V = owlSpec_nonces;

    open spec fn view(&self) -> owlSpec_nonces {
        owlSpec_nonces { owlSpec__nR: self.owl__nR.view(), owlSpec__nT1: self.owl__nT1.view() }
    }
}

pub exec fn parse_owl_nonces<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_nonces<'a>>)
    ensures
        res is Some ==> parse_owlSpec_nonces(arg.view()) is Some,
        res is None ==> parse_owlSpec_nonces(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nonces(arg.view())->Some_0,
{
    reveal(parse_owlSpec_nonces);
    let exec_comb = exec_combinator_owl_nonces();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__nR, owl__nT1) = parsed;
        Some(
            owl_nonces {
                owl__nR: OwlBuf::another_ref(&owl__nR),
                owl__nT1: SecretBuf::from_buf(owl__nT1.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_nonces_inner<'a>(arg: &owl_nonces<'a>) -> (res: Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_nonces_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_nonces_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_nonces_inner);
    if no_usize_overflows![ arg.owl__nR.len(), arg.owl__nT1.len(), 0 ] {
        let exec_comb = exec_combinator_owl_nonces();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__nR.len() + arg.owl__nT1.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::from_buf(arg.owl__nR.another_ref()), SecretBuf::another_ref(&arg.owl__nT1)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_nonces_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_nonces<'a>(arg: &owl_nonces<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_nonces(arg.view()),
{
    reveal(serialize_owlSpec_nonces);
    let res = serialize_owl_nonces_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_nonces<'a> {
    pub owl__nR: SecretBuf<'a>,
    pub owl__nT1: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_nonces<'a>(arg_owl__nR: SecretBuf<'a>, arg_owl__nT1: SecretBuf<'a>) -> (res:
    owl_secret_nonces<'a>)
    ensures
        res.owl__nR.view() == arg_owl__nR.view(),
        res.owl__nT1.view() == arg_owl__nT1.view(),
{
    owl_secret_nonces { owl__nR: arg_owl__nR, owl__nT1: arg_owl__nT1 }
}

impl<'a> owl_secret_nonces<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_nonces<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_nonces {
            owl__nR: SecretBuf::another_ref(&self.owl__nR),
            owl__nT1: SecretBuf::another_ref(&self.owl__nT1),
        }
    }
}

impl View for owl_secret_nonces<'_> {
    type V = owlSpec_secret_nonces;

    open spec fn view(&self) -> owlSpec_secret_nonces {
        owlSpec_secret_nonces {
            owlSpec__nR: self.owl__nR.view(),
            owlSpec__nT1: self.owl__nT1.view(),
        }
    }
}

pub exec fn parse_owl_secret_nonces<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_secret_nonces<'a>>)
    ensures
        res is Some ==> parse_owlSpec_secret_nonces(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_nonces(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_nonces(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_nonces);
    let exec_comb = exec_combinator_owl_secret_nonces();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__nR, owl__nT1) = parsed;
        Some(
            owl_secret_nonces {
                owl__nR: SecretBuf::from_buf(owl__nR.another_ref()),
                owl__nT1: SecretBuf::from_buf(owl__nT1.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_nonces<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_nonces<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_nonces(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_nonces(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_nonces(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_nonces);
    let exec_comb = exec_combinator_owl_secret_nonces();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (owl__nR, owl__nT1) = parsed;
        Some(
            owl_secret_nonces {
                owl__nR: SecretBuf::another_ref(&owl__nR),
                owl__nT1: SecretBuf::another_ref(&owl__nT1),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_nonces_inner<'a>(arg: &owl_secret_nonces<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_secret_nonces_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_nonces_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_secret_nonces_inner);
    if no_usize_overflows![ arg.owl__nR.len(), arg.owl__nT1.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_nonces();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__nR.len() + arg.owl__nT1.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__nR), SecretBuf::another_ref(&arg.owl__nT1)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_nonces_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_nonces<'a>(arg: &owl_secret_nonces<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_nonces(arg.view()),
{
    reveal(serialize_owlSpec_secret_nonces);
    let res = serialize_owl_secret_nonces_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_s<'a> {
    pub owl__nT2: OwlBuf<'a>,
    pub owl__m: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_s<'a>(arg_owl__nT2: OwlBuf<'a>, arg_owl__m: OwlBuf<'a>) -> (res: owl_s<'a>)
    ensures
        res.owl__nT2.view() == arg_owl__nT2.view(),
        res.owl__m.view() == arg_owl__m.view(),
{
    owl_s { owl__nT2: arg_owl__nT2, owl__m: arg_owl__m }
}

impl<'a> owl_s<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_s<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_s {
            owl__nT2: OwlBuf::another_ref(&self.owl__nT2),
            owl__m: OwlBuf::another_ref(&self.owl__m),
        }
    }
}

impl View for owl_s<'_> {
    type V = owlSpec_s;

    open spec fn view(&self) -> owlSpec_s {
        owlSpec_s { owlSpec__nT2: self.owl__nT2.view(), owlSpec__m: self.owl__m.view() }
    }
}

pub exec fn parse_owl_s<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_s<'a>>)
    ensures
        res is Some ==> parse_owlSpec_s(arg.view()) is Some,
        res is None ==> parse_owlSpec_s(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_s(arg.view())->Some_0,
{
    reveal(parse_owlSpec_s);
    let exec_comb = exec_combinator_owl_s();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__nT2, owl__m) = parsed;
        Some(
            owl_s {
                owl__nT2: OwlBuf::another_ref(&owl__nT2),
                owl__m: OwlBuf::another_ref(&owl__m),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_s_inner<'a>(arg: &owl_s<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_s_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_s_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_s_inner);
    if no_usize_overflows![ arg.owl__nT2.len(), arg.owl__m.len(), 0 ] {
        let exec_comb = exec_combinator_owl_s();
        let mut obuf = vec_u8_of_len(arg.owl__nT2.len() + arg.owl__m.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl__nT2), OwlBuf::another_ref(&arg.owl__m)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_s_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_s<'a>(arg: &owl_s<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_s(arg.view()),
{
    reveal(serialize_owlSpec_s);
    let res = serialize_owl_s_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_reader_response<'a> {
    owl_No(),
    owl_Yes(OwlBuf<'a>),
}

use owl_reader_response::*;

impl<'a> owl_reader_response<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_reader_response<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_No() => owl_No(),
            owl_Yes(x) => owl_Yes(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_reader_response<'_> {
    type V = owlSpec_reader_response;

    open spec fn view(&self) -> owlSpec_reader_response {
        match self {
            owl_No() => owlSpec_reader_response::owlSpec_No(),
            owl_Yes(v) => owlSpec_reader_response::owlSpec_Yes(v.view()),
        }
    }
}

#[inline]
pub fn owl_No_enumtest(x: &owl_reader_response<'_>) -> (res: bool)
    ensures
        res == No_enumtest(x.view()),
{
    match x {
        owl_reader_response::owl_No() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_Yes_enumtest(x: &owl_reader_response<'_>) -> (res: bool)
    ensures
        res == Yes_enumtest(x.view()),
{
    match x {
        owl_reader_response::owl_Yes(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_reader_response<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_reader_response<'a>>)
    ensures
        res is Some ==> parse_owlSpec_reader_response(arg.view()) is Some,
        res is None ==> parse_owlSpec_reader_response(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_reader_response(arg.view())->Some_0,
{
    reveal(parse_owlSpec_reader_response);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(0)), (Tag::new(U8, 2), Variable(12)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owl_reader_response::owl_No(),
            inj_ord_choice_pat!(*, (_,x)) => owl_reader_response::owl_Yes(OwlBuf::another_ref(&x)),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_reader_response<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_reader_response<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_reader_response(arg.view()) is Some,
        res is None ==> parse_owlSpec_reader_response(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_reader_response(arg.view())->Some_0,
{
    reveal(parse_owlSpec_reader_response);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_reader_response_inner(arg: &owl_reader_response) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_reader_response_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_reader_response_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_reader_response_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_reader_response(arg: &owl_reader_response) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_reader_response(arg.view()),
{
    reveal(serialize_owlSpec_reader_response);
    let res = serialize_owl_reader_response_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct state_R {}

impl state_R {
    #[verifier::external_body]
    pub fn init_state_R() -> Self {
        state_R {  }
    }
}

pub struct cfg_R<'R> {
    pub owl_NR: SecretBuf<'R>,
    pub owl_K: SecretBuf<'R>,
}

impl cfg_R<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_R_main<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_reader_response, state_R), Endpoint>>,
        mut_state: &mut state_R,
    ) -> (res: Result<
        (
            owl_reader_response<'a>,
            Tracked<ITreeToken<(owlSpec_reader_response, state_R), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == R_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_reader_response<'a>,
            Tracked<ITreeToken<(owlSpec_reader_response, state_R), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(R_main_spec);
            let tmp_owl_nR69 = { SecretBuf::another_ref(&self.owl_NR) };
            let owl_nR69 = SecretBuf::another_ref(&tmp_owl_nR69);
            let (tmp_owl__71, owl_ev_t70) = {
                effects.owl_input::<(owlSpec_reader_response, state_R)>(Tracked(&mut itree))
            };
            let owl__71 = OwlBuf::from_vec(tmp_owl__71);
            let tmp_owl_declassified_buf972 = {
                let tracked owl_declassify_tok73 = consume_itree_declassify::<
                    (owlSpec_reader_response, state_R),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_nR69).declassify(Tracked(owl_declassify_tok73)) }
            };
            let owl_declassified_buf972 = OwlBuf::another_ref(&tmp_owl_declassified_buf972);
            let owl__74 = {
                effects.owl_output::<(owlSpec_reader_response, state_R)>(
                    Tracked(&mut itree),
                    owl_declassified_buf972.as_slice(),
                    Some(&owl_ev_t70.as_str()),
                    &R_addr(),
                );
            };
            let (tmp_owl_inp76, owl__75) = {
                effects.owl_input::<(owlSpec_reader_response, state_R)>(Tracked(&mut itree))
            };
            let owl_inp76 = OwlBuf::from_vec(tmp_owl_inp76);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp76);
            if let Some(parseval) = parse_owl_s(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_nT78 = OwlBuf::another_ref(&parseval.owl__nT2);
                let owl_mc77 = OwlBuf::another_ref(&parseval.owl__m);
                let (tmp_owl_x79, Tracked(itree)) = {
                    let tmp_arg1109 = OwlBuf::another_ref(&owl_nT78);
                    owl_call_ret_option!(effects, itree, *mut_state, lookupKeys_spec(*self, *mut_state, tmp_arg1109.view()), self.owl_lookupKeys(mut_state, tmp_arg1109))
                };
                let owl_x79 = SecretBuf::another_ref_option(&tmp_owl_x79);
                match SecretBuf::another_ref_option(&owl_x79) {
                    Option::None => { (owl_reader_response::another_ref(&owl_No()), Tracked(itree))
                    },
                    Option::Some(tmp_owl_k_packed80) => {
                        let owl_k_packed80 = SecretBuf::another_ref(&tmp_owl_k_packed80);
                        let tmp_owl_k81 = { SecretBuf::another_ref(&owl_k_packed80) };
                        let owl_k81 = SecretBuf::another_ref(&tmp_owl_k81);
                        let tmp_owl_declassified_buf2582 = {
                            let tracked owl_declassify_tok83 = consume_itree_declassify::<
                                (owlSpec_reader_response, state_R),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_nR69).declassify(
                                    Tracked(owl_declassify_tok83),
                                )
                            }
                        };
                        let owl_declassified_buf2582 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf2582,
                        );
                        let tmp_owl_msg_to_verify84 = {
                            owl_nonces(
                                OwlBuf::another_ref(&owl_declassified_buf2582),
                                SecretBuf::another_ref(
                                    &SecretBuf::from_buf(owl_nT78.another_ref()),
                                ),
                            )
                        };
                        let owl_msg_to_verify84 = owl_nonces::another_ref(&tmp_owl_msg_to_verify84);
                        let tmp_owl_caseval85 = {
                            let tracked owl_declassify_tok86 = consume_itree_declassify::<
                                (owlSpec_reader_response, state_R),
                                Endpoint,
                            >(&mut itree);
                            owl_mac_vrfy(
                                SecretBuf::another_ref(&owl_k81),
                                SecretBuf::another_ref(&serialize_owl_nonces(&owl_msg_to_verify84)),
                                OwlBuf::another_ref(&owl_mc77),
                                Tracked(owl_declassify_tok86),
                            )
                        };
                        let owl_caseval85 = SecretBuf::another_ref_option(&tmp_owl_caseval85);
                        match SecretBuf::another_ref_option(&owl_caseval85) {
                            Option::None => {
                                (owl_reader_response::another_ref(&owl_No()), Tracked(itree))
                            },
                            Option::Some(tmp_owl_m87) => {
                                let owl_m87 = SecretBuf::another_ref(&tmp_owl_m87);
                                let parseval_tmp = SecretBuf::another_ref(&owl_m87);
                                if let Some(parseval) = secret_parse_owl_secret_nonces(
                                    SecretBuf::another_ref(&parseval_tmp),
                                ) {
                                    let owl_nR89 = SecretBuf::another_ref(&parseval.owl__nR);
                                    let owl_mm88 = SecretBuf::another_ref(&parseval.owl__nT1);
                                    let tmp_owl_declassified_buf3790 = {
                                        let tracked owl_declassify_tok91 =
                                            consume_itree_declassify::<
                                            (owlSpec_reader_response, state_R),
                                            Endpoint,
                                        >(&mut itree);
                                        {
                                            SecretBuf::another_ref(&owl_nR89).declassify(
                                                Tracked(owl_declassify_tok91),
                                            )
                                        }
                                    };
                                    let owl_declassified_buf3790 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf3790,
                                    );
                                    let tmp_owl_mmm92 = { SecretBuf::another_ref(&owl_mm88) };
                                    let owl_mmm92 = SecretBuf::another_ref(&tmp_owl_mmm92);
                                    let tmp_owl_m_93 = { SecretBuf::another_ref(&owl_mmm92) };
                                    let owl_m_93 = SecretBuf::another_ref(&tmp_owl_m_93);
                                    let tmp_owl_res94 = { SecretBuf::another_ref(&owl_m_93) };
                                    let owl_res94 = SecretBuf::another_ref(&tmp_owl_res94);
                                    let tmp_owl_declassified_buf4395 = {
                                        let tracked owl_declassify_tok96 =
                                            consume_itree_declassify::<
                                            (owlSpec_reader_response, state_R),
                                            Endpoint,
                                        >(&mut itree);
                                        {
                                            SecretBuf::another_ref(&owl_res94).declassify(
                                                Tracked(owl_declassify_tok96),
                                            )
                                        }
                                    };
                                    let owl_declassified_buf4395 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf4395,
                                    );
                                    (
                                        owl_reader_response::another_ref(
                                            &owl_Yes(
                                                OwlBuf::another_ref(&owl_declassified_buf4395),
                                            ),
                                        ),
                                        Tracked(itree),
                                    )
                                } else {
                                    (owl_reader_response::another_ref(&owl_No()), Tracked(itree))
                                }
                            },
                        }
                    },
                }
            } else {
                (owl_reader_response::another_ref(&owl_No()), Tracked(itree))
            }
        };
        Ok((owl_reader_response::another_ref(&res_inner), Tracked(itree)))
    }

    #[verifier::external_body]
    #[verifier::spinoff_prover]
    pub fn owl_lookupKeys<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_R), Endpoint>>,
        mut_state: &mut state_R,
        owl_x110: OwlBuf<'a>,
    ) -> (res: Result<
        (Option<SecretBuf<'_>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_R), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == lookupKeys_spec(*self, *old(mut_state), owl_x110.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<SecretBuf<'_>>,
            Tracked<ITreeToken<(Option<Seq<u8>>, state_R), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(lookupKeys_spec);
            unimplemented!(/* implement owl_lookupKeys by hand */)
        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub struct state_T {}

impl state_T {
    #[verifier::external_body]
    pub fn init_state_T() -> Self {
        state_T {  }
    }
}

pub struct cfg_T<'T> {
    pub owl_NT: SecretBuf<'T>,
    pub owl_K: SecretBuf<'T>,
}

impl cfg_T<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_T_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_T), Endpoint>>,
        mut_state: &mut state_T,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_T), Endpoint>>), OwlError>)
        requires
            itree.view() == T_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_T), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(T_main_spec);
            let owl__98 = {
                effects.owl_output::<((), state_T)>(
                    Tracked(&mut itree),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                    Some(&R_addr()),
                    &T_addr(),
                );
            };
            let (tmp_owl_inp100, owl__99) = {
                effects.owl_input::<((), state_T)>(Tracked(&mut itree))
            };
            let owl_inp100 = OwlBuf::from_vec(tmp_owl_inp100);

            if owl_inp100.len() == NONCE_SIZE {
                let tmp_owl_inp_101 = { OwlBuf::another_ref(&owl_inp100) };
                let owl_inp_101 = OwlBuf::another_ref(&tmp_owl_inp_101);
                let tmp_owl_nT102 = { SecretBuf::another_ref(&self.owl_NT) };
                let owl_nT102 = SecretBuf::another_ref(&tmp_owl_nT102);
                let tmp_owl_msg_to_mac103 = {
                    owl_nonces(
                        OwlBuf::another_ref(&owl_inp_101),
                        SecretBuf::another_ref(&owl_nT102),
                    )
                };
                let owl_msg_to_mac103 = owl_nonces::another_ref(&tmp_owl_msg_to_mac103);
                let tmp_owl_declassified_buf54104 = {
                    let tracked owl_declassify_tok105 = consume_itree_declassify::<
                        ((), state_T),
                        Endpoint,
                    >(&mut itree);
                    {
                        SecretBuf::another_ref(
                            &serialize_owl_nonces(&owl_msg_to_mac103),
                        ).declassify(Tracked(owl_declassify_tok105))
                    }
                };
                let owl_declassified_buf54104 = OwlBuf::another_ref(&tmp_owl_declassified_buf54104);
                let tmp_owl_m106 = {
                    owl_mac(
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_K)),
                        OwlBuf::another_ref(&owl_declassified_buf54104),
                    )
                };
                let owl_m106 = OwlBuf::from_vec(tmp_owl_m106);
                let tmp_owl_declassified_buf58107 = {
                    let tracked owl_declassify_tok108 = consume_itree_declassify::<
                        ((), state_T),
                        Endpoint,
                    >(&mut itree);
                    {
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_NT)).declassify(
                            Tracked(owl_declassify_tok108),
                        )
                    }
                };
                let owl_declassified_buf58107 = OwlBuf::another_ref(&tmp_owl_declassified_buf58107);
                effects.owl_output::<((), state_T)>(
                    Tracked(&mut itree),
                    serialize_owl_s(
                        &owl_s(
                            OwlBuf::another_ref(&owl_declassified_buf58107),
                            OwlBuf::another_ref(&owl_m106),
                        ),
                    ).as_slice(),
                    Some(&R_addr()),
                    &T_addr(),
                );
                ((), Tracked(itree))
            } else {
                (owl_unit(), Tracked(itree))
            }

        };
        Ok((res_inner, Tracked(itree)))
    }
}

} // verus!
