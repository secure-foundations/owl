// Extracted verus code from file owl_toy_protocols/lak-indexed.owl:
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
spec fn spec_combinator_owlSpec_m1() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_m1() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_m1(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_m1 {
    pub owlSpec_m1_nr: Seq<u8>,
    pub owlSpec_m1_nt: Seq<u8>,
    pub owlSpec_m1_tag: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_m1(x: Seq<u8>) -> Option<owlSpec_m1> {
    let spec_comb = spec_combinator_owlSpec_m1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec_m1_nr, owlSpec_m1_nt), owlSpec_m1_tag)) = parsed;
        Some(owlSpec_m1 { owlSpec_m1_nr, owlSpec_m1_nt, owlSpec_m1_tag })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_m1_inner(x: owlSpec_m1) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_m1_nr.len(), x.owlSpec_m1_nt.len(), x.owlSpec_m1_tag.len() ] {
        let spec_comb = spec_combinator_owlSpec_m1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec_m1_nr, x.owlSpec_m1_nt), x.owlSpec_m1_tag)),
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
    arg_owlSpec_m1_nr: Seq<u8>,
    arg_owlSpec_m1_nt: Seq<u8>,
    arg_owlSpec_m1_tag: Seq<u8>,
) -> owlSpec_m1 {
    owlSpec_m1 {
        owlSpec_m1_nr: arg_owlSpec_m1_nr,
        owlSpec_m1_nt: arg_owlSpec_m1_nt,
        owlSpec_m1_tag: arg_owlSpec_m1_tag,
    }
}

spec fn spec_combinator_owlSpec_m2() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(16);
    (field_1, field_2)
}

exec fn exec_combinator_owl_m2() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_m2(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(16);
    (field_1, field_2)
}

pub struct owlSpec_m2 {
    pub owlSpec_m2_nt: Seq<u8>,
    pub owlSpec_m2_mac: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_m2(x: Seq<u8>) -> Option<owlSpec_m2> {
    let spec_comb = spec_combinator_owlSpec_m2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec_m2_nt, owlSpec_m2_mac)) = parsed;
        Some(owlSpec_m2 { owlSpec_m2_nt, owlSpec_m2_mac })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_m2_inner(x: owlSpec_m2) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_m2_nt.len(), x.owlSpec_m2_mac.len() ] {
        let spec_comb = spec_combinator_owlSpec_m2();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec_m2_nt, x.owlSpec_m2_mac))) {
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

pub open spec fn m2(arg_owlSpec_m2_nt: Seq<u8>, arg_owlSpec_m2_mac: Seq<u8>) -> owlSpec_m2 {
    owlSpec_m2 { owlSpec_m2_nt: arg_owlSpec_m2_nt, owlSpec_m2_mac: arg_owlSpec_m2_mac }
}

spec fn spec_combinator_owlSpec_m3() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(16);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_m3() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_m3(),
{
    let field_1 = Variable(16);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_m3 {
    pub owlSpec_m3_mac: Seq<u8>,
    pub owlSpec_m3_nr: Seq<u8>,
    pub owlSpec_m3_tag: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_m3(x: Seq<u8>) -> Option<owlSpec_m3> {
    let spec_comb = spec_combinator_owlSpec_m3();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec_m3_mac, owlSpec_m3_nr), owlSpec_m3_tag)) = parsed;
        Some(owlSpec_m3 { owlSpec_m3_mac, owlSpec_m3_nr, owlSpec_m3_tag })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_m3_inner(x: owlSpec_m3) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_m3_mac.len(), x.owlSpec_m3_nr.len(), x.owlSpec_m3_tag.len() ] {
        let spec_comb = spec_combinator_owlSpec_m3();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec_m3_mac, x.owlSpec_m3_nr), x.owlSpec_m3_tag)),
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
pub closed spec fn serialize_owlSpec_m3(x: owlSpec_m3) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_m3_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_m3 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_m3(self)
    }
}

pub open spec fn m3(
    arg_owlSpec_m3_mac: Seq<u8>,
    arg_owlSpec_m3_nr: Seq<u8>,
    arg_owlSpec_m3_tag: Seq<u8>,
) -> owlSpec_m3 {
    owlSpec_m3 {
        owlSpec_m3_mac: arg_owlSpec_m3_mac,
        owlSpec_m3_nr: arg_owlSpec_m3_nr,
        owlSpec_m3_tag: arg_owlSpec_m3_tag,
    }
}

pub enum owlSpec_macd_by_k {
    owlSpec_msg1(owlSpec_m1),
    owlSpec_msg2(owlSpec_m3),
}

use owlSpec_macd_by_k::*;

#[verifier::external_body]
pub closed spec fn parse_owlSpec_macd_by_k(x: Seq<u8>) -> Option<owlSpec_macd_by_k> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_macd_by_k_inner(x: owlSpec_macd_by_k) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_macd_by_k(x: owlSpec_macd_by_k) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_macd_by_k {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_macd_by_k(self)
    }
}

pub open spec fn msg1(x: owlSpec_m1) -> owlSpec_macd_by_k {
    crate::owlSpec_macd_by_k::owlSpec_msg1(x)
}

pub open spec fn msg2(x: owlSpec_m3) -> owlSpec_macd_by_k {
    crate::owlSpec_macd_by_k::owlSpec_msg2(x)
}

pub open spec fn msg1_enumtest(x: owlSpec_macd_by_k) -> bool {
    match x {
        owlSpec_macd_by_k::owlSpec_msg1(_) => true,
        _ => false,
    }
}

pub open spec fn msg2_enumtest(x: owlSpec_macd_by_k) -> bool {
    match x {
        owlSpec_macd_by_k::owlSpec_msg2(_) => true,
        _ => false,
    }
}

pub enum owlSpec_reader_response {
    owlSpec_No(),
    owlSpec_Yes(),
}

use owlSpec_reader_response::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_reader_response(x: Seq<u8>) -> Option<owlSpec_reader_response> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(0)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owlSpec_reader_response::owlSpec_No(),
            inj_ord_choice_pat!(*, _) => owlSpec_reader_response::owlSpec_Yes(),
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
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(0)));
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
        owlSpec_reader_response::owlSpec_Yes() => {
            if no_usize_overflows_spec![ 1, 0 ] {
                if let Ok(serialized) = spec_comb.spec_serialize(
                    inj_ord_choice_result!(*, ((), seq![])),
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

pub open spec fn Yes() -> owlSpec_reader_response {
    crate::owlSpec_reader_response::owlSpec_Yes()
}

pub open spec fn No_enumtest(x: owlSpec_reader_response) -> bool {
    match x {
        owlSpec_reader_response::owlSpec_No() => true,
        _ => false,
    }
}

pub open spec fn Yes_enumtest(x: owlSpec_reader_response) -> bool {
    match x {
        owlSpec_reader_response::owlSpec_Yes() => true,
        _ => false,
    }
}

#[verifier::opaque]
pub open spec fn R_main_spec(cfg: cfg_R, mut_state: state_R) -> (res: ITree<
    (owlSpec_reader_response, state_R),
    Endpoint,
>) {
    owl_spec!(mut_state, state_R,
        let tag1 = ((ret(cfg.owl_tag1_tag.view()))) in
let tag2 = ((ret(cfg.owl_tag2_tag.view()))) in
let NR = ((ret(cfg.owl_nR.view()))) in
let declassified_buf17 = ((declassify(DeclassifyingOp::ControlFlow(NR))) in
(ret((NR)))) in
(output (declassified_buf17) to (Some(Endpoint::Loc_T))) in
(input(inp,_21)) in
(parse (parse_owlSpec_m2(inp)) as (owlSpec_m2{owlSpec_m2_nt : NT, owlSpec_m2_mac : mc}) in {
let declassified_buf27 = ((declassify(DeclassifyingOp::ControlFlow(NR))) in
(ret((NR)))) in
let declassified_buf30 = ((declassify(DeclassifyingOp::ControlFlow(tag1))) in
(ret((tag1)))) in
let msg_to_mac_verify = ((ret(msg1(m1(declassified_buf27, NT, declassified_buf30))))) in
let x = (call(lookupKeys_spec(cfg, mut_state, NT))) in
(case (x) {
| None => {
(ret(No()))
},
| Some(k_packed) => {
let k = ((ret(k_packed))) in
let caseval = ((declassify(DeclassifyingOp::MacVrfy(k, serialize_owlSpec_macd_by_k(msg_to_mac_verify), mc))) in
(ret(mac_vrfy(k, serialize_owlSpec_macd_by_k(msg_to_mac_verify), mc)))) in
(case (caseval) {
| None => {
(ret(No()))
},
| Some(m) => {
let b = ((ret(length(mc) == MACLEN_SIZE))) in
(if (b) then
(let mc = ((ret(mc))) in
let declassified_buf45 = ((declassify(DeclassifyingOp::ControlFlow(NR))) in
(ret((NR)))) in
let declassified_buf48 = ((declassify(DeclassifyingOp::ControlFlow(tag2))) in
(ret((tag2)))) in
let msg_to_mac = ((ret(msg2(m3(mc, declassified_buf45, declassified_buf48))))) in
let mac_msg = ((ret(mac(k, serialize_owlSpec_macd_by_k(msg_to_mac))))) in
(output (mac_msg) to (Some(Endpoint::Loc_T))) in
(ret(Yes())))
else
((ret(No()))))
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
        let tag1 = ((ret(cfg.owl_tag1_tag.view()))) in
(input(NR,_57)) in
let b = ((ret(length(NR) == NONCE_SIZE))) in
(if (b) then
(let NR = ((ret(NR))) in
let declassified_buf61 = ((declassify(DeclassifyingOp::ControlFlow(cfg.owl_nT.view()))) in
(ret((cfg.owl_nT.view())))) in
let declassified_buf64 = ((declassify(DeclassifyingOp::ControlFlow(tag1))) in
(ret((tag1)))) in
let msg_to_mac = ((ret(msg1(m1(NR, declassified_buf61, declassified_buf64))))) in
let msg = ((ret(mac(cfg.owl_K.view(), serialize_owlSpec_macd_by_k(msg_to_mac))))) in
(output (msg) to (Some(Endpoint::Loc_R))))
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

pub struct owl_m1<'a> {
    pub owl_m1_nr: OwlBuf<'a>,
    pub owl_m1_nt: OwlBuf<'a>,
    pub owl_m1_tag: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_m1<'a>(
    arg_owl_m1_nr: OwlBuf<'a>,
    arg_owl_m1_nt: OwlBuf<'a>,
    arg_owl_m1_tag: OwlBuf<'a>,
) -> (res: owl_m1<'a>)
    ensures
        res.owl_m1_nr.view() == arg_owl_m1_nr.view(),
        res.owl_m1_nt.view() == arg_owl_m1_nt.view(),
        res.owl_m1_tag.view() == arg_owl_m1_tag.view(),
{
    owl_m1 { owl_m1_nr: arg_owl_m1_nr, owl_m1_nt: arg_owl_m1_nt, owl_m1_tag: arg_owl_m1_tag }
}

impl<'a> owl_m1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_m1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_m1 {
            owl_m1_nr: OwlBuf::another_ref(&self.owl_m1_nr),
            owl_m1_nt: OwlBuf::another_ref(&self.owl_m1_nt),
            owl_m1_tag: OwlBuf::another_ref(&self.owl_m1_tag),
        }
    }
}

impl View for owl_m1<'_> {
    type V = owlSpec_m1;

    open spec fn view(&self) -> owlSpec_m1 {
        owlSpec_m1 {
            owlSpec_m1_nr: self.owl_m1_nr.view(),
            owlSpec_m1_nt: self.owl_m1_nt.view(),
            owlSpec_m1_tag: self.owl_m1_tag.view(),
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
        let ((owl_m1_nr, owl_m1_nt), owl_m1_tag) = parsed;
        Some(
            owl_m1 {
                owl_m1_nr: OwlBuf::another_ref(&owl_m1_nr),
                owl_m1_nt: OwlBuf::another_ref(&owl_m1_nt),
                owl_m1_tag: OwlBuf::another_ref(&owl_m1_tag),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_m1_inner<'a>(arg: &owl_m1<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_m1_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_m1_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_m1_inner);
    if no_usize_overflows![ arg.owl_m1_nr.len(), arg.owl_m1_nt.len(), arg.owl_m1_tag.len(), 0 ] {
        let exec_comb = exec_combinator_owl_m1();
        let mut obuf = vec_u8_of_len(
            arg.owl_m1_nr.len() + arg.owl_m1_nt.len() + arg.owl_m1_tag.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (OwlBuf::another_ref(&arg.owl_m1_nr), OwlBuf::another_ref(&arg.owl_m1_nt)),
                OwlBuf::another_ref(&arg.owl_m1_tag),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_m1_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_m1<'a>(arg: &owl_m1<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_m1(arg.view()),
{
    reveal(serialize_owlSpec_m1);
    let res = serialize_owl_m1_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_m2<'a> {
    pub owl_m2_nt: OwlBuf<'a>,
    pub owl_m2_mac: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_m2<'a>(arg_owl_m2_nt: OwlBuf<'a>, arg_owl_m2_mac: OwlBuf<'a>) -> (res: owl_m2<'a>)
    ensures
        res.owl_m2_nt.view() == arg_owl_m2_nt.view(),
        res.owl_m2_mac.view() == arg_owl_m2_mac.view(),
{
    owl_m2 { owl_m2_nt: arg_owl_m2_nt, owl_m2_mac: arg_owl_m2_mac }
}

impl<'a> owl_m2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_m2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_m2 {
            owl_m2_nt: OwlBuf::another_ref(&self.owl_m2_nt),
            owl_m2_mac: OwlBuf::another_ref(&self.owl_m2_mac),
        }
    }
}

impl View for owl_m2<'_> {
    type V = owlSpec_m2;

    open spec fn view(&self) -> owlSpec_m2 {
        owlSpec_m2 { owlSpec_m2_nt: self.owl_m2_nt.view(), owlSpec_m2_mac: self.owl_m2_mac.view() }
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
        let (owl_m2_nt, owl_m2_mac) = parsed;
        Some(
            owl_m2 {
                owl_m2_nt: OwlBuf::another_ref(&owl_m2_nt),
                owl_m2_mac: OwlBuf::another_ref(&owl_m2_mac),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_m2_inner<'a>(arg: &owl_m2<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_m2_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_m2_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_m2_inner);
    if no_usize_overflows![ arg.owl_m2_nt.len(), arg.owl_m2_mac.len(), 0 ] {
        let exec_comb = exec_combinator_owl_m2();
        let mut obuf = vec_u8_of_len(arg.owl_m2_nt.len() + arg.owl_m2_mac.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl_m2_nt), OwlBuf::another_ref(&arg.owl_m2_mac)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_m2_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_m2<'a>(arg: &owl_m2<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_m2(arg.view()),
{
    reveal(serialize_owlSpec_m2);
    let res = serialize_owl_m2_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_m3<'a> {
    pub owl_m3_mac: OwlBuf<'a>,
    pub owl_m3_nr: OwlBuf<'a>,
    pub owl_m3_tag: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_m3<'a>(
    arg_owl_m3_mac: OwlBuf<'a>,
    arg_owl_m3_nr: OwlBuf<'a>,
    arg_owl_m3_tag: OwlBuf<'a>,
) -> (res: owl_m3<'a>)
    ensures
        res.owl_m3_mac.view() == arg_owl_m3_mac.view(),
        res.owl_m3_nr.view() == arg_owl_m3_nr.view(),
        res.owl_m3_tag.view() == arg_owl_m3_tag.view(),
{
    owl_m3 { owl_m3_mac: arg_owl_m3_mac, owl_m3_nr: arg_owl_m3_nr, owl_m3_tag: arg_owl_m3_tag }
}

impl<'a> owl_m3<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_m3<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_m3 {
            owl_m3_mac: OwlBuf::another_ref(&self.owl_m3_mac),
            owl_m3_nr: OwlBuf::another_ref(&self.owl_m3_nr),
            owl_m3_tag: OwlBuf::another_ref(&self.owl_m3_tag),
        }
    }
}

impl View for owl_m3<'_> {
    type V = owlSpec_m3;

    open spec fn view(&self) -> owlSpec_m3 {
        owlSpec_m3 {
            owlSpec_m3_mac: self.owl_m3_mac.view(),
            owlSpec_m3_nr: self.owl_m3_nr.view(),
            owlSpec_m3_tag: self.owl_m3_tag.view(),
        }
    }
}

pub exec fn parse_owl_m3<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_m3<'a>>)
    ensures
        res is Some ==> parse_owlSpec_m3(arg.view()) is Some,
        res is None ==> parse_owlSpec_m3(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_m3(arg.view())->Some_0,
{
    reveal(parse_owlSpec_m3);
    let exec_comb = exec_combinator_owl_m3();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl_m3_mac, owl_m3_nr), owl_m3_tag) = parsed;
        Some(
            owl_m3 {
                owl_m3_mac: OwlBuf::another_ref(&owl_m3_mac),
                owl_m3_nr: OwlBuf::another_ref(&owl_m3_nr),
                owl_m3_tag: OwlBuf::another_ref(&owl_m3_tag),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_m3_inner<'a>(arg: &owl_m3<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_m3_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_m3_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_m3_inner);
    if no_usize_overflows![ arg.owl_m3_mac.len(), arg.owl_m3_nr.len(), arg.owl_m3_tag.len(), 0 ] {
        let exec_comb = exec_combinator_owl_m3();
        let mut obuf = vec_u8_of_len(
            arg.owl_m3_mac.len() + arg.owl_m3_nr.len() + arg.owl_m3_tag.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (OwlBuf::another_ref(&arg.owl_m3_mac), OwlBuf::another_ref(&arg.owl_m3_nr)),
                OwlBuf::another_ref(&arg.owl_m3_tag),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_m3_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_m3<'a>(arg: &owl_m3<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_m3(arg.view()),
{
    reveal(serialize_owlSpec_m3);
    let res = serialize_owl_m3_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_macd_by_k<'a> {
    owl_msg1(owl_m1<'a>),
    owl_msg2(owl_m3<'a>),
}

use owl_macd_by_k::*;

impl<'a> owl_macd_by_k<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_macd_by_k<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_msg1(x) => owl_msg1(owl_m1::another_ref(x)),
            owl_msg2(x) => owl_msg2(owl_m3::another_ref(x)),
        }
    }
}

impl View for owl_macd_by_k<'_> {
    type V = owlSpec_macd_by_k;

    open spec fn view(&self) -> owlSpec_macd_by_k {
        match self {
            owl_msg1(v) => owlSpec_macd_by_k::owlSpec_msg1(v.view()),
            owl_msg2(v) => owlSpec_macd_by_k::owlSpec_msg2(v.view()),
        }
    }
}

#[inline]
pub fn owl_msg1_enumtest(x: &owl_macd_by_k<'_>) -> (res: bool)
    ensures
        res == msg1_enumtest(x.view()),
{
    match x {
        owl_macd_by_k::owl_msg1(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl_msg2_enumtest(x: &owl_macd_by_k<'_>) -> (res: bool)
    ensures
        res == msg2_enumtest(x.view()),
{
    match x {
        owl_macd_by_k::owl_msg2(_) => true,
        _ => false,
    }
}

#[verifier::external_body]
pub exec fn parse_owl_macd_by_k<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_macd_by_k<'a>>)
    ensures
        res is Some ==> parse_owlSpec_macd_by_k(arg.view()) is Some,
        res is None ==> parse_owlSpec_macd_by_k(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_macd_by_k(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_macd_by_k_inner(arg: &owl_macd_by_k) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_macd_by_k_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_macd_by_k_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_macd_by_k_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_macd_by_k(arg: &owl_macd_by_k) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_macd_by_k(arg.view()),
{
    unimplemented!()
}

pub enum owl_reader_response {
    owl_No(),
    owl_Yes(),
}

use owl_reader_response::*;

impl owl_reader_response {
    pub fn another_ref<'other>(&'other self) -> (result: owl_reader_response)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_No() => owl_No(),
            owl_Yes() => owl_Yes(),
        }
    }
}

impl View for owl_reader_response {
    type V = owlSpec_reader_response;

    open spec fn view(&self) -> owlSpec_reader_response {
        match self {
            owl_No() => owlSpec_reader_response::owlSpec_No(),
            owl_Yes() => owlSpec_reader_response::owlSpec_Yes(),
        }
    }
}

#[inline]
pub fn owl_No_enumtest(x: &owl_reader_response) -> (res: bool)
    ensures
        res == No_enumtest(x.view()),
{
    match x {
        owl_reader_response::owl_No() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_Yes_enumtest(x: &owl_reader_response) -> (res: bool)
    ensures
        res == Yes_enumtest(x.view()),
{
    match x {
        owl_reader_response::owl_Yes() => true,
        _ => false,
    }
}

pub exec fn parse_owl_reader_response<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_reader_response>)
    ensures
        res is Some ==> parse_owlSpec_reader_response(arg.view()) is Some,
        res is None ==> parse_owlSpec_reader_response(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_reader_response(arg.view())->Some_0,
{
    reveal(parse_owlSpec_reader_response);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(0)), (Tag::new(U8, 2), Variable(0)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owl_reader_response::owl_No(),
            inj_ord_choice_pat!(*, _) => owl_reader_response::owl_Yes(),
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
) -> (res: Option<owl_reader_response>)
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
    pub owl_nR: SecretBuf<'R>,
    pub owl_tag2_tag: SecretBuf<'R>,
    pub owl_tag1_tag: SecretBuf<'R>,
    pub owl_K: SecretBuf<'R>,
}

impl cfg_R<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_R_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_reader_response, state_R), Endpoint>>,
        mut_state: &mut state_R,
    ) -> (res: Result<
        (owl_reader_response, Tracked<ITreeToken<(owlSpec_reader_response, state_R), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == R_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_reader_response,
            Tracked<ITreeToken<(owlSpec_reader_response, state_R), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(R_main_spec);
            let tmp_owl_tag184 = { SecretBuf::another_ref(&self.owl_tag1_tag) };
            let owl_tag184 = SecretBuf::another_ref(&tmp_owl_tag184);
            let tmp_owl_tag285 = { SecretBuf::another_ref(&self.owl_tag2_tag) };
            let owl_tag285 = SecretBuf::another_ref(&tmp_owl_tag285);
            let tmp_owl_NR86 = { SecretBuf::another_ref(&self.owl_nR) };
            let owl_NR86 = SecretBuf::another_ref(&tmp_owl_NR86);
            let tmp_owl_declassified_buf1787 = {
                let tracked owl_declassify_tok88 = consume_itree_declassify::<
                    (owlSpec_reader_response, state_R),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_NR86).declassify(Tracked(owl_declassify_tok88)) }
            };
            let owl_declassified_buf1787 = OwlBuf::another_ref(&tmp_owl_declassified_buf1787);
            let owl__89 = {
                effects.owl_output::<(owlSpec_reader_response, state_R)>(
                    Tracked(&mut itree),
                    owl_declassified_buf1787.as_slice(),
                    Some(&T_addr()),
                    &R_addr(),
                );
            };
            let (tmp_owl_inp91, owl__90) = {
                effects.owl_input::<(owlSpec_reader_response, state_R)>(Tracked(&mut itree))
            };
            let owl_inp91 = OwlBuf::from_vec(tmp_owl_inp91);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp91);
            if let Some(parseval) = parse_owl_m2(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_NT93 = OwlBuf::another_ref(&parseval.owl_m2_nt);
                let owl_mc92 = OwlBuf::another_ref(&parseval.owl_m2_mac);
                {
                    let tmp_owl_declassified_buf2794 = {
                        let tracked owl_declassify_tok95 = consume_itree_declassify::<
                            (owlSpec_reader_response, state_R),
                            Endpoint,
                        >(&mut itree);
                        {
                            SecretBuf::another_ref(&owl_NR86).declassify(
                                Tracked(owl_declassify_tok95),
                            )
                        }
                    };
                    let owl_declassified_buf2794 = OwlBuf::another_ref(
                        &tmp_owl_declassified_buf2794,
                    );
                    let tmp_owl_declassified_buf3096 = {
                        let tracked owl_declassify_tok97 = consume_itree_declassify::<
                            (owlSpec_reader_response, state_R),
                            Endpoint,
                        >(&mut itree);
                        {
                            SecretBuf::another_ref(&owl_tag184).declassify(
                                Tracked(owl_declassify_tok97),
                            )
                        }
                    };
                    let owl_declassified_buf3096 = OwlBuf::another_ref(
                        &tmp_owl_declassified_buf3096,
                    );
                    let tmp_owl_msg_to_mac_verify98 = {
                        owl_msg1(
                            owl_m1::another_ref(
                                &owl_m1(
                                    OwlBuf::another_ref(&owl_declassified_buf2794),
                                    OwlBuf::another_ref(&owl_NT93),
                                    OwlBuf::another_ref(&owl_declassified_buf3096),
                                ),
                            ),
                        )
                    };
                    let owl_msg_to_mac_verify98 = owl_macd_by_k::another_ref(
                        &tmp_owl_msg_to_mac_verify98,
                    );
                    let (tmp_owl_x99, Tracked(itree)) = {
                        let tmp_arg1126 = OwlBuf::another_ref(&owl_NT93);
                        owl_call_ret_option!(effects, itree, *mut_state, lookupKeys_spec(*self, *mut_state, tmp_arg1126.view()), self.owl_lookupKeys(mut_state, tmp_arg1126))
                    };
                    let owl_x99 = SecretBuf::another_ref_option(&tmp_owl_x99);
                    match SecretBuf::another_ref_option(&owl_x99) {
                        Option::None => {
                            (owl_reader_response::another_ref(&owl_No()), Tracked(itree))
                        },
                        Option::Some(tmp_owl_k_packed100) => {
                            let owl_k_packed100 = SecretBuf::another_ref(&tmp_owl_k_packed100);
                            let tmp_owl_k101 = { SecretBuf::another_ref(&owl_k_packed100) };
                            let owl_k101 = SecretBuf::another_ref(&tmp_owl_k101);
                            let tmp_owl_caseval102 = {
                                let tracked owl_declassify_tok103 = consume_itree_declassify::<
                                    (owlSpec_reader_response, state_R),
                                    Endpoint,
                                >(&mut itree);
                                owl_mac_vrfy(
                                    SecretBuf::another_ref(&owl_k101),
                                    SecretBuf::another_ref(
                                        &SecretBuf::from_buf(
                                            OwlBuf::from_vec(
                                                serialize_owl_macd_by_k(&owl_msg_to_mac_verify98),
                                            ).another_ref(),
                                        ),
                                    ),
                                    OwlBuf::another_ref(&owl_mc92),
                                    Tracked(owl_declassify_tok103),
                                )
                            };
                            let owl_caseval102 = SecretBuf::another_ref_option(&tmp_owl_caseval102);
                            match SecretBuf::another_ref_option(&owl_caseval102) {
                                Option::None => {
                                    (owl_reader_response::another_ref(&owl_No()), Tracked(itree))
                                },
                                Option::Some(tmp_owl_m104) => {
                                    let owl_m104 = SecretBuf::another_ref(&tmp_owl_m104);
                                    let owl_b105 = { owl_mc92.len() == MACLEN_SIZE };

                                    if owl_b105 {
                                        let tmp_owl_mc106 = { OwlBuf::another_ref(&owl_mc92) };
                                        let owl_mc106 = OwlBuf::another_ref(&tmp_owl_mc106);
                                        let tmp_owl_declassified_buf45107 = {
                                            let tracked owl_declassify_tok108 =
                                                consume_itree_declassify::<
                                                (owlSpec_reader_response, state_R),
                                                Endpoint,
                                            >(&mut itree);
                                            {
                                                SecretBuf::another_ref(&owl_NR86).declassify(
                                                    Tracked(owl_declassify_tok108),
                                                )
                                            }
                                        };
                                        let owl_declassified_buf45107 = OwlBuf::another_ref(
                                            &tmp_owl_declassified_buf45107,
                                        );
                                        let tmp_owl_declassified_buf48109 = {
                                            let tracked owl_declassify_tok110 =
                                                consume_itree_declassify::<
                                                (owlSpec_reader_response, state_R),
                                                Endpoint,
                                            >(&mut itree);
                                            {
                                                SecretBuf::another_ref(&owl_tag285).declassify(
                                                    Tracked(owl_declassify_tok110),
                                                )
                                            }
                                        };
                                        let owl_declassified_buf48109 = OwlBuf::another_ref(
                                            &tmp_owl_declassified_buf48109,
                                        );
                                        let tmp_owl_msg_to_mac111 = {
                                            owl_msg2(
                                                owl_m3::another_ref(
                                                    &owl_m3(
                                                        OwlBuf::another_ref(&owl_mc106),
                                                        OwlBuf::another_ref(
                                                            &owl_declassified_buf45107,
                                                        ),
                                                        OwlBuf::another_ref(
                                                            &owl_declassified_buf48109,
                                                        ),
                                                    ),
                                                ),
                                            )
                                        };
                                        let owl_msg_to_mac111 = owl_macd_by_k::another_ref(
                                            &tmp_owl_msg_to_mac111,
                                        );
                                        let tmp_owl_mac_msg112 = {
                                            owl_mac(
                                                SecretBuf::another_ref(&owl_k101),
                                                OwlBuf::another_ref(
                                                    &OwlBuf::from_vec(
                                                        serialize_owl_macd_by_k(&owl_msg_to_mac111),
                                                    ),
                                                ),
                                            )
                                        };
                                        let owl_mac_msg112 = OwlBuf::from_vec(tmp_owl_mac_msg112);
                                        let owl__113 = {
                                            effects.owl_output::<
                                                (owlSpec_reader_response, state_R),
                                            >(
                                                Tracked(&mut itree),
                                                owl_mac_msg112.as_slice(),
                                                Some(&T_addr()),
                                                &R_addr(),
                                            );
                                        };
                                        (
                                            owl_reader_response::another_ref(&owl_Yes()),
                                            Tracked(itree),
                                        )
                                    } else {
                                        (
                                            owl_reader_response::another_ref(&owl_No()),
                                            Tracked(itree),
                                        )
                                    }

                                },
                            }
                        },
                    }
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
        owl_x127: OwlBuf<'a>,
    ) -> (res: Result<
        (Option<SecretBuf<'_>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_R), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == lookupKeys_spec(*self, *old(mut_state), owl_x127.view()),
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
    pub owl_nT: SecretBuf<'T>,
    pub owl_tag2_tag: SecretBuf<'T>,
    pub owl_tag1_tag: SecretBuf<'T>,
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
            let tmp_owl_tag1115 = { SecretBuf::another_ref(&self.owl_tag1_tag) };
            let owl_tag1115 = SecretBuf::another_ref(&tmp_owl_tag1115);
            let (tmp_owl_NR117, owl__116) = {
                effects.owl_input::<((), state_T)>(Tracked(&mut itree))
            };
            let owl_NR117 = OwlBuf::from_vec(tmp_owl_NR117);
            let owl_b118 = { owl_NR117.len() == NONCE_SIZE };

            if owl_b118 {
                let tmp_owl_NR119 = { OwlBuf::another_ref(&owl_NR117) };
                let owl_NR119 = OwlBuf::another_ref(&tmp_owl_NR119);
                let tmp_owl_declassified_buf61120 = {
                    let tracked owl_declassify_tok121 = consume_itree_declassify::<
                        ((), state_T),
                        Endpoint,
                    >(&mut itree);
                    {
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_nT)).declassify(
                            Tracked(owl_declassify_tok121),
                        )
                    }
                };
                let owl_declassified_buf61120 = OwlBuf::another_ref(&tmp_owl_declassified_buf61120);
                let tmp_owl_declassified_buf64122 = {
                    let tracked owl_declassify_tok123 = consume_itree_declassify::<
                        ((), state_T),
                        Endpoint,
                    >(&mut itree);
                    {
                        SecretBuf::another_ref(&owl_tag1115).declassify(
                            Tracked(owl_declassify_tok123),
                        )
                    }
                };
                let owl_declassified_buf64122 = OwlBuf::another_ref(&tmp_owl_declassified_buf64122);
                let tmp_owl_msg_to_mac124 = {
                    owl_msg1(
                        owl_m1::another_ref(
                            &owl_m1(
                                OwlBuf::another_ref(&owl_NR119),
                                OwlBuf::another_ref(&owl_declassified_buf61120),
                                OwlBuf::another_ref(&owl_declassified_buf64122),
                            ),
                        ),
                    )
                };
                let owl_msg_to_mac124 = owl_macd_by_k::another_ref(&tmp_owl_msg_to_mac124);
                let tmp_owl_msg125 = {
                    owl_mac(
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_K)),
                        OwlBuf::another_ref(
                            &OwlBuf::from_vec(serialize_owl_macd_by_k(&owl_msg_to_mac124)),
                        ),
                    )
                };
                let owl_msg125 = OwlBuf::from_vec(tmp_owl_msg125);
                effects.owl_output::<((), state_T)>(
                    Tracked(&mut itree),
                    owl_msg125.as_slice(),
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
