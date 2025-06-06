// Extracted verus code from file owl_toy_protocols/mw-indexed.owl:
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
spec fn spec_combinator_owlSpec_h1_t() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(1);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_h1_t() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_h1_t(),
{
    let field_1 = Variable(1);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_h1_t {
    pub owlSpec_h1_c: Seq<u8>,
    pub owlSpec_h1_nr: Seq<u8>,
    pub owlSpec_h1_nt: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_h1_t(x: Seq<u8>) -> Option<owlSpec_h1_t> {
    let spec_comb = spec_combinator_owlSpec_h1_t();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec_h1_c, owlSpec_h1_nr), owlSpec_h1_nt)) = parsed;
        Some(owlSpec_h1_t { owlSpec_h1_c, owlSpec_h1_nr, owlSpec_h1_nt })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_h1_t_inner(x: owlSpec_h1_t) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_h1_c.len(), x.owlSpec_h1_nr.len(), x.owlSpec_h1_nt.len() ] {
        let spec_comb = spec_combinator_owlSpec_h1_t();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec_h1_c, x.owlSpec_h1_nr), x.owlSpec_h1_nt)),
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
pub closed spec fn serialize_owlSpec_h1_t(x: owlSpec_h1_t) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_h1_t_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_h1_t {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_h1_t(self)
    }
}

pub open spec fn h1_t(
    arg_owlSpec_h1_c: Seq<u8>,
    arg_owlSpec_h1_nr: Seq<u8>,
    arg_owlSpec_h1_nt: Seq<u8>,
) -> owlSpec_h1_t {
    owlSpec_h1_t {
        owlSpec_h1_c: arg_owlSpec_h1_c,
        owlSpec_h1_nr: arg_owlSpec_h1_nr,
        owlSpec_h1_nt: arg_owlSpec_h1_nt,
    }
}

spec fn spec_combinator_owlSpec_secret_h1_t() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(1);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_secret_h1_t() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_h1_t(),
{
    let field_1 = Variable(1);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_secret_h1_t {
    pub owlSpec_h1_c: Seq<u8>,
    pub owlSpec_h1_nr: Seq<u8>,
    pub owlSpec_h1_nt: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_h1_t(x: Seq<u8>) -> Option<owlSpec_secret_h1_t> {
    let spec_comb = spec_combinator_owlSpec_secret_h1_t();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec_h1_c, owlSpec_h1_nr), owlSpec_h1_nt)) = parsed;
        Some(owlSpec_secret_h1_t { owlSpec_h1_c, owlSpec_h1_nr, owlSpec_h1_nt })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_h1_t_inner(x: owlSpec_secret_h1_t) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_h1_c.len(), x.owlSpec_h1_nr.len(), x.owlSpec_h1_nt.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_h1_t();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec_h1_c, x.owlSpec_h1_nr), x.owlSpec_h1_nt)),
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
pub closed spec fn serialize_owlSpec_secret_h1_t(x: owlSpec_secret_h1_t) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_secret_h1_t_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_h1_t {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_h1_t(self)
    }
}

pub open spec fn secret_h1_t(
    arg_owlSpec_h1_c: Seq<u8>,
    arg_owlSpec_h1_nr: Seq<u8>,
    arg_owlSpec_h1_nt: Seq<u8>,
) -> owlSpec_secret_h1_t {
    owlSpec_secret_h1_t {
        owlSpec_h1_c: arg_owlSpec_h1_c,
        owlSpec_h1_nr: arg_owlSpec_h1_nr,
        owlSpec_h1_nt: arg_owlSpec_h1_nt,
    }
}

spec fn spec_combinator_owlSpec_m1_t() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_m1_t() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_m1_t(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_m1_t {
    pub owlSpec_m1_nt: Seq<u8>,
    pub owlSpec_m1_xormac: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_m1_t(x: Seq<u8>) -> Option<owlSpec_m1_t> {
    let spec_comb = spec_combinator_owlSpec_m1_t();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec_m1_nt, owlSpec_m1_xormac)) = parsed;
        Some(owlSpec_m1_t { owlSpec_m1_nt, owlSpec_m1_xormac })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_m1_t_inner(x: owlSpec_m1_t) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_m1_nt.len(), x.owlSpec_m1_xormac.len() ] {
        let spec_comb = spec_combinator_owlSpec_m1_t();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec_m1_nt, x.owlSpec_m1_xormac))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_m1_t(x: owlSpec_m1_t) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_m1_t_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_m1_t {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_m1_t(self)
    }
}

pub open spec fn m1_t(arg_owlSpec_m1_nt: Seq<u8>, arg_owlSpec_m1_xormac: Seq<u8>) -> owlSpec_m1_t {
    owlSpec_m1_t { owlSpec_m1_nt: arg_owlSpec_m1_nt, owlSpec_m1_xormac: arg_owlSpec_m1_xormac }
}

spec fn spec_combinator_owlSpec_pair() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(64);
    (field_1, field_2)
}

exec fn exec_combinator_owl_pair() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_pair(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(64);
    (field_1, field_2)
}

pub struct owlSpec_pair {
    pub owlSpec__id: Seq<u8>,
    pub owlSpec__k: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_pair(x: Seq<u8>) -> Option<owlSpec_pair> {
    let spec_comb = spec_combinator_owlSpec_pair();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__id, owlSpec__k)) = parsed;
        Some(owlSpec_pair { owlSpec__id, owlSpec__k })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_pair_inner(x: owlSpec_pair) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__id.len(), x.owlSpec__k.len() ] {
        let spec_comb = spec_combinator_owlSpec_pair();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__id, x.owlSpec__k))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_pair(x: owlSpec_pair) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_pair_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_pair {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_pair(self)
    }
}

pub open spec fn pair(arg_owlSpec__id: Seq<u8>, arg_owlSpec__k: Seq<u8>) -> owlSpec_pair {
    owlSpec_pair { owlSpec__id: arg_owlSpec__id, owlSpec__k: arg_owlSpec__k }
}

spec fn spec_combinator_owlSpec_secret_pair() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(64);
    (field_1, field_2)
}

exec fn exec_combinator_owl_secret_pair() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_pair(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(64);
    (field_1, field_2)
}

pub struct owlSpec_secret_pair {
    pub owlSpec__id: Seq<u8>,
    pub owlSpec__k: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_pair(x: Seq<u8>) -> Option<owlSpec_secret_pair> {
    let spec_comb = spec_combinator_owlSpec_secret_pair();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__id, owlSpec__k)) = parsed;
        Some(owlSpec_secret_pair { owlSpec__id, owlSpec__k })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_pair_inner(x: owlSpec_secret_pair) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__id.len(), x.owlSpec__k.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_pair();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__id, x.owlSpec__k))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_pair(x: owlSpec_secret_pair) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_secret_pair_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_pair {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_pair(self)
    }
}

pub open spec fn secret_pair(
    arg_owlSpec__id: Seq<u8>,
    arg_owlSpec__k: Seq<u8>,
) -> owlSpec_secret_pair {
    owlSpec_secret_pair { owlSpec__id: arg_owlSpec__id, owlSpec__k: arg_owlSpec__k }
}

pub enum owlSpec_reader_response {
    owlSpec_No(),
    owlSpec_Yes(Seq<u8>),
}

use owlSpec_reader_response::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_reader_response(x: Seq<u8>) -> Option<owlSpec_reader_response> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Tail));
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
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Tail));
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
let declassified_buf11 = ((declassify(DeclassifyingOp::ControlFlow(nR))) in
(ret((nR)))) in
(output (declassified_buf11) to (Some(Endpoint::Loc_T))) in
(input(inp,_15)) in
(parse (parse_owlSpec_m1_t(inp)) as (owlSpec_m1_t{owlSpec_m1_nt : nT, owlSpec_m1_xormac : mc}) in {
let x = (call(lookupKeys_spec(cfg, mut_state, nT))) in
(case (x) {
| None => {
(ret(No()))
},
| Some(p_packed) => {
let p = ((ret(p_packed))) in
(parse (p) as (owlSpec_pair{owlSpec__id : id, owlSpec__k : k}) in {
let declassified_buf35 = ((declassify(DeclassifyingOp::ControlFlow(nR))) in
(ret((nR)))) in
let mac_to_verify = ((ret(h1_t(zz(), declassified_buf35, nT)))) in
let mc_ = ((ret(xor(id, mc)))) in
let caseval = ((declassify(DeclassifyingOp::MacVrfy(k, serialize_owlSpec_h1_t(mac_to_verify), mc_))) in
(ret(mac_vrfy(k, serialize_owlSpec_h1_t(mac_to_verify), mc_)))) in
(case (caseval) {
| None => {
(ret(No()))
},
| Some(m) => {
let _assert_79 = ((ret(ghost_unit()))) in
(parse (parse_owlSpec_secret_h1_t(m)) as (owlSpec_secret_h1_t{owlSpec_h1_c : c, owlSpec_h1_nr : nr, owlSpec_h1_nt : nT_}) in {
let declassified_buf51 = ((declassify(DeclassifyingOp::ControlFlow(c))) in
(ret((c)))) in
let declassified_buf54 = ((declassify(DeclassifyingOp::ControlFlow(nr))) in
(ret((nr)))) in
let nT_ = ((ret(nT_))) in
let nT__ = ((ret(nT_))) in
let declassified_buf59 = ((declassify(DeclassifyingOp::ControlFlow(nR))) in
(ret((nR)))) in
let msg_to_mac = ((ret(h1_t(oo(), declassified_buf59, nT_)))) in
let declassified_buf63 = ((declassify(DeclassifyingOp::ControlFlow(xor(id, serialize_owlSpec_h1_t(msg_to_mac))))) in
(ret((xor(id, serialize_owlSpec_h1_t(msg_to_mac)))))) in
(output (declassified_buf63) to (Some(Endpoint::Loc_T))) in
let res = ((ret(nT__))) in
let declassified_buf69 = ((declassify(DeclassifyingOp::ControlFlow(res))) in
(ret((res)))) in
(ret(Yes(declassified_buf69)))
} otherwise ((ret(No()))))
},
}
)
} )
},
}
)
} otherwise ((ret(No()))))
    )
}

#[verifier::opaque]
pub open spec fn lookupKeys_spec(cfg: cfg_R, mut_state: state_R, x: Seq<u8>) -> (res: ITree<
    (Option<owlSpec_pair>, state_R),
    Endpoint,
>) {
    owl_spec!(mut_state, state_R,
        (ret(lookupKeys_pure(x)))
    )
}

#[verifier(external_body)]
pub closed spec fn lookupKeys_pure(x: Seq<u8>) -> Option<owlSpec_pair> {
    unimplemented!()
}

#[verifier::opaque]
pub open spec fn T_main_spec(cfg: cfg_T, mut_state: state_T) -> (res: ITree<
    ((), state_T),
    Endpoint,
>) {
    owl_spec!(mut_state, state_T,
        let id_i = ((ret(cfg.owl_id.view()))) in
(input(inp,_78)) in
(if (length(inp) == NONCE_SIZE) then
(let inp = ((ret(inp))) in
let nT = ((ret(cfg.owl_NT.view()))) in
let msg_to_mac = ((ret(h1_t(zz(), inp, nT)))) in
let declassified_buf83 = ((declassify(DeclassifyingOp::ControlFlow(serialize_owlSpec_h1_t(msg_to_mac)))) in
(ret((serialize_owlSpec_h1_t(msg_to_mac))))) in
let m = ((ret(mac(cfg.owl_K.view(), declassified_buf83)))) in
let x = ((ret(xor(id_i, m)))) in
let declassified_buf88 = ((declassify(DeclassifyingOp::ControlFlow(nT))) in
(ret((nT)))) in
let declassified_buf91 = ((declassify(DeclassifyingOp::ControlFlow(x))) in
(ret((x)))) in
(output (serialize_owlSpec_m1_t(m1_t(declassified_buf88, declassified_buf91))) to (Some(Endpoint::Loc_R))))
else
((output (empty_seq_u8()) to (Some(Endpoint::Loc_R)))))
    )
}

#[verifier::opaque]
pub closed spec fn oo() -> (res: Seq<u8>) {
    seq![0x01u8]
}

#[verifier::opaque]
pub closed spec fn zz() -> (res: Seq<u8>) {
    seq![0x00u8]
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

pub struct owl_h1_t<'a> {
    pub owl_h1_c: OwlBuf<'a>,
    pub owl_h1_nr: OwlBuf<'a>,
    pub owl_h1_nt: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_h1_t<'a>(
    arg_owl_h1_c: OwlBuf<'a>,
    arg_owl_h1_nr: OwlBuf<'a>,
    arg_owl_h1_nt: SecretBuf<'a>,
) -> (res: owl_h1_t<'a>)
    ensures
        res.owl_h1_c.view() == arg_owl_h1_c.view(),
        res.owl_h1_nr.view() == arg_owl_h1_nr.view(),
        res.owl_h1_nt.view() == arg_owl_h1_nt.view(),
{
    owl_h1_t { owl_h1_c: arg_owl_h1_c, owl_h1_nr: arg_owl_h1_nr, owl_h1_nt: arg_owl_h1_nt }
}

impl<'a> owl_h1_t<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_h1_t<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_h1_t {
            owl_h1_c: OwlBuf::another_ref(&self.owl_h1_c),
            owl_h1_nr: OwlBuf::another_ref(&self.owl_h1_nr),
            owl_h1_nt: SecretBuf::another_ref(&self.owl_h1_nt),
        }
    }
}

impl View for owl_h1_t<'_> {
    type V = owlSpec_h1_t;

    open spec fn view(&self) -> owlSpec_h1_t {
        owlSpec_h1_t {
            owlSpec_h1_c: self.owl_h1_c.view(),
            owlSpec_h1_nr: self.owl_h1_nr.view(),
            owlSpec_h1_nt: self.owl_h1_nt.view(),
        }
    }
}

pub exec fn parse_owl_h1_t<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_h1_t<'a>>)
    ensures
        res is Some ==> parse_owlSpec_h1_t(arg.view()) is Some,
        res is None ==> parse_owlSpec_h1_t(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_h1_t(arg.view())->Some_0,
{
    reveal(parse_owlSpec_h1_t);
    let exec_comb = exec_combinator_owl_h1_t();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl_h1_c, owl_h1_nr), owl_h1_nt) = parsed;
        Some(
            owl_h1_t {
                owl_h1_c: OwlBuf::another_ref(&owl_h1_c),
                owl_h1_nr: OwlBuf::another_ref(&owl_h1_nr),
                owl_h1_nt: SecretBuf::from_buf(owl_h1_nt.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_h1_t_inner<'a>(arg: &owl_h1_t<'a>) -> (res: Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_h1_t_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_h1_t_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_h1_t_inner);
    if no_usize_overflows![ arg.owl_h1_c.len(), arg.owl_h1_nr.len(), arg.owl_h1_nt.len(), 0 ] {
        let exec_comb = exec_combinator_owl_h1_t();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl_h1_c.len() + arg.owl_h1_nr.len() + arg.owl_h1_nt.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    SecretBuf::from_buf(arg.owl_h1_c.another_ref()),
                    SecretBuf::from_buf(arg.owl_h1_nr.another_ref()),
                ),
                SecretBuf::another_ref(&arg.owl_h1_nt),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_h1_t_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_h1_t<'a>(arg: &owl_h1_t<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_h1_t(arg.view()),
{
    reveal(serialize_owlSpec_h1_t);
    let res = serialize_owl_h1_t_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_h1_t<'a> {
    pub owl_h1_c: SecretBuf<'a>,
    pub owl_h1_nr: SecretBuf<'a>,
    pub owl_h1_nt: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_h1_t<'a>(
    arg_owl_h1_c: SecretBuf<'a>,
    arg_owl_h1_nr: SecretBuf<'a>,
    arg_owl_h1_nt: SecretBuf<'a>,
) -> (res: owl_secret_h1_t<'a>)
    ensures
        res.owl_h1_c.view() == arg_owl_h1_c.view(),
        res.owl_h1_nr.view() == arg_owl_h1_nr.view(),
        res.owl_h1_nt.view() == arg_owl_h1_nt.view(),
{
    owl_secret_h1_t { owl_h1_c: arg_owl_h1_c, owl_h1_nr: arg_owl_h1_nr, owl_h1_nt: arg_owl_h1_nt }
}

impl<'a> owl_secret_h1_t<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_h1_t<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_h1_t {
            owl_h1_c: SecretBuf::another_ref(&self.owl_h1_c),
            owl_h1_nr: SecretBuf::another_ref(&self.owl_h1_nr),
            owl_h1_nt: SecretBuf::another_ref(&self.owl_h1_nt),
        }
    }
}

impl View for owl_secret_h1_t<'_> {
    type V = owlSpec_secret_h1_t;

    open spec fn view(&self) -> owlSpec_secret_h1_t {
        owlSpec_secret_h1_t {
            owlSpec_h1_c: self.owl_h1_c.view(),
            owlSpec_h1_nr: self.owl_h1_nr.view(),
            owlSpec_h1_nt: self.owl_h1_nt.view(),
        }
    }
}

pub exec fn parse_owl_secret_h1_t<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_secret_h1_t<'a>>)
    ensures
        res is Some ==> parse_owlSpec_secret_h1_t(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_h1_t(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_h1_t(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_h1_t);
    let exec_comb = exec_combinator_owl_secret_h1_t();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl_h1_c, owl_h1_nr), owl_h1_nt) = parsed;
        Some(
            owl_secret_h1_t {
                owl_h1_c: SecretBuf::from_buf(owl_h1_c.another_ref()),
                owl_h1_nr: SecretBuf::from_buf(owl_h1_nr.another_ref()),
                owl_h1_nt: SecretBuf::from_buf(owl_h1_nt.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_h1_t<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_h1_t<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_h1_t(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_h1_t(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_h1_t(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_h1_t);
    let exec_comb = exec_combinator_owl_secret_h1_t();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let ((owl_h1_c, owl_h1_nr), owl_h1_nt) = parsed;
        Some(
            owl_secret_h1_t {
                owl_h1_c: SecretBuf::another_ref(&owl_h1_c),
                owl_h1_nr: SecretBuf::another_ref(&owl_h1_nr),
                owl_h1_nt: SecretBuf::another_ref(&owl_h1_nt),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_h1_t_inner<'a>(arg: &owl_secret_h1_t<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_secret_h1_t_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_h1_t_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_secret_h1_t_inner);
    if no_usize_overflows![ arg.owl_h1_c.len(), arg.owl_h1_nr.len(), arg.owl_h1_nt.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_h1_t();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl_h1_c.len() + arg.owl_h1_nr.len() + arg.owl_h1_nt.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (SecretBuf::another_ref(&arg.owl_h1_c), SecretBuf::another_ref(&arg.owl_h1_nr)),
                SecretBuf::another_ref(&arg.owl_h1_nt),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_h1_t_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_h1_t<'a>(arg: &owl_secret_h1_t<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_h1_t(arg.view()),
{
    reveal(serialize_owlSpec_secret_h1_t);
    let res = serialize_owl_secret_h1_t_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_m1_t<'a> {
    pub owl_m1_nt: OwlBuf<'a>,
    pub owl_m1_xormac: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_m1_t<'a>(arg_owl_m1_nt: OwlBuf<'a>, arg_owl_m1_xormac: OwlBuf<'a>) -> (res: owl_m1_t<'a>)
    ensures
        res.owl_m1_nt.view() == arg_owl_m1_nt.view(),
        res.owl_m1_xormac.view() == arg_owl_m1_xormac.view(),
{
    owl_m1_t { owl_m1_nt: arg_owl_m1_nt, owl_m1_xormac: arg_owl_m1_xormac }
}

impl<'a> owl_m1_t<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_m1_t<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_m1_t {
            owl_m1_nt: OwlBuf::another_ref(&self.owl_m1_nt),
            owl_m1_xormac: OwlBuf::another_ref(&self.owl_m1_xormac),
        }
    }
}

impl View for owl_m1_t<'_> {
    type V = owlSpec_m1_t;

    open spec fn view(&self) -> owlSpec_m1_t {
        owlSpec_m1_t {
            owlSpec_m1_nt: self.owl_m1_nt.view(),
            owlSpec_m1_xormac: self.owl_m1_xormac.view(),
        }
    }
}

pub exec fn parse_owl_m1_t<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_m1_t<'a>>)
    ensures
        res is Some ==> parse_owlSpec_m1_t(arg.view()) is Some,
        res is None ==> parse_owlSpec_m1_t(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_m1_t(arg.view())->Some_0,
{
    reveal(parse_owlSpec_m1_t);
    let exec_comb = exec_combinator_owl_m1_t();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl_m1_nt, owl_m1_xormac) = parsed;
        Some(
            owl_m1_t {
                owl_m1_nt: OwlBuf::another_ref(&owl_m1_nt),
                owl_m1_xormac: OwlBuf::another_ref(&owl_m1_xormac),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_m1_t_inner<'a>(arg: &owl_m1_t<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_m1_t_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_m1_t_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_m1_t_inner);
    if no_usize_overflows![ arg.owl_m1_nt.len(), arg.owl_m1_xormac.len(), 0 ] {
        let exec_comb = exec_combinator_owl_m1_t();
        let mut obuf = vec_u8_of_len(arg.owl_m1_nt.len() + arg.owl_m1_xormac.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl_m1_nt), OwlBuf::another_ref(&arg.owl_m1_xormac)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_m1_t_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_m1_t<'a>(arg: &owl_m1_t<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_m1_t(arg.view()),
{
    reveal(serialize_owlSpec_m1_t);
    let res = serialize_owl_m1_t_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_pair<'a> {
    pub owl__id: OwlBuf<'a>,
    pub owl__k: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_pair<'a>(arg_owl__id: OwlBuf<'a>, arg_owl__k: SecretBuf<'a>) -> (res: owl_pair<'a>)
    ensures
        res.owl__id.view() == arg_owl__id.view(),
        res.owl__k.view() == arg_owl__k.view(),
{
    owl_pair { owl__id: arg_owl__id, owl__k: arg_owl__k }
}

impl<'a> owl_pair<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_pair<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_pair {
            owl__id: OwlBuf::another_ref(&self.owl__id),
            owl__k: SecretBuf::another_ref(&self.owl__k),
        }
    }
}

impl View for owl_pair<'_> {
    type V = owlSpec_pair;

    open spec fn view(&self) -> owlSpec_pair {
        owlSpec_pair { owlSpec__id: self.owl__id.view(), owlSpec__k: self.owl__k.view() }
    }
}

pub exec fn parse_owl_pair<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_pair<'a>>)
    ensures
        res is Some ==> parse_owlSpec_pair(arg.view()) is Some,
        res is None ==> parse_owlSpec_pair(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_pair(arg.view())->Some_0,
{
    reveal(parse_owlSpec_pair);
    let exec_comb = exec_combinator_owl_pair();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__id, owl__k) = parsed;
        Some(
            owl_pair {
                owl__id: OwlBuf::another_ref(&owl__id),
                owl__k: SecretBuf::from_buf(owl__k.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_pair_inner<'a>(arg: &owl_pair<'a>) -> (res: Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_pair_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_pair_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_pair_inner);
    if no_usize_overflows![ arg.owl__id.len(), arg.owl__k.len(), 0 ] {
        let exec_comb = exec_combinator_owl_pair();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__id.len() + arg.owl__k.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::from_buf(arg.owl__id.another_ref()), SecretBuf::another_ref(&arg.owl__k)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_pair_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_pair<'a>(arg: &owl_pair<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_pair(arg.view()),
{
    reveal(serialize_owlSpec_pair);
    let res = serialize_owl_pair_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_pair<'a> {
    pub owl__id: SecretBuf<'a>,
    pub owl__k: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_pair<'a>(arg_owl__id: SecretBuf<'a>, arg_owl__k: SecretBuf<'a>) -> (res:
    owl_secret_pair<'a>)
    ensures
        res.owl__id.view() == arg_owl__id.view(),
        res.owl__k.view() == arg_owl__k.view(),
{
    owl_secret_pair { owl__id: arg_owl__id, owl__k: arg_owl__k }
}

impl<'a> owl_secret_pair<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_pair<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_pair {
            owl__id: SecretBuf::another_ref(&self.owl__id),
            owl__k: SecretBuf::another_ref(&self.owl__k),
        }
    }
}

impl View for owl_secret_pair<'_> {
    type V = owlSpec_secret_pair;

    open spec fn view(&self) -> owlSpec_secret_pair {
        owlSpec_secret_pair { owlSpec__id: self.owl__id.view(), owlSpec__k: self.owl__k.view() }
    }
}

pub exec fn parse_owl_secret_pair<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_secret_pair<'a>>)
    ensures
        res is Some ==> parse_owlSpec_secret_pair(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_pair(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_pair(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_pair);
    let exec_comb = exec_combinator_owl_secret_pair();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__id, owl__k) = parsed;
        Some(
            owl_secret_pair {
                owl__id: SecretBuf::from_buf(owl__id.another_ref()),
                owl__k: SecretBuf::from_buf(owl__k.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_pair<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_pair<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_pair(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_pair(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_pair(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_pair);
    let exec_comb = exec_combinator_owl_secret_pair();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (owl__id, owl__k) = parsed;
        Some(
            owl_secret_pair {
                owl__id: SecretBuf::another_ref(&owl__id),
                owl__k: SecretBuf::another_ref(&owl__k),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_pair_inner<'a>(arg: &owl_secret_pair<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_secret_pair_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_pair_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_secret_pair_inner);
    if no_usize_overflows![ arg.owl__id.len(), arg.owl__k.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_pair();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__id.len() + arg.owl__k.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__id), SecretBuf::another_ref(&arg.owl__k)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_pair_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_pair<'a>(arg: &owl_secret_pair<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_pair(arg.view()),
{
    reveal(serialize_owlSpec_secret_pair);
    let res = serialize_owl_secret_pair_inner(arg);
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
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(0)), (Tag::new(U8, 2), Tail));
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
            let tmp_owl_nR105 = { SecretBuf::another_ref(&self.owl_NR) };
            let owl_nR105 = SecretBuf::another_ref(&tmp_owl_nR105);
            let tmp_owl_declassified_buf11106 = {
                let tracked owl_declassify_tok107 = consume_itree_declassify::<
                    (owlSpec_reader_response, state_R),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_nR105).declassify(Tracked(owl_declassify_tok107)) }
            };
            let owl_declassified_buf11106 = OwlBuf::another_ref(&tmp_owl_declassified_buf11106);
            let owl__108 = {
                effects.owl_output::<(owlSpec_reader_response, state_R)>(
                    Tracked(&mut itree),
                    owl_declassified_buf11106.as_slice(),
                    Some(&T_addr()),
                    &R_addr(),
                );
            };
            let (tmp_owl_inp110, owl__109) = {
                effects.owl_input::<(owlSpec_reader_response, state_R)>(Tracked(&mut itree))
            };
            let owl_inp110 = OwlBuf::from_vec(tmp_owl_inp110);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp110);
            if let Some(parseval) = parse_owl_m1_t(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_nT112 = OwlBuf::another_ref(&parseval.owl_m1_nt);
                let owl_mc111 = OwlBuf::another_ref(&parseval.owl_m1_xormac);
                let (owl_x113, Tracked(itree)) = {
                    let tmp_arg1159 = OwlBuf::another_ref(&owl_nT112);
                    owl_call_ret_option!(effects, itree, *mut_state, lookupKeys_spec(*self, *mut_state, tmp_arg1159.view()), self.owl_lookupKeys(mut_state, tmp_arg1159))
                };
                match owl_x113 {
                    Option::None => { (owl_reader_response::another_ref(&owl_No()), Tracked(itree))
                    },
                    Option::Some(tmp_owl_p_packed114) => {
                        let owl_p_packed114 = owl_pair::another_ref(&tmp_owl_p_packed114);
                        let tmp_owl_p115 = { owl_pair::another_ref(&owl_p_packed114) };
                        let owl_p115 = owl_pair::another_ref(&tmp_owl_p115);
                        let parseval = owl_pair::another_ref(&owl_p115);
                        let owl_id117 = OwlBuf::another_ref(&parseval.owl__id);
                        let owl_k116 = SecretBuf::another_ref(&parseval.owl__k);
                        let tmp_owl_declassified_buf35118 = {
                            let tracked owl_declassify_tok119 = consume_itree_declassify::<
                                (owlSpec_reader_response, state_R),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_nR105).declassify(
                                    Tracked(owl_declassify_tok119),
                                )
                            }
                        };
                        let owl_declassified_buf35118 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf35118,
                        );
                        let tmp_owl_mac_to_verify120 = {
                            owl_h1_t(
                                OwlBuf::another_ref(&owl_public_zz()),
                                OwlBuf::another_ref(&owl_declassified_buf35118),
                                SecretBuf::another_ref(
                                    &SecretBuf::from_buf(owl_nT112.another_ref()),
                                ),
                            )
                        };
                        let owl_mac_to_verify120 = owl_h1_t::another_ref(&tmp_owl_mac_to_verify120);
                        let tmp_owl_mc_121 = { owl_xor(owl_id117.as_slice(), owl_mc111.as_slice())
                        };
                        let owl_mc_121 = OwlBuf::from_vec(tmp_owl_mc_121);
                        let tmp_owl_caseval122 = {
                            let tracked owl_declassify_tok123 = consume_itree_declassify::<
                                (owlSpec_reader_response, state_R),
                                Endpoint,
                            >(&mut itree);
                            owl_mac_vrfy(
                                SecretBuf::another_ref(&owl_k116),
                                SecretBuf::another_ref(&serialize_owl_h1_t(&owl_mac_to_verify120)),
                                OwlBuf::another_ref(&owl_mc_121),
                                Tracked(owl_declassify_tok123),
                            )
                        };
                        let owl_caseval122 = SecretBuf::another_ref_option(&tmp_owl_caseval122);
                        match SecretBuf::another_ref_option(&owl_caseval122) {
                            Option::None => {
                                (owl_reader_response::another_ref(&owl_No()), Tracked(itree))
                            },
                            Option::Some(tmp_owl_m124) => {
                                let owl_m124 = SecretBuf::another_ref(&tmp_owl_m124);
                                let owl__assert_79125 = { owl_ghost_unit() };
                                let parseval_tmp = SecretBuf::another_ref(&owl_m124);
                                if let Some(parseval) = secret_parse_owl_secret_h1_t(
                                    SecretBuf::another_ref(&parseval_tmp),
                                ) {
                                    let owl_c128 = SecretBuf::another_ref(&parseval.owl_h1_c);
                                    let owl_nr127 = SecretBuf::another_ref(&parseval.owl_h1_nr);
                                    let owl_nT_126 = SecretBuf::another_ref(&parseval.owl_h1_nt);
                                    let tmp_owl_declassified_buf51129 = {
                                        let tracked owl_declassify_tok130 =
                                            consume_itree_declassify::<
                                            (owlSpec_reader_response, state_R),
                                            Endpoint,
                                        >(&mut itree);
                                        {
                                            SecretBuf::another_ref(&owl_c128).declassify(
                                                Tracked(owl_declassify_tok130),
                                            )
                                        }
                                    };
                                    let owl_declassified_buf51129 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf51129,
                                    );
                                    let tmp_owl_declassified_buf54131 = {
                                        let tracked owl_declassify_tok132 =
                                            consume_itree_declassify::<
                                            (owlSpec_reader_response, state_R),
                                            Endpoint,
                                        >(&mut itree);
                                        {
                                            SecretBuf::another_ref(&owl_nr127).declassify(
                                                Tracked(owl_declassify_tok132),
                                            )
                                        }
                                    };
                                    let owl_declassified_buf54131 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf54131,
                                    );
                                    let tmp_owl_nT_133 = { SecretBuf::another_ref(&owl_nT_126) };
                                    let owl_nT_133 = SecretBuf::another_ref(&tmp_owl_nT_133);
                                    let tmp_owl_nT__134 = { SecretBuf::another_ref(&owl_nT_133) };
                                    let owl_nT__134 = SecretBuf::another_ref(&tmp_owl_nT__134);
                                    let tmp_owl_declassified_buf59135 = {
                                        let tracked owl_declassify_tok136 =
                                            consume_itree_declassify::<
                                            (owlSpec_reader_response, state_R),
                                            Endpoint,
                                        >(&mut itree);
                                        {
                                            SecretBuf::another_ref(&owl_nR105).declassify(
                                                Tracked(owl_declassify_tok136),
                                            )
                                        }
                                    };
                                    let owl_declassified_buf59135 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf59135,
                                    );
                                    let tmp_owl_msg_to_mac137 = {
                                        owl_h1_t(
                                            OwlBuf::another_ref(&owl_public_oo()),
                                            OwlBuf::another_ref(&owl_declassified_buf59135),
                                            SecretBuf::another_ref(&owl_nT_133),
                                        )
                                    };
                                    let owl_msg_to_mac137 = owl_h1_t::another_ref(
                                        &tmp_owl_msg_to_mac137,
                                    );
                                    let tmp_owl_declassified_buf63138 = {
                                        let tracked owl_declassify_tok139 =
                                            consume_itree_declassify::<
                                            (owlSpec_reader_response, state_R),
                                            Endpoint,
                                        >(&mut itree);
                                        {
                                            SecretBuf::another_ref(
                                                &owl_secret_xor(
                                                    SecretBuf::from_buf(owl_id117.another_ref()),
                                                    serialize_owl_h1_t(&owl_msg_to_mac137),
                                                ),
                                            ).declassify(Tracked(owl_declassify_tok139))
                                        }
                                    };
                                    let owl_declassified_buf63138 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf63138,
                                    );
                                    let owl__140 = {
                                        effects.owl_output::<(owlSpec_reader_response, state_R)>(
                                            Tracked(&mut itree),
                                            owl_declassified_buf63138.as_slice(),
                                            Some(&T_addr()),
                                            &R_addr(),
                                        );
                                    };
                                    let tmp_owl_res141 = { SecretBuf::another_ref(&owl_nT__134) };
                                    let owl_res141 = SecretBuf::another_ref(&tmp_owl_res141);
                                    let tmp_owl_declassified_buf69142 = {
                                        let tracked owl_declassify_tok143 =
                                            consume_itree_declassify::<
                                            (owlSpec_reader_response, state_R),
                                            Endpoint,
                                        >(&mut itree);
                                        {
                                            SecretBuf::another_ref(&owl_res141).declassify(
                                                Tracked(owl_declassify_tok143),
                                            )
                                        }
                                    };
                                    let owl_declassified_buf69142 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf69142,
                                    );
                                    (
                                        owl_reader_response::another_ref(
                                            &owl_Yes(
                                                OwlBuf::another_ref(&owl_declassified_buf69142),
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
        Tracked(itree): Tracked<ITreeToken<(Option<owlSpec_pair>, state_R), Endpoint>>,
        mut_state: &mut state_R,
        owl_x160: OwlBuf<'a>,
    ) -> (res: Result<
        (Option<owl_pair<'a>>, Tracked<ITreeToken<(Option<owlSpec_pair>, state_R), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == lookupKeys_spec(*self, *old(mut_state), owl_x160.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_pair<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_pair>, state_R), Endpoint>>,
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
    pub owl_id: SecretBuf<'T>,
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
            let tmp_owl_id_i145 = { SecretBuf::another_ref(&self.owl_id) };
            let owl_id_i145 = SecretBuf::another_ref(&tmp_owl_id_i145);
            let (tmp_owl_inp147, owl__146) = {
                effects.owl_input::<((), state_T)>(Tracked(&mut itree))
            };
            let owl_inp147 = OwlBuf::from_vec(tmp_owl_inp147);

            if owl_inp147.len() == NONCE_SIZE {
                let tmp_owl_inp148 = { OwlBuf::another_ref(&owl_inp147) };
                let owl_inp148 = OwlBuf::another_ref(&tmp_owl_inp148);
                let tmp_owl_nT149 = { SecretBuf::another_ref(&self.owl_NT) };
                let owl_nT149 = SecretBuf::another_ref(&tmp_owl_nT149);
                let tmp_owl_msg_to_mac150 = {
                    owl_h1_t(
                        OwlBuf::another_ref(&owl_public_zz()),
                        OwlBuf::another_ref(&owl_inp148),
                        SecretBuf::another_ref(&owl_nT149),
                    )
                };
                let owl_msg_to_mac150 = owl_h1_t::another_ref(&tmp_owl_msg_to_mac150);
                let tmp_owl_declassified_buf83151 = {
                    let tracked owl_declassify_tok152 = consume_itree_declassify::<
                        ((), state_T),
                        Endpoint,
                    >(&mut itree);
                    {
                        SecretBuf::another_ref(&serialize_owl_h1_t(&owl_msg_to_mac150)).declassify(
                            Tracked(owl_declassify_tok152),
                        )
                    }
                };
                let owl_declassified_buf83151 = OwlBuf::another_ref(&tmp_owl_declassified_buf83151);
                let tmp_owl_m153 = {
                    owl_mac(
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_K)),
                        OwlBuf::another_ref(&owl_declassified_buf83151),
                    )
                };
                let owl_m153 = OwlBuf::from_vec(tmp_owl_m153);
                let tmp_owl_x154 = {
                    owl_secret_xor(
                        SecretBuf::another_ref(&owl_id_i145),
                        SecretBuf::from_buf(owl_m153.another_ref()),
                    )
                };
                let owl_x154 = SecretBuf::another_ref(&tmp_owl_x154);
                let tmp_owl_declassified_buf88155 = {
                    let tracked owl_declassify_tok156 = consume_itree_declassify::<
                        ((), state_T),
                        Endpoint,
                    >(&mut itree);
                    { SecretBuf::another_ref(&owl_nT149).declassify(Tracked(owl_declassify_tok156))
                    }
                };
                let owl_declassified_buf88155 = OwlBuf::another_ref(&tmp_owl_declassified_buf88155);
                let tmp_owl_declassified_buf91157 = {
                    let tracked owl_declassify_tok158 = consume_itree_declassify::<
                        ((), state_T),
                        Endpoint,
                    >(&mut itree);
                    { SecretBuf::another_ref(&owl_x154).declassify(Tracked(owl_declassify_tok158)) }
                };
                let owl_declassified_buf91157 = OwlBuf::another_ref(&tmp_owl_declassified_buf91157);
                effects.owl_output::<((), state_T)>(
                    Tracked(&mut itree),
                    serialize_owl_m1_t(
                        &owl_m1_t(
                            OwlBuf::another_ref(&owl_declassified_buf88155),
                            OwlBuf::another_ref(&owl_declassified_buf91157),
                        ),
                    ).as_slice(),
                    Some(&R_addr()),
                    &T_addr(),
                );
                ((), Tracked(itree))
            } else {
                effects.owl_output::<((), state_T)>(
                    Tracked(&mut itree),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                    Some(&R_addr()),
                    &T_addr(),
                );
                ((), Tracked(itree))
            }

        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub fn owl_secret_oo<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == oo(),
{
    reveal(oo);
    let res = {
        OwlBuf::another_ref(
            &{
                let x = mk_vec_u8![0x01u8 ];
                OwlBuf::from_vec(x)
            },
        )
    };
    assert(res.view() == oo());
    res
}

pub fn owl_public_oo<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == oo(),
{
    reveal(oo);
    let res = {
        OwlBuf::another_ref(
            &{
                let x = mk_vec_u8![0x01u8 ];
                OwlBuf::from_vec(x)
            },
        )
    };
    assert(res.view() == oo());
    res
}

pub fn owl_secret_zz<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == zz(),
{
    reveal(zz);
    let res = {
        OwlBuf::another_ref(
            &{
                let x = mk_vec_u8![0x00u8 ];
                OwlBuf::from_vec(x)
            },
        )
    };
    assert(res.view() == zz());
    res
}

pub fn owl_public_zz<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == zz(),
{
    reveal(zz);
    let res = {
        OwlBuf::another_ref(
            &{
                let x = mk_vec_u8![0x00u8 ];
                OwlBuf::from_vec(x)
            },
        )
    };
    assert(res.view() == zz());
    res
}

} // verus!
