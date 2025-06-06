// Extracted verus code from file owl_toy_protocols/ssh.owl:
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
pub enum owlSpec_sign_request_response {
    owlSpec__req(Seq<u8>),
    owlSpec__res(Seq<u8>),
}

use owlSpec_sign_request_response::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_sign_request_response(x: Seq<u8>) -> Option<
    owlSpec_sign_request_response,
> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Tail), (Tag::spec_new(U8, 2), Tail));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owlSpec_sign_request_response::owlSpec__req(x),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_sign_request_response::owlSpec__res(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_sign_request_response_inner(
    x: owlSpec_sign_request_response,
) -> Option<Seq<u8>> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Tail), (Tag::spec_new(U8, 2), Tail));
    match x {
        owlSpec_sign_request_response::owlSpec__req(x) => {
            if no_usize_overflows_spec![ 1, x.len() ] {
                if let Ok(serialized) = spec_comb.spec_serialize(
                    inj_ord_choice_result!(((), x), *),
                ) {
                    Some(serialized)
                } else {
                    None
                }
            } else {
                None
            }
        },
        owlSpec_sign_request_response::owlSpec__res(x) => {
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
pub closed spec fn serialize_owlSpec_sign_request_response(x: owlSpec_sign_request_response) -> Seq<
    u8,
> {
    if let Some(val) = serialize_owlSpec_sign_request_response_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_sign_request_response {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_sign_request_response(self)
    }
}

pub open spec fn _req(x: Seq<u8>) -> owlSpec_sign_request_response {
    crate::owlSpec_sign_request_response::owlSpec__req(x)
}

pub open spec fn _res(x: Seq<u8>) -> owlSpec_sign_request_response {
    crate::owlSpec_sign_request_response::owlSpec__res(x)
}

pub open spec fn _req_enumtest(x: owlSpec_sign_request_response) -> bool {
    match x {
        owlSpec_sign_request_response::owlSpec__req(_) => true,
        _ => false,
    }
}

pub open spec fn _res_enumtest(x: owlSpec_sign_request_response) -> bool {
    match x {
        owlSpec_sign_request_response::owlSpec__res(_) => true,
        _ => false,
    }
}

pub enum owlSpec_dhpk_b {
    owlSpec__comm_with_pfa(Seq<u8>),
    owlSpec__comm_with_sdis(Seq<u8>),
}

use owlSpec_dhpk_b::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_dhpk_b(x: Seq<u8>) -> Option<owlSpec_dhpk_b> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(32)), (Tag::spec_new(U8, 2), Variable(32)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owlSpec_dhpk_b::owlSpec__comm_with_pfa(x),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_dhpk_b::owlSpec__comm_with_sdis(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_dhpk_b_inner(x: owlSpec_dhpk_b) -> Option<Seq<u8>> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(32)), (Tag::spec_new(U8, 2), Variable(32)));
    match x {
        owlSpec_dhpk_b::owlSpec__comm_with_pfa(x) => {
            if no_usize_overflows_spec![ 1, x.len() ] {
                if let Ok(serialized) = spec_comb.spec_serialize(
                    inj_ord_choice_result!(((), x), *),
                ) {
                    Some(serialized)
                } else {
                    None
                }
            } else {
                None
            }
        },
        owlSpec_dhpk_b::owlSpec__comm_with_sdis(x) => {
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
pub closed spec fn serialize_owlSpec_dhpk_b(x: owlSpec_dhpk_b) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_dhpk_b_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_dhpk_b {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_dhpk_b(self)
    }
}

pub open spec fn _comm_with_pfa(x: Seq<u8>) -> owlSpec_dhpk_b {
    crate::owlSpec_dhpk_b::owlSpec__comm_with_pfa(x)
}

pub open spec fn _comm_with_sdis(x: Seq<u8>) -> owlSpec_dhpk_b {
    crate::owlSpec_dhpk_b::owlSpec__comm_with_sdis(x)
}

pub open spec fn _comm_with_pfa_enumtest(x: owlSpec_dhpk_b) -> bool {
    match x {
        owlSpec_dhpk_b::owlSpec__comm_with_pfa(_) => true,
        _ => false,
    }
}

pub open spec fn _comm_with_sdis_enumtest(x: owlSpec_dhpk_b) -> bool {
    match x {
        owlSpec_dhpk_b::owlSpec__comm_with_sdis(_) => true,
        _ => false,
    }
}

pub enum owlSpec_signed_by_PFA {
    owlSpec__signed_by_PFA_g_pow_a(Seq<u8>),
    owlSpec__signed_by_PFA_hash(Seq<u8>),
}

use owlSpec_signed_by_PFA::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_signed_by_PFA(x: Seq<u8>) -> Option<owlSpec_signed_by_PFA> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Variable(32)), (Tag::spec_new(U8, 2), Tail));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owlSpec_signed_by_PFA::owlSpec__signed_by_PFA_g_pow_a(
                x,
            ),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_signed_by_PFA::owlSpec__signed_by_PFA_hash(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_signed_by_PFA_inner(x: owlSpec_signed_by_PFA) -> Option<
    Seq<u8>,
> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Variable(32)), (Tag::spec_new(U8, 2), Tail));
    match x {
        owlSpec_signed_by_PFA::owlSpec__signed_by_PFA_g_pow_a(x) => {
            if no_usize_overflows_spec![ 1, x.len() ] {
                if let Ok(serialized) = spec_comb.spec_serialize(
                    inj_ord_choice_result!(((), x), *),
                ) {
                    Some(serialized)
                } else {
                    None
                }
            } else {
                None
            }
        },
        owlSpec_signed_by_PFA::owlSpec__signed_by_PFA_hash(x) => {
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
pub closed spec fn serialize_owlSpec_signed_by_PFA(x: owlSpec_signed_by_PFA) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_signed_by_PFA_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_signed_by_PFA {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_signed_by_PFA(self)
    }
}

pub open spec fn _signed_by_PFA_g_pow_a(x: Seq<u8>) -> owlSpec_signed_by_PFA {
    crate::owlSpec_signed_by_PFA::owlSpec__signed_by_PFA_g_pow_a(x)
}

pub open spec fn _signed_by_PFA_hash(x: Seq<u8>) -> owlSpec_signed_by_PFA {
    crate::owlSpec_signed_by_PFA::owlSpec__signed_by_PFA_hash(x)
}

pub open spec fn _signed_by_PFA_g_pow_a_enumtest(x: owlSpec_signed_by_PFA) -> bool {
    match x {
        owlSpec_signed_by_PFA::owlSpec__signed_by_PFA_g_pow_a(_) => true,
        _ => false,
    }
}

pub open spec fn _signed_by_PFA_hash_enumtest(x: owlSpec_signed_by_PFA) -> bool {
    match x {
        owlSpec_signed_by_PFA::owlSpec__signed_by_PFA_hash(_) => true,
        _ => false,
    }
}

spec fn spec_combinator_owlSpec_pfa_msg() -> (Variable, Variable) {
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

exec fn exec_combinator_owl_pfa_msg() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_pfa_msg(),
{
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

pub struct owlSpec_pfa_msg {
    pub owlSpec__pfa1: Seq<u8>,
    pub owlSpec__pfa2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_pfa_msg(x: Seq<u8>) -> Option<owlSpec_pfa_msg> {
    let spec_comb = spec_combinator_owlSpec_pfa_msg();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__pfa1, owlSpec__pfa2)) = parsed;
        Some(owlSpec_pfa_msg { owlSpec__pfa1, owlSpec__pfa2 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_pfa_msg_inner(x: owlSpec_pfa_msg) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__pfa1.len(), x.owlSpec__pfa2.len() ] {
        let spec_comb = spec_combinator_owlSpec_pfa_msg();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__pfa1, x.owlSpec__pfa2))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_pfa_msg(x: owlSpec_pfa_msg) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_pfa_msg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_pfa_msg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_pfa_msg(self)
    }
}

pub open spec fn pfa_msg(
    arg_owlSpec__pfa1: Seq<u8>,
    arg_owlSpec__pfa2: Seq<u8>,
) -> owlSpec_pfa_msg {
    owlSpec_pfa_msg { owlSpec__pfa1: arg_owlSpec__pfa1, owlSpec__pfa2: arg_owlSpec__pfa2 }
}

spec fn spec_combinator_owlSpec_pdis_msg1() -> (Variable, Variable) {
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

exec fn exec_combinator_owl_pdis_msg1() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_pdis_msg1(),
{
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

pub struct owlSpec_pdis_msg1 {
    pub owlSpec__pdis1_1: Seq<u8>,
    pub owlSpec__pdis2_1: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_pdis_msg1(x: Seq<u8>) -> Option<owlSpec_pdis_msg1> {
    let spec_comb = spec_combinator_owlSpec_pdis_msg1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__pdis1_1, owlSpec__pdis2_1)) = parsed;
        Some(owlSpec_pdis_msg1 { owlSpec__pdis1_1, owlSpec__pdis2_1 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_pdis_msg1_inner(x: owlSpec_pdis_msg1) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__pdis1_1.len(), x.owlSpec__pdis2_1.len() ] {
        let spec_comb = spec_combinator_owlSpec_pdis_msg1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((x.owlSpec__pdis1_1, x.owlSpec__pdis2_1)),
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
pub closed spec fn serialize_owlSpec_pdis_msg1(x: owlSpec_pdis_msg1) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_pdis_msg1_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_pdis_msg1 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_pdis_msg1(self)
    }
}

pub open spec fn pdis_msg1(
    arg_owlSpec__pdis1_1: Seq<u8>,
    arg_owlSpec__pdis2_1: Seq<u8>,
) -> owlSpec_pdis_msg1 {
    owlSpec_pdis_msg1 {
        owlSpec__pdis1_1: arg_owlSpec__pdis1_1,
        owlSpec__pdis2_1: arg_owlSpec__pdis2_1,
    }
}

spec fn spec_combinator_owlSpec_pdis_msg2() -> (Variable, Variable) {
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

exec fn exec_combinator_owl_pdis_msg2() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_pdis_msg2(),
{
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

pub struct owlSpec_pdis_msg2 {
    pub owlSpec__pdis1_2: Seq<u8>,
    pub owlSpec__pdis2_2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_pdis_msg2(x: Seq<u8>) -> Option<owlSpec_pdis_msg2> {
    let spec_comb = spec_combinator_owlSpec_pdis_msg2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__pdis1_2, owlSpec__pdis2_2)) = parsed;
        Some(owlSpec_pdis_msg2 { owlSpec__pdis1_2, owlSpec__pdis2_2 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_pdis_msg2_inner(x: owlSpec_pdis_msg2) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__pdis1_2.len(), x.owlSpec__pdis2_2.len() ] {
        let spec_comb = spec_combinator_owlSpec_pdis_msg2();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((x.owlSpec__pdis1_2, x.owlSpec__pdis2_2)),
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
pub closed spec fn serialize_owlSpec_pdis_msg2(x: owlSpec_pdis_msg2) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_pdis_msg2_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_pdis_msg2 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_pdis_msg2(self)
    }
}

pub open spec fn pdis_msg2(
    arg_owlSpec__pdis1_2: Seq<u8>,
    arg_owlSpec__pdis2_2: Seq<u8>,
) -> owlSpec_pdis_msg2 {
    owlSpec_pdis_msg2 {
        owlSpec__pdis1_2: arg_owlSpec__pdis1_2,
        owlSpec__pdis2_2: arg_owlSpec__pdis2_2,
    }
}

spec fn spec_combinator_owlSpec_sdis_msg() -> (Variable, Variable) {
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

exec fn exec_combinator_owl_sdis_msg() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_sdis_msg(),
{
    let field_1 = Variable(32);
    let field_2 = Variable(64);
    (field_1, field_2)
}

pub struct owlSpec_sdis_msg {
    pub owlSpec__sdis1: Seq<u8>,
    pub owlSpec__sdis2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_sdis_msg(x: Seq<u8>) -> Option<owlSpec_sdis_msg> {
    let spec_comb = spec_combinator_owlSpec_sdis_msg();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__sdis1, owlSpec__sdis2)) = parsed;
        Some(owlSpec_sdis_msg { owlSpec__sdis1, owlSpec__sdis2 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_sdis_msg_inner(x: owlSpec_sdis_msg) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__sdis1.len(), x.owlSpec__sdis2.len() ] {
        let spec_comb = spec_combinator_owlSpec_sdis_msg();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__sdis1, x.owlSpec__sdis2))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_sdis_msg(x: owlSpec_sdis_msg) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_sdis_msg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_sdis_msg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_sdis_msg(self)
    }
}

pub open spec fn sdis_msg(
    arg_owlSpec__sdis1: Seq<u8>,
    arg_owlSpec__sdis2: Seq<u8>,
) -> owlSpec_sdis_msg {
    owlSpec_sdis_msg { owlSpec__sdis1: arg_owlSpec__sdis1, owlSpec__sdis2: arg_owlSpec__sdis2 }
}

#[verifier::opaque]
pub open spec fn PDIS_main_spec(cfg: cfg_PDIS, mut_state: state_PDIS) -> (res: ITree<
    ((), state_PDIS),
    Endpoint,
>) {
    owl_spec!(mut_state, state_PDIS,
        call(PDIS_KE_spec(cfg, mut_state))
    )
}

#[verifier::opaque]
pub open spec fn PDIS_KE_spec(cfg: cfg_PDIS, mut_state: state_PDIS) -> (res: ITree<
    ((), state_PDIS),
    Endpoint,
>) {
    owl_spec!(mut_state, state_PDIS,
        let g_pow_b = ((ret(dhpk(cfg.owl_b.view())))) in
let signed_g_pow_b = ((ret(sign(cfg.owl_skPDIS.view(), serialize_owlSpec_dhpk_b(_comm_with_pfa(g_pow_b)))))) in
(output (serialize_owlSpec_pdis_msg1(pdis_msg1(g_pow_b, signed_g_pow_b))) to (Some(Endpoint::Loc_PFA))) in
(input(inp,_11)) in
let vkPFA = ((ret(cfg.pk_owl_skPFA.view()))) in
(parse (parse_owlSpec_pfa_msg(inp)) as (owlSpec_pfa_msg{owlSpec__pfa1 : pfa1, owlSpec__pfa2 : pfa2}) in {
let caseval = ((declassify(DeclassifyingOp::SigVrfy(vkPFA, pfa1, pfa2))) in
(ret(vrfy(vkPFA, pfa1, pfa2)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(m) => {
let declassified_buf31 = ((declassify(DeclassifyingOp::ControlFlow(m))) in
(ret((m)))) in
(parse (parse_owlSpec_signed_by_PFA(declassified_buf31)) as (parsed_caseval : owlSpec_signed_by_PFA) in {
(case (parsed_caseval) {
| owlSpec__signed_by_PFA_hash(_unused151) => {
(ret(()))
},
| owlSpec__signed_by_PFA_g_pow_a(g_pow_a) => {
(if (notb(is_group_elem(g_pow_a))) then
((ret(())))
else
(let ss = ((ret(dh_combine(g_pow_a, cfg.owl_b.view())))) in
let kdfval24 = ((ret(kdf((0 + ENCKEY_SIZE) as usize, empty_seq_u8(), ss, seq![0x01u8 ])))) in
let k11 = ((ret(Seq::subrange(kdfval24, 0, 0 + ENCKEY_SIZE)))) in
(output (empty_seq_u8()) to (Some(Endpoint::Loc_SDIS))) in
call(PDIS_actual_spec(cfg, mut_state, ghost_unit(), k11))))
},
}
)
} otherwise (ret(())))
},
}
)
} otherwise ((ret(()))))
    )
}

#[verifier::opaque]
pub open spec fn PDIS_actual_spec(
    cfg: cfg_PDIS,
    mut_state: state_PDIS,
    gb: Ghost<()>,
    k11: Seq<u8>,
) -> (res: ITree<((), state_PDIS), Endpoint>) {
    owl_spec!(mut_state, state_PDIS,
        let g_pow_b1 = ((ret(dhpk(cfg.owl_b1.view())))) in
let signed_g_pow_b1 = ((ret(sign(cfg.owl_skPDIS.view(), serialize_owlSpec_dhpk_b(_comm_with_sdis(g_pow_b1)))))) in
(output (serialize_owlSpec_pdis_msg2(pdis_msg2(g_pow_b1, signed_g_pow_b1))) to (Some(Endpoint::Loc_SDIS))) in
(input(inp,_39)) in
let vkSDIS = ((ret(cfg.pk_owl_skSDIS.view()))) in
(parse (parse_owlSpec_sdis_msg(inp)) as (owlSpec_sdis_msg{owlSpec__sdis1 : sdis1, owlSpec__sdis2 : sdis2}) in {
let caseval = ((declassify(DeclassifyingOp::SigVrfy(vkSDIS, sdis1, sdis2))) in
(ret(vrfy(vkSDIS, sdis1, sdis2)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(g_pow_c) => {
(if (notb(is_group_elem(g_pow_c))) then
((ret(())))
else
(let ss = ((ret(dh_combine(g_pow_c, cfg.owl_b1.view())))) in
let kdfval50 = ((ret(kdf((0 + ENCKEY_SIZE) as usize, empty_seq_u8(), ss, seq![0x02u8 ])))) in
let k = ((ret(Seq::subrange(kdfval50, 0, 0 + ENCKEY_SIZE)))) in
let request = ((ret(_req(seq![0x01u8 ])))) in
let enc_request = ((sample(NONCE_SIZE, enc(k11, serialize_owlSpec_sign_request_response(request))))) in
(output (enc_request) to (Some(Endpoint::Loc_PFA))) in
(input(inp2,_57)) in
let caseval = ((declassify(DeclassifyingOp::ADec(k11, inp2))) in
(ret(dec(k11, inp2)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(m_) => {
(declassify(DeclassifyingOp::EnumParse(m_))) in
(parse (parse_owlSpec_sign_request_response(m_)) as (parsed_caseval : owlSpec_sign_request_response) in {
(case (parsed_caseval) {
| owlSpec__req(_unused154) => {
(ret(()))
},
| owlSpec__res(h2) => {
let msg_to_send_SDIS = ((sample(NONCE_SIZE, enc(k, h2)))) in
(output (msg_to_send_SDIS) to (Some(Endpoint::Loc_SDIS))) in
(ret(()))
},
}
)
} otherwise (ret(())))
},
}
)))
},
}
)
} otherwise ((ret(()))))
    )
}

#[verifier::opaque]
pub open spec fn PFA_main_spec(cfg: cfg_PFA, mut_state: state_PFA) -> (res: ITree<
    ((), state_PFA),
    Endpoint,
>) {
    owl_spec!(mut_state, state_PFA,
        call(PFA_KE_spec(cfg, mut_state))
    )
}

#[verifier::opaque]
pub open spec fn PFA_KE_spec(cfg: cfg_PFA, mut_state: state_PFA) -> (res: ITree<
    ((), state_PFA),
    Endpoint,
>) {
    owl_spec!(mut_state, state_PFA,
        let g_pow_a = ((ret(dhpk(cfg.owl_a.view())))) in
let signed_g_pow_a = ((ret(sign(cfg.owl_skPFA.view(), serialize_owlSpec_signed_by_PFA(_signed_by_PFA_g_pow_a(g_pow_a)))))) in
(output (serialize_owlSpec_pfa_msg(pfa_msg(g_pow_a, signed_g_pow_a))) to (Some(Endpoint::Loc_PDIS))) in
(input(inp,_72)) in
let vkPDIS = ((ret(cfg.pk_owl_skPDIS.view()))) in
(parse (parse_owlSpec_pdis_msg1(inp)) as (owlSpec_pdis_msg1{owlSpec__pdis1_1 : pdis1_1, owlSpec__pdis2_1 : pdis2_1}) in {
let caseval = ((declassify(DeclassifyingOp::SigVrfy(vkPDIS, pdis1_1, pdis2_1))) in
(ret(vrfy(vkPDIS, pdis1_1, pdis2_1)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(m) => {
let declassified_buf91 = ((declassify(DeclassifyingOp::ControlFlow(m))) in
(ret((m)))) in
(parse (parse_owlSpec_dhpk_b(declassified_buf91)) as (parsed_caseval : owlSpec_dhpk_b) in {
(case (parsed_caseval) {
| owlSpec__comm_with_sdis(_unused155) => {
(ret(()))
},
| owlSpec__comm_with_pfa(g_pow_b) => {
(if (notb(is_group_elem(g_pow_b))) then
((ret(())))
else
(let ss = ((ret(dh_combine(g_pow_b, cfg.owl_a.view())))) in
let kdfval85 = ((ret(kdf((0 + ENCKEY_SIZE) as usize, empty_seq_u8(), ss, seq![0x01u8 ])))) in
let k11 = ((ret(Seq::subrange(kdfval85, 0, 0 + ENCKEY_SIZE)))) in
call(PFA_FW_spec(cfg, mut_state, ghost_unit(), k11))))
},
}
)
} otherwise (ret(())))
},
}
)
} otherwise ((ret(()))))
    )
}

#[verifier::opaque]
pub open spec fn PFA_FW_spec(
    cfg: cfg_PFA,
    mut_state: state_PFA,
    gb: Ghost<()>,
    k11: Seq<u8>,
) -> (res: ITree<((), state_PFA), Endpoint>) {
    owl_spec!(mut_state, state_PFA,
        (input(inp,_96)) in
let caseval = ((declassify(DeclassifyingOp::ADec(k11, inp))) in
(ret(dec(k11, inp)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(m_) => {
(declassify(DeclassifyingOp::EnumParse(m_))) in
(parse (parse_owlSpec_sign_request_response(m_)) as (parsed_caseval : owlSpec_sign_request_response) in {
(case (parsed_caseval) {
| owlSpec__res(_unused158) => {
(ret(()))
},
| owlSpec__req(hh) => {
let declassified_buf103 = ((declassify(DeclassifyingOp::ControlFlow(hh))) in
(ret((hh)))) in
let signed = ((ret(sign(cfg.owl_skPFA.view(), serialize_owlSpec_signed_by_PFA(_signed_by_PFA_hash(declassified_buf103)))))) in
let declassified_buf107 = ((declassify(DeclassifyingOp::ControlFlow(serialize_owlSpec_sign_request_response(_res(signed))))) in
(ret((serialize_owlSpec_sign_request_response(_res(signed)))))) in
let msg_to_send_PDIS = ((sample(NONCE_SIZE, enc(k11, serialize_owlSpec_sign_request_response(_res(declassified_buf107)))))) in
(output (msg_to_send_PDIS) to (Some(Endpoint::Loc_PDIS))) in
(ret(()))
},
}
)
} otherwise (ret(())))
},
}
)
    )
}

#[verifier::opaque]
pub open spec fn SDIS_main_spec(cfg: cfg_SDIS, mut_state: state_SDIS) -> (res: ITree<
    ((), state_SDIS),
    Endpoint,
>) {
    owl_spec!(mut_state, state_SDIS,
        call(SDIS_actual_spec(cfg, mut_state))
    )
}

#[verifier::opaque]
pub open spec fn SDIS_actual_spec(cfg: cfg_SDIS, mut_state: state_SDIS) -> (res: ITree<
    ((), state_SDIS),
    Endpoint,
>) {
    owl_spec!(mut_state, state_SDIS,
        let g_pow_c = ((ret(dhpk(cfg.owl_c.view())))) in
let signed_g_pow_c = ((ret(sign(cfg.owl_skSDIS.view(), g_pow_c)))) in
(output (serialize_owlSpec_sdis_msg(sdis_msg(g_pow_c, signed_g_pow_c))) to (Some(Endpoint::Loc_PDIS))) in
(input(inp,_118)) in
let vkPDIS = ((ret(cfg.pk_owl_skPDIS.view()))) in
(parse (parse_owlSpec_pdis_msg2(inp)) as (owlSpec_pdis_msg2{owlSpec__pdis1_2 : pdis1_2, owlSpec__pdis2_2 : pdis2_2}) in {
let caseval = ((declassify(DeclassifyingOp::SigVrfy(vkPDIS, pdis1_2, pdis2_2))) in
(ret(vrfy(vkPDIS, pdis1_2, pdis2_2)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(m) => {
let declassified_buf140 = ((declassify(DeclassifyingOp::ControlFlow(m))) in
(ret((m)))) in
(parse (parse_owlSpec_dhpk_b(declassified_buf140)) as (parsed_caseval : owlSpec_dhpk_b) in {
(case (parsed_caseval) {
| owlSpec__comm_with_pfa(_unused159) => {
(ret(()))
},
| owlSpec__comm_with_sdis(g_pow_b1) => {
(if (notb(is_group_elem(g_pow_b1))) then
((ret(())))
else
(let ss = ((ret(dh_combine(g_pow_b1, cfg.owl_c.view())))) in
let kdfval131 = ((ret(kdf((0 + ENCKEY_SIZE) as usize, empty_seq_u8(), ss, seq![0x02u8 ])))) in
let k = ((ret(Seq::subrange(kdfval131, 0, 0 + ENCKEY_SIZE)))) in
(input(inp2,_134)) in
let caseval = ((declassify(DeclassifyingOp::ADec(k, inp2))) in
(ret(dec(k, inp2)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(m__) => {
(ret(()))
},
}
)))
},
}
)
} otherwise (ret(())))
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
    Loc_PDIS,
    Loc_PFA,
    Loc_SDIS,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier(external_body)]
pub const fn PDIS_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_PDIS,
{
    "127.0.0.1:9001"
}

#[verifier(external_body)]
pub const fn PFA_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_PFA,
{
    "127.0.0.1:9002"
}

#[verifier(external_body)]
pub const fn SDIS_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_SDIS,
{
    "127.0.0.1:9003"
}

pub enum owl_sign_request_response<'a> {
    owl__req(SecretBuf<'a>),
    owl__res(OwlBuf<'a>),
}

use owl_sign_request_response::*;

impl<'a> owl_sign_request_response<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_sign_request_response<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl__req(x) => owl__req(SecretBuf::another_ref(x)),
            owl__res(x) => owl__res(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_sign_request_response<'_> {
    type V = owlSpec_sign_request_response;

    open spec fn view(&self) -> owlSpec_sign_request_response {
        match self {
            owl__req(v) => owlSpec_sign_request_response::owlSpec__req(v.view()),
            owl__res(v) => owlSpec_sign_request_response::owlSpec__res(v.view()),
        }
    }
}

#[inline]
pub fn owl__req_enumtest(x: &owl_sign_request_response<'_>) -> (res: bool)
    ensures
        res == _req_enumtest(x.view()),
{
    match x {
        owl_sign_request_response::owl__req(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl__res_enumtest(x: &owl_sign_request_response<'_>) -> (res: bool)
    ensures
        res == _res_enumtest(x.view()),
{
    match x {
        owl_sign_request_response::owl__res(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_sign_request_response<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_sign_request_response<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_sign_request_response(arg.view()) is Some,
        res is None ==> parse_owlSpec_sign_request_response(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_sign_request_response(arg.view())->Some_0,
{
    reveal(parse_owlSpec_sign_request_response);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Tail), (Tag::new(U8, 2), Tail));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owl_sign_request_response::owl__req(
                SecretBuf::from_buf(x.another_ref()),
            ),
            inj_ord_choice_pat!(*, (_,x)) => owl_sign_request_response::owl__res(
                OwlBuf::another_ref(&x),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_sign_request_response<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_sign_request_response<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_sign_request_response(arg.view()) is Some,
        res is None ==> parse_owlSpec_sign_request_response(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_sign_request_response(arg.view())->Some_0,
{
    reveal(parse_owlSpec_sign_request_response);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_sign_request_response_inner(arg: &owl_sign_request_response) -> (res:
    Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_sign_request_response_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_sign_request_response_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_sign_request_response_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_sign_request_response(arg: &owl_sign_request_response) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_sign_request_response(arg.view()),
{
    reveal(serialize_owlSpec_sign_request_response);
    let res = serialize_owl_sign_request_response_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_dhpk_b<'a> {
    owl__comm_with_pfa(OwlBuf<'a>),
    owl__comm_with_sdis(OwlBuf<'a>),
}

use owl_dhpk_b::*;

impl<'a> owl_dhpk_b<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_dhpk_b<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl__comm_with_pfa(x) => owl__comm_with_pfa(OwlBuf::another_ref(x)),
            owl__comm_with_sdis(x) => owl__comm_with_sdis(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_dhpk_b<'_> {
    type V = owlSpec_dhpk_b;

    open spec fn view(&self) -> owlSpec_dhpk_b {
        match self {
            owl__comm_with_pfa(v) => owlSpec_dhpk_b::owlSpec__comm_with_pfa(v.view()),
            owl__comm_with_sdis(v) => owlSpec_dhpk_b::owlSpec__comm_with_sdis(v.view()),
        }
    }
}

#[inline]
pub fn owl__comm_with_pfa_enumtest(x: &owl_dhpk_b<'_>) -> (res: bool)
    ensures
        res == _comm_with_pfa_enumtest(x.view()),
{
    match x {
        owl_dhpk_b::owl__comm_with_pfa(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl__comm_with_sdis_enumtest(x: &owl_dhpk_b<'_>) -> (res: bool)
    ensures
        res == _comm_with_sdis_enumtest(x.view()),
{
    match x {
        owl_dhpk_b::owl__comm_with_sdis(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_dhpk_b<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_dhpk_b<'a>>)
    ensures
        res is Some ==> parse_owlSpec_dhpk_b(arg.view()) is Some,
        res is None ==> parse_owlSpec_dhpk_b(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_dhpk_b(arg.view())->Some_0,
{
    reveal(parse_owlSpec_dhpk_b);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(32)), (Tag::new(U8, 2), Variable(32)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owl_dhpk_b::owl__comm_with_pfa(
                OwlBuf::another_ref(&x),
            ),
            inj_ord_choice_pat!(*, (_,x)) => owl_dhpk_b::owl__comm_with_sdis(
                OwlBuf::another_ref(&x),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn serialize_owl_dhpk_b_inner(arg: &owl_dhpk_b) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_dhpk_b_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_dhpk_b_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_dhpk_b_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_dhpk_b(arg: &owl_dhpk_b) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_dhpk_b(arg.view()),
{
    reveal(serialize_owlSpec_dhpk_b);
    let res = serialize_owl_dhpk_b_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_signed_by_PFA<'a> {
    owl__signed_by_PFA_g_pow_a(OwlBuf<'a>),
    owl__signed_by_PFA_hash(OwlBuf<'a>),
}

use owl_signed_by_PFA::*;

impl<'a> owl_signed_by_PFA<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_signed_by_PFA<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl__signed_by_PFA_g_pow_a(x) => owl__signed_by_PFA_g_pow_a(OwlBuf::another_ref(x)),
            owl__signed_by_PFA_hash(x) => owl__signed_by_PFA_hash(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_signed_by_PFA<'_> {
    type V = owlSpec_signed_by_PFA;

    open spec fn view(&self) -> owlSpec_signed_by_PFA {
        match self {
            owl__signed_by_PFA_g_pow_a(v) => owlSpec_signed_by_PFA::owlSpec__signed_by_PFA_g_pow_a(
                v.view(),
            ),
            owl__signed_by_PFA_hash(v) => owlSpec_signed_by_PFA::owlSpec__signed_by_PFA_hash(
                v.view(),
            ),
        }
    }
}

#[inline]
pub fn owl__signed_by_PFA_g_pow_a_enumtest(x: &owl_signed_by_PFA<'_>) -> (res: bool)
    ensures
        res == _signed_by_PFA_g_pow_a_enumtest(x.view()),
{
    match x {
        owl_signed_by_PFA::owl__signed_by_PFA_g_pow_a(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl__signed_by_PFA_hash_enumtest(x: &owl_signed_by_PFA<'_>) -> (res: bool)
    ensures
        res == _signed_by_PFA_hash_enumtest(x.view()),
{
    match x {
        owl_signed_by_PFA::owl__signed_by_PFA_hash(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_signed_by_PFA<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_signed_by_PFA<'a>>)
    ensures
        res is Some ==> parse_owlSpec_signed_by_PFA(arg.view()) is Some,
        res is None ==> parse_owlSpec_signed_by_PFA(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_signed_by_PFA(arg.view())->Some_0,
{
    reveal(parse_owlSpec_signed_by_PFA);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(32)), (Tag::new(U8, 2), Tail));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owl_signed_by_PFA::owl__signed_by_PFA_g_pow_a(
                OwlBuf::another_ref(&x),
            ),
            inj_ord_choice_pat!(*, (_,x)) => owl_signed_by_PFA::owl__signed_by_PFA_hash(
                OwlBuf::another_ref(&x),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn serialize_owl_signed_by_PFA_inner(arg: &owl_signed_by_PFA) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_signed_by_PFA_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_signed_by_PFA_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_signed_by_PFA_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_signed_by_PFA(arg: &owl_signed_by_PFA) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_signed_by_PFA(arg.view()),
{
    reveal(serialize_owlSpec_signed_by_PFA);
    let res = serialize_owl_signed_by_PFA_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_pfa_msg<'a> {
    pub owl__pfa1: OwlBuf<'a>,
    pub owl__pfa2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_pfa_msg<'a>(arg_owl__pfa1: OwlBuf<'a>, arg_owl__pfa2: OwlBuf<'a>) -> (res: owl_pfa_msg<
    'a,
>)
    ensures
        res.owl__pfa1.view() == arg_owl__pfa1.view(),
        res.owl__pfa2.view() == arg_owl__pfa2.view(),
{
    owl_pfa_msg { owl__pfa1: arg_owl__pfa1, owl__pfa2: arg_owl__pfa2 }
}

impl<'a> owl_pfa_msg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_pfa_msg<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_pfa_msg {
            owl__pfa1: OwlBuf::another_ref(&self.owl__pfa1),
            owl__pfa2: OwlBuf::another_ref(&self.owl__pfa2),
        }
    }
}

impl View for owl_pfa_msg<'_> {
    type V = owlSpec_pfa_msg;

    open spec fn view(&self) -> owlSpec_pfa_msg {
        owlSpec_pfa_msg {
            owlSpec__pfa1: self.owl__pfa1.view(),
            owlSpec__pfa2: self.owl__pfa2.view(),
        }
    }
}

pub exec fn parse_owl_pfa_msg<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_pfa_msg<'a>>)
    ensures
        res is Some ==> parse_owlSpec_pfa_msg(arg.view()) is Some,
        res is None ==> parse_owlSpec_pfa_msg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_pfa_msg(arg.view())->Some_0,
{
    reveal(parse_owlSpec_pfa_msg);
    let exec_comb = exec_combinator_owl_pfa_msg();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__pfa1, owl__pfa2) = parsed;
        Some(
            owl_pfa_msg {
                owl__pfa1: OwlBuf::another_ref(&owl__pfa1),
                owl__pfa2: OwlBuf::another_ref(&owl__pfa2),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_pfa_msg_inner<'a>(arg: &owl_pfa_msg<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_pfa_msg_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_pfa_msg_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_pfa_msg_inner);
    if no_usize_overflows![ arg.owl__pfa1.len(), arg.owl__pfa2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_pfa_msg();
        let mut obuf = vec_u8_of_len(arg.owl__pfa1.len() + arg.owl__pfa2.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl__pfa1), OwlBuf::another_ref(&arg.owl__pfa2)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_pfa_msg_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_pfa_msg<'a>(arg: &owl_pfa_msg<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_pfa_msg(arg.view()),
{
    reveal(serialize_owlSpec_pfa_msg);
    let res = serialize_owl_pfa_msg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_pdis_msg1<'a> {
    pub owl__pdis1_1: OwlBuf<'a>,
    pub owl__pdis2_1: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_pdis_msg1<'a>(arg_owl__pdis1_1: OwlBuf<'a>, arg_owl__pdis2_1: OwlBuf<'a>) -> (res:
    owl_pdis_msg1<'a>)
    ensures
        res.owl__pdis1_1.view() == arg_owl__pdis1_1.view(),
        res.owl__pdis2_1.view() == arg_owl__pdis2_1.view(),
{
    owl_pdis_msg1 { owl__pdis1_1: arg_owl__pdis1_1, owl__pdis2_1: arg_owl__pdis2_1 }
}

impl<'a> owl_pdis_msg1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_pdis_msg1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_pdis_msg1 {
            owl__pdis1_1: OwlBuf::another_ref(&self.owl__pdis1_1),
            owl__pdis2_1: OwlBuf::another_ref(&self.owl__pdis2_1),
        }
    }
}

impl View for owl_pdis_msg1<'_> {
    type V = owlSpec_pdis_msg1;

    open spec fn view(&self) -> owlSpec_pdis_msg1 {
        owlSpec_pdis_msg1 {
            owlSpec__pdis1_1: self.owl__pdis1_1.view(),
            owlSpec__pdis2_1: self.owl__pdis2_1.view(),
        }
    }
}

pub exec fn parse_owl_pdis_msg1<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_pdis_msg1<'a>>)
    ensures
        res is Some ==> parse_owlSpec_pdis_msg1(arg.view()) is Some,
        res is None ==> parse_owlSpec_pdis_msg1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_pdis_msg1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_pdis_msg1);
    let exec_comb = exec_combinator_owl_pdis_msg1();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__pdis1_1, owl__pdis2_1) = parsed;
        Some(
            owl_pdis_msg1 {
                owl__pdis1_1: OwlBuf::another_ref(&owl__pdis1_1),
                owl__pdis2_1: OwlBuf::another_ref(&owl__pdis2_1),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_pdis_msg1_inner<'a>(arg: &owl_pdis_msg1<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_pdis_msg1_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_pdis_msg1_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_pdis_msg1_inner);
    if no_usize_overflows![ arg.owl__pdis1_1.len(), arg.owl__pdis2_1.len(), 0 ] {
        let exec_comb = exec_combinator_owl_pdis_msg1();
        let mut obuf = vec_u8_of_len(arg.owl__pdis1_1.len() + arg.owl__pdis2_1.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl__pdis1_1), OwlBuf::another_ref(&arg.owl__pdis2_1)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_pdis_msg1_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_pdis_msg1<'a>(arg: &owl_pdis_msg1<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_pdis_msg1(arg.view()),
{
    reveal(serialize_owlSpec_pdis_msg1);
    let res = serialize_owl_pdis_msg1_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_pdis_msg2<'a> {
    pub owl__pdis1_2: OwlBuf<'a>,
    pub owl__pdis2_2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_pdis_msg2<'a>(arg_owl__pdis1_2: OwlBuf<'a>, arg_owl__pdis2_2: OwlBuf<'a>) -> (res:
    owl_pdis_msg2<'a>)
    ensures
        res.owl__pdis1_2.view() == arg_owl__pdis1_2.view(),
        res.owl__pdis2_2.view() == arg_owl__pdis2_2.view(),
{
    owl_pdis_msg2 { owl__pdis1_2: arg_owl__pdis1_2, owl__pdis2_2: arg_owl__pdis2_2 }
}

impl<'a> owl_pdis_msg2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_pdis_msg2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_pdis_msg2 {
            owl__pdis1_2: OwlBuf::another_ref(&self.owl__pdis1_2),
            owl__pdis2_2: OwlBuf::another_ref(&self.owl__pdis2_2),
        }
    }
}

impl View for owl_pdis_msg2<'_> {
    type V = owlSpec_pdis_msg2;

    open spec fn view(&self) -> owlSpec_pdis_msg2 {
        owlSpec_pdis_msg2 {
            owlSpec__pdis1_2: self.owl__pdis1_2.view(),
            owlSpec__pdis2_2: self.owl__pdis2_2.view(),
        }
    }
}

pub exec fn parse_owl_pdis_msg2<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_pdis_msg2<'a>>)
    ensures
        res is Some ==> parse_owlSpec_pdis_msg2(arg.view()) is Some,
        res is None ==> parse_owlSpec_pdis_msg2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_pdis_msg2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_pdis_msg2);
    let exec_comb = exec_combinator_owl_pdis_msg2();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__pdis1_2, owl__pdis2_2) = parsed;
        Some(
            owl_pdis_msg2 {
                owl__pdis1_2: OwlBuf::another_ref(&owl__pdis1_2),
                owl__pdis2_2: OwlBuf::another_ref(&owl__pdis2_2),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_pdis_msg2_inner<'a>(arg: &owl_pdis_msg2<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_pdis_msg2_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_pdis_msg2_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_pdis_msg2_inner);
    if no_usize_overflows![ arg.owl__pdis1_2.len(), arg.owl__pdis2_2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_pdis_msg2();
        let mut obuf = vec_u8_of_len(arg.owl__pdis1_2.len() + arg.owl__pdis2_2.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl__pdis1_2), OwlBuf::another_ref(&arg.owl__pdis2_2)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_pdis_msg2_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_pdis_msg2<'a>(arg: &owl_pdis_msg2<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_pdis_msg2(arg.view()),
{
    reveal(serialize_owlSpec_pdis_msg2);
    let res = serialize_owl_pdis_msg2_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_sdis_msg<'a> {
    pub owl__sdis1: OwlBuf<'a>,
    pub owl__sdis2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_sdis_msg<'a>(arg_owl__sdis1: OwlBuf<'a>, arg_owl__sdis2: OwlBuf<'a>) -> (res:
    owl_sdis_msg<'a>)
    ensures
        res.owl__sdis1.view() == arg_owl__sdis1.view(),
        res.owl__sdis2.view() == arg_owl__sdis2.view(),
{
    owl_sdis_msg { owl__sdis1: arg_owl__sdis1, owl__sdis2: arg_owl__sdis2 }
}

impl<'a> owl_sdis_msg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_sdis_msg<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_sdis_msg {
            owl__sdis1: OwlBuf::another_ref(&self.owl__sdis1),
            owl__sdis2: OwlBuf::another_ref(&self.owl__sdis2),
        }
    }
}

impl View for owl_sdis_msg<'_> {
    type V = owlSpec_sdis_msg;

    open spec fn view(&self) -> owlSpec_sdis_msg {
        owlSpec_sdis_msg {
            owlSpec__sdis1: self.owl__sdis1.view(),
            owlSpec__sdis2: self.owl__sdis2.view(),
        }
    }
}

pub exec fn parse_owl_sdis_msg<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_sdis_msg<'a>>)
    ensures
        res is Some ==> parse_owlSpec_sdis_msg(arg.view()) is Some,
        res is None ==> parse_owlSpec_sdis_msg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_sdis_msg(arg.view())->Some_0,
{
    reveal(parse_owlSpec_sdis_msg);
    let exec_comb = exec_combinator_owl_sdis_msg();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__sdis1, owl__sdis2) = parsed;
        Some(
            owl_sdis_msg {
                owl__sdis1: OwlBuf::another_ref(&owl__sdis1),
                owl__sdis2: OwlBuf::another_ref(&owl__sdis2),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_sdis_msg_inner<'a>(arg: &owl_sdis_msg<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_sdis_msg_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_sdis_msg_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_sdis_msg_inner);
    if no_usize_overflows![ arg.owl__sdis1.len(), arg.owl__sdis2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_sdis_msg();
        let mut obuf = vec_u8_of_len(arg.owl__sdis1.len() + arg.owl__sdis2.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl__sdis1), OwlBuf::another_ref(&arg.owl__sdis2)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_sdis_msg_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_sdis_msg<'a>(arg: &owl_sdis_msg<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_sdis_msg(arg.view()),
{
    reveal(serialize_owlSpec_sdis_msg);
    let res = serialize_owl_sdis_msg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct state_PDIS {}

impl state_PDIS {
    #[verifier::external_body]
    pub fn init_state_PDIS() -> Self {
        state_PDIS {  }
    }
}

pub struct cfg_PDIS<'PDIS> {
    pub owl_skPDIS: SecretBuf<'PDIS>,
    pub owl_b1: SecretBuf<'PDIS>,
    pub owl_b: SecretBuf<'PDIS>,
    pub pk_owl_skSDIS: OwlBuf<'PDIS>,
    pub pk_owl_skPDIS: OwlBuf<'PDIS>,
    pub pk_owl_skPFA: OwlBuf<'PDIS>,
    pub pk_owl_c: OwlBuf<'PDIS>,
    pub pk_owl_b1: OwlBuf<'PDIS>,
    pub pk_owl_b: OwlBuf<'PDIS>,
    pub pk_owl_a: OwlBuf<'PDIS>,
}

impl cfg_PDIS<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_PDIS_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_PDIS), Endpoint>>,
        mut_state: &mut state_PDIS,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_PDIS), Endpoint>>), OwlError>)
        requires
            itree.view() == PDIS_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_PDIS), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(PDIS_main_spec);

            owl_call_ret_unit!(effects, itree, *mut_state, PDIS_KE_spec(*self, *mut_state), self.owl_PDIS_KE(mut_state))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_PDIS_KE<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_PDIS), Endpoint>>,
        mut_state: &mut state_PDIS,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_PDIS), Endpoint>>), OwlError>)
        requires
            itree.view() == PDIS_KE_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_PDIS), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(PDIS_KE_spec);
            let tmp_owl_g_pow_b160 = {
                owl_dhpk(SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_b)))
            };
            let owl_g_pow_b160 = OwlBuf::from_vec(tmp_owl_g_pow_b160);
            let tmp_owl_signed_g_pow_b161 = {
                owl_sign(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skPDIS)),
                    OwlBuf::another_ref(
                        &OwlBuf::from_vec(
                            serialize_owl_dhpk_b(
                                &owl__comm_with_pfa(OwlBuf::another_ref(&owl_g_pow_b160)),
                            ),
                        ),
                    ),
                )
            };
            let owl_signed_g_pow_b161 = OwlBuf::from_vec(tmp_owl_signed_g_pow_b161);
            let owl__162 = {
                effects.owl_output::<((), state_PDIS)>(
                    Tracked(&mut itree),
                    serialize_owl_pdis_msg1(
                        &owl_pdis_msg1(
                            OwlBuf::another_ref(&owl_g_pow_b160),
                            OwlBuf::another_ref(&owl_signed_g_pow_b161),
                        ),
                    ).as_slice(),
                    Some(&PFA_addr()),
                    &PDIS_addr(),
                );
            };
            let (tmp_owl_inp164, owl__163) = {
                effects.owl_input::<((), state_PDIS)>(Tracked(&mut itree))
            };
            let owl_inp164 = OwlBuf::from_vec(tmp_owl_inp164);
            let tmp_owl_vkPFA165 = { OwlBuf::another_ref(&self.pk_owl_skPFA) };
            let owl_vkPFA165 = OwlBuf::another_ref(&tmp_owl_vkPFA165);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp164);
            if let Some(parseval) = parse_owl_pfa_msg(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_pfa1167 = OwlBuf::another_ref(&parseval.owl__pfa1);
                let owl_pfa2166 = OwlBuf::another_ref(&parseval.owl__pfa2);
                let tmp_owl_caseval168 = {
                    let tracked owl_declassify_tok169 = consume_itree_declassify::<
                        ((), state_PDIS),
                        Endpoint,
                    >(&mut itree);
                    owl_vrfy(
                        OwlBuf::another_ref(&owl_vkPFA165),
                        SecretBuf::another_ref(&SecretBuf::from_buf(owl_pfa1167.another_ref())),
                        OwlBuf::another_ref(&owl_pfa2166),
                        Tracked(owl_declassify_tok169),
                    )
                };
                let owl_caseval168 = SecretBuf::another_ref_option(&tmp_owl_caseval168);
                match SecretBuf::another_ref_option(&owl_caseval168) {
                    Option::None => { (owl_unit(), Tracked(itree)) },
                    Option::Some(tmp_owl_m170) => {
                        let owl_m170 = SecretBuf::another_ref(&tmp_owl_m170);
                        let tmp_owl_declassified_buf31171 = {
                            let tracked owl_declassify_tok172 = consume_itree_declassify::<
                                ((), state_PDIS),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_m170).declassify(
                                    Tracked(owl_declassify_tok172),
                                )
                            }
                        };
                        let owl_declassified_buf31171 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf31171,
                        );
                        let parseval_tmp = OwlBuf::another_ref(&owl_declassified_buf31171);
                        if let Some(parseval) = parse_owl_signed_by_PFA(
                            OwlBuf::another_ref(&parseval_tmp),
                        ) {
                            let owl_parsed_caseval173 = owl_signed_by_PFA::another_ref(&parseval);
                            match owl_signed_by_PFA::another_ref(&owl_parsed_caseval173) {
                                owl_signed_by_PFA::owl__signed_by_PFA_hash(tmp_owl__174) => {
                                    let owl__174 = OwlBuf::another_ref(&tmp_owl__174);
                                    (owl_unit(), Tracked(itree))
                                },
                                owl_signed_by_PFA::owl__signed_by_PFA_g_pow_a(
                                    tmp_owl_g_pow_a175,
                                ) => {
                                    let owl_g_pow_a175 = OwlBuf::another_ref(&tmp_owl_g_pow_a175);

                                    if !(owl_is_group_elem(
                                        SecretBuf::from_buf(owl_g_pow_a175.another_ref()),
                                    )) {
                                        (owl_unit(), Tracked(itree))
                                    } else {
                                        {
                                            let tmp_owl_ss176 = {
                                                owl_dh_combine(
                                                    SecretBuf::from_buf(
                                                        owl_g_pow_a175.another_ref(),
                                                    ),
                                                    SecretBuf::another_ref(
                                                        &SecretBuf::another_ref(&self.owl_b),
                                                    ),
                                                )
                                            };
                                            let owl_ss176 = SecretBuf::another_ref(&tmp_owl_ss176);
                                            let tmp_owl_kdfval24177 = {
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
                                                    SecretBuf::another_ref(&owl_ss176),
                                                    OwlBuf::another_ref(
                                                        &{
                                                            let x = mk_vec_u8![0x01u8 ];
                                                            OwlBuf::from_vec(x)
                                                        },
                                                    ),
                                                )
                                            };
                                            let owl_kdfval24177 = SecretBuf::another_ref(
                                                &tmp_owl_kdfval24177,
                                            );
                                            let tmp_owl_k11178 = {
                                                {
                                                    SecretBuf::another_ref(
                                                        &owl_kdfval24177,
                                                    ).subrange(0, 0 + ENCKEY_SIZE)
                                                }
                                            };
                                            let owl_k11178 = SecretBuf::another_ref(
                                                &tmp_owl_k11178,
                                            );
                                            let owl__179 = {
                                                effects.owl_output::<((), state_PDIS)>(
                                                    Tracked(&mut itree),
                                                    {
                                                        let x = mk_vec_u8![];
                                                        OwlBuf::from_vec(x)
                                                    }.as_slice(),
                                                    Some(&SDIS_addr()),
                                                    &PDIS_addr(),
                                                );
                                            };
                                            let tmp_arg1274 = owl_ghost_unit();
                                            let tmp_arg2275 = SecretBuf::another_ref(&owl_k11178);
                                            owl_call_ret_unit!(effects, itree, *mut_state, PDIS_actual_spec(*self, *mut_state, tmp_arg1274, tmp_arg2275.view()), self.owl_PDIS_actual(mut_state, tmp_arg1274, tmp_arg2275))
                                        }
                                    }

                                },
                            }
                        } else {
                            (owl_unit(), Tracked(itree))
                        }
                    },
                }
            } else {
                (owl_unit(), Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_PDIS_actual<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_PDIS), Endpoint>>,
        mut_state: &mut state_PDIS,
        owl_gb276: Ghost<()>,
        owl_k11277: SecretBuf<'_>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_PDIS), Endpoint>>), OwlError>)
        requires
            itree.view() == PDIS_actual_spec(*self, *old(mut_state), owl_gb276, owl_k11277.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_PDIS), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(PDIS_actual_spec);
            let tmp_owl_g_pow_b1182 = {
                owl_dhpk(SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_b1)))
            };
            let owl_g_pow_b1182 = OwlBuf::from_vec(tmp_owl_g_pow_b1182);
            let tmp_owl_signed_g_pow_b1183 = {
                owl_sign(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skPDIS)),
                    OwlBuf::another_ref(
                        &OwlBuf::from_vec(
                            serialize_owl_dhpk_b(
                                &owl__comm_with_sdis(OwlBuf::another_ref(&owl_g_pow_b1182)),
                            ),
                        ),
                    ),
                )
            };
            let owl_signed_g_pow_b1183 = OwlBuf::from_vec(tmp_owl_signed_g_pow_b1183);
            let owl__184 = {
                effects.owl_output::<((), state_PDIS)>(
                    Tracked(&mut itree),
                    serialize_owl_pdis_msg2(
                        &owl_pdis_msg2(
                            OwlBuf::another_ref(&owl_g_pow_b1182),
                            OwlBuf::another_ref(&owl_signed_g_pow_b1183),
                        ),
                    ).as_slice(),
                    Some(&SDIS_addr()),
                    &PDIS_addr(),
                );
            };
            let (tmp_owl_inp186, owl__185) = {
                effects.owl_input::<((), state_PDIS)>(Tracked(&mut itree))
            };
            let owl_inp186 = OwlBuf::from_vec(tmp_owl_inp186);
            let tmp_owl_vkSDIS187 = { OwlBuf::another_ref(&self.pk_owl_skSDIS) };
            let owl_vkSDIS187 = OwlBuf::another_ref(&tmp_owl_vkSDIS187);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp186);
            if let Some(parseval) = parse_owl_sdis_msg(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_sdis1189 = OwlBuf::another_ref(&parseval.owl__sdis1);
                let owl_sdis2188 = OwlBuf::another_ref(&parseval.owl__sdis2);
                let tmp_owl_caseval190 = {
                    let tracked owl_declassify_tok191 = consume_itree_declassify::<
                        ((), state_PDIS),
                        Endpoint,
                    >(&mut itree);
                    owl_vrfy(
                        OwlBuf::another_ref(&owl_vkSDIS187),
                        SecretBuf::another_ref(&SecretBuf::from_buf(owl_sdis1189.another_ref())),
                        OwlBuf::another_ref(&owl_sdis2188),
                        Tracked(owl_declassify_tok191),
                    )
                };
                let owl_caseval190 = SecretBuf::another_ref_option(&tmp_owl_caseval190);
                match SecretBuf::another_ref_option(&owl_caseval190) {
                    Option::None => { (owl_unit(), Tracked(itree)) },
                    Option::Some(tmp_owl_g_pow_c192) => {
                        let owl_g_pow_c192 = SecretBuf::another_ref(&tmp_owl_g_pow_c192);

                        if !(owl_is_group_elem(SecretBuf::another_ref(&owl_g_pow_c192))) {
                            (owl_unit(), Tracked(itree))
                        } else {
                            {
                                let tmp_owl_ss193 = {
                                    owl_dh_combine(
                                        SecretBuf::another_ref(&owl_g_pow_c192),
                                        SecretBuf::another_ref(
                                            &SecretBuf::another_ref(&self.owl_b1),
                                        ),
                                    )
                                };
                                let owl_ss193 = SecretBuf::another_ref(&tmp_owl_ss193);
                                let tmp_owl_kdfval50194 = {
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
                                        SecretBuf::another_ref(&owl_ss193),
                                        OwlBuf::another_ref(
                                            &{
                                                let x = mk_vec_u8![0x02u8 ];
                                                OwlBuf::from_vec(x)
                                            },
                                        ),
                                    )
                                };
                                let owl_kdfval50194 = SecretBuf::another_ref(&tmp_owl_kdfval50194);
                                let tmp_owl_k195 = {
                                    {
                                        SecretBuf::another_ref(&owl_kdfval50194).subrange(
                                            0,
                                            0 + ENCKEY_SIZE,
                                        )
                                    }
                                };
                                let owl_k195 = SecretBuf::another_ref(&tmp_owl_k195);
                                let tmp_owl_request196 = {
                                    owl__req(
                                        SecretBuf::another_ref(
                                            &SecretBuf::from_buf(
                                                {
                                                    let x = mk_vec_u8![0x01u8 ];
                                                    OwlBuf::from_vec(x)
                                                }.another_ref(),
                                            ),
                                        ),
                                    )
                                };
                                let owl_request196 = owl_sign_request_response::another_ref(
                                    &tmp_owl_request196,
                                );
                                let tmp_owl_enc_request197 = {
                                    let tmp_owl_coins198 = effects.owl_sample::<((), state_PDIS)>(
                                        Tracked(&mut itree),
                                        NONCE_SIZE,
                                    );
                                    let owl_coins198 = SecretBuf::another_ref(&tmp_owl_coins198);
                                    owl_enc(
                                        SecretBuf::another_ref(&owl_k11277),
                                        SecretBuf::another_ref(
                                            &OwlBuf::from_vec(
                                                serialize_owl_sign_request_response(
                                                    &owl_request196,
                                                ),
                                            ).into_secret(),
                                        ),
                                        SecretBuf::another_ref(&owl_coins198),
                                    )
                                };
                                let owl_enc_request197 = OwlBuf::from_vec(tmp_owl_enc_request197);
                                let owl__199 = {
                                    effects.owl_output::<((), state_PDIS)>(
                                        Tracked(&mut itree),
                                        owl_enc_request197.as_slice(),
                                        Some(&PFA_addr()),
                                        &PDIS_addr(),
                                    );
                                };
                                let (tmp_owl_inp2201, owl__200) = {
                                    effects.owl_input::<((), state_PDIS)>(Tracked(&mut itree))
                                };
                                let owl_inp2201 = OwlBuf::from_vec(tmp_owl_inp2201);
                                let tmp_owl_caseval202 = {
                                    let tracked owl_declassify_tok203 = consume_itree_declassify::<
                                        ((), state_PDIS),
                                        Endpoint,
                                    >(&mut itree);
                                    owl_dec(
                                        SecretBuf::another_ref(&owl_k11277),
                                        OwlBuf::another_ref(&owl_inp2201),
                                        Tracked(owl_declassify_tok203),
                                    )
                                };
                                let owl_caseval202 = SecretBuf::another_ref_option(
                                    &tmp_owl_caseval202,
                                );
                                match SecretBuf::another_ref_option(&owl_caseval202) {
                                    Option::None => { (owl_unit(), Tracked(itree)) },
                                    Option::Some(tmp_owl_m_204) => {
                                        let owl_m_204 = SecretBuf::another_ref(&tmp_owl_m_204);
                                        let tracked owl_declassify_tok205 =
                                            consume_itree_declassify::<((), state_PDIS), Endpoint>(
                                            &mut itree,
                                        );
                                        let parseval_tmp = SecretBuf::another_ref(&owl_m_204);
                                        if let Some(parseval) =
                                            secret_parse_owl_sign_request_response(
                                            SecretBuf::another_ref(&parseval_tmp),
                                            Tracked(owl_declassify_tok205),
                                        ) {
                                            let owl_parsed_caseval206 =
                                                owl_sign_request_response::another_ref(&parseval);
                                            match owl_sign_request_response::another_ref(
                                                &owl_parsed_caseval206,
                                            ) {
                                                owl_sign_request_response::owl__req(
                                                    tmp_owl__207,
                                                ) => {
                                                    let owl__207 = SecretBuf::another_ref(
                                                        &tmp_owl__207,
                                                    );
                                                    (owl_unit(), Tracked(itree))
                                                },
                                                owl_sign_request_response::owl__res(
                                                    tmp_owl_h2208,
                                                ) => {
                                                    let owl_h2208 = OwlBuf::another_ref(
                                                        &tmp_owl_h2208,
                                                    );
                                                    let tmp_owl_msg_to_send_SDIS209 = {
                                                        let tmp_owl_coins210 = effects.owl_sample::<
                                                            ((), state_PDIS),
                                                        >(Tracked(&mut itree), NONCE_SIZE);
                                                        let owl_coins210 = SecretBuf::another_ref(
                                                            &tmp_owl_coins210,
                                                        );
                                                        owl_enc(
                                                            SecretBuf::another_ref(&owl_k195),
                                                            SecretBuf::another_ref(
                                                                &SecretBuf::from_buf(
                                                                    owl_h2208.another_ref(),
                                                                ),
                                                            ),
                                                            SecretBuf::another_ref(&owl_coins210),
                                                        )
                                                    };
                                                    let owl_msg_to_send_SDIS209 = OwlBuf::from_vec(
                                                        tmp_owl_msg_to_send_SDIS209,
                                                    );
                                                    let owl__211 = {
                                                        effects.owl_output::<((), state_PDIS)>(
                                                            Tracked(&mut itree),
                                                            owl_msg_to_send_SDIS209.as_slice(),
                                                            Some(&SDIS_addr()),
                                                            &PDIS_addr(),
                                                        );
                                                    };
                                                    (owl_unit(), Tracked(itree))
                                                },
                                            }
                                        } else {
                                            (owl_unit(), Tracked(itree))
                                        }
                                    },
                                }
                            }
                        }

                    },
                }
            } else {
                (owl_unit(), Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub struct state_PFA {}

impl state_PFA {
    #[verifier::external_body]
    pub fn init_state_PFA() -> Self {
        state_PFA {  }
    }
}

pub struct cfg_PFA<'PFA> {
    pub owl_skPFA: SecretBuf<'PFA>,
    pub owl_a: SecretBuf<'PFA>,
    pub pk_owl_skSDIS: OwlBuf<'PFA>,
    pub pk_owl_skPDIS: OwlBuf<'PFA>,
    pub pk_owl_skPFA: OwlBuf<'PFA>,
    pub pk_owl_c: OwlBuf<'PFA>,
    pub pk_owl_b1: OwlBuf<'PFA>,
    pub pk_owl_b: OwlBuf<'PFA>,
    pub pk_owl_a: OwlBuf<'PFA>,
}

impl cfg_PFA<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_PFA_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_PFA), Endpoint>>,
        mut_state: &mut state_PFA,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_PFA), Endpoint>>), OwlError>)
        requires
            itree.view() == PFA_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_PFA), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(PFA_main_spec);

            owl_call_ret_unit!(effects, itree, *mut_state, PFA_KE_spec(*self, *mut_state), self.owl_PFA_KE(mut_state))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_PFA_KE<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_PFA), Endpoint>>,
        mut_state: &mut state_PFA,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_PFA), Endpoint>>), OwlError>)
        requires
            itree.view() == PFA_KE_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_PFA), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(PFA_KE_spec);
            let tmp_owl_g_pow_a212 = {
                owl_dhpk(SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_a)))
            };
            let owl_g_pow_a212 = OwlBuf::from_vec(tmp_owl_g_pow_a212);
            let tmp_owl_signed_g_pow_a213 = {
                owl_sign(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skPFA)),
                    OwlBuf::another_ref(
                        &OwlBuf::from_vec(
                            serialize_owl_signed_by_PFA(
                                &owl__signed_by_PFA_g_pow_a(OwlBuf::another_ref(&owl_g_pow_a212)),
                            ),
                        ),
                    ),
                )
            };
            let owl_signed_g_pow_a213 = OwlBuf::from_vec(tmp_owl_signed_g_pow_a213);
            let owl__214 = {
                effects.owl_output::<((), state_PFA)>(
                    Tracked(&mut itree),
                    serialize_owl_pfa_msg(
                        &owl_pfa_msg(
                            OwlBuf::another_ref(&owl_g_pow_a212),
                            OwlBuf::another_ref(&owl_signed_g_pow_a213),
                        ),
                    ).as_slice(),
                    Some(&PDIS_addr()),
                    &PFA_addr(),
                );
            };
            let (tmp_owl_inp216, owl__215) = {
                effects.owl_input::<((), state_PFA)>(Tracked(&mut itree))
            };
            let owl_inp216 = OwlBuf::from_vec(tmp_owl_inp216);
            let tmp_owl_vkPDIS217 = { OwlBuf::another_ref(&self.pk_owl_skPDIS) };
            let owl_vkPDIS217 = OwlBuf::another_ref(&tmp_owl_vkPDIS217);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp216);
            if let Some(parseval) = parse_owl_pdis_msg1(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_pdis1_1219 = OwlBuf::another_ref(&parseval.owl__pdis1_1);
                let owl_pdis2_1218 = OwlBuf::another_ref(&parseval.owl__pdis2_1);
                let tmp_owl_caseval220 = {
                    let tracked owl_declassify_tok221 = consume_itree_declassify::<
                        ((), state_PFA),
                        Endpoint,
                    >(&mut itree);
                    owl_vrfy(
                        OwlBuf::another_ref(&owl_vkPDIS217),
                        SecretBuf::another_ref(&SecretBuf::from_buf(owl_pdis1_1219.another_ref())),
                        OwlBuf::another_ref(&owl_pdis2_1218),
                        Tracked(owl_declassify_tok221),
                    )
                };
                let owl_caseval220 = SecretBuf::another_ref_option(&tmp_owl_caseval220);
                match SecretBuf::another_ref_option(&owl_caseval220) {
                    Option::None => { (owl_unit(), Tracked(itree)) },
                    Option::Some(tmp_owl_m222) => {
                        let owl_m222 = SecretBuf::another_ref(&tmp_owl_m222);
                        let tmp_owl_declassified_buf91223 = {
                            let tracked owl_declassify_tok224 = consume_itree_declassify::<
                                ((), state_PFA),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_m222).declassify(
                                    Tracked(owl_declassify_tok224),
                                )
                            }
                        };
                        let owl_declassified_buf91223 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf91223,
                        );
                        let parseval_tmp = OwlBuf::another_ref(&owl_declassified_buf91223);
                        if let Some(parseval) = parse_owl_dhpk_b(
                            OwlBuf::another_ref(&parseval_tmp),
                        ) {
                            let owl_parsed_caseval225 = owl_dhpk_b::another_ref(&parseval);
                            match owl_dhpk_b::another_ref(&owl_parsed_caseval225) {
                                owl_dhpk_b::owl__comm_with_sdis(tmp_owl__226) => {
                                    let owl__226 = OwlBuf::another_ref(&tmp_owl__226);
                                    (owl_unit(), Tracked(itree))
                                },
                                owl_dhpk_b::owl__comm_with_pfa(tmp_owl_g_pow_b227) => {
                                    let owl_g_pow_b227 = OwlBuf::another_ref(&tmp_owl_g_pow_b227);

                                    if !(owl_is_group_elem(
                                        SecretBuf::from_buf(owl_g_pow_b227.another_ref()),
                                    )) {
                                        (owl_unit(), Tracked(itree))
                                    } else {
                                        {
                                            let tmp_owl_ss228 = {
                                                owl_dh_combine(
                                                    SecretBuf::from_buf(
                                                        owl_g_pow_b227.another_ref(),
                                                    ),
                                                    SecretBuf::another_ref(
                                                        &SecretBuf::another_ref(&self.owl_a),
                                                    ),
                                                )
                                            };
                                            let owl_ss228 = SecretBuf::another_ref(&tmp_owl_ss228);
                                            let tmp_owl_kdfval85229 = {
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
                                                    SecretBuf::another_ref(&owl_ss228),
                                                    OwlBuf::another_ref(
                                                        &{
                                                            let x = mk_vec_u8![0x01u8 ];
                                                            OwlBuf::from_vec(x)
                                                        },
                                                    ),
                                                )
                                            };
                                            let owl_kdfval85229 = SecretBuf::another_ref(
                                                &tmp_owl_kdfval85229,
                                            );
                                            let tmp_owl_k11230 = {
                                                {
                                                    SecretBuf::another_ref(
                                                        &owl_kdfval85229,
                                                    ).subrange(0, 0 + ENCKEY_SIZE)
                                                }
                                            };
                                            let owl_k11230 = SecretBuf::another_ref(
                                                &tmp_owl_k11230,
                                            );
                                            let tmp_arg1278 = owl_ghost_unit();
                                            let tmp_arg2279 = SecretBuf::another_ref(&owl_k11230);
                                            owl_call_ret_unit!(effects, itree, *mut_state, PFA_FW_spec(*self, *mut_state, tmp_arg1278, tmp_arg2279.view()), self.owl_PFA_FW(mut_state, tmp_arg1278, tmp_arg2279))
                                        }
                                    }

                                },
                            }
                        } else {
                            (owl_unit(), Tracked(itree))
                        }
                    },
                }
            } else {
                (owl_unit(), Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_PFA_FW<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_PFA), Endpoint>>,
        mut_state: &mut state_PFA,
        owl_gb280: Ghost<()>,
        owl_k11281: SecretBuf<'_>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_PFA), Endpoint>>), OwlError>)
        requires
            itree.view() == PFA_FW_spec(*self, *old(mut_state), owl_gb280, owl_k11281.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_PFA), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(PFA_FW_spec);
            let (tmp_owl_inp234, owl__233) = {
                effects.owl_input::<((), state_PFA)>(Tracked(&mut itree))
            };
            let owl_inp234 = OwlBuf::from_vec(tmp_owl_inp234);
            let tmp_owl_caseval235 = {
                let tracked owl_declassify_tok236 = consume_itree_declassify::<
                    ((), state_PFA),
                    Endpoint,
                >(&mut itree);
                owl_dec(
                    SecretBuf::another_ref(&owl_k11281),
                    OwlBuf::another_ref(&owl_inp234),
                    Tracked(owl_declassify_tok236),
                )
            };
            let owl_caseval235 = SecretBuf::another_ref_option(&tmp_owl_caseval235);
            match SecretBuf::another_ref_option(&owl_caseval235) {
                Option::None => { (owl_unit(), Tracked(itree)) },
                Option::Some(tmp_owl_m_237) => {
                    let owl_m_237 = SecretBuf::another_ref(&tmp_owl_m_237);
                    let tracked owl_declassify_tok238 = consume_itree_declassify::<
                        ((), state_PFA),
                        Endpoint,
                    >(&mut itree);
                    let parseval_tmp = SecretBuf::another_ref(&owl_m_237);
                    if let Some(parseval) = secret_parse_owl_sign_request_response(
                        SecretBuf::another_ref(&parseval_tmp),
                        Tracked(owl_declassify_tok238),
                    ) {
                        let owl_parsed_caseval239 = owl_sign_request_response::another_ref(
                            &parseval,
                        );
                        match owl_sign_request_response::another_ref(&owl_parsed_caseval239) {
                            owl_sign_request_response::owl__res(tmp_owl__240) => {
                                let owl__240 = OwlBuf::another_ref(&tmp_owl__240);
                                (owl_unit(), Tracked(itree))
                            },
                            owl_sign_request_response::owl__req(tmp_owl_hh241) => {
                                let owl_hh241 = SecretBuf::another_ref(&tmp_owl_hh241);
                                let tmp_owl_declassified_buf103242 = {
                                    let tracked owl_declassify_tok243 = consume_itree_declassify::<
                                        ((), state_PFA),
                                        Endpoint,
                                    >(&mut itree);
                                    {
                                        SecretBuf::another_ref(&owl_hh241).declassify(
                                            Tracked(owl_declassify_tok243),
                                        )
                                    }
                                };
                                let owl_declassified_buf103242 = OwlBuf::another_ref(
                                    &tmp_owl_declassified_buf103242,
                                );
                                let tmp_owl_signed244 = {
                                    owl_sign(
                                        SecretBuf::another_ref(
                                            &SecretBuf::another_ref(&self.owl_skPFA),
                                        ),
                                        OwlBuf::another_ref(
                                            &OwlBuf::from_vec(
                                                serialize_owl_signed_by_PFA(
                                                    &owl__signed_by_PFA_hash(
                                                        OwlBuf::another_ref(
                                                            &owl_declassified_buf103242,
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    )
                                };
                                let owl_signed244 = OwlBuf::from_vec(tmp_owl_signed244);
                                let tmp_owl_declassified_buf107245 = {
                                    let tracked owl_declassify_tok246 = consume_itree_declassify::<
                                        ((), state_PFA),
                                        Endpoint,
                                    >(&mut itree);
                                    {
                                        SecretBuf::another_ref(
                                            &OwlBuf::from_vec(
                                                serialize_owl_sign_request_response(
                                                    &owl__res(OwlBuf::another_ref(&owl_signed244)),
                                                ),
                                            ).into_secret(),
                                        ).declassify(Tracked(owl_declassify_tok246))
                                    }
                                };
                                let owl_declassified_buf107245 = OwlBuf::another_ref(
                                    &tmp_owl_declassified_buf107245,
                                );
                                let tmp_owl_msg_to_send_PDIS247 = {
                                    let tmp_owl_coins248 = effects.owl_sample::<((), state_PFA)>(
                                        Tracked(&mut itree),
                                        NONCE_SIZE,
                                    );
                                    let owl_coins248 = SecretBuf::another_ref(&tmp_owl_coins248);
                                    owl_enc(
                                        SecretBuf::another_ref(&owl_k11281),
                                        SecretBuf::another_ref(
                                            &OwlBuf::from_vec(
                                                serialize_owl_sign_request_response(
                                                    &owl__res(
                                                        OwlBuf::another_ref(
                                                            &owl_declassified_buf107245,
                                                        ),
                                                    ),
                                                ),
                                            ).into_secret(),
                                        ),
                                        SecretBuf::another_ref(&owl_coins248),
                                    )
                                };
                                let owl_msg_to_send_PDIS247 = OwlBuf::from_vec(
                                    tmp_owl_msg_to_send_PDIS247,
                                );
                                let owl__249 = {
                                    effects.owl_output::<((), state_PFA)>(
                                        Tracked(&mut itree),
                                        owl_msg_to_send_PDIS247.as_slice(),
                                        Some(&PDIS_addr()),
                                        &PFA_addr(),
                                    );
                                };
                                (owl_unit(), Tracked(itree))
                            },
                        }
                    } else {
                        (owl_unit(), Tracked(itree))
                    }
                },
            }
        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub struct state_SDIS {}

impl state_SDIS {
    #[verifier::external_body]
    pub fn init_state_SDIS() -> Self {
        state_SDIS {  }
    }
}

pub struct cfg_SDIS<'SDIS> {
    pub owl_skSDIS: SecretBuf<'SDIS>,
    pub owl_c: SecretBuf<'SDIS>,
    pub pk_owl_skSDIS: OwlBuf<'SDIS>,
    pub pk_owl_skPDIS: OwlBuf<'SDIS>,
    pub pk_owl_skPFA: OwlBuf<'SDIS>,
    pub pk_owl_c: OwlBuf<'SDIS>,
    pub pk_owl_b1: OwlBuf<'SDIS>,
    pub pk_owl_b: OwlBuf<'SDIS>,
    pub pk_owl_a: OwlBuf<'SDIS>,
}

impl cfg_SDIS<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_SDIS_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_SDIS), Endpoint>>,
        mut_state: &mut state_SDIS,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_SDIS), Endpoint>>), OwlError>)
        requires
            itree.view() == SDIS_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_SDIS), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(SDIS_main_spec);

            owl_call_ret_unit!(effects, itree, *mut_state, SDIS_actual_spec(*self, *mut_state), self.owl_SDIS_actual(mut_state))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_SDIS_actual<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_SDIS), Endpoint>>,
        mut_state: &mut state_SDIS,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_SDIS), Endpoint>>), OwlError>)
        requires
            itree.view() == SDIS_actual_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_SDIS), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(SDIS_actual_spec);
            let tmp_owl_g_pow_c250 = {
                owl_dhpk(SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_c)))
            };
            let owl_g_pow_c250 = OwlBuf::from_vec(tmp_owl_g_pow_c250);
            let tmp_owl_signed_g_pow_c251 = {
                owl_sign(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skSDIS)),
                    OwlBuf::another_ref(&owl_g_pow_c250),
                )
            };
            let owl_signed_g_pow_c251 = OwlBuf::from_vec(tmp_owl_signed_g_pow_c251);
            let owl__252 = {
                effects.owl_output::<((), state_SDIS)>(
                    Tracked(&mut itree),
                    serialize_owl_sdis_msg(
                        &owl_sdis_msg(
                            OwlBuf::another_ref(&owl_g_pow_c250),
                            OwlBuf::another_ref(&owl_signed_g_pow_c251),
                        ),
                    ).as_slice(),
                    Some(&PDIS_addr()),
                    &SDIS_addr(),
                );
            };
            let (tmp_owl_inp254, owl__253) = {
                effects.owl_input::<((), state_SDIS)>(Tracked(&mut itree))
            };
            let owl_inp254 = OwlBuf::from_vec(tmp_owl_inp254);
            let tmp_owl_vkPDIS255 = { OwlBuf::another_ref(&self.pk_owl_skPDIS) };
            let owl_vkPDIS255 = OwlBuf::another_ref(&tmp_owl_vkPDIS255);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp254);
            if let Some(parseval) = parse_owl_pdis_msg2(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_pdis1_2257 = OwlBuf::another_ref(&parseval.owl__pdis1_2);
                let owl_pdis2_2256 = OwlBuf::another_ref(&parseval.owl__pdis2_2);
                let tmp_owl_caseval258 = {
                    let tracked owl_declassify_tok259 = consume_itree_declassify::<
                        ((), state_SDIS),
                        Endpoint,
                    >(&mut itree);
                    owl_vrfy(
                        OwlBuf::another_ref(&owl_vkPDIS255),
                        SecretBuf::another_ref(&SecretBuf::from_buf(owl_pdis1_2257.another_ref())),
                        OwlBuf::another_ref(&owl_pdis2_2256),
                        Tracked(owl_declassify_tok259),
                    )
                };
                let owl_caseval258 = SecretBuf::another_ref_option(&tmp_owl_caseval258);
                match SecretBuf::another_ref_option(&owl_caseval258) {
                    Option::None => { (owl_unit(), Tracked(itree)) },
                    Option::Some(tmp_owl_m260) => {
                        let owl_m260 = SecretBuf::another_ref(&tmp_owl_m260);
                        let tmp_owl_declassified_buf140261 = {
                            let tracked owl_declassify_tok262 = consume_itree_declassify::<
                                ((), state_SDIS),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_m260).declassify(
                                    Tracked(owl_declassify_tok262),
                                )
                            }
                        };
                        let owl_declassified_buf140261 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf140261,
                        );
                        let parseval_tmp = OwlBuf::another_ref(&owl_declassified_buf140261);
                        if let Some(parseval) = parse_owl_dhpk_b(
                            OwlBuf::another_ref(&parseval_tmp),
                        ) {
                            let owl_parsed_caseval263 = owl_dhpk_b::another_ref(&parseval);
                            match owl_dhpk_b::another_ref(&owl_parsed_caseval263) {
                                owl_dhpk_b::owl__comm_with_pfa(tmp_owl__264) => {
                                    let owl__264 = OwlBuf::another_ref(&tmp_owl__264);
                                    (owl_unit(), Tracked(itree))
                                },
                                owl_dhpk_b::owl__comm_with_sdis(tmp_owl_g_pow_b1265) => {
                                    let owl_g_pow_b1265 = OwlBuf::another_ref(&tmp_owl_g_pow_b1265);

                                    if !(owl_is_group_elem(
                                        SecretBuf::from_buf(owl_g_pow_b1265.another_ref()),
                                    )) {
                                        (owl_unit(), Tracked(itree))
                                    } else {
                                        {
                                            let tmp_owl_ss266 = {
                                                owl_dh_combine(
                                                    SecretBuf::from_buf(
                                                        owl_g_pow_b1265.another_ref(),
                                                    ),
                                                    SecretBuf::another_ref(
                                                        &SecretBuf::another_ref(&self.owl_c),
                                                    ),
                                                )
                                            };
                                            let owl_ss266 = SecretBuf::another_ref(&tmp_owl_ss266);
                                            let tmp_owl_kdfval131267 = {
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
                                                    SecretBuf::another_ref(&owl_ss266),
                                                    OwlBuf::another_ref(
                                                        &{
                                                            let x = mk_vec_u8![0x02u8 ];
                                                            OwlBuf::from_vec(x)
                                                        },
                                                    ),
                                                )
                                            };
                                            let owl_kdfval131267 = SecretBuf::another_ref(
                                                &tmp_owl_kdfval131267,
                                            );
                                            let tmp_owl_k268 = {
                                                {
                                                    SecretBuf::another_ref(
                                                        &owl_kdfval131267,
                                                    ).subrange(0, 0 + ENCKEY_SIZE)
                                                }
                                            };
                                            let owl_k268 = SecretBuf::another_ref(&tmp_owl_k268);
                                            let (tmp_owl_inp2270, owl__269) = {
                                                effects.owl_input::<((), state_SDIS)>(
                                                    Tracked(&mut itree),
                                                )
                                            };
                                            let owl_inp2270 = OwlBuf::from_vec(tmp_owl_inp2270);
                                            let tmp_owl_caseval271 = {
                                                let tracked owl_declassify_tok272 =
                                                    consume_itree_declassify::<
                                                    ((), state_SDIS),
                                                    Endpoint,
                                                >(&mut itree);
                                                owl_dec(
                                                    SecretBuf::another_ref(&owl_k268),
                                                    OwlBuf::another_ref(&owl_inp2270),
                                                    Tracked(owl_declassify_tok272),
                                                )
                                            };
                                            let owl_caseval271 = SecretBuf::another_ref_option(
                                                &tmp_owl_caseval271,
                                            );
                                            match SecretBuf::another_ref_option(&owl_caseval271) {
                                                Option::None => { (owl_unit(), Tracked(itree)) },
                                                Option::Some(tmp_owl_m__273) => {
                                                    let owl_m__273 = SecretBuf::another_ref(
                                                        &tmp_owl_m__273,
                                                    );
                                                    (owl_unit(), Tracked(itree))
                                                },
                                            }
                                        }
                                    }

                                },
                            }
                        } else {
                            (owl_unit(), Tracked(itree))
                        }
                    },
                }
            } else {
                (owl_unit(), Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }
}

} // verus!
