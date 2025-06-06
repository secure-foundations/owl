// Extracted verus code from file owl_toy_protocols/ns-sym-indexed.owl:
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
pub enum owlSpec_KABEnum {
    owlSpec_Other(Seq<u8>),
    owlSpec_nonceB(Seq<u8>),
}

use owlSpec_KABEnum::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_KABEnum(x: Seq<u8>) -> Option<owlSpec_KABEnum> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Tail), (Tag::spec_new(U8, 2), Variable(12)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owlSpec_KABEnum::owlSpec_Other(x),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_KABEnum::owlSpec_nonceB(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_KABEnum_inner(x: owlSpec_KABEnum) -> Option<Seq<u8>> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Tail), (Tag::spec_new(U8, 2), Variable(12)));
    match x {
        owlSpec_KABEnum::owlSpec_Other(x) => {
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
        owlSpec_KABEnum::owlSpec_nonceB(x) => {
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
pub closed spec fn serialize_owlSpec_KABEnum(x: owlSpec_KABEnum) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_KABEnum_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_KABEnum {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_KABEnum(self)
    }
}

pub open spec fn Other(x: Seq<u8>) -> owlSpec_KABEnum {
    crate::owlSpec_KABEnum::owlSpec_Other(x)
}

pub open spec fn nonceB(x: Seq<u8>) -> owlSpec_KABEnum {
    crate::owlSpec_KABEnum::owlSpec_nonceB(x)
}

pub open spec fn Other_enumtest(x: owlSpec_KABEnum) -> bool {
    match x {
        owlSpec_KABEnum::owlSpec_Other(_) => true,
        _ => false,
    }
}

pub open spec fn nonceB_enumtest(x: owlSpec_KABEnum) -> bool {
    match x {
        owlSpec_KABEnum::owlSpec_nonceB(_) => true,
        _ => false,
    }
}

spec fn spec_combinator_owlSpec_kB_message() -> (Variable, Variable) {
    let field_1 = Variable(32);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_kB_message() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_kB_message(),
{
    let field_1 = Variable(32);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_kB_message {
    pub owlSpec__kAB1: Seq<u8>,
    pub owlSpec__A: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_kB_message(x: Seq<u8>) -> Option<owlSpec_kB_message> {
    let spec_comb = spec_combinator_owlSpec_kB_message();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__kAB1, owlSpec__A)) = parsed;
        Some(owlSpec_kB_message { owlSpec__kAB1, owlSpec__A })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kB_message_inner(x: owlSpec_kB_message) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__kAB1.len(), x.owlSpec__A.len() ] {
        let spec_comb = spec_combinator_owlSpec_kB_message();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__kAB1, x.owlSpec__A))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kB_message(x: owlSpec_kB_message) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_kB_message_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_kB_message {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_kB_message(self)
    }
}

pub open spec fn kB_message(
    arg_owlSpec__kAB1: Seq<u8>,
    arg_owlSpec__A: Seq<u8>,
) -> owlSpec_kB_message {
    owlSpec_kB_message { owlSpec__kAB1: arg_owlSpec__kAB1, owlSpec__A: arg_owlSpec__A }
}

spec fn spec_combinator_owlSpec_secret_kB_message() -> (Variable, Variable) {
    let field_1 = Variable(32);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_secret_kB_message() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_kB_message(),
{
    let field_1 = Variable(32);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_secret_kB_message {
    pub owlSpec__kAB1: Seq<u8>,
    pub owlSpec__A: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_kB_message(x: Seq<u8>) -> Option<
    owlSpec_secret_kB_message,
> {
    let spec_comb = spec_combinator_owlSpec_secret_kB_message();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__kAB1, owlSpec__A)) = parsed;
        Some(owlSpec_secret_kB_message { owlSpec__kAB1, owlSpec__A })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kB_message_inner(
    x: owlSpec_secret_kB_message,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__kAB1.len(), x.owlSpec__A.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_kB_message();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__kAB1, x.owlSpec__A))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kB_message(x: owlSpec_secret_kB_message) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_secret_kB_message_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_kB_message {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_kB_message(self)
    }
}

pub open spec fn secret_kB_message(
    arg_owlSpec__kAB1: Seq<u8>,
    arg_owlSpec__A: Seq<u8>,
) -> owlSpec_secret_kB_message {
    owlSpec_secret_kB_message { owlSpec__kAB1: arg_owlSpec__kAB1, owlSpec__A: arg_owlSpec__A }
}

spec fn spec_combinator_owlSpec_kA_message() -> (((Variable, Variable), Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    let field_4 = Variable(60);
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_kA_message() -> (res: (((Variable, Variable), Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_kA_message(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    let field_4 = Variable(60);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_kA_message {
    pub owlSpec__nA: Seq<u8>,
    pub owlSpec__kAB2: Seq<u8>,
    pub owlSpec__B: Seq<u8>,
    pub owlSpec__x: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_kA_message(x: Seq<u8>) -> Option<owlSpec_kA_message> {
    let spec_comb = spec_combinator_owlSpec_kA_message();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec__nA, owlSpec__kAB2), owlSpec__B), owlSpec__x)) = parsed;
        Some(owlSpec_kA_message { owlSpec__nA, owlSpec__kAB2, owlSpec__B, owlSpec__x })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kA_message_inner(x: owlSpec_kA_message) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__nA.len(), x.owlSpec__kAB2.len(), x.owlSpec__B.len(), x.owlSpec__x.len() ] {
        let spec_comb = spec_combinator_owlSpec_kA_message();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec__nA, x.owlSpec__kAB2), x.owlSpec__B), x.owlSpec__x)),
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
pub closed spec fn serialize_owlSpec_kA_message(x: owlSpec_kA_message) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_kA_message_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_kA_message {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_kA_message(self)
    }
}

pub open spec fn kA_message(
    arg_owlSpec__nA: Seq<u8>,
    arg_owlSpec__kAB2: Seq<u8>,
    arg_owlSpec__B: Seq<u8>,
    arg_owlSpec__x: Seq<u8>,
) -> owlSpec_kA_message {
    owlSpec_kA_message {
        owlSpec__nA: arg_owlSpec__nA,
        owlSpec__kAB2: arg_owlSpec__kAB2,
        owlSpec__B: arg_owlSpec__B,
        owlSpec__x: arg_owlSpec__x,
    }
}

spec fn spec_combinator_owlSpec_secret_kA_message() -> (
    ((Variable, Variable), Variable),
    Variable,
) {
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    let field_4 = Variable(60);
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_secret_kA_message() -> (res: (
    ((Variable, Variable), Variable),
    Variable,
))
    ensures
        res.view() == spec_combinator_owlSpec_secret_kA_message(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    let field_4 = Variable(60);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_secret_kA_message {
    pub owlSpec__nA: Seq<u8>,
    pub owlSpec__kAB2: Seq<u8>,
    pub owlSpec__B: Seq<u8>,
    pub owlSpec__x: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_kA_message(x: Seq<u8>) -> Option<
    owlSpec_secret_kA_message,
> {
    let spec_comb = spec_combinator_owlSpec_secret_kA_message();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec__nA, owlSpec__kAB2), owlSpec__B), owlSpec__x)) = parsed;
        Some(owlSpec_secret_kA_message { owlSpec__nA, owlSpec__kAB2, owlSpec__B, owlSpec__x })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kA_message_inner(
    x: owlSpec_secret_kA_message,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__nA.len(), x.owlSpec__kAB2.len(), x.owlSpec__B.len(), x.owlSpec__x.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_kA_message();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec__nA, x.owlSpec__kAB2), x.owlSpec__B), x.owlSpec__x)),
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
pub closed spec fn serialize_owlSpec_secret_kA_message(x: owlSpec_secret_kA_message) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_secret_kA_message_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_kA_message {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_kA_message(self)
    }
}

pub open spec fn secret_kA_message(
    arg_owlSpec__nA: Seq<u8>,
    arg_owlSpec__kAB2: Seq<u8>,
    arg_owlSpec__B: Seq<u8>,
    arg_owlSpec__x: Seq<u8>,
) -> owlSpec_secret_kA_message {
    owlSpec_secret_kA_message {
        owlSpec__nA: arg_owlSpec__nA,
        owlSpec__kAB2: arg_owlSpec__kAB2,
        owlSpec__B: arg_owlSpec__B,
        owlSpec__x: arg_owlSpec__x,
    }
}

spec fn spec_combinator_owlSpec_msg1_AtoS() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_msg1_AtoS() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_msg1_AtoS(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_msg1_AtoS {
    pub owlSpec_msg1_A: Seq<u8>,
    pub owlSpec_msg1_B: Seq<u8>,
    pub owlSpec_msg1_nA: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_msg1_AtoS(x: Seq<u8>) -> Option<owlSpec_msg1_AtoS> {
    let spec_comb = spec_combinator_owlSpec_msg1_AtoS();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec_msg1_A, owlSpec_msg1_B), owlSpec_msg1_nA)) = parsed;
        Some(owlSpec_msg1_AtoS { owlSpec_msg1_A, owlSpec_msg1_B, owlSpec_msg1_nA })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_msg1_AtoS_inner(x: owlSpec_msg1_AtoS) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_msg1_A.len(), x.owlSpec_msg1_B.len(), x.owlSpec_msg1_nA.len() ] {
        let spec_comb = spec_combinator_owlSpec_msg1_AtoS();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec_msg1_A, x.owlSpec_msg1_B), x.owlSpec_msg1_nA)),
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
pub closed spec fn serialize_owlSpec_msg1_AtoS(x: owlSpec_msg1_AtoS) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_msg1_AtoS_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_msg1_AtoS {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg1_AtoS(self)
    }
}

pub open spec fn msg1_AtoS(
    arg_owlSpec_msg1_A: Seq<u8>,
    arg_owlSpec_msg1_B: Seq<u8>,
    arg_owlSpec_msg1_nA: Seq<u8>,
) -> owlSpec_msg1_AtoS {
    owlSpec_msg1_AtoS {
        owlSpec_msg1_A: arg_owlSpec_msg1_A,
        owlSpec_msg1_B: arg_owlSpec_msg1_B,
        owlSpec_msg1_nA: arg_owlSpec_msg1_nA,
    }
}

pub enum owlSpec_alice_result {
    owlSpec_alice_None(),
    owlSpec_alice_Some(Seq<u8>),
}

use owlSpec_alice_result::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_alice_result(x: Seq<u8>) -> Option<owlSpec_alice_result> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(32)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owlSpec_alice_result::owlSpec_alice_None(),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_alice_result::owlSpec_alice_Some(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_alice_result_inner(x: owlSpec_alice_result) -> Option<
    Seq<u8>,
> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(32)));
    match x {
        owlSpec_alice_result::owlSpec_alice_None() => {
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
        owlSpec_alice_result::owlSpec_alice_Some(x) => {
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
pub closed spec fn serialize_owlSpec_alice_result(x: owlSpec_alice_result) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_alice_result_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_alice_result {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_alice_result(self)
    }
}

pub open spec fn alice_None() -> owlSpec_alice_result {
    crate::owlSpec_alice_result::owlSpec_alice_None()
}

pub open spec fn alice_Some(x: Seq<u8>) -> owlSpec_alice_result {
    crate::owlSpec_alice_result::owlSpec_alice_Some(x)
}

pub open spec fn alice_None_enumtest(x: owlSpec_alice_result) -> bool {
    match x {
        owlSpec_alice_result::owlSpec_alice_None() => true,
        _ => false,
    }
}

pub open spec fn alice_Some_enumtest(x: owlSpec_alice_result) -> bool {
    match x {
        owlSpec_alice_result::owlSpec_alice_Some(_) => true,
        _ => false,
    }
}

pub enum owlSpec_bob_result {
    owlSpec_bob_None(),
    owlSpec_bob_Some(Seq<u8>),
}

use owlSpec_bob_result::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_bob_result(x: Seq<u8>) -> Option<owlSpec_bob_result> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(32)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owlSpec_bob_result::owlSpec_bob_None(),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_bob_result::owlSpec_bob_Some(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_bob_result_inner(x: owlSpec_bob_result) -> Option<Seq<u8>> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(32)));
    match x {
        owlSpec_bob_result::owlSpec_bob_None() => {
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
        owlSpec_bob_result::owlSpec_bob_Some(x) => {
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
pub closed spec fn serialize_owlSpec_bob_result(x: owlSpec_bob_result) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_bob_result_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_bob_result {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_bob_result(self)
    }
}

pub open spec fn bob_None() -> owlSpec_bob_result {
    crate::owlSpec_bob_result::owlSpec_bob_None()
}

pub open spec fn bob_Some(x: Seq<u8>) -> owlSpec_bob_result {
    crate::owlSpec_bob_result::owlSpec_bob_Some(x)
}

pub open spec fn bob_None_enumtest(x: owlSpec_bob_result) -> bool {
    match x {
        owlSpec_bob_result::owlSpec_bob_None() => true,
        _ => false,
    }
}

pub open spec fn bob_Some_enumtest(x: owlSpec_bob_result) -> bool {
    match x {
        owlSpec_bob_result::owlSpec_bob_Some(_) => true,
        _ => false,
    }
}

#[verifier::opaque]
pub open spec fn AS_main_spec(cfg: cfg_AS, mut_state: state_AS) -> (res: ITree<
    ((), state_AS),
    Endpoint,
>) {
    owl_spec!(mut_state, state_AS,
        (input(inp,_16)) in
(parse (parse_owlSpec_msg1_AtoS(inp)) as (owlSpec_msg1_AtoS{owlSpec_msg1_A : A_, owlSpec_msg1_B : B_, owlSpec_msg1_nA : nA_}) in {
let kAB = ((ret(cfg.owl_KAB.view()))) in
let kAB_ = ((ret(kAB))) in
let kA = ((ret(cfg.owl_KA.view()))) in
let kB = ((ret(cfg.owl_KB.view()))) in
let encm1 = ((sample(NONCE_SIZE, enc(kB, serialize_owlSpec_kB_message(kB_message(kAB_, A_)))))) in
let encm2 = ((sample(NONCE_SIZE, enc(kA, serialize_owlSpec_kA_message(kA_message(nA_, kAB_, B_, encm1)))))) in
(output (encm2) to (Some(Endpoint::Loc_Alice))) in
(ret(()))
} otherwise ((output (empty_seq_u8()) to (Some(Endpoint::Loc_Alice))) in
(ret(()))))
    )
}

#[verifier::opaque]
pub open spec fn Alice_main_spec(cfg: cfg_Alice, mut_state: state_Alice) -> (res: ITree<
    (owlSpec_alice_result, state_Alice),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Alice,
        let A = ((ret(cfg.owl_A_username.view()))) in
let B = ((ret(cfg.owl_B_username.view()))) in
let kA = ((ret(cfg.owl_KA.view()))) in
let nA = ((ret(cfg.owl_NA.view()))) in
let declassified_buf38 = ((declassify(DeclassifyingOp::ControlFlow(A))) in
(ret((A)))) in
let declassified_buf41 = ((declassify(DeclassifyingOp::ControlFlow(B))) in
(ret((B)))) in
let declassified_buf44 = ((declassify(DeclassifyingOp::ControlFlow(nA))) in
(ret((nA)))) in
(output (serialize_owlSpec_msg1_AtoS(msg1_AtoS(declassified_buf38, declassified_buf41, declassified_buf44))) to (Some(Endpoint::Loc_AS))) in
(input(inp,_48)) in
let caseval = ((declassify(DeclassifyingOp::ADec(kA, inp))) in
(ret(dec(kA, inp)))) in
(case (caseval) {
| None => {
(ret(alice_None()))
},
| Some(res) => {
(parse (parse_owlSpec_secret_kA_message(res)) as (owlSpec_secret_kA_message{owlSpec__nA : nA_, owlSpec__kAB2 : kAB, owlSpec__B : B_, owlSpec__x : m1}) in {
let declassified_buf66 = ((declassify(DeclassifyingOp::ControlFlow(nA_))) in
(ret((nA_)))) in
let declassified_buf69 = ((declassify(DeclassifyingOp::ControlFlow(B_))) in
(ret((B_)))) in
let declassified_buf72 = ((declassify(DeclassifyingOp::ControlFlow(m1))) in
(ret((m1)))) in
let kAB_ = ((ret(kAB))) in
(output (declassified_buf72) to (Some(Endpoint::Loc_Bob))) in
(input(inp2,_78)) in
let _assert_114 = ((ret(ghost_unit()))) in
let caseval = ((declassify(DeclassifyingOp::ADec(kAB_, inp2))) in
(ret(dec(kAB_, inp2)))) in
(case (caseval) {
| None => {
(ret(alice_None()))
},
| Some(res2) => {
let nB_ = ((ret(res2))) in
let encm = ((sample(NONCE_SIZE, enc(kAB_, nB_)))) in
(output (encm) to (Some(Endpoint::Loc_Bob))) in
(ret(alice_Some(kAB_)))
},
}
)
} otherwise ((ret(alice_None()))))
},
}
)
    )
}

#[verifier::opaque]
pub open spec fn Bob_main_spec(cfg: cfg_Bob, mut_state: state_Bob) -> (res: ITree<
    (owlSpec_bob_result, state_Bob),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Bob,
        let kB = ((ret(cfg.owl_KB.view()))) in
(input(inp,_89)) in
let caseval = ((declassify(DeclassifyingOp::ADec(kB, inp))) in
(ret(dec(kB, inp)))) in
(case (caseval) {
| None => {
(ret(bob_None()))
},
| Some(res) => {
(parse (parse_owlSpec_secret_kB_message(res)) as (owlSpec_secret_kB_message{owlSpec__kAB1 : kAB, owlSpec__A : A_}) in {
let declassified_buf103 = ((declassify(DeclassifyingOp::ControlFlow(A_))) in
(ret((A_)))) in
let kAB_ = ((ret(kAB))) in
let m = ((ret(nonceB(cfg.owl_NB.view())))) in
let encm = ((sample(NONCE_SIZE, enc(kAB_, serialize_owlSpec_KABEnum(m))))) in
(output (encm) to (Some(Endpoint::Loc_Alice))) in
(input(inp2,_112)) in
let caseval = ((declassify(DeclassifyingOp::ADec(kAB_, inp2))) in
(ret(dec(kAB_, inp2)))) in
(case (caseval) {
| None => {
(ret(bob_None()))
},
| Some(res2) => {
let _assert_178 = ((ret(ghost_unit()))) in
let m = ((ret(kAB_))) in
(ret(bob_Some(m)))
},
}
)
} otherwise ((ret(bob_None()))))
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
    Loc_AS,
    Loc_Alice,
    Loc_Bob,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier(external_body)]
pub const fn AS_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_AS,
{
    "127.0.0.1:9001"
}

#[verifier(external_body)]
pub const fn Alice_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_Alice,
{
    "127.0.0.1:9002"
}

#[verifier(external_body)]
pub const fn Bob_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_Bob,
{
    "127.0.0.1:9003"
}

pub enum owl_KABEnum<'a> {
    owl_Other(OwlBuf<'a>),
    owl_nonceB(SecretBuf<'a>),
}

use owl_KABEnum::*;

impl<'a> owl_KABEnum<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_KABEnum<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_Other(x) => owl_Other(OwlBuf::another_ref(x)),
            owl_nonceB(x) => owl_nonceB(SecretBuf::another_ref(x)),
        }
    }
}

impl View for owl_KABEnum<'_> {
    type V = owlSpec_KABEnum;

    open spec fn view(&self) -> owlSpec_KABEnum {
        match self {
            owl_Other(v) => owlSpec_KABEnum::owlSpec_Other(v.view()),
            owl_nonceB(v) => owlSpec_KABEnum::owlSpec_nonceB(v.view()),
        }
    }
}

#[inline]
pub fn owl_Other_enumtest(x: &owl_KABEnum<'_>) -> (res: bool)
    ensures
        res == Other_enumtest(x.view()),
{
    match x {
        owl_KABEnum::owl_Other(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl_nonceB_enumtest(x: &owl_KABEnum<'_>) -> (res: bool)
    ensures
        res == nonceB_enumtest(x.view()),
{
    match x {
        owl_KABEnum::owl_nonceB(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_KABEnum<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_KABEnum<'a>>)
    ensures
        res is Some ==> parse_owlSpec_KABEnum(arg.view()) is Some,
        res is None ==> parse_owlSpec_KABEnum(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_KABEnum(arg.view())->Some_0,
{
    reveal(parse_owlSpec_KABEnum);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Tail), (Tag::new(U8, 2), Variable(12)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owl_KABEnum::owl_Other(OwlBuf::another_ref(&x)),
            inj_ord_choice_pat!(*, (_,x)) => owl_KABEnum::owl_nonceB(
                SecretBuf::from_buf(x.another_ref()),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_KABEnum<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_KABEnum<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_KABEnum(arg.view()) is Some,
        res is None ==> parse_owlSpec_KABEnum(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_KABEnum(arg.view())->Some_0,
{
    reveal(parse_owlSpec_KABEnum);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_KABEnum_inner(arg: &owl_KABEnum) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_KABEnum_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_KABEnum_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_KABEnum_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_KABEnum(arg: &owl_KABEnum) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_KABEnum(arg.view()),
{
    reveal(serialize_owlSpec_KABEnum);
    let res = serialize_owl_KABEnum_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_kB_message<'a> {
    pub owl__kAB1: SecretBuf<'a>,
    pub owl__A: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_kB_message<'a>(arg_owl__kAB1: SecretBuf<'a>, arg_owl__A: OwlBuf<'a>) -> (res:
    owl_kB_message<'a>)
    ensures
        res.owl__kAB1.view() == arg_owl__kAB1.view(),
        res.owl__A.view() == arg_owl__A.view(),
{
    owl_kB_message { owl__kAB1: arg_owl__kAB1, owl__A: arg_owl__A }
}

impl<'a> owl_kB_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kB_message<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_kB_message {
            owl__kAB1: SecretBuf::another_ref(&self.owl__kAB1),
            owl__A: OwlBuf::another_ref(&self.owl__A),
        }
    }
}

impl View for owl_kB_message<'_> {
    type V = owlSpec_kB_message;

    open spec fn view(&self) -> owlSpec_kB_message {
        owlSpec_kB_message { owlSpec__kAB1: self.owl__kAB1.view(), owlSpec__A: self.owl__A.view() }
    }
}

pub exec fn parse_owl_kB_message<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_kB_message<'a>>)
    ensures
        res is Some ==> parse_owlSpec_kB_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_kB_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kB_message(arg.view())->Some_0,
{
    reveal(parse_owlSpec_kB_message);
    let exec_comb = exec_combinator_owl_kB_message();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__kAB1, owl__A) = parsed;
        Some(
            owl_kB_message {
                owl__kAB1: SecretBuf::from_buf(owl__kAB1.another_ref()),
                owl__A: OwlBuf::another_ref(&owl__A),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_kB_message_inner<'a>(arg: &owl_kB_message<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_kB_message_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_kB_message_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_kB_message_inner);
    if no_usize_overflows![ arg.owl__kAB1.len(), arg.owl__A.len(), 0 ] {
        let exec_comb = exec_combinator_owl_kB_message();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__kAB1.len() + arg.owl__A.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__kAB1), SecretBuf::from_buf(arg.owl__A.another_ref())),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_kB_message_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_kB_message<'a>(arg: &owl_kB_message<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_kB_message(arg.view()),
{
    reveal(serialize_owlSpec_kB_message);
    let res = serialize_owl_kB_message_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_kB_message<'a> {
    pub owl__kAB1: SecretBuf<'a>,
    pub owl__A: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_kB_message<'a>(arg_owl__kAB1: SecretBuf<'a>, arg_owl__A: SecretBuf<'a>) -> (res:
    owl_secret_kB_message<'a>)
    ensures
        res.owl__kAB1.view() == arg_owl__kAB1.view(),
        res.owl__A.view() == arg_owl__A.view(),
{
    owl_secret_kB_message { owl__kAB1: arg_owl__kAB1, owl__A: arg_owl__A }
}

impl<'a> owl_secret_kB_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_kB_message<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_kB_message {
            owl__kAB1: SecretBuf::another_ref(&self.owl__kAB1),
            owl__A: SecretBuf::another_ref(&self.owl__A),
        }
    }
}

impl View for owl_secret_kB_message<'_> {
    type V = owlSpec_secret_kB_message;

    open spec fn view(&self) -> owlSpec_secret_kB_message {
        owlSpec_secret_kB_message {
            owlSpec__kAB1: self.owl__kAB1.view(),
            owlSpec__A: self.owl__A.view(),
        }
    }
}

pub exec fn parse_owl_secret_kB_message<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_secret_kB_message<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kB_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kB_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kB_message(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kB_message);
    let exec_comb = exec_combinator_owl_secret_kB_message();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__kAB1, owl__A) = parsed;
        Some(
            owl_secret_kB_message {
                owl__kAB1: SecretBuf::from_buf(owl__kAB1.another_ref()),
                owl__A: SecretBuf::from_buf(owl__A.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_kB_message<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_kB_message<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kB_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kB_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kB_message(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kB_message);
    let exec_comb = exec_combinator_owl_secret_kB_message();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (owl__kAB1, owl__A) = parsed;
        Some(
            owl_secret_kB_message {
                owl__kAB1: SecretBuf::another_ref(&owl__kAB1),
                owl__A: SecretBuf::another_ref(&owl__A),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_kB_message_inner<'a>(arg: &owl_secret_kB_message<'a>) -> (res:
    Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_secret_kB_message_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_kB_message_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_secret_kB_message_inner);
    if no_usize_overflows![ arg.owl__kAB1.len(), arg.owl__A.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_kB_message();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__kAB1.len() + arg.owl__A.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__kAB1), SecretBuf::another_ref(&arg.owl__A)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_kB_message_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_kB_message<'a>(arg: &owl_secret_kB_message<'a>) -> (res: SecretBuf<
    'a,
>)
    ensures
        res.view() == serialize_owlSpec_secret_kB_message(arg.view()),
{
    reveal(serialize_owlSpec_secret_kB_message);
    let res = serialize_owl_secret_kB_message_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_kA_message<'a> {
    pub owl__nA: OwlBuf<'a>,
    pub owl__kAB2: SecretBuf<'a>,
    pub owl__B: OwlBuf<'a>,
    pub owl__x: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_kA_message<'a>(
    arg_owl__nA: OwlBuf<'a>,
    arg_owl__kAB2: SecretBuf<'a>,
    arg_owl__B: OwlBuf<'a>,
    arg_owl__x: OwlBuf<'a>,
) -> (res: owl_kA_message<'a>)
    ensures
        res.owl__nA.view() == arg_owl__nA.view(),
        res.owl__kAB2.view() == arg_owl__kAB2.view(),
        res.owl__B.view() == arg_owl__B.view(),
        res.owl__x.view() == arg_owl__x.view(),
{
    owl_kA_message {
        owl__nA: arg_owl__nA,
        owl__kAB2: arg_owl__kAB2,
        owl__B: arg_owl__B,
        owl__x: arg_owl__x,
    }
}

impl<'a> owl_kA_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kA_message<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_kA_message {
            owl__nA: OwlBuf::another_ref(&self.owl__nA),
            owl__kAB2: SecretBuf::another_ref(&self.owl__kAB2),
            owl__B: OwlBuf::another_ref(&self.owl__B),
            owl__x: OwlBuf::another_ref(&self.owl__x),
        }
    }
}

impl View for owl_kA_message<'_> {
    type V = owlSpec_kA_message;

    open spec fn view(&self) -> owlSpec_kA_message {
        owlSpec_kA_message {
            owlSpec__nA: self.owl__nA.view(),
            owlSpec__kAB2: self.owl__kAB2.view(),
            owlSpec__B: self.owl__B.view(),
            owlSpec__x: self.owl__x.view(),
        }
    }
}

pub exec fn parse_owl_kA_message<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_kA_message<'a>>)
    ensures
        res is Some ==> parse_owlSpec_kA_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_kA_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kA_message(arg.view())->Some_0,
{
    reveal(parse_owlSpec_kA_message);
    let exec_comb = exec_combinator_owl_kA_message();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (((owl__nA, owl__kAB2), owl__B), owl__x) = parsed;
        Some(
            owl_kA_message {
                owl__nA: OwlBuf::another_ref(&owl__nA),
                owl__kAB2: SecretBuf::from_buf(owl__kAB2.another_ref()),
                owl__B: OwlBuf::another_ref(&owl__B),
                owl__x: OwlBuf::another_ref(&owl__x),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_kA_message_inner<'a>(arg: &owl_kA_message<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_kA_message_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_kA_message_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_kA_message_inner);
    if no_usize_overflows![ arg.owl__nA.len(), arg.owl__kAB2.len(), arg.owl__B.len(), arg.owl__x.len(), 0 ] {
        let exec_comb = exec_combinator_owl_kA_message();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__nA.len() + arg.owl__kAB2.len() + arg.owl__B.len() + arg.owl__x.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        SecretBuf::from_buf(arg.owl__nA.another_ref()),
                        SecretBuf::another_ref(&arg.owl__kAB2),
                    ),
                    SecretBuf::from_buf(arg.owl__B.another_ref()),
                ),
                SecretBuf::from_buf(arg.owl__x.another_ref()),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_kA_message_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_kA_message<'a>(arg: &owl_kA_message<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_kA_message(arg.view()),
{
    reveal(serialize_owlSpec_kA_message);
    let res = serialize_owl_kA_message_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_kA_message<'a> {
    pub owl__nA: SecretBuf<'a>,
    pub owl__kAB2: SecretBuf<'a>,
    pub owl__B: SecretBuf<'a>,
    pub owl__x: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_kA_message<'a>(
    arg_owl__nA: SecretBuf<'a>,
    arg_owl__kAB2: SecretBuf<'a>,
    arg_owl__B: SecretBuf<'a>,
    arg_owl__x: SecretBuf<'a>,
) -> (res: owl_secret_kA_message<'a>)
    ensures
        res.owl__nA.view() == arg_owl__nA.view(),
        res.owl__kAB2.view() == arg_owl__kAB2.view(),
        res.owl__B.view() == arg_owl__B.view(),
        res.owl__x.view() == arg_owl__x.view(),
{
    owl_secret_kA_message {
        owl__nA: arg_owl__nA,
        owl__kAB2: arg_owl__kAB2,
        owl__B: arg_owl__B,
        owl__x: arg_owl__x,
    }
}

impl<'a> owl_secret_kA_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_kA_message<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_kA_message {
            owl__nA: SecretBuf::another_ref(&self.owl__nA),
            owl__kAB2: SecretBuf::another_ref(&self.owl__kAB2),
            owl__B: SecretBuf::another_ref(&self.owl__B),
            owl__x: SecretBuf::another_ref(&self.owl__x),
        }
    }
}

impl View for owl_secret_kA_message<'_> {
    type V = owlSpec_secret_kA_message;

    open spec fn view(&self) -> owlSpec_secret_kA_message {
        owlSpec_secret_kA_message {
            owlSpec__nA: self.owl__nA.view(),
            owlSpec__kAB2: self.owl__kAB2.view(),
            owlSpec__B: self.owl__B.view(),
            owlSpec__x: self.owl__x.view(),
        }
    }
}

pub exec fn parse_owl_secret_kA_message<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_secret_kA_message<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kA_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kA_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kA_message(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kA_message);
    let exec_comb = exec_combinator_owl_secret_kA_message();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (((owl__nA, owl__kAB2), owl__B), owl__x) = parsed;
        Some(
            owl_secret_kA_message {
                owl__nA: SecretBuf::from_buf(owl__nA.another_ref()),
                owl__kAB2: SecretBuf::from_buf(owl__kAB2.another_ref()),
                owl__B: SecretBuf::from_buf(owl__B.another_ref()),
                owl__x: SecretBuf::from_buf(owl__x.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_kA_message<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_kA_message<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kA_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kA_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kA_message(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kA_message);
    let exec_comb = exec_combinator_owl_secret_kA_message();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (((owl__nA, owl__kAB2), owl__B), owl__x) = parsed;
        Some(
            owl_secret_kA_message {
                owl__nA: SecretBuf::another_ref(&owl__nA),
                owl__kAB2: SecretBuf::another_ref(&owl__kAB2),
                owl__B: SecretBuf::another_ref(&owl__B),
                owl__x: SecretBuf::another_ref(&owl__x),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_kA_message_inner<'a>(arg: &owl_secret_kA_message<'a>) -> (res:
    Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_secret_kA_message_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_kA_message_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_secret_kA_message_inner);
    if no_usize_overflows![ arg.owl__nA.len(), arg.owl__kAB2.len(), arg.owl__B.len(), arg.owl__x.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_kA_message();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__nA.len() + arg.owl__kAB2.len() + arg.owl__B.len() + arg.owl__x.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (SecretBuf::another_ref(&arg.owl__nA), SecretBuf::another_ref(&arg.owl__kAB2)),
                    SecretBuf::another_ref(&arg.owl__B),
                ),
                SecretBuf::another_ref(&arg.owl__x),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_kA_message_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_kA_message<'a>(arg: &owl_secret_kA_message<'a>) -> (res: SecretBuf<
    'a,
>)
    ensures
        res.view() == serialize_owlSpec_secret_kA_message(arg.view()),
{
    reveal(serialize_owlSpec_secret_kA_message);
    let res = serialize_owl_secret_kA_message_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_msg1_AtoS<'a> {
    pub owl_msg1_A: OwlBuf<'a>,
    pub owl_msg1_B: OwlBuf<'a>,
    pub owl_msg1_nA: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg1_AtoS<'a>(
    arg_owl_msg1_A: OwlBuf<'a>,
    arg_owl_msg1_B: OwlBuf<'a>,
    arg_owl_msg1_nA: OwlBuf<'a>,
) -> (res: owl_msg1_AtoS<'a>)
    ensures
        res.owl_msg1_A.view() == arg_owl_msg1_A.view(),
        res.owl_msg1_B.view() == arg_owl_msg1_B.view(),
        res.owl_msg1_nA.view() == arg_owl_msg1_nA.view(),
{
    owl_msg1_AtoS {
        owl_msg1_A: arg_owl_msg1_A,
        owl_msg1_B: arg_owl_msg1_B,
        owl_msg1_nA: arg_owl_msg1_nA,
    }
}

impl<'a> owl_msg1_AtoS<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg1_AtoS<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg1_AtoS {
            owl_msg1_A: OwlBuf::another_ref(&self.owl_msg1_A),
            owl_msg1_B: OwlBuf::another_ref(&self.owl_msg1_B),
            owl_msg1_nA: OwlBuf::another_ref(&self.owl_msg1_nA),
        }
    }
}

impl View for owl_msg1_AtoS<'_> {
    type V = owlSpec_msg1_AtoS;

    open spec fn view(&self) -> owlSpec_msg1_AtoS {
        owlSpec_msg1_AtoS {
            owlSpec_msg1_A: self.owl_msg1_A.view(),
            owlSpec_msg1_B: self.owl_msg1_B.view(),
            owlSpec_msg1_nA: self.owl_msg1_nA.view(),
        }
    }
}

pub exec fn parse_owl_msg1_AtoS<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg1_AtoS<'a>>)
    ensures
        res is Some ==> parse_owlSpec_msg1_AtoS(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg1_AtoS(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg1_AtoS(arg.view())->Some_0,
{
    reveal(parse_owlSpec_msg1_AtoS);
    let exec_comb = exec_combinator_owl_msg1_AtoS();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl_msg1_A, owl_msg1_B), owl_msg1_nA) = parsed;
        Some(
            owl_msg1_AtoS {
                owl_msg1_A: OwlBuf::another_ref(&owl_msg1_A),
                owl_msg1_B: OwlBuf::another_ref(&owl_msg1_B),
                owl_msg1_nA: OwlBuf::another_ref(&owl_msg1_nA),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_msg1_AtoS_inner<'a>(arg: &owl_msg1_AtoS<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_msg1_AtoS_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg1_AtoS_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_msg1_AtoS_inner);
    if no_usize_overflows![ arg.owl_msg1_A.len(), arg.owl_msg1_B.len(), arg.owl_msg1_nA.len(), 0 ] {
        let exec_comb = exec_combinator_owl_msg1_AtoS();
        let mut obuf = vec_u8_of_len(
            arg.owl_msg1_A.len() + arg.owl_msg1_B.len() + arg.owl_msg1_nA.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (OwlBuf::another_ref(&arg.owl_msg1_A), OwlBuf::another_ref(&arg.owl_msg1_B)),
                OwlBuf::another_ref(&arg.owl_msg1_nA),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_msg1_AtoS_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_msg1_AtoS<'a>(arg: &owl_msg1_AtoS<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_msg1_AtoS(arg.view()),
{
    reveal(serialize_owlSpec_msg1_AtoS);
    let res = serialize_owl_msg1_AtoS_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_alice_result<'a> {
    owl_alice_None(),
    owl_alice_Some(SecretBuf<'a>),
}

use owl_alice_result::*;

impl<'a> owl_alice_result<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_alice_result<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_alice_None() => owl_alice_None(),
            owl_alice_Some(x) => owl_alice_Some(SecretBuf::another_ref(x)),
        }
    }
}

impl View for owl_alice_result<'_> {
    type V = owlSpec_alice_result;

    open spec fn view(&self) -> owlSpec_alice_result {
        match self {
            owl_alice_None() => owlSpec_alice_result::owlSpec_alice_None(),
            owl_alice_Some(v) => owlSpec_alice_result::owlSpec_alice_Some(v.view()),
        }
    }
}

#[inline]
pub fn owl_alice_None_enumtest(x: &owl_alice_result<'_>) -> (res: bool)
    ensures
        res == alice_None_enumtest(x.view()),
{
    match x {
        owl_alice_result::owl_alice_None() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_alice_Some_enumtest(x: &owl_alice_result<'_>) -> (res: bool)
    ensures
        res == alice_Some_enumtest(x.view()),
{
    match x {
        owl_alice_result::owl_alice_Some(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_alice_result<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_alice_result<'a>>)
    ensures
        res is Some ==> parse_owlSpec_alice_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_alice_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_alice_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_alice_result);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(0)), (Tag::new(U8, 2), Variable(32)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owl_alice_result::owl_alice_None(),
            inj_ord_choice_pat!(*, (_,x)) => owl_alice_result::owl_alice_Some(
                SecretBuf::from_buf(x.another_ref()),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_alice_result<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_alice_result<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_alice_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_alice_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_alice_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_alice_result);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_alice_result_inner(arg: &owl_alice_result) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_alice_result_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_alice_result_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_alice_result_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_alice_result(arg: &owl_alice_result) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_alice_result(arg.view()),
{
    reveal(serialize_owlSpec_alice_result);
    let res = serialize_owl_alice_result_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_bob_result<'a> {
    owl_bob_None(),
    owl_bob_Some(SecretBuf<'a>),
}

use owl_bob_result::*;

impl<'a> owl_bob_result<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_bob_result<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_bob_None() => owl_bob_None(),
            owl_bob_Some(x) => owl_bob_Some(SecretBuf::another_ref(x)),
        }
    }
}

impl View for owl_bob_result<'_> {
    type V = owlSpec_bob_result;

    open spec fn view(&self) -> owlSpec_bob_result {
        match self {
            owl_bob_None() => owlSpec_bob_result::owlSpec_bob_None(),
            owl_bob_Some(v) => owlSpec_bob_result::owlSpec_bob_Some(v.view()),
        }
    }
}

#[inline]
pub fn owl_bob_None_enumtest(x: &owl_bob_result<'_>) -> (res: bool)
    ensures
        res == bob_None_enumtest(x.view()),
{
    match x {
        owl_bob_result::owl_bob_None() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_bob_Some_enumtest(x: &owl_bob_result<'_>) -> (res: bool)
    ensures
        res == bob_Some_enumtest(x.view()),
{
    match x {
        owl_bob_result::owl_bob_Some(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_bob_result<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_bob_result<'a>>)
    ensures
        res is Some ==> parse_owlSpec_bob_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_bob_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_bob_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_bob_result);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(0)), (Tag::new(U8, 2), Variable(32)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owl_bob_result::owl_bob_None(),
            inj_ord_choice_pat!(*, (_,x)) => owl_bob_result::owl_bob_Some(
                SecretBuf::from_buf(x.another_ref()),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_bob_result<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_bob_result<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_bob_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_bob_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_bob_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_bob_result);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_bob_result_inner(arg: &owl_bob_result) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_bob_result_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_bob_result_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_bob_result_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_bob_result(arg: &owl_bob_result) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_bob_result(arg.view()),
{
    reveal(serialize_owlSpec_bob_result);
    let res = serialize_owl_bob_result_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct state_AS {}

impl state_AS {
    #[verifier::external_body]
    pub fn init_state_AS() -> Self {
        state_AS {  }
    }
}

pub struct cfg_AS<'AS> {
    pub owl_KAB: SecretBuf<'AS>,
    pub owl_KA: SecretBuf<'AS>,
    pub owl_KB: SecretBuf<'AS>,
}

impl cfg_AS<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_AS_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_AS), Endpoint>>,
        mut_state: &mut state_AS,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_AS), Endpoint>>), OwlError>)
        requires
            itree.view() == AS_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_AS), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(AS_main_spec);
            let (tmp_owl_inp136, owl__135) = {
                effects.owl_input::<((), state_AS)>(Tracked(&mut itree))
            };
            let owl_inp136 = OwlBuf::from_vec(tmp_owl_inp136);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp136);
            if let Some(parseval) = parse_owl_msg1_AtoS(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_A_139 = OwlBuf::another_ref(&parseval.owl_msg1_A);
                let owl_B_138 = OwlBuf::another_ref(&parseval.owl_msg1_B);
                let owl_nA_137 = OwlBuf::another_ref(&parseval.owl_msg1_nA);
                let tmp_owl_kAB140 = { SecretBuf::another_ref(&self.owl_KAB) };
                let owl_kAB140 = SecretBuf::another_ref(&tmp_owl_kAB140);
                let tmp_owl_kAB_141 = { SecretBuf::another_ref(&owl_kAB140) };
                let owl_kAB_141 = SecretBuf::another_ref(&tmp_owl_kAB_141);
                let tmp_owl_kA142 = { SecretBuf::another_ref(&self.owl_KA) };
                let owl_kA142 = SecretBuf::another_ref(&tmp_owl_kA142);
                let tmp_owl_kB143 = { SecretBuf::another_ref(&self.owl_KB) };
                let owl_kB143 = SecretBuf::another_ref(&tmp_owl_kB143);
                let tmp_owl_encm1144 = {
                    let tmp_owl_coins145 = effects.owl_sample::<((), state_AS)>(
                        Tracked(&mut itree),
                        NONCE_SIZE,
                    );
                    let owl_coins145 = SecretBuf::another_ref(&tmp_owl_coins145);
                    owl_enc(
                        SecretBuf::another_ref(&owl_kB143),
                        SecretBuf::another_ref(
                            &serialize_owl_kB_message(
                                &owl_kB_message(
                                    SecretBuf::another_ref(&owl_kAB_141),
                                    OwlBuf::another_ref(&owl_A_139),
                                ),
                            ),
                        ),
                        SecretBuf::another_ref(&owl_coins145),
                    )
                };
                let owl_encm1144 = OwlBuf::from_vec(tmp_owl_encm1144);
                let tmp_owl_encm2146 = {
                    let tmp_owl_coins147 = effects.owl_sample::<((), state_AS)>(
                        Tracked(&mut itree),
                        NONCE_SIZE,
                    );
                    let owl_coins147 = SecretBuf::another_ref(&tmp_owl_coins147);
                    owl_enc(
                        SecretBuf::another_ref(&owl_kA142),
                        SecretBuf::another_ref(
                            &serialize_owl_kA_message(
                                &owl_kA_message(
                                    OwlBuf::another_ref(&owl_nA_137),
                                    SecretBuf::another_ref(&owl_kAB_141),
                                    OwlBuf::another_ref(&owl_B_138),
                                    OwlBuf::another_ref(&owl_encm1144),
                                ),
                            ),
                        ),
                        SecretBuf::another_ref(&owl_coins147),
                    )
                };
                let owl_encm2146 = OwlBuf::from_vec(tmp_owl_encm2146);
                let owl__148 = {
                    effects.owl_output::<((), state_AS)>(
                        Tracked(&mut itree),
                        owl_encm2146.as_slice(),
                        Some(&Alice_addr()),
                        &AS_addr(),
                    );
                };
                (owl_unit(), Tracked(itree))
            } else {
                let owl__149 = {
                    effects.owl_output::<((), state_AS)>(
                        Tracked(&mut itree),
                        {
                            let x = mk_vec_u8![];
                            OwlBuf::from_vec(x)
                        }.as_slice(),
                        Some(&Alice_addr()),
                        &AS_addr(),
                    );
                };
                (owl_unit(), Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub struct state_Alice {}

impl state_Alice {
    #[verifier::external_body]
    pub fn init_state_Alice() -> Self {
        state_Alice {  }
    }
}

pub struct cfg_Alice<'Alice> {
    pub owl_B_username: SecretBuf<'Alice>,
    pub owl_A_username: SecretBuf<'Alice>,
    pub owl_NA: SecretBuf<'Alice>,
    pub owl_KA: SecretBuf<'Alice>,
}

impl cfg_Alice<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_Alice_main<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_alice_result, state_Alice), Endpoint>>,
        mut_state: &mut state_Alice,
    ) -> (res: Result<
        (owl_alice_result<'a>, Tracked<ITreeToken<(owlSpec_alice_result, state_Alice), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == Alice_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_alice_result<'a>,
            Tracked<ITreeToken<(owlSpec_alice_result, state_Alice), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(Alice_main_spec);
            let tmp_owl_A150 = { SecretBuf::another_ref(&self.owl_A_username) };
            let owl_A150 = SecretBuf::another_ref(&tmp_owl_A150);
            let tmp_owl_B151 = { SecretBuf::another_ref(&self.owl_B_username) };
            let owl_B151 = SecretBuf::another_ref(&tmp_owl_B151);
            let tmp_owl_kA152 = { SecretBuf::another_ref(&self.owl_KA) };
            let owl_kA152 = SecretBuf::another_ref(&tmp_owl_kA152);
            let tmp_owl_nA153 = { SecretBuf::another_ref(&self.owl_NA) };
            let owl_nA153 = SecretBuf::another_ref(&tmp_owl_nA153);
            let tmp_owl_declassified_buf38154 = {
                let tracked owl_declassify_tok155 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_A150).declassify(Tracked(owl_declassify_tok155)) }
            };
            let owl_declassified_buf38154 = OwlBuf::another_ref(&tmp_owl_declassified_buf38154);
            let tmp_owl_declassified_buf41156 = {
                let tracked owl_declassify_tok157 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_B151).declassify(Tracked(owl_declassify_tok157)) }
            };
            let owl_declassified_buf41156 = OwlBuf::another_ref(&tmp_owl_declassified_buf41156);
            let tmp_owl_declassified_buf44158 = {
                let tracked owl_declassify_tok159 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_nA153).declassify(Tracked(owl_declassify_tok159)) }
            };
            let owl_declassified_buf44158 = OwlBuf::another_ref(&tmp_owl_declassified_buf44158);
            let owl__160 = {
                effects.owl_output::<(owlSpec_alice_result, state_Alice)>(
                    Tracked(&mut itree),
                    serialize_owl_msg1_AtoS(
                        &owl_msg1_AtoS(
                            OwlBuf::another_ref(&owl_declassified_buf38154),
                            OwlBuf::another_ref(&owl_declassified_buf41156),
                            OwlBuf::another_ref(&owl_declassified_buf44158),
                        ),
                    ).as_slice(),
                    Some(&AS_addr()),
                    &Alice_addr(),
                );
            };
            let (tmp_owl_inp162, owl__161) = {
                effects.owl_input::<(owlSpec_alice_result, state_Alice)>(Tracked(&mut itree))
            };
            let owl_inp162 = OwlBuf::from_vec(tmp_owl_inp162);
            let tmp_owl_caseval163 = {
                let tracked owl_declassify_tok164 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                owl_dec(
                    SecretBuf::another_ref(&owl_kA152),
                    OwlBuf::another_ref(&owl_inp162),
                    Tracked(owl_declassify_tok164),
                )
            };
            let owl_caseval163 = SecretBuf::another_ref_option(&tmp_owl_caseval163);
            match SecretBuf::another_ref_option(&owl_caseval163) {
                Option::None => {
                    let owl__165 = { owl_unit() };
                    (owl_alice_result::another_ref(&owl_alice_None()), Tracked(itree))
                },
                Option::Some(tmp_owl_res166) => {
                    let owl_res166 = SecretBuf::another_ref(&tmp_owl_res166);
                    let parseval_tmp = SecretBuf::another_ref(&owl_res166);
                    if let Some(parseval) = secret_parse_owl_secret_kA_message(
                        SecretBuf::another_ref(&parseval_tmp),
                    ) {
                        let owl_nA_170 = SecretBuf::another_ref(&parseval.owl__nA);
                        let owl_kAB169 = SecretBuf::another_ref(&parseval.owl__kAB2);
                        let owl_B_168 = SecretBuf::another_ref(&parseval.owl__B);
                        let owl_m1167 = SecretBuf::another_ref(&parseval.owl__x);
                        let tmp_owl_declassified_buf66171 = {
                            let tracked owl_declassify_tok172 = consume_itree_declassify::<
                                (owlSpec_alice_result, state_Alice),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_nA_170).declassify(
                                    Tracked(owl_declassify_tok172),
                                )
                            }
                        };
                        let owl_declassified_buf66171 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf66171,
                        );
                        let tmp_owl_declassified_buf69173 = {
                            let tracked owl_declassify_tok174 = consume_itree_declassify::<
                                (owlSpec_alice_result, state_Alice),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_B_168).declassify(
                                    Tracked(owl_declassify_tok174),
                                )
                            }
                        };
                        let owl_declassified_buf69173 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf69173,
                        );
                        let tmp_owl_declassified_buf72175 = {
                            let tracked owl_declassify_tok176 = consume_itree_declassify::<
                                (owlSpec_alice_result, state_Alice),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_m1167).declassify(
                                    Tracked(owl_declassify_tok176),
                                )
                            }
                        };
                        let owl_declassified_buf72175 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf72175,
                        );
                        let tmp_owl_kAB_177 = { SecretBuf::another_ref(&owl_kAB169) };
                        let owl_kAB_177 = SecretBuf::another_ref(&tmp_owl_kAB_177);
                        let owl__178 = {
                            effects.owl_output::<(owlSpec_alice_result, state_Alice)>(
                                Tracked(&mut itree),
                                owl_declassified_buf72175.as_slice(),
                                Some(&Bob_addr()),
                                &Alice_addr(),
                            );
                        };
                        let (tmp_owl_inp2180, owl__179) = {
                            effects.owl_input::<(owlSpec_alice_result, state_Alice)>(
                                Tracked(&mut itree),
                            )
                        };
                        let owl_inp2180 = OwlBuf::from_vec(tmp_owl_inp2180);
                        let owl__assert_114181 = { owl_ghost_unit() };
                        let tmp_owl_caseval182 = {
                            let tracked owl_declassify_tok183 = consume_itree_declassify::<
                                (owlSpec_alice_result, state_Alice),
                                Endpoint,
                            >(&mut itree);
                            owl_dec(
                                SecretBuf::another_ref(&owl_kAB_177),
                                OwlBuf::another_ref(&owl_inp2180),
                                Tracked(owl_declassify_tok183),
                            )
                        };
                        let owl_caseval182 = SecretBuf::another_ref_option(&tmp_owl_caseval182);
                        match SecretBuf::another_ref_option(&owl_caseval182) {
                            Option::None => {
                                (owl_alice_result::another_ref(&owl_alice_None()), Tracked(itree))
                            },
                            Option::Some(tmp_owl_res2184) => {
                                let owl_res2184 = SecretBuf::another_ref(&tmp_owl_res2184);
                                let tmp_owl_nB_185 = { SecretBuf::another_ref(&owl_res2184) };
                                let owl_nB_185 = SecretBuf::another_ref(&tmp_owl_nB_185);
                                let tmp_owl_encm186 = {
                                    let tmp_owl_coins187 = effects.owl_sample::<
                                        (owlSpec_alice_result, state_Alice),
                                    >(Tracked(&mut itree), NONCE_SIZE);
                                    let owl_coins187 = SecretBuf::another_ref(&tmp_owl_coins187);
                                    owl_enc(
                                        SecretBuf::another_ref(&owl_kAB_177),
                                        SecretBuf::another_ref(&owl_nB_185),
                                        SecretBuf::another_ref(&owl_coins187),
                                    )
                                };
                                let owl_encm186 = OwlBuf::from_vec(tmp_owl_encm186);
                                let owl__188 = {
                                    effects.owl_output::<(owlSpec_alice_result, state_Alice)>(
                                        Tracked(&mut itree),
                                        owl_encm186.as_slice(),
                                        Some(&Bob_addr()),
                                        &Alice_addr(),
                                    );
                                };
                                (
                                    owl_alice_result::another_ref(
                                        &owl_alice_Some(SecretBuf::another_ref(&owl_kAB_177)),
                                    ),
                                    Tracked(itree),
                                )
                            },
                        }
                    } else {
                        {
                            let owl__189 = { owl_unit() };
                            (owl_alice_result::another_ref(&owl_alice_None()), Tracked(itree))
                        }
                    }
                },
            }
        };
        Ok((owl_alice_result::another_ref(&res_inner), Tracked(itree)))
    }
}

pub struct state_Bob {}

impl state_Bob {
    #[verifier::external_body]
    pub fn init_state_Bob() -> Self {
        state_Bob {  }
    }
}

pub struct cfg_Bob<'Bob> {
    pub owl_NB: SecretBuf<'Bob>,
    pub owl_KB: SecretBuf<'Bob>,
}

impl cfg_Bob<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_Bob_main<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_bob_result, state_Bob), Endpoint>>,
        mut_state: &mut state_Bob,
    ) -> (res: Result<
        (owl_bob_result<'a>, Tracked<ITreeToken<(owlSpec_bob_result, state_Bob), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == Bob_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_bob_result<'a>,
            Tracked<ITreeToken<(owlSpec_bob_result, state_Bob), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(Bob_main_spec);
            let tmp_owl_kB190 = { SecretBuf::another_ref(&self.owl_KB) };
            let owl_kB190 = SecretBuf::another_ref(&tmp_owl_kB190);
            let (tmp_owl_inp192, owl__191) = {
                effects.owl_input::<(owlSpec_bob_result, state_Bob)>(Tracked(&mut itree))
            };
            let owl_inp192 = OwlBuf::from_vec(tmp_owl_inp192);
            let tmp_owl_caseval193 = {
                let tracked owl_declassify_tok194 = consume_itree_declassify::<
                    (owlSpec_bob_result, state_Bob),
                    Endpoint,
                >(&mut itree);
                owl_dec(
                    SecretBuf::another_ref(&owl_kB190),
                    OwlBuf::another_ref(&owl_inp192),
                    Tracked(owl_declassify_tok194),
                )
            };
            let owl_caseval193 = SecretBuf::another_ref_option(&tmp_owl_caseval193);
            match SecretBuf::another_ref_option(&owl_caseval193) {
                Option::None => {
                    let owl__195 = { owl_unit() };
                    (owl_bob_result::another_ref(&owl_bob_None()), Tracked(itree))
                },
                Option::Some(tmp_owl_res196) => {
                    let owl_res196 = SecretBuf::another_ref(&tmp_owl_res196);
                    let parseval_tmp = SecretBuf::another_ref(&owl_res196);
                    if let Some(parseval) = secret_parse_owl_secret_kB_message(
                        SecretBuf::another_ref(&parseval_tmp),
                    ) {
                        let owl_kAB198 = SecretBuf::another_ref(&parseval.owl__kAB1);
                        let owl_A_197 = SecretBuf::another_ref(&parseval.owl__A);
                        let tmp_owl_declassified_buf103199 = {
                            let tracked owl_declassify_tok200 = consume_itree_declassify::<
                                (owlSpec_bob_result, state_Bob),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_A_197).declassify(
                                    Tracked(owl_declassify_tok200),
                                )
                            }
                        };
                        let owl_declassified_buf103199 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf103199,
                        );
                        let tmp_owl_kAB_201 = { SecretBuf::another_ref(&owl_kAB198) };
                        let owl_kAB_201 = SecretBuf::another_ref(&tmp_owl_kAB_201);
                        let tmp_owl_m202 = {
                            owl_nonceB(
                                SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_NB)),
                            )
                        };
                        let owl_m202 = owl_KABEnum::another_ref(&tmp_owl_m202);
                        let tmp_owl_encm203 = {
                            let tmp_owl_coins204 = effects.owl_sample::<
                                (owlSpec_bob_result, state_Bob),
                            >(Tracked(&mut itree), NONCE_SIZE);
                            let owl_coins204 = SecretBuf::another_ref(&tmp_owl_coins204);
                            owl_enc(
                                SecretBuf::another_ref(&owl_kAB_201),
                                SecretBuf::another_ref(
                                    &OwlBuf::from_vec(
                                        serialize_owl_KABEnum(&owl_m202),
                                    ).into_secret(),
                                ),
                                SecretBuf::another_ref(&owl_coins204),
                            )
                        };
                        let owl_encm203 = OwlBuf::from_vec(tmp_owl_encm203);
                        let owl__205 = {
                            effects.owl_output::<(owlSpec_bob_result, state_Bob)>(
                                Tracked(&mut itree),
                                owl_encm203.as_slice(),
                                Some(&Alice_addr()),
                                &Bob_addr(),
                            );
                        };
                        let (tmp_owl_inp2207, owl__206) = {
                            effects.owl_input::<(owlSpec_bob_result, state_Bob)>(
                                Tracked(&mut itree),
                            )
                        };
                        let owl_inp2207 = OwlBuf::from_vec(tmp_owl_inp2207);
                        let tmp_owl_caseval208 = {
                            let tracked owl_declassify_tok209 = consume_itree_declassify::<
                                (owlSpec_bob_result, state_Bob),
                                Endpoint,
                            >(&mut itree);
                            owl_dec(
                                SecretBuf::another_ref(&owl_kAB_201),
                                OwlBuf::another_ref(&owl_inp2207),
                                Tracked(owl_declassify_tok209),
                            )
                        };
                        let owl_caseval208 = SecretBuf::another_ref_option(&tmp_owl_caseval208);
                        match SecretBuf::another_ref_option(&owl_caseval208) {
                            Option::None => {
                                (owl_bob_result::another_ref(&owl_bob_None()), Tracked(itree))
                            },
                            Option::Some(tmp_owl_res2210) => {
                                let owl_res2210 = SecretBuf::another_ref(&tmp_owl_res2210);
                                let owl__assert_178211 = { owl_ghost_unit() };
                                let tmp_owl_m212 = { SecretBuf::another_ref(&owl_kAB_201) };
                                let owl_m212 = SecretBuf::another_ref(&tmp_owl_m212);
                                (
                                    owl_bob_result::another_ref(
                                        &owl_bob_Some(SecretBuf::another_ref(&owl_m212)),
                                    ),
                                    Tracked(itree),
                                )
                            },
                        }
                    } else {
                        {
                            let owl__213 = { owl_unit() };
                            (owl_bob_result::another_ref(&owl_bob_None()), Tracked(itree))
                        }
                    }
                },
            }
        };
        Ok((owl_bob_result::another_ref(&res_inner), Tracked(itree)))
    }
}

} // verus!
