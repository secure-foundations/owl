// Extracted verus code from file owl_toy_protocols/yahalom-indexed.owl:
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
spec fn spec_combinator_owlSpec_kA_message() -> (((Variable, Variable), Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_kA_message() -> (res: (((Variable, Variable), Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_kA_message(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_kA_message {
    pub owlSpec__B_kA: Seq<u8>,
    pub owlSpec__kAB_kA: Seq<u8>,
    pub owlSpec__nA_kA: Seq<u8>,
    pub owlSpec__nB_kA: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_kA_message(x: Seq<u8>) -> Option<owlSpec_kA_message> {
    let spec_comb = spec_combinator_owlSpec_kA_message();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec__B_kA, owlSpec__kAB_kA), owlSpec__nA_kA), owlSpec__nB_kA)) = parsed;
        Some(owlSpec_kA_message { owlSpec__B_kA, owlSpec__kAB_kA, owlSpec__nA_kA, owlSpec__nB_kA })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kA_message_inner(x: owlSpec_kA_message) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__B_kA.len(), x.owlSpec__kAB_kA.len(), x.owlSpec__nA_kA.len(), x.owlSpec__nB_kA.len() ] {
        let spec_comb = spec_combinator_owlSpec_kA_message();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec__B_kA, x.owlSpec__kAB_kA), x.owlSpec__nA_kA), x.owlSpec__nB_kA)),
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
    arg_owlSpec__B_kA: Seq<u8>,
    arg_owlSpec__kAB_kA: Seq<u8>,
    arg_owlSpec__nA_kA: Seq<u8>,
    arg_owlSpec__nB_kA: Seq<u8>,
) -> owlSpec_kA_message {
    owlSpec_kA_message {
        owlSpec__B_kA: arg_owlSpec__B_kA,
        owlSpec__kAB_kA: arg_owlSpec__kAB_kA,
        owlSpec__nA_kA: arg_owlSpec__nA_kA,
        owlSpec__nB_kA: arg_owlSpec__nB_kA,
    }
}

spec fn spec_combinator_owlSpec_secret_kA_message() -> (
    ((Variable, Variable), Variable),
    Variable,
) {
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
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
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_secret_kA_message {
    pub owlSpec__B_kA: Seq<u8>,
    pub owlSpec__kAB_kA: Seq<u8>,
    pub owlSpec__nA_kA: Seq<u8>,
    pub owlSpec__nB_kA: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_kA_message(x: Seq<u8>) -> Option<
    owlSpec_secret_kA_message,
> {
    let spec_comb = spec_combinator_owlSpec_secret_kA_message();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec__B_kA, owlSpec__kAB_kA), owlSpec__nA_kA), owlSpec__nB_kA)) = parsed;
        Some(
            owlSpec_secret_kA_message {
                owlSpec__B_kA,
                owlSpec__kAB_kA,
                owlSpec__nA_kA,
                owlSpec__nB_kA,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kA_message_inner(
    x: owlSpec_secret_kA_message,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__B_kA.len(), x.owlSpec__kAB_kA.len(), x.owlSpec__nA_kA.len(), x.owlSpec__nB_kA.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_kA_message();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec__B_kA, x.owlSpec__kAB_kA), x.owlSpec__nA_kA), x.owlSpec__nB_kA)),
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
    arg_owlSpec__B_kA: Seq<u8>,
    arg_owlSpec__kAB_kA: Seq<u8>,
    arg_owlSpec__nA_kA: Seq<u8>,
    arg_owlSpec__nB_kA: Seq<u8>,
) -> owlSpec_secret_kA_message {
    owlSpec_secret_kA_message {
        owlSpec__B_kA: arg_owlSpec__B_kA,
        owlSpec__kAB_kA: arg_owlSpec__kAB_kA,
        owlSpec__nA_kA: arg_owlSpec__nA_kA,
        owlSpec__nB_kA: arg_owlSpec__nB_kA,
    }
}

spec fn spec_combinator_owlSpec_kB_message_1() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_kB_message_1() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_kB_message_1(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_kB_message_1 {
    pub owlSpec__A_kB1: Seq<u8>,
    pub owlSpec__nA_kB1: Seq<u8>,
    pub owlSpec__nB_kB1: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_kB_message_1(x: Seq<u8>) -> Option<owlSpec_kB_message_1> {
    let spec_comb = spec_combinator_owlSpec_kB_message_1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec__A_kB1, owlSpec__nA_kB1), owlSpec__nB_kB1)) = parsed;
        Some(owlSpec_kB_message_1 { owlSpec__A_kB1, owlSpec__nA_kB1, owlSpec__nB_kB1 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kB_message_1_inner(x: owlSpec_kB_message_1) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__A_kB1.len(), x.owlSpec__nA_kB1.len(), x.owlSpec__nB_kB1.len() ] {
        let spec_comb = spec_combinator_owlSpec_kB_message_1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec__A_kB1, x.owlSpec__nA_kB1), x.owlSpec__nB_kB1)),
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
pub closed spec fn serialize_owlSpec_kB_message_1(x: owlSpec_kB_message_1) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_kB_message_1_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_kB_message_1 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_kB_message_1(self)
    }
}

pub open spec fn kB_message_1(
    arg_owlSpec__A_kB1: Seq<u8>,
    arg_owlSpec__nA_kB1: Seq<u8>,
    arg_owlSpec__nB_kB1: Seq<u8>,
) -> owlSpec_kB_message_1 {
    owlSpec_kB_message_1 {
        owlSpec__A_kB1: arg_owlSpec__A_kB1,
        owlSpec__nA_kB1: arg_owlSpec__nA_kB1,
        owlSpec__nB_kB1: arg_owlSpec__nB_kB1,
    }
}

spec fn spec_combinator_owlSpec_secret_kB_message_1() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_secret_kB_message_1() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_kB_message_1(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_secret_kB_message_1 {
    pub owlSpec__A_kB1: Seq<u8>,
    pub owlSpec__nA_kB1: Seq<u8>,
    pub owlSpec__nB_kB1: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_kB_message_1(x: Seq<u8>) -> Option<
    owlSpec_secret_kB_message_1,
> {
    let spec_comb = spec_combinator_owlSpec_secret_kB_message_1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec__A_kB1, owlSpec__nA_kB1), owlSpec__nB_kB1)) = parsed;
        Some(owlSpec_secret_kB_message_1 { owlSpec__A_kB1, owlSpec__nA_kB1, owlSpec__nB_kB1 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kB_message_1_inner(
    x: owlSpec_secret_kB_message_1,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__A_kB1.len(), x.owlSpec__nA_kB1.len(), x.owlSpec__nB_kB1.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_kB_message_1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec__A_kB1, x.owlSpec__nA_kB1), x.owlSpec__nB_kB1)),
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
pub closed spec fn serialize_owlSpec_secret_kB_message_1(x: owlSpec_secret_kB_message_1) -> Seq<
    u8,
> {
    if let Some(val) = serialize_owlSpec_secret_kB_message_1_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_kB_message_1 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_kB_message_1(self)
    }
}

pub open spec fn secret_kB_message_1(
    arg_owlSpec__A_kB1: Seq<u8>,
    arg_owlSpec__nA_kB1: Seq<u8>,
    arg_owlSpec__nB_kB1: Seq<u8>,
) -> owlSpec_secret_kB_message_1 {
    owlSpec_secret_kB_message_1 {
        owlSpec__A_kB1: arg_owlSpec__A_kB1,
        owlSpec__nA_kB1: arg_owlSpec__nA_kB1,
        owlSpec__nB_kB1: arg_owlSpec__nB_kB1,
    }
}

spec fn spec_combinator_owlSpec_kB_message_2() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_kB_message_2() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_kB_message_2(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_kB_message_2 {
    pub owlSpec__A_kB2: Seq<u8>,
    pub owlSpec__kAB_kB2: Seq<u8>,
    pub owlSpec__nB_kB2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_kB_message_2(x: Seq<u8>) -> Option<owlSpec_kB_message_2> {
    let spec_comb = spec_combinator_owlSpec_kB_message_2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec__A_kB2, owlSpec__kAB_kB2), owlSpec__nB_kB2)) = parsed;
        Some(owlSpec_kB_message_2 { owlSpec__A_kB2, owlSpec__kAB_kB2, owlSpec__nB_kB2 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kB_message_2_inner(x: owlSpec_kB_message_2) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__A_kB2.len(), x.owlSpec__kAB_kB2.len(), x.owlSpec__nB_kB2.len() ] {
        let spec_comb = spec_combinator_owlSpec_kB_message_2();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec__A_kB2, x.owlSpec__kAB_kB2), x.owlSpec__nB_kB2)),
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
pub closed spec fn serialize_owlSpec_kB_message_2(x: owlSpec_kB_message_2) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_kB_message_2_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_kB_message_2 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_kB_message_2(self)
    }
}

pub open spec fn kB_message_2(
    arg_owlSpec__A_kB2: Seq<u8>,
    arg_owlSpec__kAB_kB2: Seq<u8>,
    arg_owlSpec__nB_kB2: Seq<u8>,
) -> owlSpec_kB_message_2 {
    owlSpec_kB_message_2 {
        owlSpec__A_kB2: arg_owlSpec__A_kB2,
        owlSpec__kAB_kB2: arg_owlSpec__kAB_kB2,
        owlSpec__nB_kB2: arg_owlSpec__nB_kB2,
    }
}

spec fn spec_combinator_owlSpec_secret_kB_message_2() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_secret_kB_message_2() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_kB_message_2(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    let field_3 = Variable(12);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_secret_kB_message_2 {
    pub owlSpec__A_kB2: Seq<u8>,
    pub owlSpec__kAB_kB2: Seq<u8>,
    pub owlSpec__nB_kB2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_kB_message_2(x: Seq<u8>) -> Option<
    owlSpec_secret_kB_message_2,
> {
    let spec_comb = spec_combinator_owlSpec_secret_kB_message_2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec__A_kB2, owlSpec__kAB_kB2), owlSpec__nB_kB2)) = parsed;
        Some(owlSpec_secret_kB_message_2 { owlSpec__A_kB2, owlSpec__kAB_kB2, owlSpec__nB_kB2 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kB_message_2_inner(
    x: owlSpec_secret_kB_message_2,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__A_kB2.len(), x.owlSpec__kAB_kB2.len(), x.owlSpec__nB_kB2.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_kB_message_2();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec__A_kB2, x.owlSpec__kAB_kB2), x.owlSpec__nB_kB2)),
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
pub closed spec fn serialize_owlSpec_secret_kB_message_2(x: owlSpec_secret_kB_message_2) -> Seq<
    u8,
> {
    if let Some(val) = serialize_owlSpec_secret_kB_message_2_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_kB_message_2 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_kB_message_2(self)
    }
}

pub open spec fn secret_kB_message_2(
    arg_owlSpec__A_kB2: Seq<u8>,
    arg_owlSpec__kAB_kB2: Seq<u8>,
    arg_owlSpec__nB_kB2: Seq<u8>,
) -> owlSpec_secret_kB_message_2 {
    owlSpec_secret_kB_message_2 {
        owlSpec__A_kB2: arg_owlSpec__A_kB2,
        owlSpec__kAB_kB2: arg_owlSpec__kAB_kB2,
        owlSpec__nB_kB2: arg_owlSpec__nB_kB2,
    }
}

pub enum owlSpec_kB_messages {
    owlSpec_mB1(owlSpec_kB_message_1),
    owlSpec_mB2(owlSpec_kB_message_2),
}

use owlSpec_kB_messages::*;

#[verifier::external_body]
pub closed spec fn parse_owlSpec_kB_messages(x: Seq<u8>) -> Option<owlSpec_kB_messages> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_kB_messages_inner(x: owlSpec_kB_messages) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_kB_messages(x: owlSpec_kB_messages) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_kB_messages {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_kB_messages(self)
    }
}

pub open spec fn mB1(x: owlSpec_kB_message_1) -> owlSpec_kB_messages {
    crate::owlSpec_kB_messages::owlSpec_mB1(x)
}

pub open spec fn mB2(x: owlSpec_kB_message_2) -> owlSpec_kB_messages {
    crate::owlSpec_kB_messages::owlSpec_mB2(x)
}

pub open spec fn mB1_enumtest(x: owlSpec_kB_messages) -> bool {
    match x {
        owlSpec_kB_messages::owlSpec_mB1(_) => true,
        _ => false,
    }
}

pub open spec fn mB2_enumtest(x: owlSpec_kB_messages) -> bool {
    match x {
        owlSpec_kB_messages::owlSpec_mB2(_) => true,
        _ => false,
    }
}

pub enum owlSpec_encd_by_kB {
    owlSpec_e1(Seq<u8>),
    owlSpec_e2(Seq<u8>),
}

use owlSpec_encd_by_kB::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_encd_by_kB(x: Seq<u8>) -> Option<owlSpec_encd_by_kB> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Tail), (Tag::spec_new(U8, 2), Tail));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owlSpec_encd_by_kB::owlSpec_e1(x),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_encd_by_kB::owlSpec_e2(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_encd_by_kB_inner(x: owlSpec_encd_by_kB) -> Option<Seq<u8>> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Tail), (Tag::spec_new(U8, 2), Tail));
    match x {
        owlSpec_encd_by_kB::owlSpec_e1(x) => {
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
        owlSpec_encd_by_kB::owlSpec_e2(x) => {
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
pub closed spec fn serialize_owlSpec_encd_by_kB(x: owlSpec_encd_by_kB) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_encd_by_kB_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_encd_by_kB {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_encd_by_kB(self)
    }
}

pub open spec fn e1(x: Seq<u8>) -> owlSpec_encd_by_kB {
    crate::owlSpec_encd_by_kB::owlSpec_e1(x)
}

pub open spec fn e2(x: Seq<u8>) -> owlSpec_encd_by_kB {
    crate::owlSpec_encd_by_kB::owlSpec_e2(x)
}

pub open spec fn e1_enumtest(x: owlSpec_encd_by_kB) -> bool {
    match x {
        owlSpec_encd_by_kB::owlSpec_e1(_) => true,
        _ => false,
    }
}

pub open spec fn e2_enumtest(x: owlSpec_encd_by_kB) -> bool {
    match x {
        owlSpec_encd_by_kB::owlSpec_e2(_) => true,
        _ => false,
    }
}

spec fn spec_combinator_owlSpec_msg1_AtoB() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_msg1_AtoB() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_msg1_AtoB(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_msg1_AtoB {
    pub owlSpec_msg1_A: Seq<u8>,
    pub owlSpec_msg1_nA: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_msg1_AtoB(x: Seq<u8>) -> Option<owlSpec_msg1_AtoB> {
    let spec_comb = spec_combinator_owlSpec_msg1_AtoB();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec_msg1_A, owlSpec_msg1_nA)) = parsed;
        Some(owlSpec_msg1_AtoB { owlSpec_msg1_A, owlSpec_msg1_nA })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_msg1_AtoB_inner(x: owlSpec_msg1_AtoB) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_msg1_A.len(), x.owlSpec_msg1_nA.len() ] {
        let spec_comb = spec_combinator_owlSpec_msg1_AtoB();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec_msg1_A, x.owlSpec_msg1_nA))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_msg1_AtoB(x: owlSpec_msg1_AtoB) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_msg1_AtoB_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_msg1_AtoB {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg1_AtoB(self)
    }
}

pub open spec fn msg1_AtoB(
    arg_owlSpec_msg1_A: Seq<u8>,
    arg_owlSpec_msg1_nA: Seq<u8>,
) -> owlSpec_msg1_AtoB {
    owlSpec_msg1_AtoB { owlSpec_msg1_A: arg_owlSpec_msg1_A, owlSpec_msg1_nA: arg_owlSpec_msg1_nA }
}

pub struct owlSpec_msg2_BtoS {
    pub owlSpec_msg2_B: Seq<u8>,
    pub owlSpec_msg2_x: owlSpec_encd_by_kB,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_msg2_BtoS(x: Seq<u8>) -> Option<owlSpec_msg2_BtoS> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_msg2_BtoS_inner(x: owlSpec_msg2_BtoS) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_msg2_BtoS(x: owlSpec_msg2_BtoS) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_msg2_BtoS {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg2_BtoS(self)
    }
}

pub open spec fn msg2_BtoS(
    arg_owlSpec_msg2_B: Seq<u8>,
    arg_owlSpec_msg2_x: owlSpec_encd_by_kB,
) -> owlSpec_msg2_BtoS {
    owlSpec_msg2_BtoS { owlSpec_msg2_B: arg_owlSpec_msg2_B, owlSpec_msg2_x: arg_owlSpec_msg2_x }
}

pub struct owlSpec_msg3_StoA {
    pub owlSpec_msg3_tkt1: Seq<u8>,
    pub owlSpec_msg3_tkt2: owlSpec_encd_by_kB,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_msg3_StoA(x: Seq<u8>) -> Option<owlSpec_msg3_StoA> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_msg3_StoA_inner(x: owlSpec_msg3_StoA) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_msg3_StoA(x: owlSpec_msg3_StoA) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_msg3_StoA {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg3_StoA(self)
    }
}

pub open spec fn msg3_StoA(
    arg_owlSpec_msg3_tkt1: Seq<u8>,
    arg_owlSpec_msg3_tkt2: owlSpec_encd_by_kB,
) -> owlSpec_msg3_StoA {
    owlSpec_msg3_StoA {
        owlSpec_msg3_tkt1: arg_owlSpec_msg3_tkt1,
        owlSpec_msg3_tkt2: arg_owlSpec_msg3_tkt2,
    }
}

pub struct owlSpec_msg4_AtoB {
    pub owlSpec_msg4_x: Seq<u8>,
    pub owlSpec_msg4_tkt: owlSpec_encd_by_kB,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_msg4_AtoB(x: Seq<u8>) -> Option<owlSpec_msg4_AtoB> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_msg4_AtoB_inner(x: owlSpec_msg4_AtoB) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_msg4_AtoB(x: owlSpec_msg4_AtoB) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_msg4_AtoB {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg4_AtoB(self)
    }
}

pub open spec fn msg4_AtoB(
    arg_owlSpec_msg4_x: Seq<u8>,
    arg_owlSpec_msg4_tkt: owlSpec_encd_by_kB,
) -> owlSpec_msg4_AtoB {
    owlSpec_msg4_AtoB { owlSpec_msg4_x: arg_owlSpec_msg4_x, owlSpec_msg4_tkt: arg_owlSpec_msg4_tkt }
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
        let kAB = ((ret(cfg.owl_KAB.view()))) in
let kA = ((ret(cfg.owl_KA.view()))) in
let kB = ((ret(cfg.owl_KB.view()))) in
(input(inp,_40)) in
(parse (parse_owlSpec_msg2_BtoS(inp)) as (owlSpec_msg2_BtoS{owlSpec_msg2_B : B_, owlSpec_msg2_x : x_}) in {
(case (x_) {
| owlSpec_e2(_unused237) => {
(ret(()))
},
| owlSpec_e1(x__) => {
let caseval = ((declassify(DeclassifyingOp::ADec(kB, x__))) in
(ret(dec(kB, x__)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(res) => {
let res_ = ((ret(res))) in
let res__ = ((ret(res_))) in
(declassify(DeclassifyingOp::EnumParse(res__))) in
(parse (parse_owlSpec_kB_messages(res__)) as (parsed_caseval : owlSpec_kB_messages) in {
(case (parsed_caseval) {
| owlSpec_mB1(msg1) => {
(parse (msg1) as (owlSpec_kB_message_1{owlSpec__A_kB1 : A_, owlSpec__nA_kB1 : nA_, owlSpec__nB_kB1 : nB_}) in {
let declassified_buf74 = ((declassify(DeclassifyingOp::ControlFlow(nB_))) in
(ret((nB_)))) in
let m = ((ret(kA_message(B_, kAB, nA_, declassified_buf74)))) in
let encmA = ((sample(NONCE_SIZE, enc(kA, serialize_owlSpec_kA_message(m))))) in
let m = ((ret(mB2(kB_message_2(A_, kAB, nB_))))) in
let encmB = ((sample(NONCE_SIZE, enc(kB, serialize_owlSpec_kB_messages(m))))) in
(output (serialize_owlSpec_msg3_StoA(msg3_StoA(encmA, e2(encmB)))) to (Some(Endpoint::Loc_Alice))) in
(ret(()))
} )
},
| owlSpec_mB2(_unused238) => {
(ret(()))
},
}
)
} otherwise (ret(())))
},
}
)
},
}
)
} otherwise ((ret(()))))
    )
}

#[verifier::opaque]
pub open spec fn Alice_main_spec(cfg: cfg_Alice, mut_state: state_Alice) -> (res: ITree<
    (owlSpec_alice_result, state_Alice),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Alice,
        let A = ((ret(cfg.owl_Alice_username.view()))) in
let nA = ((ret(cfg.owl_NA.view()))) in
let kA = ((ret(cfg.owl_KA.view()))) in
let declassified_buf90 = ((declassify(DeclassifyingOp::ControlFlow(A))) in
(ret((A)))) in
let declassified_buf93 = ((declassify(DeclassifyingOp::ControlFlow(nA))) in
(ret((nA)))) in
(output (serialize_owlSpec_msg1_AtoB(msg1_AtoB(declassified_buf90, declassified_buf93))) to (Some(Endpoint::Loc_Bob))) in
(input(inp1,_97)) in
(parse (parse_owlSpec_msg3_StoA(inp1)) as (owlSpec_msg3_StoA{owlSpec_msg3_tkt1 : tkt1, owlSpec_msg3_tkt2 : tkt2}) in {
let caseval = ((declassify(DeclassifyingOp::ADec(kA, tkt1))) in
(ret(dec(kA, tkt1)))) in
(case (caseval) {
| None => {
(ret(alice_None()))
},
| Some(res) => {
let res_ = ((ret(res))) in
(parse (parse_owlSpec_secret_kA_message(res_)) as (owlSpec_secret_kA_message{owlSpec__B_kA : B_, owlSpec__kAB_kA : kAB_, owlSpec__nA_kA : nA_, owlSpec__nB_kA : nB_}) in {
let declassified_buf121 = ((declassify(DeclassifyingOp::ControlFlow(B_))) in
(ret((B_)))) in
let declassified_buf124 = ((declassify(DeclassifyingOp::ControlFlow(nA_))) in
(ret((nA_)))) in
let declassified_buf127 = ((declassify(DeclassifyingOp::ControlFlow(nB_))) in
(ret((nB_)))) in
let encm = ((sample(NONCE_SIZE, enc(kAB_, declassified_buf127)))) in
(output (serialize_owlSpec_msg4_AtoB(msg4_AtoB(encm, tkt2))) to (Some(Endpoint::Loc_Bob))) in
(ret(alice_Some(kAB_)))
} otherwise ((ret(alice_None()))))
},
}
)
} otherwise ((ret(alice_None()))))
    )
}

#[verifier::opaque]
pub open spec fn Bob_main_spec(cfg: cfg_Bob, mut_state: state_Bob) -> (res: ITree<
    (owlSpec_bob_result, state_Bob),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Bob,
        let B = ((ret(cfg.owl_Bob_username.view()))) in
let nB = ((ret(cfg.owl_NB.view()))) in
let kB = ((ret(cfg.owl_KB.view()))) in
(input(inp,_136)) in
(parse (parse_owlSpec_msg1_AtoB(inp)) as (owlSpec_msg1_AtoB{owlSpec_msg1_A : A_, owlSpec_msg1_nA : nA_}) in {
let temp_packed = ((ret(mB1(kB_message_1(A_, nA_, nB))))) in
let encm = ((sample(NONCE_SIZE, enc(kB, serialize_owlSpec_kB_messages(temp_packed))))) in
let declassified_buf147 = ((declassify(DeclassifyingOp::ControlFlow(B))) in
(ret((B)))) in
(output (serialize_owlSpec_msg2_BtoS(msg2_BtoS(declassified_buf147, e1(encm)))) to (Some(Endpoint::Loc_AS))) in
(input(inp2,_151)) in
(parse (parse_owlSpec_msg4_AtoB(inp2)) as (owlSpec_msg4_AtoB{owlSpec_msg4_x : x, owlSpec_msg4_tkt : tkt_}) in {
(case (tkt_) {
| owlSpec_e1(_unused239) => {
(ret(bob_None()))
},
| owlSpec_e2(tkt) => {
let caseval = ((declassify(DeclassifyingOp::ADec(kB, tkt))) in
(ret(dec(kB, tkt)))) in
(case (caseval) {
| None => {
(ret(bob_None()))
},
| Some(res) => {
let res_ = ((ret(res))) in
let res__ = ((ret(res_))) in
(declassify(DeclassifyingOp::EnumParse(res__))) in
(parse (parse_owlSpec_kB_messages(res__)) as (parsed_caseval : owlSpec_kB_messages) in {
(case (parsed_caseval) {
| owlSpec_mB1(_unused240) => {
(ret(bob_None()))
},
| owlSpec_mB2(msg2) => {
(parse (msg2) as (owlSpec_kB_message_2{owlSpec__A_kB2 : A__, owlSpec__kAB_kB2 : kAB_, owlSpec__nB_kB2 : nB_}) in {
let eq_bool187 = ((declassify(DeclassifyingOp::EqCheck(nB_, nB))) in
(ret(nB_ == nB))) in
(if (eq_bool187) then
(let _assert_169 = ((ret(ghost_unit()))) in
let caseval = ((declassify(DeclassifyingOp::ADec(kAB_, x))) in
(ret(dec(kAB_, x)))) in
(case (caseval) {
| None => {
(ret(bob_None()))
},
| Some(res2) => {
let nB_ = ((ret(res2))) in
let eq_bool195 = ((declassify(DeclassifyingOp::EqCheck(nB_, nB))) in
(ret(nB_ == nB))) in
(if (eq_bool195) then
((ret(bob_Some(kAB_))))
else
((ret(bob_None()))))
},
}
))
else
((ret(bob_None()))))
} )
},
}
)
} otherwise (ret(bob_None())))
},
}
)
},
}
)
} otherwise ((ret(bob_None()))))
} otherwise ((ret(bob_None()))))
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

pub struct owl_kA_message<'a> {
    pub owl__B_kA: OwlBuf<'a>,
    pub owl__kAB_kA: SecretBuf<'a>,
    pub owl__nA_kA: OwlBuf<'a>,
    pub owl__nB_kA: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_kA_message<'a>(
    arg_owl__B_kA: OwlBuf<'a>,
    arg_owl__kAB_kA: SecretBuf<'a>,
    arg_owl__nA_kA: OwlBuf<'a>,
    arg_owl__nB_kA: OwlBuf<'a>,
) -> (res: owl_kA_message<'a>)
    ensures
        res.owl__B_kA.view() == arg_owl__B_kA.view(),
        res.owl__kAB_kA.view() == arg_owl__kAB_kA.view(),
        res.owl__nA_kA.view() == arg_owl__nA_kA.view(),
        res.owl__nB_kA.view() == arg_owl__nB_kA.view(),
{
    owl_kA_message {
        owl__B_kA: arg_owl__B_kA,
        owl__kAB_kA: arg_owl__kAB_kA,
        owl__nA_kA: arg_owl__nA_kA,
        owl__nB_kA: arg_owl__nB_kA,
    }
}

impl<'a> owl_kA_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kA_message<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_kA_message {
            owl__B_kA: OwlBuf::another_ref(&self.owl__B_kA),
            owl__kAB_kA: SecretBuf::another_ref(&self.owl__kAB_kA),
            owl__nA_kA: OwlBuf::another_ref(&self.owl__nA_kA),
            owl__nB_kA: OwlBuf::another_ref(&self.owl__nB_kA),
        }
    }
}

impl View for owl_kA_message<'_> {
    type V = owlSpec_kA_message;

    open spec fn view(&self) -> owlSpec_kA_message {
        owlSpec_kA_message {
            owlSpec__B_kA: self.owl__B_kA.view(),
            owlSpec__kAB_kA: self.owl__kAB_kA.view(),
            owlSpec__nA_kA: self.owl__nA_kA.view(),
            owlSpec__nB_kA: self.owl__nB_kA.view(),
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
        let (((owl__B_kA, owl__kAB_kA), owl__nA_kA), owl__nB_kA) = parsed;
        Some(
            owl_kA_message {
                owl__B_kA: OwlBuf::another_ref(&owl__B_kA),
                owl__kAB_kA: SecretBuf::from_buf(owl__kAB_kA.another_ref()),
                owl__nA_kA: OwlBuf::another_ref(&owl__nA_kA),
                owl__nB_kA: OwlBuf::another_ref(&owl__nB_kA),
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
    if no_usize_overflows![ arg.owl__B_kA.len(), arg.owl__kAB_kA.len(), arg.owl__nA_kA.len(), arg.owl__nB_kA.len(), 0 ] {
        let exec_comb = exec_combinator_owl_kA_message();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__B_kA.len() + arg.owl__kAB_kA.len() + arg.owl__nA_kA.len()
                + arg.owl__nB_kA.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        SecretBuf::from_buf(arg.owl__B_kA.another_ref()),
                        SecretBuf::another_ref(&arg.owl__kAB_kA),
                    ),
                    SecretBuf::from_buf(arg.owl__nA_kA.another_ref()),
                ),
                SecretBuf::from_buf(arg.owl__nB_kA.another_ref()),
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
    pub owl__B_kA: SecretBuf<'a>,
    pub owl__kAB_kA: SecretBuf<'a>,
    pub owl__nA_kA: SecretBuf<'a>,
    pub owl__nB_kA: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_kA_message<'a>(
    arg_owl__B_kA: SecretBuf<'a>,
    arg_owl__kAB_kA: SecretBuf<'a>,
    arg_owl__nA_kA: SecretBuf<'a>,
    arg_owl__nB_kA: SecretBuf<'a>,
) -> (res: owl_secret_kA_message<'a>)
    ensures
        res.owl__B_kA.view() == arg_owl__B_kA.view(),
        res.owl__kAB_kA.view() == arg_owl__kAB_kA.view(),
        res.owl__nA_kA.view() == arg_owl__nA_kA.view(),
        res.owl__nB_kA.view() == arg_owl__nB_kA.view(),
{
    owl_secret_kA_message {
        owl__B_kA: arg_owl__B_kA,
        owl__kAB_kA: arg_owl__kAB_kA,
        owl__nA_kA: arg_owl__nA_kA,
        owl__nB_kA: arg_owl__nB_kA,
    }
}

impl<'a> owl_secret_kA_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_kA_message<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_kA_message {
            owl__B_kA: SecretBuf::another_ref(&self.owl__B_kA),
            owl__kAB_kA: SecretBuf::another_ref(&self.owl__kAB_kA),
            owl__nA_kA: SecretBuf::another_ref(&self.owl__nA_kA),
            owl__nB_kA: SecretBuf::another_ref(&self.owl__nB_kA),
        }
    }
}

impl View for owl_secret_kA_message<'_> {
    type V = owlSpec_secret_kA_message;

    open spec fn view(&self) -> owlSpec_secret_kA_message {
        owlSpec_secret_kA_message {
            owlSpec__B_kA: self.owl__B_kA.view(),
            owlSpec__kAB_kA: self.owl__kAB_kA.view(),
            owlSpec__nA_kA: self.owl__nA_kA.view(),
            owlSpec__nB_kA: self.owl__nB_kA.view(),
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
        let (((owl__B_kA, owl__kAB_kA), owl__nA_kA), owl__nB_kA) = parsed;
        Some(
            owl_secret_kA_message {
                owl__B_kA: SecretBuf::from_buf(owl__B_kA.another_ref()),
                owl__kAB_kA: SecretBuf::from_buf(owl__kAB_kA.another_ref()),
                owl__nA_kA: SecretBuf::from_buf(owl__nA_kA.another_ref()),
                owl__nB_kA: SecretBuf::from_buf(owl__nB_kA.another_ref()),
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
        let (((owl__B_kA, owl__kAB_kA), owl__nA_kA), owl__nB_kA) = parsed;
        Some(
            owl_secret_kA_message {
                owl__B_kA: SecretBuf::another_ref(&owl__B_kA),
                owl__kAB_kA: SecretBuf::another_ref(&owl__kAB_kA),
                owl__nA_kA: SecretBuf::another_ref(&owl__nA_kA),
                owl__nB_kA: SecretBuf::another_ref(&owl__nB_kA),
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
    if no_usize_overflows![ arg.owl__B_kA.len(), arg.owl__kAB_kA.len(), arg.owl__nA_kA.len(), arg.owl__nB_kA.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_kA_message();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__B_kA.len() + arg.owl__kAB_kA.len() + arg.owl__nA_kA.len()
                + arg.owl__nB_kA.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        SecretBuf::another_ref(&arg.owl__B_kA),
                        SecretBuf::another_ref(&arg.owl__kAB_kA),
                    ),
                    SecretBuf::another_ref(&arg.owl__nA_kA),
                ),
                SecretBuf::another_ref(&arg.owl__nB_kA),
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

pub struct owl_kB_message_1<'a> {
    pub owl__A_kB1: OwlBuf<'a>,
    pub owl__nA_kB1: OwlBuf<'a>,
    pub owl__nB_kB1: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_kB_message_1<'a>(
    arg_owl__A_kB1: OwlBuf<'a>,
    arg_owl__nA_kB1: OwlBuf<'a>,
    arg_owl__nB_kB1: SecretBuf<'a>,
) -> (res: owl_kB_message_1<'a>)
    ensures
        res.owl__A_kB1.view() == arg_owl__A_kB1.view(),
        res.owl__nA_kB1.view() == arg_owl__nA_kB1.view(),
        res.owl__nB_kB1.view() == arg_owl__nB_kB1.view(),
{
    owl_kB_message_1 {
        owl__A_kB1: arg_owl__A_kB1,
        owl__nA_kB1: arg_owl__nA_kB1,
        owl__nB_kB1: arg_owl__nB_kB1,
    }
}

impl<'a> owl_kB_message_1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kB_message_1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_kB_message_1 {
            owl__A_kB1: OwlBuf::another_ref(&self.owl__A_kB1),
            owl__nA_kB1: OwlBuf::another_ref(&self.owl__nA_kB1),
            owl__nB_kB1: SecretBuf::another_ref(&self.owl__nB_kB1),
        }
    }
}

impl View for owl_kB_message_1<'_> {
    type V = owlSpec_kB_message_1;

    open spec fn view(&self) -> owlSpec_kB_message_1 {
        owlSpec_kB_message_1 {
            owlSpec__A_kB1: self.owl__A_kB1.view(),
            owlSpec__nA_kB1: self.owl__nA_kB1.view(),
            owlSpec__nB_kB1: self.owl__nB_kB1.view(),
        }
    }
}

pub exec fn parse_owl_kB_message_1<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_kB_message_1<'a>>)
    ensures
        res is Some ==> parse_owlSpec_kB_message_1(arg.view()) is Some,
        res is None ==> parse_owlSpec_kB_message_1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kB_message_1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_kB_message_1);
    let exec_comb = exec_combinator_owl_kB_message_1();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl__A_kB1, owl__nA_kB1), owl__nB_kB1) = parsed;
        Some(
            owl_kB_message_1 {
                owl__A_kB1: OwlBuf::another_ref(&owl__A_kB1),
                owl__nA_kB1: OwlBuf::another_ref(&owl__nA_kB1),
                owl__nB_kB1: SecretBuf::from_buf(owl__nB_kB1.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_kB_message_1_inner<'a>(arg: &owl_kB_message_1<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_kB_message_1_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_kB_message_1_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_kB_message_1_inner);
    if no_usize_overflows![ arg.owl__A_kB1.len(), arg.owl__nA_kB1.len(), arg.owl__nB_kB1.len(), 0 ] {
        let exec_comb = exec_combinator_owl_kB_message_1();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__A_kB1.len() + arg.owl__nA_kB1.len() + arg.owl__nB_kB1.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    SecretBuf::from_buf(arg.owl__A_kB1.another_ref()),
                    SecretBuf::from_buf(arg.owl__nA_kB1.another_ref()),
                ),
                SecretBuf::another_ref(&arg.owl__nB_kB1),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_kB_message_1_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_kB_message_1<'a>(arg: &owl_kB_message_1<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_kB_message_1(arg.view()),
{
    reveal(serialize_owlSpec_kB_message_1);
    let res = serialize_owl_kB_message_1_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_kB_message_1<'a> {
    pub owl__A_kB1: SecretBuf<'a>,
    pub owl__nA_kB1: SecretBuf<'a>,
    pub owl__nB_kB1: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_kB_message_1<'a>(
    arg_owl__A_kB1: SecretBuf<'a>,
    arg_owl__nA_kB1: SecretBuf<'a>,
    arg_owl__nB_kB1: SecretBuf<'a>,
) -> (res: owl_secret_kB_message_1<'a>)
    ensures
        res.owl__A_kB1.view() == arg_owl__A_kB1.view(),
        res.owl__nA_kB1.view() == arg_owl__nA_kB1.view(),
        res.owl__nB_kB1.view() == arg_owl__nB_kB1.view(),
{
    owl_secret_kB_message_1 {
        owl__A_kB1: arg_owl__A_kB1,
        owl__nA_kB1: arg_owl__nA_kB1,
        owl__nB_kB1: arg_owl__nB_kB1,
    }
}

impl<'a> owl_secret_kB_message_1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_kB_message_1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_kB_message_1 {
            owl__A_kB1: SecretBuf::another_ref(&self.owl__A_kB1),
            owl__nA_kB1: SecretBuf::another_ref(&self.owl__nA_kB1),
            owl__nB_kB1: SecretBuf::another_ref(&self.owl__nB_kB1),
        }
    }
}

impl View for owl_secret_kB_message_1<'_> {
    type V = owlSpec_secret_kB_message_1;

    open spec fn view(&self) -> owlSpec_secret_kB_message_1 {
        owlSpec_secret_kB_message_1 {
            owlSpec__A_kB1: self.owl__A_kB1.view(),
            owlSpec__nA_kB1: self.owl__nA_kB1.view(),
            owlSpec__nB_kB1: self.owl__nB_kB1.view(),
        }
    }
}

pub exec fn parse_owl_secret_kB_message_1<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_secret_kB_message_1<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kB_message_1(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kB_message_1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kB_message_1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kB_message_1);
    let exec_comb = exec_combinator_owl_secret_kB_message_1();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl__A_kB1, owl__nA_kB1), owl__nB_kB1) = parsed;
        Some(
            owl_secret_kB_message_1 {
                owl__A_kB1: SecretBuf::from_buf(owl__A_kB1.another_ref()),
                owl__nA_kB1: SecretBuf::from_buf(owl__nA_kB1.another_ref()),
                owl__nB_kB1: SecretBuf::from_buf(owl__nB_kB1.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_kB_message_1<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_kB_message_1<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kB_message_1(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kB_message_1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kB_message_1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kB_message_1);
    let exec_comb = exec_combinator_owl_secret_kB_message_1();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let ((owl__A_kB1, owl__nA_kB1), owl__nB_kB1) = parsed;
        Some(
            owl_secret_kB_message_1 {
                owl__A_kB1: SecretBuf::another_ref(&owl__A_kB1),
                owl__nA_kB1: SecretBuf::another_ref(&owl__nA_kB1),
                owl__nB_kB1: SecretBuf::another_ref(&owl__nB_kB1),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_kB_message_1_inner<'a>(arg: &owl_secret_kB_message_1<'a>) -> (res:
    Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_secret_kB_message_1_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_kB_message_1_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_secret_kB_message_1_inner);
    if no_usize_overflows![ arg.owl__A_kB1.len(), arg.owl__nA_kB1.len(), arg.owl__nB_kB1.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_kB_message_1();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__A_kB1.len() + arg.owl__nA_kB1.len() + arg.owl__nB_kB1.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (SecretBuf::another_ref(&arg.owl__A_kB1), SecretBuf::another_ref(&arg.owl__nA_kB1)),
                SecretBuf::another_ref(&arg.owl__nB_kB1),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_kB_message_1_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_kB_message_1<'a>(arg: &owl_secret_kB_message_1<'a>) -> (res:
    SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_kB_message_1(arg.view()),
{
    reveal(serialize_owlSpec_secret_kB_message_1);
    let res = serialize_owl_secret_kB_message_1_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_kB_message_2<'a> {
    pub owl__A_kB2: OwlBuf<'a>,
    pub owl__kAB_kB2: SecretBuf<'a>,
    pub owl__nB_kB2: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_kB_message_2<'a>(
    arg_owl__A_kB2: OwlBuf<'a>,
    arg_owl__kAB_kB2: SecretBuf<'a>,
    arg_owl__nB_kB2: SecretBuf<'a>,
) -> (res: owl_kB_message_2<'a>)
    ensures
        res.owl__A_kB2.view() == arg_owl__A_kB2.view(),
        res.owl__kAB_kB2.view() == arg_owl__kAB_kB2.view(),
        res.owl__nB_kB2.view() == arg_owl__nB_kB2.view(),
{
    owl_kB_message_2 {
        owl__A_kB2: arg_owl__A_kB2,
        owl__kAB_kB2: arg_owl__kAB_kB2,
        owl__nB_kB2: arg_owl__nB_kB2,
    }
}

impl<'a> owl_kB_message_2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kB_message_2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_kB_message_2 {
            owl__A_kB2: OwlBuf::another_ref(&self.owl__A_kB2),
            owl__kAB_kB2: SecretBuf::another_ref(&self.owl__kAB_kB2),
            owl__nB_kB2: SecretBuf::another_ref(&self.owl__nB_kB2),
        }
    }
}

impl View for owl_kB_message_2<'_> {
    type V = owlSpec_kB_message_2;

    open spec fn view(&self) -> owlSpec_kB_message_2 {
        owlSpec_kB_message_2 {
            owlSpec__A_kB2: self.owl__A_kB2.view(),
            owlSpec__kAB_kB2: self.owl__kAB_kB2.view(),
            owlSpec__nB_kB2: self.owl__nB_kB2.view(),
        }
    }
}

pub exec fn parse_owl_kB_message_2<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_kB_message_2<'a>>)
    ensures
        res is Some ==> parse_owlSpec_kB_message_2(arg.view()) is Some,
        res is None ==> parse_owlSpec_kB_message_2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kB_message_2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_kB_message_2);
    let exec_comb = exec_combinator_owl_kB_message_2();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl__A_kB2, owl__kAB_kB2), owl__nB_kB2) = parsed;
        Some(
            owl_kB_message_2 {
                owl__A_kB2: OwlBuf::another_ref(&owl__A_kB2),
                owl__kAB_kB2: SecretBuf::from_buf(owl__kAB_kB2.another_ref()),
                owl__nB_kB2: SecretBuf::from_buf(owl__nB_kB2.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_kB_message_2_inner<'a>(arg: &owl_kB_message_2<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_kB_message_2_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_kB_message_2_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_kB_message_2_inner);
    if no_usize_overflows![ arg.owl__A_kB2.len(), arg.owl__kAB_kB2.len(), arg.owl__nB_kB2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_kB_message_2();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__A_kB2.len() + arg.owl__kAB_kB2.len() + arg.owl__nB_kB2.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    SecretBuf::from_buf(arg.owl__A_kB2.another_ref()),
                    SecretBuf::another_ref(&arg.owl__kAB_kB2),
                ),
                SecretBuf::another_ref(&arg.owl__nB_kB2),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_kB_message_2_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_kB_message_2<'a>(arg: &owl_kB_message_2<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_kB_message_2(arg.view()),
{
    reveal(serialize_owlSpec_kB_message_2);
    let res = serialize_owl_kB_message_2_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_kB_message_2<'a> {
    pub owl__A_kB2: SecretBuf<'a>,
    pub owl__kAB_kB2: SecretBuf<'a>,
    pub owl__nB_kB2: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_kB_message_2<'a>(
    arg_owl__A_kB2: SecretBuf<'a>,
    arg_owl__kAB_kB2: SecretBuf<'a>,
    arg_owl__nB_kB2: SecretBuf<'a>,
) -> (res: owl_secret_kB_message_2<'a>)
    ensures
        res.owl__A_kB2.view() == arg_owl__A_kB2.view(),
        res.owl__kAB_kB2.view() == arg_owl__kAB_kB2.view(),
        res.owl__nB_kB2.view() == arg_owl__nB_kB2.view(),
{
    owl_secret_kB_message_2 {
        owl__A_kB2: arg_owl__A_kB2,
        owl__kAB_kB2: arg_owl__kAB_kB2,
        owl__nB_kB2: arg_owl__nB_kB2,
    }
}

impl<'a> owl_secret_kB_message_2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_kB_message_2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_kB_message_2 {
            owl__A_kB2: SecretBuf::another_ref(&self.owl__A_kB2),
            owl__kAB_kB2: SecretBuf::another_ref(&self.owl__kAB_kB2),
            owl__nB_kB2: SecretBuf::another_ref(&self.owl__nB_kB2),
        }
    }
}

impl View for owl_secret_kB_message_2<'_> {
    type V = owlSpec_secret_kB_message_2;

    open spec fn view(&self) -> owlSpec_secret_kB_message_2 {
        owlSpec_secret_kB_message_2 {
            owlSpec__A_kB2: self.owl__A_kB2.view(),
            owlSpec__kAB_kB2: self.owl__kAB_kB2.view(),
            owlSpec__nB_kB2: self.owl__nB_kB2.view(),
        }
    }
}

pub exec fn parse_owl_secret_kB_message_2<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_secret_kB_message_2<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kB_message_2(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kB_message_2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kB_message_2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kB_message_2);
    let exec_comb = exec_combinator_owl_secret_kB_message_2();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl__A_kB2, owl__kAB_kB2), owl__nB_kB2) = parsed;
        Some(
            owl_secret_kB_message_2 {
                owl__A_kB2: SecretBuf::from_buf(owl__A_kB2.another_ref()),
                owl__kAB_kB2: SecretBuf::from_buf(owl__kAB_kB2.another_ref()),
                owl__nB_kB2: SecretBuf::from_buf(owl__nB_kB2.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_kB_message_2<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_kB_message_2<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kB_message_2(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kB_message_2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kB_message_2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kB_message_2);
    let exec_comb = exec_combinator_owl_secret_kB_message_2();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let ((owl__A_kB2, owl__kAB_kB2), owl__nB_kB2) = parsed;
        Some(
            owl_secret_kB_message_2 {
                owl__A_kB2: SecretBuf::another_ref(&owl__A_kB2),
                owl__kAB_kB2: SecretBuf::another_ref(&owl__kAB_kB2),
                owl__nB_kB2: SecretBuf::another_ref(&owl__nB_kB2),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_kB_message_2_inner<'a>(arg: &owl_secret_kB_message_2<'a>) -> (res:
    Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_secret_kB_message_2_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_kB_message_2_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_secret_kB_message_2_inner);
    if no_usize_overflows![ arg.owl__A_kB2.len(), arg.owl__kAB_kB2.len(), arg.owl__nB_kB2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_kB_message_2();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__A_kB2.len() + arg.owl__kAB_kB2.len() + arg.owl__nB_kB2.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    SecretBuf::another_ref(&arg.owl__A_kB2),
                    SecretBuf::another_ref(&arg.owl__kAB_kB2),
                ),
                SecretBuf::another_ref(&arg.owl__nB_kB2),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_kB_message_2_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_kB_message_2<'a>(arg: &owl_secret_kB_message_2<'a>) -> (res:
    SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_kB_message_2(arg.view()),
{
    reveal(serialize_owlSpec_secret_kB_message_2);
    let res = serialize_owl_secret_kB_message_2_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_kB_messages<'a> {
    owl_mB1(owl_kB_message_1<'a>),
    owl_mB2(owl_kB_message_2<'a>),
}

use owl_kB_messages::*;

impl<'a> owl_kB_messages<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kB_messages<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_mB1(x) => owl_mB1(owl_kB_message_1::another_ref(x)),
            owl_mB2(x) => owl_mB2(owl_kB_message_2::another_ref(x)),
        }
    }
}

impl View for owl_kB_messages<'_> {
    type V = owlSpec_kB_messages;

    open spec fn view(&self) -> owlSpec_kB_messages {
        match self {
            owl_mB1(v) => owlSpec_kB_messages::owlSpec_mB1(v.view()),
            owl_mB2(v) => owlSpec_kB_messages::owlSpec_mB2(v.view()),
        }
    }
}

#[inline]
pub fn owl_mB1_enumtest(x: &owl_kB_messages<'_>) -> (res: bool)
    ensures
        res == mB1_enumtest(x.view()),
{
    match x {
        owl_kB_messages::owl_mB1(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl_mB2_enumtest(x: &owl_kB_messages<'_>) -> (res: bool)
    ensures
        res == mB2_enumtest(x.view()),
{
    match x {
        owl_kB_messages::owl_mB2(_) => true,
        _ => false,
    }
}

#[verifier::external_body]
pub exec fn parse_owl_kB_messages<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_kB_messages<'a>>)
    ensures
        res is Some ==> parse_owlSpec_kB_messages(arg.view()) is Some,
        res is None ==> parse_owlSpec_kB_messages(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kB_messages(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_kB_messages<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_kB_messages<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_kB_messages(arg.view()) is Some,
        res is None ==> parse_owlSpec_kB_messages(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kB_messages(arg.view())->Some_0,
{
    reveal(parse_owlSpec_kB_messages);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_kB_messages_inner(arg: &owl_kB_messages) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_kB_messages_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_kB_messages_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_kB_messages_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_kB_messages(arg: &owl_kB_messages) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_kB_messages(arg.view()),
{
    unimplemented!()
}

pub enum owl_encd_by_kB<'a> {
    owl_e1(OwlBuf<'a>),
    owl_e2(OwlBuf<'a>),
}

use owl_encd_by_kB::*;

impl<'a> owl_encd_by_kB<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_encd_by_kB<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_e1(x) => owl_e1(OwlBuf::another_ref(x)),
            owl_e2(x) => owl_e2(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_encd_by_kB<'_> {
    type V = owlSpec_encd_by_kB;

    open spec fn view(&self) -> owlSpec_encd_by_kB {
        match self {
            owl_e1(v) => owlSpec_encd_by_kB::owlSpec_e1(v.view()),
            owl_e2(v) => owlSpec_encd_by_kB::owlSpec_e2(v.view()),
        }
    }
}

#[inline]
pub fn owl_e1_enumtest(x: &owl_encd_by_kB<'_>) -> (res: bool)
    ensures
        res == e1_enumtest(x.view()),
{
    match x {
        owl_encd_by_kB::owl_e1(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl_e2_enumtest(x: &owl_encd_by_kB<'_>) -> (res: bool)
    ensures
        res == e2_enumtest(x.view()),
{
    match x {
        owl_encd_by_kB::owl_e2(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_encd_by_kB<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_encd_by_kB<'a>>)
    ensures
        res is Some ==> parse_owlSpec_encd_by_kB(arg.view()) is Some,
        res is None ==> parse_owlSpec_encd_by_kB(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_encd_by_kB(arg.view())->Some_0,
{
    reveal(parse_owlSpec_encd_by_kB);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Tail), (Tag::new(U8, 2), Tail));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owl_encd_by_kB::owl_e1(OwlBuf::another_ref(&x)),
            inj_ord_choice_pat!(*, (_,x)) => owl_encd_by_kB::owl_e2(OwlBuf::another_ref(&x)),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn serialize_owl_encd_by_kB_inner(arg: &owl_encd_by_kB) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_encd_by_kB_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_encd_by_kB_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_encd_by_kB_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_encd_by_kB(arg: &owl_encd_by_kB) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_encd_by_kB(arg.view()),
{
    reveal(serialize_owlSpec_encd_by_kB);
    let res = serialize_owl_encd_by_kB_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_msg1_AtoB<'a> {
    pub owl_msg1_A: OwlBuf<'a>,
    pub owl_msg1_nA: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg1_AtoB<'a>(arg_owl_msg1_A: OwlBuf<'a>, arg_owl_msg1_nA: OwlBuf<'a>) -> (res:
    owl_msg1_AtoB<'a>)
    ensures
        res.owl_msg1_A.view() == arg_owl_msg1_A.view(),
        res.owl_msg1_nA.view() == arg_owl_msg1_nA.view(),
{
    owl_msg1_AtoB { owl_msg1_A: arg_owl_msg1_A, owl_msg1_nA: arg_owl_msg1_nA }
}

impl<'a> owl_msg1_AtoB<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg1_AtoB<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg1_AtoB {
            owl_msg1_A: OwlBuf::another_ref(&self.owl_msg1_A),
            owl_msg1_nA: OwlBuf::another_ref(&self.owl_msg1_nA),
        }
    }
}

impl View for owl_msg1_AtoB<'_> {
    type V = owlSpec_msg1_AtoB;

    open spec fn view(&self) -> owlSpec_msg1_AtoB {
        owlSpec_msg1_AtoB {
            owlSpec_msg1_A: self.owl_msg1_A.view(),
            owlSpec_msg1_nA: self.owl_msg1_nA.view(),
        }
    }
}

pub exec fn parse_owl_msg1_AtoB<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg1_AtoB<'a>>)
    ensures
        res is Some ==> parse_owlSpec_msg1_AtoB(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg1_AtoB(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg1_AtoB(arg.view())->Some_0,
{
    reveal(parse_owlSpec_msg1_AtoB);
    let exec_comb = exec_combinator_owl_msg1_AtoB();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl_msg1_A, owl_msg1_nA) = parsed;
        Some(
            owl_msg1_AtoB {
                owl_msg1_A: OwlBuf::another_ref(&owl_msg1_A),
                owl_msg1_nA: OwlBuf::another_ref(&owl_msg1_nA),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_msg1_AtoB_inner<'a>(arg: &owl_msg1_AtoB<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_msg1_AtoB_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg1_AtoB_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_msg1_AtoB_inner);
    if no_usize_overflows![ arg.owl_msg1_A.len(), arg.owl_msg1_nA.len(), 0 ] {
        let exec_comb = exec_combinator_owl_msg1_AtoB();
        let mut obuf = vec_u8_of_len(arg.owl_msg1_A.len() + arg.owl_msg1_nA.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl_msg1_A), OwlBuf::another_ref(&arg.owl_msg1_nA)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_msg1_AtoB_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_msg1_AtoB<'a>(arg: &owl_msg1_AtoB<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_msg1_AtoB(arg.view()),
{
    reveal(serialize_owlSpec_msg1_AtoB);
    let res = serialize_owl_msg1_AtoB_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_msg2_BtoS<'a> {
    pub owl_msg2_B: OwlBuf<'a>,
    pub owl_msg2_x: owl_encd_by_kB<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg2_BtoS<'a>(arg_owl_msg2_B: OwlBuf<'a>, arg_owl_msg2_x: owl_encd_by_kB<'a>) -> (res:
    owl_msg2_BtoS<'a>)
    ensures
        res.owl_msg2_B.view() == arg_owl_msg2_B.view(),
        res.owl_msg2_x.view() == arg_owl_msg2_x.view(),
{
    owl_msg2_BtoS { owl_msg2_B: arg_owl_msg2_B, owl_msg2_x: arg_owl_msg2_x }
}

impl<'a> owl_msg2_BtoS<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg2_BtoS<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg2_BtoS {
            owl_msg2_B: OwlBuf::another_ref(&self.owl_msg2_B),
            owl_msg2_x: owl_encd_by_kB::another_ref(&self.owl_msg2_x),
        }
    }
}

impl View for owl_msg2_BtoS<'_> {
    type V = owlSpec_msg2_BtoS;

    open spec fn view(&self) -> owlSpec_msg2_BtoS {
        owlSpec_msg2_BtoS {
            owlSpec_msg2_B: self.owl_msg2_B.view(),
            owlSpec_msg2_x: self.owl_msg2_x.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_msg2_BtoS<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg2_BtoS<'a>>)
    ensures
        res is Some ==> parse_owlSpec_msg2_BtoS(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg2_BtoS(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg2_BtoS(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_msg2_BtoS_inner<'a>(arg: &owl_msg2_BtoS) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_msg2_BtoS_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg2_BtoS_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_msg2_BtoS<'a>(arg: &owl_msg2_BtoS) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_msg2_BtoS(arg.view()),
{
    unimplemented!()
}

pub struct owl_msg3_StoA<'a> {
    pub owl_msg3_tkt1: OwlBuf<'a>,
    pub owl_msg3_tkt2: owl_encd_by_kB<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg3_StoA<'a>(
    arg_owl_msg3_tkt1: OwlBuf<'a>,
    arg_owl_msg3_tkt2: owl_encd_by_kB<'a>,
) -> (res: owl_msg3_StoA<'a>)
    ensures
        res.owl_msg3_tkt1.view() == arg_owl_msg3_tkt1.view(),
        res.owl_msg3_tkt2.view() == arg_owl_msg3_tkt2.view(),
{
    owl_msg3_StoA { owl_msg3_tkt1: arg_owl_msg3_tkt1, owl_msg3_tkt2: arg_owl_msg3_tkt2 }
}

impl<'a> owl_msg3_StoA<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg3_StoA<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg3_StoA {
            owl_msg3_tkt1: OwlBuf::another_ref(&self.owl_msg3_tkt1),
            owl_msg3_tkt2: owl_encd_by_kB::another_ref(&self.owl_msg3_tkt2),
        }
    }
}

impl View for owl_msg3_StoA<'_> {
    type V = owlSpec_msg3_StoA;

    open spec fn view(&self) -> owlSpec_msg3_StoA {
        owlSpec_msg3_StoA {
            owlSpec_msg3_tkt1: self.owl_msg3_tkt1.view(),
            owlSpec_msg3_tkt2: self.owl_msg3_tkt2.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_msg3_StoA<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg3_StoA<'a>>)
    ensures
        res is Some ==> parse_owlSpec_msg3_StoA(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg3_StoA(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg3_StoA(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_msg3_StoA_inner<'a>(arg: &owl_msg3_StoA) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_msg3_StoA_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg3_StoA_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_msg3_StoA<'a>(arg: &owl_msg3_StoA) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_msg3_StoA(arg.view()),
{
    unimplemented!()
}

pub struct owl_msg4_AtoB<'a> {
    pub owl_msg4_x: OwlBuf<'a>,
    pub owl_msg4_tkt: owl_encd_by_kB<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg4_AtoB<'a>(arg_owl_msg4_x: OwlBuf<'a>, arg_owl_msg4_tkt: owl_encd_by_kB<'a>) -> (res:
    owl_msg4_AtoB<'a>)
    ensures
        res.owl_msg4_x.view() == arg_owl_msg4_x.view(),
        res.owl_msg4_tkt.view() == arg_owl_msg4_tkt.view(),
{
    owl_msg4_AtoB { owl_msg4_x: arg_owl_msg4_x, owl_msg4_tkt: arg_owl_msg4_tkt }
}

impl<'a> owl_msg4_AtoB<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg4_AtoB<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg4_AtoB {
            owl_msg4_x: OwlBuf::another_ref(&self.owl_msg4_x),
            owl_msg4_tkt: owl_encd_by_kB::another_ref(&self.owl_msg4_tkt),
        }
    }
}

impl View for owl_msg4_AtoB<'_> {
    type V = owlSpec_msg4_AtoB;

    open spec fn view(&self) -> owlSpec_msg4_AtoB {
        owlSpec_msg4_AtoB {
            owlSpec_msg4_x: self.owl_msg4_x.view(),
            owlSpec_msg4_tkt: self.owl_msg4_tkt.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_msg4_AtoB<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg4_AtoB<'a>>)
    ensures
        res is Some ==> parse_owlSpec_msg4_AtoB(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg4_AtoB(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg4_AtoB(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_msg4_AtoB_inner<'a>(arg: &owl_msg4_AtoB) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_msg4_AtoB_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg4_AtoB_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_msg4_AtoB<'a>(arg: &owl_msg4_AtoB) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_msg4_AtoB(arg.view()),
{
    unimplemented!()
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
    pub owl_KB: SecretBuf<'AS>,
    pub owl_KA: SecretBuf<'AS>,
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
            let tmp_owl_kAB241 = { SecretBuf::another_ref(&self.owl_KAB) };
            let owl_kAB241 = SecretBuf::another_ref(&tmp_owl_kAB241);
            let tmp_owl_kA242 = { SecretBuf::another_ref(&self.owl_KA) };
            let owl_kA242 = SecretBuf::another_ref(&tmp_owl_kA242);
            let tmp_owl_kB243 = { SecretBuf::another_ref(&self.owl_KB) };
            let owl_kB243 = SecretBuf::another_ref(&tmp_owl_kB243);
            let (tmp_owl_inp245, owl__244) = {
                effects.owl_input::<((), state_AS)>(Tracked(&mut itree))
            };
            let owl_inp245 = OwlBuf::from_vec(tmp_owl_inp245);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp245);
            if let Some(parseval) = parse_owl_msg2_BtoS(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_B_247 = OwlBuf::another_ref(&parseval.owl_msg2_B);
                let owl_x_246 = owl_encd_by_kB::another_ref(&parseval.owl_msg2_x);
                {
                    match owl_encd_by_kB::another_ref(&owl_x_246) {
                        owl_encd_by_kB::owl_e2(tmp_owl__248) => {
                            let owl__248 = OwlBuf::another_ref(&tmp_owl__248);
                            (owl_unit(), Tracked(itree))
                        },
                        owl_encd_by_kB::owl_e1(tmp_owl_x__249) => {
                            let owl_x__249 = OwlBuf::another_ref(&tmp_owl_x__249);
                            let tmp_owl_caseval250 = {
                                let tracked owl_declassify_tok251 = consume_itree_declassify::<
                                    ((), state_AS),
                                    Endpoint,
                                >(&mut itree);
                                owl_dec(
                                    SecretBuf::another_ref(&owl_kB243),
                                    OwlBuf::another_ref(&owl_x__249),
                                    Tracked(owl_declassify_tok251),
                                )
                            };
                            let owl_caseval250 = SecretBuf::another_ref_option(&tmp_owl_caseval250);
                            match SecretBuf::another_ref_option(&owl_caseval250) {
                                Option::None => { (owl_unit(), Tracked(itree)) },
                                Option::Some(tmp_owl_res252) => {
                                    let owl_res252 = SecretBuf::another_ref(&tmp_owl_res252);
                                    let tmp_owl_res_253 = { SecretBuf::another_ref(&owl_res252) };
                                    let owl_res_253 = SecretBuf::another_ref(&tmp_owl_res_253);
                                    let tmp_owl_res__254 = { SecretBuf::another_ref(&owl_res_253) };
                                    let owl_res__254 = SecretBuf::another_ref(&tmp_owl_res__254);
                                    let tracked owl_declassify_tok255 = consume_itree_declassify::<
                                        ((), state_AS),
                                        Endpoint,
                                    >(&mut itree);
                                    let parseval_tmp = SecretBuf::another_ref(&owl_res__254);
                                    if let Some(parseval) = secret_parse_owl_kB_messages(
                                        SecretBuf::another_ref(&parseval_tmp),
                                        Tracked(owl_declassify_tok255),
                                    ) {
                                        let owl_parsed_caseval256 = owl_kB_messages::another_ref(
                                            &parseval,
                                        );
                                        match owl_kB_messages::another_ref(&owl_parsed_caseval256) {
                                            owl_kB_messages::owl_mB1(tmp_owl_msg1257) => {
                                                let owl_msg1257 = owl_kB_message_1::another_ref(
                                                    &tmp_owl_msg1257,
                                                );
                                                let parseval = owl_kB_message_1::another_ref(
                                                    &owl_msg1257,
                                                );
                                                let owl_A_260 = OwlBuf::another_ref(
                                                    &parseval.owl__A_kB1,
                                                );
                                                let owl_nA_259 = OwlBuf::another_ref(
                                                    &parseval.owl__nA_kB1,
                                                );
                                                let owl_nB_258 = SecretBuf::another_ref(
                                                    &parseval.owl__nB_kB1,
                                                );
                                                {
                                                    let tmp_owl_declassified_buf74261 = {
                                                        let tracked owl_declassify_tok262 =
                                                            consume_itree_declassify::<
                                                            ((), state_AS),
                                                            Endpoint,
                                                        >(&mut itree);
                                                        {
                                                            SecretBuf::another_ref(
                                                                &owl_nB_258,
                                                            ).declassify(
                                                                Tracked(owl_declassify_tok262),
                                                            )
                                                        }
                                                    };
                                                    let owl_declassified_buf74261 =
                                                        OwlBuf::another_ref(
                                                        &tmp_owl_declassified_buf74261,
                                                    );
                                                    let tmp_owl_m263 = {
                                                        owl_kA_message(
                                                            OwlBuf::another_ref(&owl_B_247),
                                                            SecretBuf::another_ref(&owl_kAB241),
                                                            OwlBuf::another_ref(&owl_nA_259),
                                                            OwlBuf::another_ref(
                                                                &owl_declassified_buf74261,
                                                            ),
                                                        )
                                                    };
                                                    let owl_m263 = owl_kA_message::another_ref(
                                                        &tmp_owl_m263,
                                                    );
                                                    let tmp_owl_encmA264 = {
                                                        let tmp_owl_coins265 = effects.owl_sample::<
                                                            ((), state_AS),
                                                        >(Tracked(&mut itree), NONCE_SIZE);
                                                        let owl_coins265 = SecretBuf::another_ref(
                                                            &tmp_owl_coins265,
                                                        );
                                                        owl_enc(
                                                            SecretBuf::another_ref(&owl_kA242),
                                                            SecretBuf::another_ref(
                                                                &serialize_owl_kA_message(
                                                                    &owl_m263,
                                                                ),
                                                            ),
                                                            SecretBuf::another_ref(&owl_coins265),
                                                        )
                                                    };
                                                    let owl_encmA264 = OwlBuf::from_vec(
                                                        tmp_owl_encmA264,
                                                    );
                                                    let tmp_owl_m266 = {
                                                        owl_mB2(
                                                            owl_kB_message_2::another_ref(
                                                                &owl_kB_message_2(
                                                                    OwlBuf::another_ref(&owl_A_260),
                                                                    SecretBuf::another_ref(
                                                                        &owl_kAB241,
                                                                    ),
                                                                    SecretBuf::another_ref(
                                                                        &owl_nB_258,
                                                                    ),
                                                                ),
                                                            ),
                                                        )
                                                    };
                                                    let owl_m266 = owl_kB_messages::another_ref(
                                                        &tmp_owl_m266,
                                                    );
                                                    let tmp_owl_encmB267 = {
                                                        let tmp_owl_coins268 = effects.owl_sample::<
                                                            ((), state_AS),
                                                        >(Tracked(&mut itree), NONCE_SIZE);
                                                        let owl_coins268 = SecretBuf::another_ref(
                                                            &tmp_owl_coins268,
                                                        );
                                                        owl_enc(
                                                            SecretBuf::another_ref(&owl_kB243),
                                                            SecretBuf::another_ref(
                                                                &OwlBuf::from_vec(
                                                                    serialize_owl_kB_messages(
                                                                        &owl_m266,
                                                                    ),
                                                                ).into_secret(),
                                                            ),
                                                            SecretBuf::another_ref(&owl_coins268),
                                                        )
                                                    };
                                                    let owl_encmB267 = OwlBuf::from_vec(
                                                        tmp_owl_encmB267,
                                                    );
                                                    let owl__269 = {
                                                        effects.owl_output::<((), state_AS)>(
                                                            Tracked(&mut itree),
                                                            serialize_owl_msg3_StoA(
                                                                &owl_msg3_StoA(
                                                                    OwlBuf::another_ref(
                                                                        &owl_encmA264,
                                                                    ),
                                                                    owl_encd_by_kB::another_ref(
                                                                        &owl_e2(
                                                                            OwlBuf::another_ref(
                                                                                &owl_encmB267,
                                                                            ),
                                                                        ),
                                                                    ),
                                                                ),
                                                            ).as_slice(),
                                                            Some(&Alice_addr()),
                                                            &AS_addr(),
                                                        );
                                                    };
                                                    (owl_unit(), Tracked(itree))
                                                }
                                            },
                                            owl_kB_messages::owl_mB2(tmp_owl__270) => {
                                                let owl__270 = owl_kB_message_2::another_ref(
                                                    &tmp_owl__270,
                                                );
                                                (owl_unit(), Tracked(itree))
                                            },
                                        }
                                    } else {
                                        (owl_unit(), Tracked(itree))
                                    }
                                },
                            }
                        },
                    }
                }
            } else {
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
    pub owl_Alice_username: SecretBuf<'Alice>,
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
            let tmp_owl_A271 = { SecretBuf::another_ref(&self.owl_Alice_username) };
            let owl_A271 = SecretBuf::another_ref(&tmp_owl_A271);
            let tmp_owl_nA272 = { SecretBuf::another_ref(&self.owl_NA) };
            let owl_nA272 = SecretBuf::another_ref(&tmp_owl_nA272);
            let tmp_owl_kA273 = { SecretBuf::another_ref(&self.owl_KA) };
            let owl_kA273 = SecretBuf::another_ref(&tmp_owl_kA273);
            let tmp_owl_declassified_buf90274 = {
                let tracked owl_declassify_tok275 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_A271).declassify(Tracked(owl_declassify_tok275)) }
            };
            let owl_declassified_buf90274 = OwlBuf::another_ref(&tmp_owl_declassified_buf90274);
            let tmp_owl_declassified_buf93276 = {
                let tracked owl_declassify_tok277 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_nA272).declassify(Tracked(owl_declassify_tok277)) }
            };
            let owl_declassified_buf93276 = OwlBuf::another_ref(&tmp_owl_declassified_buf93276);
            let owl__278 = {
                effects.owl_output::<(owlSpec_alice_result, state_Alice)>(
                    Tracked(&mut itree),
                    serialize_owl_msg1_AtoB(
                        &owl_msg1_AtoB(
                            OwlBuf::another_ref(&owl_declassified_buf90274),
                            OwlBuf::another_ref(&owl_declassified_buf93276),
                        ),
                    ).as_slice(),
                    Some(&Bob_addr()),
                    &Alice_addr(),
                );
            };
            let (tmp_owl_inp1280, owl__279) = {
                effects.owl_input::<(owlSpec_alice_result, state_Alice)>(Tracked(&mut itree))
            };
            let owl_inp1280 = OwlBuf::from_vec(tmp_owl_inp1280);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp1280);
            if let Some(parseval) = parse_owl_msg3_StoA(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_tkt1282 = OwlBuf::another_ref(&parseval.owl_msg3_tkt1);
                let owl_tkt2281 = owl_encd_by_kB::another_ref(&parseval.owl_msg3_tkt2);
                let tmp_owl_caseval283 = {
                    let tracked owl_declassify_tok284 = consume_itree_declassify::<
                        (owlSpec_alice_result, state_Alice),
                        Endpoint,
                    >(&mut itree);
                    owl_dec(
                        SecretBuf::another_ref(&owl_kA273),
                        OwlBuf::another_ref(&owl_tkt1282),
                        Tracked(owl_declassify_tok284),
                    )
                };
                let owl_caseval283 = SecretBuf::another_ref_option(&tmp_owl_caseval283);
                {
                    match SecretBuf::another_ref_option(&owl_caseval283) {
                        Option::None => {
                            let owl__285 = { owl_unit() };
                            (owl_alice_result::another_ref(&owl_alice_None()), Tracked(itree))
                        },
                        Option::Some(tmp_owl_res286) => {
                            let owl_res286 = SecretBuf::another_ref(&tmp_owl_res286);
                            let tmp_owl_res_287 = { SecretBuf::another_ref(&owl_res286) };
                            let owl_res_287 = SecretBuf::another_ref(&tmp_owl_res_287);
                            let parseval_tmp = SecretBuf::another_ref(&owl_res_287);
                            if let Some(parseval) = secret_parse_owl_secret_kA_message(
                                SecretBuf::another_ref(&parseval_tmp),
                            ) {
                                let owl_B_291 = SecretBuf::another_ref(&parseval.owl__B_kA);
                                let owl_kAB_290 = SecretBuf::another_ref(&parseval.owl__kAB_kA);
                                let owl_nA_289 = SecretBuf::another_ref(&parseval.owl__nA_kA);
                                let owl_nB_288 = SecretBuf::another_ref(&parseval.owl__nB_kA);
                                let tmp_owl_declassified_buf121292 = {
                                    let tracked owl_declassify_tok293 = consume_itree_declassify::<
                                        (owlSpec_alice_result, state_Alice),
                                        Endpoint,
                                    >(&mut itree);
                                    {
                                        SecretBuf::another_ref(&owl_B_291).declassify(
                                            Tracked(owl_declassify_tok293),
                                        )
                                    }
                                };
                                let owl_declassified_buf121292 = OwlBuf::another_ref(
                                    &tmp_owl_declassified_buf121292,
                                );
                                let tmp_owl_declassified_buf124294 = {
                                    let tracked owl_declassify_tok295 = consume_itree_declassify::<
                                        (owlSpec_alice_result, state_Alice),
                                        Endpoint,
                                    >(&mut itree);
                                    {
                                        SecretBuf::another_ref(&owl_nA_289).declassify(
                                            Tracked(owl_declassify_tok295),
                                        )
                                    }
                                };
                                let owl_declassified_buf124294 = OwlBuf::another_ref(
                                    &tmp_owl_declassified_buf124294,
                                );
                                let tmp_owl_declassified_buf127296 = {
                                    let tracked owl_declassify_tok297 = consume_itree_declassify::<
                                        (owlSpec_alice_result, state_Alice),
                                        Endpoint,
                                    >(&mut itree);
                                    {
                                        SecretBuf::another_ref(&owl_nB_288).declassify(
                                            Tracked(owl_declassify_tok297),
                                        )
                                    }
                                };
                                let owl_declassified_buf127296 = OwlBuf::another_ref(
                                    &tmp_owl_declassified_buf127296,
                                );
                                {
                                    let tmp_owl_encm298 = {
                                        let tmp_owl_coins299 = effects.owl_sample::<
                                            (owlSpec_alice_result, state_Alice),
                                        >(Tracked(&mut itree), NONCE_SIZE);
                                        let owl_coins299 = SecretBuf::another_ref(
                                            &tmp_owl_coins299,
                                        );
                                        owl_enc(
                                            SecretBuf::another_ref(&owl_kAB_290),
                                            SecretBuf::another_ref(
                                                &SecretBuf::from_buf(
                                                    owl_declassified_buf127296.another_ref(),
                                                ),
                                            ),
                                            SecretBuf::another_ref(&owl_coins299),
                                        )
                                    };
                                    let owl_encm298 = OwlBuf::from_vec(tmp_owl_encm298);
                                    let owl__300 = {
                                        effects.owl_output::<(owlSpec_alice_result, state_Alice)>(
                                            Tracked(&mut itree),
                                            serialize_owl_msg4_AtoB(
                                                &owl_msg4_AtoB(
                                                    OwlBuf::another_ref(&owl_encm298),
                                                    owl_encd_by_kB::another_ref(&owl_tkt2281),
                                                ),
                                            ).as_slice(),
                                            Some(&Bob_addr()),
                                            &Alice_addr(),
                                        );
                                    };
                                    (
                                        owl_alice_result::another_ref(
                                            &owl_alice_Some(SecretBuf::another_ref(&owl_kAB_290)),
                                        ),
                                        Tracked(itree),
                                    )
                                }
                            } else {
                                (owl_alice_result::another_ref(&owl_alice_None()), Tracked(itree))
                            }
                        },
                    }
                }
            } else {
                {
                    let owl__301 = { owl_unit() };
                    (owl_alice_result::another_ref(&owl_alice_None()), Tracked(itree))
                }
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
    pub owl_Bob_username: SecretBuf<'Bob>,
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
            let tmp_owl_B302 = { SecretBuf::another_ref(&self.owl_Bob_username) };
            let owl_B302 = SecretBuf::another_ref(&tmp_owl_B302);
            let tmp_owl_nB303 = { SecretBuf::another_ref(&self.owl_NB) };
            let owl_nB303 = SecretBuf::another_ref(&tmp_owl_nB303);
            let tmp_owl_kB304 = { SecretBuf::another_ref(&self.owl_KB) };
            let owl_kB304 = SecretBuf::another_ref(&tmp_owl_kB304);
            let (tmp_owl_inp306, owl__305) = {
                effects.owl_input::<(owlSpec_bob_result, state_Bob)>(Tracked(&mut itree))
            };
            let owl_inp306 = OwlBuf::from_vec(tmp_owl_inp306);
            let owl__307 = { owl_unit() };
            let parseval_tmp = OwlBuf::another_ref(&owl_inp306);
            if let Some(parseval) = parse_owl_msg1_AtoB(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_A_309 = OwlBuf::another_ref(&parseval.owl_msg1_A);
                let owl_nA_308 = OwlBuf::another_ref(&parseval.owl_msg1_nA);
                {
                    let tmp_owl_temp_packed310 = {
                        owl_mB1(
                            owl_kB_message_1::another_ref(
                                &owl_kB_message_1(
                                    OwlBuf::another_ref(&owl_A_309),
                                    OwlBuf::another_ref(&owl_nA_308),
                                    SecretBuf::another_ref(&owl_nB303),
                                ),
                            ),
                        )
                    };
                    let owl_temp_packed310 = owl_kB_messages::another_ref(&tmp_owl_temp_packed310);
                    let tmp_owl_encm311 = {
                        let tmp_owl_coins312 = effects.owl_sample::<
                            (owlSpec_bob_result, state_Bob),
                        >(Tracked(&mut itree), NONCE_SIZE);
                        let owl_coins312 = SecretBuf::another_ref(&tmp_owl_coins312);
                        owl_enc(
                            SecretBuf::another_ref(&owl_kB304),
                            SecretBuf::another_ref(
                                &OwlBuf::from_vec(
                                    serialize_owl_kB_messages(&owl_temp_packed310),
                                ).into_secret(),
                            ),
                            SecretBuf::another_ref(&owl_coins312),
                        )
                    };
                    let owl_encm311 = OwlBuf::from_vec(tmp_owl_encm311);
                    let tmp_owl_declassified_buf147313 = {
                        let tracked owl_declassify_tok314 = consume_itree_declassify::<
                            (owlSpec_bob_result, state_Bob),
                            Endpoint,
                        >(&mut itree);
                        {
                            SecretBuf::another_ref(&owl_B302).declassify(
                                Tracked(owl_declassify_tok314),
                            )
                        }
                    };
                    let owl_declassified_buf147313 = OwlBuf::another_ref(
                        &tmp_owl_declassified_buf147313,
                    );
                    let owl__315 = {
                        effects.owl_output::<(owlSpec_bob_result, state_Bob)>(
                            Tracked(&mut itree),
                            serialize_owl_msg2_BtoS(
                                &owl_msg2_BtoS(
                                    OwlBuf::another_ref(&owl_declassified_buf147313),
                                    owl_encd_by_kB::another_ref(
                                        &owl_e1(OwlBuf::another_ref(&owl_encm311)),
                                    ),
                                ),
                            ).as_slice(),
                            Some(&AS_addr()),
                            &Bob_addr(),
                        );
                    };
                    let (tmp_owl_inp2317, owl__316) = {
                        effects.owl_input::<(owlSpec_bob_result, state_Bob)>(Tracked(&mut itree))
                    };
                    let owl_inp2317 = OwlBuf::from_vec(tmp_owl_inp2317);
                    let parseval_tmp = OwlBuf::another_ref(&owl_inp2317);
                    if let Some(parseval) = parse_owl_msg4_AtoB(
                        OwlBuf::another_ref(&parseval_tmp),
                    ) {
                        let owl_x319 = OwlBuf::another_ref(&parseval.owl_msg4_x);
                        let owl_tkt_318 = owl_encd_by_kB::another_ref(&parseval.owl_msg4_tkt);
                        {
                            match owl_encd_by_kB::another_ref(&owl_tkt_318) {
                                owl_encd_by_kB::owl_e1(tmp_owl__320) => {
                                    let owl__320 = OwlBuf::another_ref(&tmp_owl__320);
                                    (owl_bob_result::another_ref(&owl_bob_None()), Tracked(itree))
                                },
                                owl_encd_by_kB::owl_e2(tmp_owl_tkt321) => {
                                    let owl_tkt321 = OwlBuf::another_ref(&tmp_owl_tkt321);
                                    let tmp_owl_caseval322 = {
                                        let tracked owl_declassify_tok323 =
                                            consume_itree_declassify::<
                                            (owlSpec_bob_result, state_Bob),
                                            Endpoint,
                                        >(&mut itree);
                                        owl_dec(
                                            SecretBuf::another_ref(&owl_kB304),
                                            OwlBuf::another_ref(&owl_tkt321),
                                            Tracked(owl_declassify_tok323),
                                        )
                                    };
                                    let owl_caseval322 = SecretBuf::another_ref_option(
                                        &tmp_owl_caseval322,
                                    );
                                    match SecretBuf::another_ref_option(&owl_caseval322) {
                                        Option::None => {
                                            (
                                                owl_bob_result::another_ref(&owl_bob_None()),
                                                Tracked(itree),
                                            )
                                        },
                                        Option::Some(tmp_owl_res324) => {
                                            let owl_res324 = SecretBuf::another_ref(
                                                &tmp_owl_res324,
                                            );
                                            let tmp_owl_res_325 = {
                                                SecretBuf::another_ref(&owl_res324)
                                            };
                                            let owl_res_325 = SecretBuf::another_ref(
                                                &tmp_owl_res_325,
                                            );
                                            let tmp_owl_res__326 = {
                                                SecretBuf::another_ref(&owl_res_325)
                                            };
                                            let owl_res__326 = SecretBuf::another_ref(
                                                &tmp_owl_res__326,
                                            );
                                            let tracked owl_declassify_tok327 =
                                                consume_itree_declassify::<
                                                (owlSpec_bob_result, state_Bob),
                                                Endpoint,
                                            >(&mut itree);
                                            let parseval_tmp = SecretBuf::another_ref(
                                                &owl_res__326,
                                            );
                                            if let Some(parseval) = secret_parse_owl_kB_messages(
                                                SecretBuf::another_ref(&parseval_tmp),
                                                Tracked(owl_declassify_tok327),
                                            ) {
                                                let owl_parsed_caseval328 =
                                                    owl_kB_messages::another_ref(&parseval);
                                                match owl_kB_messages::another_ref(
                                                    &owl_parsed_caseval328,
                                                ) {
                                                    owl_kB_messages::owl_mB1(tmp_owl__329) => {
                                                        let owl__329 =
                                                            owl_kB_message_1::another_ref(
                                                            &tmp_owl__329,
                                                        );
                                                        (
                                                            owl_bob_result::another_ref(
                                                                &owl_bob_None(),
                                                            ),
                                                            Tracked(itree),
                                                        )
                                                    },
                                                    owl_kB_messages::owl_mB2(tmp_owl_msg2330) => {
                                                        let owl_msg2330 =
                                                            owl_kB_message_2::another_ref(
                                                            &tmp_owl_msg2330,
                                                        );
                                                        let parseval =
                                                            owl_kB_message_2::another_ref(
                                                            &owl_msg2330,
                                                        );
                                                        let owl_A__333 = OwlBuf::another_ref(
                                                            &parseval.owl__A_kB2,
                                                        );
                                                        let owl_kAB_332 = SecretBuf::another_ref(
                                                            &parseval.owl__kAB_kB2,
                                                        );
                                                        let owl_nB_331 = SecretBuf::another_ref(
                                                            &parseval.owl__nB_kB2,
                                                        );
                                                        let owl_eq_bool187334 = {
                                                            let tracked owl_declassify_tok335 =
                                                                consume_itree_declassify::<
                                                                (owlSpec_bob_result, state_Bob),
                                                                Endpoint,
                                                            >(&mut itree);
                                                            {
                                                                SecretBuf::secret_eq(
                                                                    &owl_nB_331,
                                                                    &owl_nB303,
                                                                    Tracked(owl_declassify_tok335),
                                                                )
                                                            }
                                                        };
                                                        {
                                                            if owl_eq_bool187334 {
                                                                let owl__assert_169336 = {
                                                                    owl_ghost_unit()
                                                                };
                                                                let tmp_owl_caseval337 = {
                                                                    let tracked owl_declassify_tok338 =
                                                                        consume_itree_declassify::<
                                                                        (
                                                                            owlSpec_bob_result,
                                                                            state_Bob,
                                                                        ),
                                                                        Endpoint,
                                                                    >(&mut itree);
                                                                    owl_dec(
                                                                        SecretBuf::another_ref(
                                                                            &owl_kAB_332,
                                                                        ),
                                                                        OwlBuf::another_ref(
                                                                            &owl_x319,
                                                                        ),
                                                                        Tracked(
                                                                            owl_declassify_tok338,
                                                                        ),
                                                                    )
                                                                };
                                                                let owl_caseval337 =
                                                                    SecretBuf::another_ref_option(
                                                                    &tmp_owl_caseval337,
                                                                );
                                                                match SecretBuf::another_ref_option(
                                                                    &owl_caseval337,
                                                                ) {
                                                                    Option::None => {
                                                                        (
                                                                            owl_bob_result::another_ref(
                                                                            &owl_bob_None()),
                                                                            Tracked(itree),
                                                                        )
                                                                    },
                                                                    Option::Some(
                                                                        tmp_owl_res2339,
                                                                    ) => {
                                                                        let owl_res2339 =
                                                                            SecretBuf::another_ref(
                                                                            &tmp_owl_res2339,
                                                                        );
                                                                        let tmp_owl_nB_340 = {
                                                                            SecretBuf::another_ref(
                                                                                &owl_res2339,
                                                                            )
                                                                        };
                                                                        let owl_nB_340 =
                                                                            SecretBuf::another_ref(
                                                                            &tmp_owl_nB_340,
                                                                        );
                                                                        let owl_eq_bool195341 = {
                                                                            let tracked owl_declassify_tok342 =
                                                                                consume_itree_declassify::<
                                                                                (
                                                                                    owlSpec_bob_result,
                                                                                    state_Bob,
                                                                                ),
                                                                                Endpoint,
                                                                            >(&mut itree);
                                                                            {
                                                                                SecretBuf::secret_eq(

                                                                                    &owl_nB_340,
                                                                                    &owl_nB303,
                                                                                    Tracked(
                                                                                        owl_declassify_tok342,
                                                                                    ),
                                                                                )
                                                                            }
                                                                        };

                                                                        if owl_eq_bool195341 {
                                                                            (
                                                                                owl_bob_result::another_ref(

                                                                                    &owl_bob_Some(
                                                                                        SecretBuf::another_ref(

                                                                                            &owl_kAB_332,
                                                                                        ),
                                                                                    ),
                                                                                ),
                                                                                Tracked(itree),
                                                                            )
                                                                        } else {
                                                                            (
                                                                                owl_bob_result::another_ref(
                                                                                &owl_bob_None()),
                                                                                Tracked(itree),
                                                                            )
                                                                        }

                                                                    },
                                                                }
                                                            } else {
                                                                (
                                                                    owl_bob_result::another_ref(
                                                                        &owl_bob_None(),
                                                                    ),
                                                                    Tracked(itree),
                                                                )
                                                            }

                                                        }
                                                    },
                                                }
                                            } else {
                                                (
                                                    owl_bob_result::another_ref(&owl_bob_None()),
                                                    Tracked(itree),
                                                )
                                            }
                                        },
                                    }
                                },
                            }
                        }
                    } else {
                        (owl_bob_result::another_ref(&owl_bob_None()), Tracked(itree))
                    }
                }
            } else {
                (owl_bob_result::another_ref(&owl_bob_None()), Tracked(itree))
            }
        };
        Ok((owl_bob_result::another_ref(&res_inner), Tracked(itree)))
    }
}

} // verus!
