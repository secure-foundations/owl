// Extracted verus code from file owl_toy_protocols/otwayrees-indexed.owl:
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
spec fn spec_combinator_owlSpec_kA_message_1() -> (((Variable, Variable), Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_kA_message_1() -> (res: (((Variable, Variable), Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_kA_message_1(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_kA_message_1 {
    pub owlSpec__nA1: Seq<u8>,
    pub owlSpec__mA: Seq<u8>,
    pub owlSpec__AA: Seq<u8>,
    pub owlSpec__BA: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_kA_message_1(x: Seq<u8>) -> Option<owlSpec_kA_message_1> {
    let spec_comb = spec_combinator_owlSpec_kA_message_1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec__nA1, owlSpec__mA), owlSpec__AA), owlSpec__BA)) = parsed;
        Some(owlSpec_kA_message_1 { owlSpec__nA1, owlSpec__mA, owlSpec__AA, owlSpec__BA })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kA_message_1_inner(x: owlSpec_kA_message_1) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__nA1.len(), x.owlSpec__mA.len(), x.owlSpec__AA.len(), x.owlSpec__BA.len() ] {
        let spec_comb = spec_combinator_owlSpec_kA_message_1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec__nA1, x.owlSpec__mA), x.owlSpec__AA), x.owlSpec__BA)),
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
pub closed spec fn serialize_owlSpec_kA_message_1(x: owlSpec_kA_message_1) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_kA_message_1_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_kA_message_1 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_kA_message_1(self)
    }
}

pub open spec fn kA_message_1(
    arg_owlSpec__nA1: Seq<u8>,
    arg_owlSpec__mA: Seq<u8>,
    arg_owlSpec__AA: Seq<u8>,
    arg_owlSpec__BA: Seq<u8>,
) -> owlSpec_kA_message_1 {
    owlSpec_kA_message_1 {
        owlSpec__nA1: arg_owlSpec__nA1,
        owlSpec__mA: arg_owlSpec__mA,
        owlSpec__AA: arg_owlSpec__AA,
        owlSpec__BA: arg_owlSpec__BA,
    }
}

spec fn spec_combinator_owlSpec_secret_kA_message_1() -> (
    ((Variable, Variable), Variable),
    Variable,
) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_secret_kA_message_1() -> (res: (
    ((Variable, Variable), Variable),
    Variable,
))
    ensures
        res.view() == spec_combinator_owlSpec_secret_kA_message_1(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_secret_kA_message_1 {
    pub owlSpec__nA1: Seq<u8>,
    pub owlSpec__mA: Seq<u8>,
    pub owlSpec__AA: Seq<u8>,
    pub owlSpec__BA: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_kA_message_1(x: Seq<u8>) -> Option<
    owlSpec_secret_kA_message_1,
> {
    let spec_comb = spec_combinator_owlSpec_secret_kA_message_1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec__nA1, owlSpec__mA), owlSpec__AA), owlSpec__BA)) = parsed;
        Some(owlSpec_secret_kA_message_1 { owlSpec__nA1, owlSpec__mA, owlSpec__AA, owlSpec__BA })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kA_message_1_inner(
    x: owlSpec_secret_kA_message_1,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__nA1.len(), x.owlSpec__mA.len(), x.owlSpec__AA.len(), x.owlSpec__BA.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_kA_message_1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec__nA1, x.owlSpec__mA), x.owlSpec__AA), x.owlSpec__BA)),
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
pub closed spec fn serialize_owlSpec_secret_kA_message_1(x: owlSpec_secret_kA_message_1) -> Seq<
    u8,
> {
    if let Some(val) = serialize_owlSpec_secret_kA_message_1_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_kA_message_1 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_kA_message_1(self)
    }
}

pub open spec fn secret_kA_message_1(
    arg_owlSpec__nA1: Seq<u8>,
    arg_owlSpec__mA: Seq<u8>,
    arg_owlSpec__AA: Seq<u8>,
    arg_owlSpec__BA: Seq<u8>,
) -> owlSpec_secret_kA_message_1 {
    owlSpec_secret_kA_message_1 {
        owlSpec__nA1: arg_owlSpec__nA1,
        owlSpec__mA: arg_owlSpec__mA,
        owlSpec__AA: arg_owlSpec__AA,
        owlSpec__BA: arg_owlSpec__BA,
    }
}

spec fn spec_combinator_owlSpec_kA_message_2() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    (field_1, field_2)
}

exec fn exec_combinator_owl_kA_message_2() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_kA_message_2(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    (field_1, field_2)
}

pub struct owlSpec_kA_message_2 {
    pub owlSpec__nA2: Seq<u8>,
    pub owlSpec__kABA: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_kA_message_2(x: Seq<u8>) -> Option<owlSpec_kA_message_2> {
    let spec_comb = spec_combinator_owlSpec_kA_message_2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__nA2, owlSpec__kABA)) = parsed;
        Some(owlSpec_kA_message_2 { owlSpec__nA2, owlSpec__kABA })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kA_message_2_inner(x: owlSpec_kA_message_2) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__nA2.len(), x.owlSpec__kABA.len() ] {
        let spec_comb = spec_combinator_owlSpec_kA_message_2();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__nA2, x.owlSpec__kABA))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kA_message_2(x: owlSpec_kA_message_2) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_kA_message_2_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_kA_message_2 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_kA_message_2(self)
    }
}

pub open spec fn kA_message_2(
    arg_owlSpec__nA2: Seq<u8>,
    arg_owlSpec__kABA: Seq<u8>,
) -> owlSpec_kA_message_2 {
    owlSpec_kA_message_2 { owlSpec__nA2: arg_owlSpec__nA2, owlSpec__kABA: arg_owlSpec__kABA }
}

spec fn spec_combinator_owlSpec_secret_kA_message_2() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    (field_1, field_2)
}

exec fn exec_combinator_owl_secret_kA_message_2() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_kA_message_2(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    (field_1, field_2)
}

pub struct owlSpec_secret_kA_message_2 {
    pub owlSpec__nA2: Seq<u8>,
    pub owlSpec__kABA: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_kA_message_2(x: Seq<u8>) -> Option<
    owlSpec_secret_kA_message_2,
> {
    let spec_comb = spec_combinator_owlSpec_secret_kA_message_2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__nA2, owlSpec__kABA)) = parsed;
        Some(owlSpec_secret_kA_message_2 { owlSpec__nA2, owlSpec__kABA })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kA_message_2_inner(
    x: owlSpec_secret_kA_message_2,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__nA2.len(), x.owlSpec__kABA.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_kA_message_2();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__nA2, x.owlSpec__kABA))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kA_message_2(x: owlSpec_secret_kA_message_2) -> Seq<
    u8,
> {
    if let Some(val) = serialize_owlSpec_secret_kA_message_2_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_kA_message_2 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_kA_message_2(self)
    }
}

pub open spec fn secret_kA_message_2(
    arg_owlSpec__nA2: Seq<u8>,
    arg_owlSpec__kABA: Seq<u8>,
) -> owlSpec_secret_kA_message_2 {
    owlSpec_secret_kA_message_2 { owlSpec__nA2: arg_owlSpec__nA2, owlSpec__kABA: arg_owlSpec__kABA }
}

pub enum owlSpec_kA_messages {
    owlSpec_mA1(owlSpec_kA_message_1),
    owlSpec_mA2(owlSpec_kA_message_2),
}

use owlSpec_kA_messages::*;

#[verifier::external_body]
pub closed spec fn parse_owlSpec_kA_messages(x: Seq<u8>) -> Option<owlSpec_kA_messages> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_kA_messages_inner(x: owlSpec_kA_messages) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_kA_messages(x: owlSpec_kA_messages) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_kA_messages {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_kA_messages(self)
    }
}

pub open spec fn mA1(x: owlSpec_kA_message_1) -> owlSpec_kA_messages {
    crate::owlSpec_kA_messages::owlSpec_mA1(x)
}

pub open spec fn mA2(x: owlSpec_kA_message_2) -> owlSpec_kA_messages {
    crate::owlSpec_kA_messages::owlSpec_mA2(x)
}

pub open spec fn mA1_enumtest(x: owlSpec_kA_messages) -> bool {
    match x {
        owlSpec_kA_messages::owlSpec_mA1(_) => true,
        _ => false,
    }
}

pub open spec fn mA2_enumtest(x: owlSpec_kA_messages) -> bool {
    match x {
        owlSpec_kA_messages::owlSpec_mA2(_) => true,
        _ => false,
    }
}

pub enum owlSpec_encd_kA_message {
    owlSpec_mA1_enc(Seq<u8>),
    owlSpec_mA2_enc(Seq<u8>),
}

use owlSpec_encd_kA_message::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_encd_kA_message(x: Seq<u8>) -> Option<owlSpec_encd_kA_message> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Tail), (Tag::spec_new(U8, 2), Tail));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owlSpec_encd_kA_message::owlSpec_mA1_enc(x),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_encd_kA_message::owlSpec_mA2_enc(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_encd_kA_message_inner(x: owlSpec_encd_kA_message) -> Option<
    Seq<u8>,
> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Tail), (Tag::spec_new(U8, 2), Tail));
    match x {
        owlSpec_encd_kA_message::owlSpec_mA1_enc(x) => {
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
        owlSpec_encd_kA_message::owlSpec_mA2_enc(x) => {
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
pub closed spec fn serialize_owlSpec_encd_kA_message(x: owlSpec_encd_kA_message) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_encd_kA_message_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_encd_kA_message {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_encd_kA_message(self)
    }
}

pub open spec fn mA1_enc(x: Seq<u8>) -> owlSpec_encd_kA_message {
    crate::owlSpec_encd_kA_message::owlSpec_mA1_enc(x)
}

pub open spec fn mA2_enc(x: Seq<u8>) -> owlSpec_encd_kA_message {
    crate::owlSpec_encd_kA_message::owlSpec_mA2_enc(x)
}

pub open spec fn mA1_enc_enumtest(x: owlSpec_encd_kA_message) -> bool {
    match x {
        owlSpec_encd_kA_message::owlSpec_mA1_enc(_) => true,
        _ => false,
    }
}

pub open spec fn mA2_enc_enumtest(x: owlSpec_encd_kA_message) -> bool {
    match x {
        owlSpec_encd_kA_message::owlSpec_mA2_enc(_) => true,
        _ => false,
    }
}

spec fn spec_combinator_owlSpec_kB_message_1() -> (((Variable, Variable), Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_kB_message_1() -> (res: (((Variable, Variable), Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_kB_message_1(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_kB_message_1 {
    pub owlSpec__nB1: Seq<u8>,
    pub owlSpec__mB: Seq<u8>,
    pub owlSpec__AB: Seq<u8>,
    pub owlSpec__BB: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_kB_message_1(x: Seq<u8>) -> Option<owlSpec_kB_message_1> {
    let spec_comb = spec_combinator_owlSpec_kB_message_1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec__nB1, owlSpec__mB), owlSpec__AB), owlSpec__BB)) = parsed;
        Some(owlSpec_kB_message_1 { owlSpec__nB1, owlSpec__mB, owlSpec__AB, owlSpec__BB })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kB_message_1_inner(x: owlSpec_kB_message_1) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__nB1.len(), x.owlSpec__mB.len(), x.owlSpec__AB.len(), x.owlSpec__BB.len() ] {
        let spec_comb = spec_combinator_owlSpec_kB_message_1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec__nB1, x.owlSpec__mB), x.owlSpec__AB), x.owlSpec__BB)),
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
    arg_owlSpec__nB1: Seq<u8>,
    arg_owlSpec__mB: Seq<u8>,
    arg_owlSpec__AB: Seq<u8>,
    arg_owlSpec__BB: Seq<u8>,
) -> owlSpec_kB_message_1 {
    owlSpec_kB_message_1 {
        owlSpec__nB1: arg_owlSpec__nB1,
        owlSpec__mB: arg_owlSpec__mB,
        owlSpec__AB: arg_owlSpec__AB,
        owlSpec__BB: arg_owlSpec__BB,
    }
}

spec fn spec_combinator_owlSpec_secret_kB_message_1() -> (
    ((Variable, Variable), Variable),
    Variable,
) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_secret_kB_message_1() -> (res: (
    ((Variable, Variable), Variable),
    Variable,
))
    ensures
        res.view() == spec_combinator_owlSpec_secret_kB_message_1(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    let field_3 = Variable(12);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_secret_kB_message_1 {
    pub owlSpec__nB1: Seq<u8>,
    pub owlSpec__mB: Seq<u8>,
    pub owlSpec__AB: Seq<u8>,
    pub owlSpec__BB: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_kB_message_1(x: Seq<u8>) -> Option<
    owlSpec_secret_kB_message_1,
> {
    let spec_comb = spec_combinator_owlSpec_secret_kB_message_1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec__nB1, owlSpec__mB), owlSpec__AB), owlSpec__BB)) = parsed;
        Some(owlSpec_secret_kB_message_1 { owlSpec__nB1, owlSpec__mB, owlSpec__AB, owlSpec__BB })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kB_message_1_inner(
    x: owlSpec_secret_kB_message_1,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__nB1.len(), x.owlSpec__mB.len(), x.owlSpec__AB.len(), x.owlSpec__BB.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_kB_message_1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec__nB1, x.owlSpec__mB), x.owlSpec__AB), x.owlSpec__BB)),
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
    arg_owlSpec__nB1: Seq<u8>,
    arg_owlSpec__mB: Seq<u8>,
    arg_owlSpec__AB: Seq<u8>,
    arg_owlSpec__BB: Seq<u8>,
) -> owlSpec_secret_kB_message_1 {
    owlSpec_secret_kB_message_1 {
        owlSpec__nB1: arg_owlSpec__nB1,
        owlSpec__mB: arg_owlSpec__mB,
        owlSpec__AB: arg_owlSpec__AB,
        owlSpec__BB: arg_owlSpec__BB,
    }
}

spec fn spec_combinator_owlSpec_kB_message_2() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    (field_1, field_2)
}

exec fn exec_combinator_owl_kB_message_2() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_kB_message_2(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    (field_1, field_2)
}

pub struct owlSpec_kB_message_2 {
    pub owlSpec__nB2: Seq<u8>,
    pub owlSpec__kABB: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_kB_message_2(x: Seq<u8>) -> Option<owlSpec_kB_message_2> {
    let spec_comb = spec_combinator_owlSpec_kB_message_2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__nB2, owlSpec__kABB)) = parsed;
        Some(owlSpec_kB_message_2 { owlSpec__nB2, owlSpec__kABB })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_kB_message_2_inner(x: owlSpec_kB_message_2) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__nB2.len(), x.owlSpec__kABB.len() ] {
        let spec_comb = spec_combinator_owlSpec_kB_message_2();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__nB2, x.owlSpec__kABB))) {
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
    arg_owlSpec__nB2: Seq<u8>,
    arg_owlSpec__kABB: Seq<u8>,
) -> owlSpec_kB_message_2 {
    owlSpec_kB_message_2 { owlSpec__nB2: arg_owlSpec__nB2, owlSpec__kABB: arg_owlSpec__kABB }
}

spec fn spec_combinator_owlSpec_secret_kB_message_2() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    (field_1, field_2)
}

exec fn exec_combinator_owl_secret_kB_message_2() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_kB_message_2(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(32);
    (field_1, field_2)
}

pub struct owlSpec_secret_kB_message_2 {
    pub owlSpec__nB2: Seq<u8>,
    pub owlSpec__kABB: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_kB_message_2(x: Seq<u8>) -> Option<
    owlSpec_secret_kB_message_2,
> {
    let spec_comb = spec_combinator_owlSpec_secret_kB_message_2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__nB2, owlSpec__kABB)) = parsed;
        Some(owlSpec_secret_kB_message_2 { owlSpec__nB2, owlSpec__kABB })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_kB_message_2_inner(
    x: owlSpec_secret_kB_message_2,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__nB2.len(), x.owlSpec__kABB.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_kB_message_2();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__nB2, x.owlSpec__kABB))) {
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
    arg_owlSpec__nB2: Seq<u8>,
    arg_owlSpec__kABB: Seq<u8>,
) -> owlSpec_secret_kB_message_2 {
    owlSpec_secret_kB_message_2 { owlSpec__nB2: arg_owlSpec__nB2, owlSpec__kABB: arg_owlSpec__kABB }
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

pub enum owlSpec_encd_kB_message {
    owlSpec_mB1_enc(Seq<u8>),
    owlSpec_mB2_enc(Seq<u8>),
}

use owlSpec_encd_kB_message::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_encd_kB_message(x: Seq<u8>) -> Option<owlSpec_encd_kB_message> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Tail), (Tag::spec_new(U8, 2), Tail));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owlSpec_encd_kB_message::owlSpec_mB1_enc(x),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_encd_kB_message::owlSpec_mB2_enc(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_encd_kB_message_inner(x: owlSpec_encd_kB_message) -> Option<
    Seq<u8>,
> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Tail), (Tag::spec_new(U8, 2), Tail));
    match x {
        owlSpec_encd_kB_message::owlSpec_mB1_enc(x) => {
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
        owlSpec_encd_kB_message::owlSpec_mB2_enc(x) => {
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
pub closed spec fn serialize_owlSpec_encd_kB_message(x: owlSpec_encd_kB_message) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_encd_kB_message_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_encd_kB_message {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_encd_kB_message(self)
    }
}

pub open spec fn mB1_enc(x: Seq<u8>) -> owlSpec_encd_kB_message {
    crate::owlSpec_encd_kB_message::owlSpec_mB1_enc(x)
}

pub open spec fn mB2_enc(x: Seq<u8>) -> owlSpec_encd_kB_message {
    crate::owlSpec_encd_kB_message::owlSpec_mB2_enc(x)
}

pub open spec fn mB1_enc_enumtest(x: owlSpec_encd_kB_message) -> bool {
    match x {
        owlSpec_encd_kB_message::owlSpec_mB1_enc(_) => true,
        _ => false,
    }
}

pub open spec fn mB2_enc_enumtest(x: owlSpec_encd_kB_message) -> bool {
    match x {
        owlSpec_encd_kB_message::owlSpec_mB2_enc(_) => true,
        _ => false,
    }
}

pub struct owlSpec_msg1_AtoB {
    pub owlSpec_msg1_M: Seq<u8>,
    pub owlSpec_msg1_A: Seq<u8>,
    pub owlSpec_msg1_B: Seq<u8>,
    pub owlSpec_msg1_x: owlSpec_encd_kA_message,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_msg1_AtoB(x: Seq<u8>) -> Option<owlSpec_msg1_AtoB> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_msg1_AtoB_inner(x: owlSpec_msg1_AtoB) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_msg1_AtoB(x: owlSpec_msg1_AtoB) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_msg1_AtoB {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg1_AtoB(self)
    }
}

pub open spec fn msg1_AtoB(
    arg_owlSpec_msg1_M: Seq<u8>,
    arg_owlSpec_msg1_A: Seq<u8>,
    arg_owlSpec_msg1_B: Seq<u8>,
    arg_owlSpec_msg1_x: owlSpec_encd_kA_message,
) -> owlSpec_msg1_AtoB {
    owlSpec_msg1_AtoB {
        owlSpec_msg1_M: arg_owlSpec_msg1_M,
        owlSpec_msg1_A: arg_owlSpec_msg1_A,
        owlSpec_msg1_B: arg_owlSpec_msg1_B,
        owlSpec_msg1_x: arg_owlSpec_msg1_x,
    }
}

pub struct owlSpec_msg2_BToS {
    pub owlSpec_msg2_M: Seq<u8>,
    pub owlSpec_msg2_A: Seq<u8>,
    pub owlSpec_msg2_B: Seq<u8>,
    pub owlSpec_msg2_x1: owlSpec_encd_kA_message,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_msg2_BToS(x: Seq<u8>) -> Option<owlSpec_msg2_BToS> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_msg2_BToS_inner(x: owlSpec_msg2_BToS) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_msg2_BToS(x: owlSpec_msg2_BToS) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_msg2_BToS {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg2_BToS(self)
    }
}

pub open spec fn msg2_BToS(
    arg_owlSpec_msg2_M: Seq<u8>,
    arg_owlSpec_msg2_A: Seq<u8>,
    arg_owlSpec_msg2_B: Seq<u8>,
    arg_owlSpec_msg2_x1: owlSpec_encd_kA_message,
) -> owlSpec_msg2_BToS {
    owlSpec_msg2_BToS {
        owlSpec_msg2_M: arg_owlSpec_msg2_M,
        owlSpec_msg2_A: arg_owlSpec_msg2_A,
        owlSpec_msg2_B: arg_owlSpec_msg2_B,
        owlSpec_msg2_x1: arg_owlSpec_msg2_x1,
    }
}

spec fn spec_combinator_owlSpec_msg3_StoB() -> ((Variable, Variable), Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(60);
    let field_3 = Variable(60);
    ((field_1, field_2), field_3)
}

exec fn exec_combinator_owl_msg3_StoB() -> (res: ((Variable, Variable), Variable))
    ensures
        res.view() == spec_combinator_owlSpec_msg3_StoB(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(60);
    let field_3 = Variable(60);
    ((field_1, field_2), field_3)
}

pub struct owlSpec_msg3_StoB {
    pub owlSpec_msg3_M: Seq<u8>,
    pub owlSpec_msg3_x1: Seq<u8>,
    pub owlSpec_msg3_x2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_msg3_StoB(x: Seq<u8>) -> Option<owlSpec_msg3_StoB> {
    let spec_comb = spec_combinator_owlSpec_msg3_StoB();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let (((owlSpec_msg3_M, owlSpec_msg3_x1), owlSpec_msg3_x2)) = parsed;
        Some(owlSpec_msg3_StoB { owlSpec_msg3_M, owlSpec_msg3_x1, owlSpec_msg3_x2 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_msg3_StoB_inner(x: owlSpec_msg3_StoB) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_msg3_M.len(), x.owlSpec_msg3_x1.len(), x.owlSpec_msg3_x2.len() ] {
        let spec_comb = spec_combinator_owlSpec_msg3_StoB();
        if let Ok(serialized) = spec_comb.spec_serialize(
            (((x.owlSpec_msg3_M, x.owlSpec_msg3_x1), x.owlSpec_msg3_x2)),
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
pub closed spec fn serialize_owlSpec_msg3_StoB(x: owlSpec_msg3_StoB) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_msg3_StoB_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_msg3_StoB {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg3_StoB(self)
    }
}

pub open spec fn msg3_StoB(
    arg_owlSpec_msg3_M: Seq<u8>,
    arg_owlSpec_msg3_x1: Seq<u8>,
    arg_owlSpec_msg3_x2: Seq<u8>,
) -> owlSpec_msg3_StoB {
    owlSpec_msg3_StoB {
        owlSpec_msg3_M: arg_owlSpec_msg3_M,
        owlSpec_msg3_x1: arg_owlSpec_msg3_x1,
        owlSpec_msg3_x2: arg_owlSpec_msg3_x2,
    }
}

spec fn spec_combinator_owlSpec_msg4_BtoA() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(60);
    (field_1, field_2)
}

exec fn exec_combinator_owl_msg4_BtoA() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_msg4_BtoA(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(60);
    (field_1, field_2)
}

pub struct owlSpec_msg4_BtoA {
    pub owlSpec_msg4_M: Seq<u8>,
    pub owlSpec_msg4_x1: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_msg4_BtoA(x: Seq<u8>) -> Option<owlSpec_msg4_BtoA> {
    let spec_comb = spec_combinator_owlSpec_msg4_BtoA();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec_msg4_M, owlSpec_msg4_x1)) = parsed;
        Some(owlSpec_msg4_BtoA { owlSpec_msg4_M, owlSpec_msg4_x1 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_msg4_BtoA_inner(x: owlSpec_msg4_BtoA) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec_msg4_M.len(), x.owlSpec_msg4_x1.len() ] {
        let spec_comb = spec_combinator_owlSpec_msg4_BtoA();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec_msg4_M, x.owlSpec_msg4_x1))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_msg4_BtoA(x: owlSpec_msg4_BtoA) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_msg4_BtoA_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_msg4_BtoA {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg4_BtoA(self)
    }
}

pub open spec fn msg4_BtoA(
    arg_owlSpec_msg4_M: Seq<u8>,
    arg_owlSpec_msg4_x1: Seq<u8>,
) -> owlSpec_msg4_BtoA {
    owlSpec_msg4_BtoA { owlSpec_msg4_M: arg_owlSpec_msg4_M, owlSpec_msg4_x1: arg_owlSpec_msg4_x1 }
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
        let kab = ((ret(cfg.owl_KAB.view()))) in
let kA = ((ret(cfg.owl_KA.view()))) in
let kB = ((ret(cfg.owl_KB.view()))) in
(input(inp,_60)) in
(parse (parse_owlSpec_msg2_BToS(inp)) as (owlSpec_msg2_BToS{owlSpec_msg2_M : M, owlSpec_msg2_A : A, owlSpec_msg2_B : B, owlSpec_msg2_x1 : x1}) in {
(input(x2,_70)) in
(case (x1) {
| owlSpec_mA2_enc(_unused348) => {
(ret(()))
},
| owlSpec_mA1_enc(x1_) => {
let caseval = ((declassify(DeclassifyingOp::ADec(kA, x1_))) in
(ret(dec(kA, x1_)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(resA) => {
let resA_ = ((ret(resA))) in
let resA__ = ((ret(resA_))) in
(declassify(DeclassifyingOp::EnumParse(resA__))) in
(parse (parse_owlSpec_kA_messages(resA__)) as (parsed_caseval : owlSpec_kA_messages) in {
(case (parsed_caseval) {
| owlSpec_mA1(msg1A) => {
(parse (parse_owlSpec_encd_kB_message(x2)) as (parsed_caseval : owlSpec_encd_kB_message) in {
(case (parsed_caseval) {
| owlSpec_mB2_enc(_unused349) => {
(output (empty_seq_u8()) to (Some(Endpoint::Loc_Bob))) in
(ret(()))
},
| owlSpec_mB1_enc(c) => {
let caseval = ((declassify(DeclassifyingOp::ADec(kB, c))) in
(ret(dec(kB, c)))) in
(case (caseval) {
| None => {
(output (empty_seq_u8()) to (Some(Endpoint::Loc_Bob))) in
(ret(()))
},
| Some(resB) => {
let resB_ = ((ret(resB))) in
let resB__ = ((ret(resB_))) in
(declassify(DeclassifyingOp::EnumParse(resB__))) in
(parse (parse_owlSpec_kB_messages(resB__)) as (parsed_caseval : owlSpec_kB_messages) in {
(case (parsed_caseval) {
| owlSpec_mB1(msg1B) => {
(parse (msg1A) as (owlSpec_kA_message_1{owlSpec__nA1 : nA1_, owlSpec__mA : _unused350, owlSpec__AA : _unused351, owlSpec__BA : _unused352}) in {
(parse (msg1B) as (owlSpec_kB_message_1{owlSpec__nB1 : nB1_, owlSpec__mB : _unused353, owlSpec__AB : _unused354, owlSpec__BB : _unused355}) in {
let m = ((ret(mA2(kA_message_2(nA1_, kab))))) in
let encmA = ((sample(NONCE_SIZE, enc(kA, serialize_owlSpec_kA_messages(m))))) in
let m = ((ret(mB2(kB_message_2(nB1_, kab))))) in
let encmB = ((sample(NONCE_SIZE, enc(kB, serialize_owlSpec_kB_messages(m))))) in
(output (serialize_owlSpec_msg3_StoB(msg3_StoB(M, encmA, encmB))) to (Some(Endpoint::Loc_Bob))) in
(ret(()))
} )
} )
},
| owlSpec_mB2(_unused356) => {
(output (empty_seq_u8()) to (Some(Endpoint::Loc_Bob))) in
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
} otherwise (ret(())))
},
| owlSpec_mA2(_unused357) => {
(output (empty_seq_u8()) to (Some(Endpoint::Loc_Bob))) in
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
        let A = ((ret(cfg.owl_A_username.view()))) in
let B = ((ret(cfg.owl_B_username.view()))) in
let M = ((ret(cfg.owl_m.view()))) in
let nA = ((ret(cfg.owl_NA.view()))) in
let kA = ((ret(cfg.owl_KA.view()))) in
let declassified_buf157 = ((declassify(DeclassifyingOp::ControlFlow(A))) in
(ret((A)))) in
let declassified_buf160 = ((declassify(DeclassifyingOp::ControlFlow(B))) in
(ret((B)))) in
let m = ((ret(mA1(kA_message_1(nA, M, declassified_buf157, declassified_buf160))))) in
let encm = ((sample(NONCE_SIZE, enc(kA, serialize_owlSpec_kA_messages(m))))) in
let declassified_buf166 = ((declassify(DeclassifyingOp::ControlFlow(M))) in
(ret((M)))) in
let declassified_buf169 = ((declassify(DeclassifyingOp::ControlFlow(A))) in
(ret((A)))) in
let declassified_buf172 = ((declassify(DeclassifyingOp::ControlFlow(B))) in
(ret((B)))) in
(output (serialize_owlSpec_msg1_AtoB(msg1_AtoB(declassified_buf166, declassified_buf169, declassified_buf172, mA1_enc(encm)))) to (Some(Endpoint::Loc_Bob))) in
(input(inp,_176)) in
(parse (parse_owlSpec_msg4_BtoA(inp)) as (owlSpec_msg4_BtoA{owlSpec_msg4_M : M_, owlSpec_msg4_x1 : x1_}) in {
let caseval = ((declassify(DeclassifyingOp::ADec(kA, x1_))) in
(ret(dec(kA, x1_)))) in
(case (caseval) {
| None => {
(ret(alice_None()))
},
| Some(res) => {
let res_ = ((ret(res))) in
let res__ = ((ret(res_))) in
let o = ((declassify(DeclassifyingOp::EnumParse(res__))) in
(parse (parse_owlSpec_kA_messages(res__)) as (parsed_caseval : owlSpec_kA_messages) in {
(case (parsed_caseval) {
| owlSpec_mA1(_unused358) => {
(ret(alice_None()))
},
| owlSpec_mA2(msg2) => {
(parse (msg2) as (owlSpec_kA_message_2{owlSpec__nA2 : nA_, owlSpec__kABA : kAB_}) in {
let eq_bool208 = ((declassify(DeclassifyingOp::EqCheck(nA_, nA))) in
(ret(nA_ == nA))) in
(if (eq_bool208) then
((ret(alice_Some(kAB_))))
else
((ret(alice_None()))))
} )
},
}
)
} otherwise (ret(alice_None())))) in
(ret(o))
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
        let B = ((ret(cfg.owl_B_username.view()))) in
let nB = ((ret(cfg.owl_NB.view()))) in
let kB = ((ret(cfg.owl_KB.view()))) in
(input(inp,_217)) in
(parse (parse_owlSpec_msg1_AtoB(inp)) as (owlSpec_msg1_AtoB{owlSpec_msg1_M : M_, owlSpec_msg1_A : A_, owlSpec_msg1_B : B_, owlSpec_msg1_x : encm_}) in {
(case (encm_) {
| owlSpec_mA2_enc(_unused359) => {
(output (empty_seq_u8()) to (Some(Endpoint::Loc_AS))) in
(input(_unused360,_233)) in
(output (empty_seq_u8()) to (Some(Endpoint::Loc_Alice))) in
(ret(bob_None()))
},
| owlSpec_mA1_enc(v) => {
let v_ = ((ret(mA1_enc(v)))) in
let declassified_buf238 = ((declassify(DeclassifyingOp::ControlFlow(B))) in
(ret((B)))) in
let m = ((ret(mB1(kB_message_1(nB, M_, A_, declassified_buf238))))) in
let encm = ((sample(NONCE_SIZE, enc(kB, serialize_owlSpec_kB_messages(m))))) in
let declassified_buf244 = ((declassify(DeclassifyingOp::ControlFlow(B))) in
(ret((B)))) in
(output (serialize_owlSpec_msg2_BToS(msg2_BToS(M_, A_, declassified_buf244, v_))) to (Some(Endpoint::Loc_AS))) in
(output (serialize_owlSpec_encd_kB_message(mB1_enc(encm))) to (Some(Endpoint::Loc_AS))) in
(input(inp2,_249)) in
(parse (parse_owlSpec_msg3_StoB(inp2)) as (owlSpec_msg3_StoB{owlSpec_msg3_M : M_, owlSpec_msg3_x1 : x1_, owlSpec_msg3_x2 : x2_}) in {
let caseval = ((declassify(DeclassifyingOp::ADec(kB, x2_))) in
(ret(dec(kB, x2_)))) in
(case (caseval) {
| None => {
(output (empty_seq_u8()) to (Some(Endpoint::Loc_Alice))) in
(ret(bob_None()))
},
| Some(res) => {
let res_ = ((ret(res))) in
let res__ = ((ret(res_))) in
let o = ((declassify(DeclassifyingOp::EnumParse(res__))) in
(parse (parse_owlSpec_kB_messages(res__)) as (parsed_caseval : owlSpec_kB_messages) in {
(case (parsed_caseval) {
| owlSpec_mB1(_unused361) => {
(ret(bob_None()))
},
| owlSpec_mB2(msg2) => {
(parse (msg2) as (owlSpec_kB_message_2{owlSpec__nB2 : nB_, owlSpec__kABB : msg2_}) in {
let eq_bool284 = ((declassify(DeclassifyingOp::EqCheck(nB_, nB))) in
(ret(nB_ == nB))) in
(if (eq_bool284) then
((output (serialize_owlSpec_msg4_BtoA(msg4_BtoA(M_, x1_))) to (Some(Endpoint::Loc_Alice))) in
(ret(bob_Some(msg2_))))
else
((ret(bob_None()))))
} )
},
}
)
} otherwise (ret(bob_None())))) in
(ret(o))
},
}
)
} otherwise ((ret(bob_None()))))
},
}
)
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

pub struct owl_kA_message_1<'a> {
    pub owl__nA1: SecretBuf<'a>,
    pub owl__mA: SecretBuf<'a>,
    pub owl__AA: OwlBuf<'a>,
    pub owl__BA: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_kA_message_1<'a>(
    arg_owl__nA1: SecretBuf<'a>,
    arg_owl__mA: SecretBuf<'a>,
    arg_owl__AA: OwlBuf<'a>,
    arg_owl__BA: OwlBuf<'a>,
) -> (res: owl_kA_message_1<'a>)
    ensures
        res.owl__nA1.view() == arg_owl__nA1.view(),
        res.owl__mA.view() == arg_owl__mA.view(),
        res.owl__AA.view() == arg_owl__AA.view(),
        res.owl__BA.view() == arg_owl__BA.view(),
{
    owl_kA_message_1 {
        owl__nA1: arg_owl__nA1,
        owl__mA: arg_owl__mA,
        owl__AA: arg_owl__AA,
        owl__BA: arg_owl__BA,
    }
}

impl<'a> owl_kA_message_1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kA_message_1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_kA_message_1 {
            owl__nA1: SecretBuf::another_ref(&self.owl__nA1),
            owl__mA: SecretBuf::another_ref(&self.owl__mA),
            owl__AA: OwlBuf::another_ref(&self.owl__AA),
            owl__BA: OwlBuf::another_ref(&self.owl__BA),
        }
    }
}

impl View for owl_kA_message_1<'_> {
    type V = owlSpec_kA_message_1;

    open spec fn view(&self) -> owlSpec_kA_message_1 {
        owlSpec_kA_message_1 {
            owlSpec__nA1: self.owl__nA1.view(),
            owlSpec__mA: self.owl__mA.view(),
            owlSpec__AA: self.owl__AA.view(),
            owlSpec__BA: self.owl__BA.view(),
        }
    }
}

pub exec fn parse_owl_kA_message_1<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_kA_message_1<'a>>)
    ensures
        res is Some ==> parse_owlSpec_kA_message_1(arg.view()) is Some,
        res is None ==> parse_owlSpec_kA_message_1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kA_message_1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_kA_message_1);
    let exec_comb = exec_combinator_owl_kA_message_1();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (((owl__nA1, owl__mA), owl__AA), owl__BA) = parsed;
        Some(
            owl_kA_message_1 {
                owl__nA1: SecretBuf::from_buf(owl__nA1.another_ref()),
                owl__mA: SecretBuf::from_buf(owl__mA.another_ref()),
                owl__AA: OwlBuf::another_ref(&owl__AA),
                owl__BA: OwlBuf::another_ref(&owl__BA),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_kA_message_1_inner<'a>(arg: &owl_kA_message_1<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_kA_message_1_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_kA_message_1_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_kA_message_1_inner);
    if no_usize_overflows![ arg.owl__nA1.len(), arg.owl__mA.len(), arg.owl__AA.len(), arg.owl__BA.len(), 0 ] {
        let exec_comb = exec_combinator_owl_kA_message_1();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__nA1.len() + arg.owl__mA.len() + arg.owl__AA.len() + arg.owl__BA.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (SecretBuf::another_ref(&arg.owl__nA1), SecretBuf::another_ref(&arg.owl__mA)),
                    SecretBuf::from_buf(arg.owl__AA.another_ref()),
                ),
                SecretBuf::from_buf(arg.owl__BA.another_ref()),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_kA_message_1_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_kA_message_1<'a>(arg: &owl_kA_message_1<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_kA_message_1(arg.view()),
{
    reveal(serialize_owlSpec_kA_message_1);
    let res = serialize_owl_kA_message_1_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_kA_message_1<'a> {
    pub owl__nA1: SecretBuf<'a>,
    pub owl__mA: SecretBuf<'a>,
    pub owl__AA: SecretBuf<'a>,
    pub owl__BA: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_kA_message_1<'a>(
    arg_owl__nA1: SecretBuf<'a>,
    arg_owl__mA: SecretBuf<'a>,
    arg_owl__AA: SecretBuf<'a>,
    arg_owl__BA: SecretBuf<'a>,
) -> (res: owl_secret_kA_message_1<'a>)
    ensures
        res.owl__nA1.view() == arg_owl__nA1.view(),
        res.owl__mA.view() == arg_owl__mA.view(),
        res.owl__AA.view() == arg_owl__AA.view(),
        res.owl__BA.view() == arg_owl__BA.view(),
{
    owl_secret_kA_message_1 {
        owl__nA1: arg_owl__nA1,
        owl__mA: arg_owl__mA,
        owl__AA: arg_owl__AA,
        owl__BA: arg_owl__BA,
    }
}

impl<'a> owl_secret_kA_message_1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_kA_message_1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_kA_message_1 {
            owl__nA1: SecretBuf::another_ref(&self.owl__nA1),
            owl__mA: SecretBuf::another_ref(&self.owl__mA),
            owl__AA: SecretBuf::another_ref(&self.owl__AA),
            owl__BA: SecretBuf::another_ref(&self.owl__BA),
        }
    }
}

impl View for owl_secret_kA_message_1<'_> {
    type V = owlSpec_secret_kA_message_1;

    open spec fn view(&self) -> owlSpec_secret_kA_message_1 {
        owlSpec_secret_kA_message_1 {
            owlSpec__nA1: self.owl__nA1.view(),
            owlSpec__mA: self.owl__mA.view(),
            owlSpec__AA: self.owl__AA.view(),
            owlSpec__BA: self.owl__BA.view(),
        }
    }
}

pub exec fn parse_owl_secret_kA_message_1<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_secret_kA_message_1<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kA_message_1(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kA_message_1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kA_message_1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kA_message_1);
    let exec_comb = exec_combinator_owl_secret_kA_message_1();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (((owl__nA1, owl__mA), owl__AA), owl__BA) = parsed;
        Some(
            owl_secret_kA_message_1 {
                owl__nA1: SecretBuf::from_buf(owl__nA1.another_ref()),
                owl__mA: SecretBuf::from_buf(owl__mA.another_ref()),
                owl__AA: SecretBuf::from_buf(owl__AA.another_ref()),
                owl__BA: SecretBuf::from_buf(owl__BA.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_kA_message_1<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_kA_message_1<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kA_message_1(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kA_message_1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kA_message_1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kA_message_1);
    let exec_comb = exec_combinator_owl_secret_kA_message_1();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (((owl__nA1, owl__mA), owl__AA), owl__BA) = parsed;
        Some(
            owl_secret_kA_message_1 {
                owl__nA1: SecretBuf::another_ref(&owl__nA1),
                owl__mA: SecretBuf::another_ref(&owl__mA),
                owl__AA: SecretBuf::another_ref(&owl__AA),
                owl__BA: SecretBuf::another_ref(&owl__BA),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_kA_message_1_inner<'a>(arg: &owl_secret_kA_message_1<'a>) -> (res:
    Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_secret_kA_message_1_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_kA_message_1_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_secret_kA_message_1_inner);
    if no_usize_overflows![ arg.owl__nA1.len(), arg.owl__mA.len(), arg.owl__AA.len(), arg.owl__BA.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_kA_message_1();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__nA1.len() + arg.owl__mA.len() + arg.owl__AA.len() + arg.owl__BA.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (SecretBuf::another_ref(&arg.owl__nA1), SecretBuf::another_ref(&arg.owl__mA)),
                    SecretBuf::another_ref(&arg.owl__AA),
                ),
                SecretBuf::another_ref(&arg.owl__BA),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_kA_message_1_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_kA_message_1<'a>(arg: &owl_secret_kA_message_1<'a>) -> (res:
    SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_kA_message_1(arg.view()),
{
    reveal(serialize_owlSpec_secret_kA_message_1);
    let res = serialize_owl_secret_kA_message_1_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_kA_message_2<'a> {
    pub owl__nA2: SecretBuf<'a>,
    pub owl__kABA: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_kA_message_2<'a>(arg_owl__nA2: SecretBuf<'a>, arg_owl__kABA: SecretBuf<'a>) -> (res:
    owl_kA_message_2<'a>)
    ensures
        res.owl__nA2.view() == arg_owl__nA2.view(),
        res.owl__kABA.view() == arg_owl__kABA.view(),
{
    owl_kA_message_2 { owl__nA2: arg_owl__nA2, owl__kABA: arg_owl__kABA }
}

impl<'a> owl_kA_message_2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kA_message_2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_kA_message_2 {
            owl__nA2: SecretBuf::another_ref(&self.owl__nA2),
            owl__kABA: SecretBuf::another_ref(&self.owl__kABA),
        }
    }
}

impl View for owl_kA_message_2<'_> {
    type V = owlSpec_kA_message_2;

    open spec fn view(&self) -> owlSpec_kA_message_2 {
        owlSpec_kA_message_2 {
            owlSpec__nA2: self.owl__nA2.view(),
            owlSpec__kABA: self.owl__kABA.view(),
        }
    }
}

pub exec fn parse_owl_kA_message_2<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_kA_message_2<'a>>)
    ensures
        res is Some ==> parse_owlSpec_kA_message_2(arg.view()) is Some,
        res is None ==> parse_owlSpec_kA_message_2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kA_message_2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_kA_message_2);
    let exec_comb = exec_combinator_owl_kA_message_2();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__nA2, owl__kABA) = parsed;
        Some(
            owl_kA_message_2 {
                owl__nA2: SecretBuf::from_buf(owl__nA2.another_ref()),
                owl__kABA: SecretBuf::from_buf(owl__kABA.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_kA_message_2<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_kA_message_2<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_kA_message_2(arg.view()) is Some,
        res is None ==> parse_owlSpec_kA_message_2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kA_message_2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_kA_message_2);
    let exec_comb = exec_combinator_owl_kA_message_2();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (owl__nA2, owl__kABA) = parsed;
        Some(
            owl_kA_message_2 {
                owl__nA2: SecretBuf::another_ref(&owl__nA2),
                owl__kABA: SecretBuf::another_ref(&owl__kABA),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_kA_message_2_inner<'a>(arg: &owl_kA_message_2<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_kA_message_2_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_kA_message_2_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_kA_message_2_inner);
    if no_usize_overflows![ arg.owl__nA2.len(), arg.owl__kABA.len(), 0 ] {
        let exec_comb = exec_combinator_owl_kA_message_2();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__nA2.len() + arg.owl__kABA.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__nA2), SecretBuf::another_ref(&arg.owl__kABA)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_kA_message_2_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_kA_message_2<'a>(arg: &owl_kA_message_2<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_kA_message_2(arg.view()),
{
    reveal(serialize_owlSpec_kA_message_2);
    let res = serialize_owl_kA_message_2_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_kA_message_2<'a> {
    pub owl__nA2: SecretBuf<'a>,
    pub owl__kABA: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_kA_message_2<'a>(
    arg_owl__nA2: SecretBuf<'a>,
    arg_owl__kABA: SecretBuf<'a>,
) -> (res: owl_secret_kA_message_2<'a>)
    ensures
        res.owl__nA2.view() == arg_owl__nA2.view(),
        res.owl__kABA.view() == arg_owl__kABA.view(),
{
    owl_secret_kA_message_2 { owl__nA2: arg_owl__nA2, owl__kABA: arg_owl__kABA }
}

impl<'a> owl_secret_kA_message_2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_kA_message_2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_kA_message_2 {
            owl__nA2: SecretBuf::another_ref(&self.owl__nA2),
            owl__kABA: SecretBuf::another_ref(&self.owl__kABA),
        }
    }
}

impl View for owl_secret_kA_message_2<'_> {
    type V = owlSpec_secret_kA_message_2;

    open spec fn view(&self) -> owlSpec_secret_kA_message_2 {
        owlSpec_secret_kA_message_2 {
            owlSpec__nA2: self.owl__nA2.view(),
            owlSpec__kABA: self.owl__kABA.view(),
        }
    }
}

pub exec fn parse_owl_secret_kA_message_2<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_secret_kA_message_2<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kA_message_2(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kA_message_2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kA_message_2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kA_message_2);
    let exec_comb = exec_combinator_owl_secret_kA_message_2();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__nA2, owl__kABA) = parsed;
        Some(
            owl_secret_kA_message_2 {
                owl__nA2: SecretBuf::from_buf(owl__nA2.another_ref()),
                owl__kABA: SecretBuf::from_buf(owl__kABA.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_kA_message_2<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_kA_message_2<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_kA_message_2(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_kA_message_2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_kA_message_2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_kA_message_2);
    let exec_comb = exec_combinator_owl_secret_kA_message_2();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (owl__nA2, owl__kABA) = parsed;
        Some(
            owl_secret_kA_message_2 {
                owl__nA2: SecretBuf::another_ref(&owl__nA2),
                owl__kABA: SecretBuf::another_ref(&owl__kABA),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_kA_message_2_inner<'a>(arg: &owl_secret_kA_message_2<'a>) -> (res:
    Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_secret_kA_message_2_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_kA_message_2_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_secret_kA_message_2_inner);
    if no_usize_overflows![ arg.owl__nA2.len(), arg.owl__kABA.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_kA_message_2();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__nA2.len() + arg.owl__kABA.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__nA2), SecretBuf::another_ref(&arg.owl__kABA)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_kA_message_2_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_kA_message_2<'a>(arg: &owl_secret_kA_message_2<'a>) -> (res:
    SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_kA_message_2(arg.view()),
{
    reveal(serialize_owlSpec_secret_kA_message_2);
    let res = serialize_owl_secret_kA_message_2_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_kA_messages<'a> {
    owl_mA1(owl_kA_message_1<'a>),
    owl_mA2(owl_kA_message_2<'a>),
}

use owl_kA_messages::*;

impl<'a> owl_kA_messages<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kA_messages<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_mA1(x) => owl_mA1(owl_kA_message_1::another_ref(x)),
            owl_mA2(x) => owl_mA2(owl_kA_message_2::another_ref(x)),
        }
    }
}

impl View for owl_kA_messages<'_> {
    type V = owlSpec_kA_messages;

    open spec fn view(&self) -> owlSpec_kA_messages {
        match self {
            owl_mA1(v) => owlSpec_kA_messages::owlSpec_mA1(v.view()),
            owl_mA2(v) => owlSpec_kA_messages::owlSpec_mA2(v.view()),
        }
    }
}

#[inline]
pub fn owl_mA1_enumtest(x: &owl_kA_messages<'_>) -> (res: bool)
    ensures
        res == mA1_enumtest(x.view()),
{
    match x {
        owl_kA_messages::owl_mA1(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl_mA2_enumtest(x: &owl_kA_messages<'_>) -> (res: bool)
    ensures
        res == mA2_enumtest(x.view()),
{
    match x {
        owl_kA_messages::owl_mA2(_) => true,
        _ => false,
    }
}

#[verifier::external_body]
pub exec fn parse_owl_kA_messages<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_kA_messages<'a>>)
    ensures
        res is Some ==> parse_owlSpec_kA_messages(arg.view()) is Some,
        res is None ==> parse_owlSpec_kA_messages(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kA_messages(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_kA_messages<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_kA_messages<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_kA_messages(arg.view()) is Some,
        res is None ==> parse_owlSpec_kA_messages(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kA_messages(arg.view())->Some_0,
{
    reveal(parse_owlSpec_kA_messages);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_kA_messages_inner(arg: &owl_kA_messages) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_kA_messages_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_kA_messages_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_kA_messages_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_kA_messages(arg: &owl_kA_messages) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_kA_messages(arg.view()),
{
    unimplemented!()
}

pub enum owl_encd_kA_message<'a> {
    owl_mA1_enc(OwlBuf<'a>),
    owl_mA2_enc(OwlBuf<'a>),
}

use owl_encd_kA_message::*;

impl<'a> owl_encd_kA_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_encd_kA_message<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_mA1_enc(x) => owl_mA1_enc(OwlBuf::another_ref(x)),
            owl_mA2_enc(x) => owl_mA2_enc(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_encd_kA_message<'_> {
    type V = owlSpec_encd_kA_message;

    open spec fn view(&self) -> owlSpec_encd_kA_message {
        match self {
            owl_mA1_enc(v) => owlSpec_encd_kA_message::owlSpec_mA1_enc(v.view()),
            owl_mA2_enc(v) => owlSpec_encd_kA_message::owlSpec_mA2_enc(v.view()),
        }
    }
}

#[inline]
pub fn owl_mA1_enc_enumtest(x: &owl_encd_kA_message<'_>) -> (res: bool)
    ensures
        res == mA1_enc_enumtest(x.view()),
{
    match x {
        owl_encd_kA_message::owl_mA1_enc(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl_mA2_enc_enumtest(x: &owl_encd_kA_message<'_>) -> (res: bool)
    ensures
        res == mA2_enc_enumtest(x.view()),
{
    match x {
        owl_encd_kA_message::owl_mA2_enc(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_encd_kA_message<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_encd_kA_message<'a>>)
    ensures
        res is Some ==> parse_owlSpec_encd_kA_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_encd_kA_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_encd_kA_message(arg.view())->Some_0,
{
    reveal(parse_owlSpec_encd_kA_message);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Tail), (Tag::new(U8, 2), Tail));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owl_encd_kA_message::owl_mA1_enc(
                OwlBuf::another_ref(&x),
            ),
            inj_ord_choice_pat!(*, (_,x)) => owl_encd_kA_message::owl_mA2_enc(
                OwlBuf::another_ref(&x),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn serialize_owl_encd_kA_message_inner(arg: &owl_encd_kA_message) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_encd_kA_message_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_encd_kA_message_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_encd_kA_message_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_encd_kA_message(arg: &owl_encd_kA_message) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_encd_kA_message(arg.view()),
{
    reveal(serialize_owlSpec_encd_kA_message);
    let res = serialize_owl_encd_kA_message_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_kB_message_1<'a> {
    pub owl__nB1: SecretBuf<'a>,
    pub owl__mB: OwlBuf<'a>,
    pub owl__AB: OwlBuf<'a>,
    pub owl__BB: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_kB_message_1<'a>(
    arg_owl__nB1: SecretBuf<'a>,
    arg_owl__mB: OwlBuf<'a>,
    arg_owl__AB: OwlBuf<'a>,
    arg_owl__BB: OwlBuf<'a>,
) -> (res: owl_kB_message_1<'a>)
    ensures
        res.owl__nB1.view() == arg_owl__nB1.view(),
        res.owl__mB.view() == arg_owl__mB.view(),
        res.owl__AB.view() == arg_owl__AB.view(),
        res.owl__BB.view() == arg_owl__BB.view(),
{
    owl_kB_message_1 {
        owl__nB1: arg_owl__nB1,
        owl__mB: arg_owl__mB,
        owl__AB: arg_owl__AB,
        owl__BB: arg_owl__BB,
    }
}

impl<'a> owl_kB_message_1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kB_message_1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_kB_message_1 {
            owl__nB1: SecretBuf::another_ref(&self.owl__nB1),
            owl__mB: OwlBuf::another_ref(&self.owl__mB),
            owl__AB: OwlBuf::another_ref(&self.owl__AB),
            owl__BB: OwlBuf::another_ref(&self.owl__BB),
        }
    }
}

impl View for owl_kB_message_1<'_> {
    type V = owlSpec_kB_message_1;

    open spec fn view(&self) -> owlSpec_kB_message_1 {
        owlSpec_kB_message_1 {
            owlSpec__nB1: self.owl__nB1.view(),
            owlSpec__mB: self.owl__mB.view(),
            owlSpec__AB: self.owl__AB.view(),
            owlSpec__BB: self.owl__BB.view(),
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
        let (((owl__nB1, owl__mB), owl__AB), owl__BB) = parsed;
        Some(
            owl_kB_message_1 {
                owl__nB1: SecretBuf::from_buf(owl__nB1.another_ref()),
                owl__mB: OwlBuf::another_ref(&owl__mB),
                owl__AB: OwlBuf::another_ref(&owl__AB),
                owl__BB: OwlBuf::another_ref(&owl__BB),
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
    if no_usize_overflows![ arg.owl__nB1.len(), arg.owl__mB.len(), arg.owl__AB.len(), arg.owl__BB.len(), 0 ] {
        let exec_comb = exec_combinator_owl_kB_message_1();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__nB1.len() + arg.owl__mB.len() + arg.owl__AB.len() + arg.owl__BB.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        SecretBuf::another_ref(&arg.owl__nB1),
                        SecretBuf::from_buf(arg.owl__mB.another_ref()),
                    ),
                    SecretBuf::from_buf(arg.owl__AB.another_ref()),
                ),
                SecretBuf::from_buf(arg.owl__BB.another_ref()),
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
    pub owl__nB1: SecretBuf<'a>,
    pub owl__mB: SecretBuf<'a>,
    pub owl__AB: SecretBuf<'a>,
    pub owl__BB: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_kB_message_1<'a>(
    arg_owl__nB1: SecretBuf<'a>,
    arg_owl__mB: SecretBuf<'a>,
    arg_owl__AB: SecretBuf<'a>,
    arg_owl__BB: SecretBuf<'a>,
) -> (res: owl_secret_kB_message_1<'a>)
    ensures
        res.owl__nB1.view() == arg_owl__nB1.view(),
        res.owl__mB.view() == arg_owl__mB.view(),
        res.owl__AB.view() == arg_owl__AB.view(),
        res.owl__BB.view() == arg_owl__BB.view(),
{
    owl_secret_kB_message_1 {
        owl__nB1: arg_owl__nB1,
        owl__mB: arg_owl__mB,
        owl__AB: arg_owl__AB,
        owl__BB: arg_owl__BB,
    }
}

impl<'a> owl_secret_kB_message_1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_kB_message_1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_kB_message_1 {
            owl__nB1: SecretBuf::another_ref(&self.owl__nB1),
            owl__mB: SecretBuf::another_ref(&self.owl__mB),
            owl__AB: SecretBuf::another_ref(&self.owl__AB),
            owl__BB: SecretBuf::another_ref(&self.owl__BB),
        }
    }
}

impl View for owl_secret_kB_message_1<'_> {
    type V = owlSpec_secret_kB_message_1;

    open spec fn view(&self) -> owlSpec_secret_kB_message_1 {
        owlSpec_secret_kB_message_1 {
            owlSpec__nB1: self.owl__nB1.view(),
            owlSpec__mB: self.owl__mB.view(),
            owlSpec__AB: self.owl__AB.view(),
            owlSpec__BB: self.owl__BB.view(),
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
        let (((owl__nB1, owl__mB), owl__AB), owl__BB) = parsed;
        Some(
            owl_secret_kB_message_1 {
                owl__nB1: SecretBuf::from_buf(owl__nB1.another_ref()),
                owl__mB: SecretBuf::from_buf(owl__mB.another_ref()),
                owl__AB: SecretBuf::from_buf(owl__AB.another_ref()),
                owl__BB: SecretBuf::from_buf(owl__BB.another_ref()),
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
        let (((owl__nB1, owl__mB), owl__AB), owl__BB) = parsed;
        Some(
            owl_secret_kB_message_1 {
                owl__nB1: SecretBuf::another_ref(&owl__nB1),
                owl__mB: SecretBuf::another_ref(&owl__mB),
                owl__AB: SecretBuf::another_ref(&owl__AB),
                owl__BB: SecretBuf::another_ref(&owl__BB),
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
    if no_usize_overflows![ arg.owl__nB1.len(), arg.owl__mB.len(), arg.owl__AB.len(), arg.owl__BB.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_kB_message_1();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__nB1.len() + arg.owl__mB.len() + arg.owl__AB.len() + arg.owl__BB.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (SecretBuf::another_ref(&arg.owl__nB1), SecretBuf::another_ref(&arg.owl__mB)),
                    SecretBuf::another_ref(&arg.owl__AB),
                ),
                SecretBuf::another_ref(&arg.owl__BB),
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
    pub owl__nB2: SecretBuf<'a>,
    pub owl__kABB: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_kB_message_2<'a>(arg_owl__nB2: SecretBuf<'a>, arg_owl__kABB: SecretBuf<'a>) -> (res:
    owl_kB_message_2<'a>)
    ensures
        res.owl__nB2.view() == arg_owl__nB2.view(),
        res.owl__kABB.view() == arg_owl__kABB.view(),
{
    owl_kB_message_2 { owl__nB2: arg_owl__nB2, owl__kABB: arg_owl__kABB }
}

impl<'a> owl_kB_message_2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_kB_message_2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_kB_message_2 {
            owl__nB2: SecretBuf::another_ref(&self.owl__nB2),
            owl__kABB: SecretBuf::another_ref(&self.owl__kABB),
        }
    }
}

impl View for owl_kB_message_2<'_> {
    type V = owlSpec_kB_message_2;

    open spec fn view(&self) -> owlSpec_kB_message_2 {
        owlSpec_kB_message_2 {
            owlSpec__nB2: self.owl__nB2.view(),
            owlSpec__kABB: self.owl__kABB.view(),
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
        let (owl__nB2, owl__kABB) = parsed;
        Some(
            owl_kB_message_2 {
                owl__nB2: SecretBuf::from_buf(owl__nB2.another_ref()),
                owl__kABB: SecretBuf::from_buf(owl__kABB.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_kB_message_2<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_kB_message_2<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_kB_message_2(arg.view()) is Some,
        res is None ==> parse_owlSpec_kB_message_2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_kB_message_2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_kB_message_2);
    let exec_comb = exec_combinator_owl_kB_message_2();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (owl__nB2, owl__kABB) = parsed;
        Some(
            owl_kB_message_2 {
                owl__nB2: SecretBuf::another_ref(&owl__nB2),
                owl__kABB: SecretBuf::another_ref(&owl__kABB),
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
    if no_usize_overflows![ arg.owl__nB2.len(), arg.owl__kABB.len(), 0 ] {
        let exec_comb = exec_combinator_owl_kB_message_2();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__nB2.len() + arg.owl__kABB.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__nB2), SecretBuf::another_ref(&arg.owl__kABB)),
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
    pub owl__nB2: SecretBuf<'a>,
    pub owl__kABB: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_kB_message_2<'a>(
    arg_owl__nB2: SecretBuf<'a>,
    arg_owl__kABB: SecretBuf<'a>,
) -> (res: owl_secret_kB_message_2<'a>)
    ensures
        res.owl__nB2.view() == arg_owl__nB2.view(),
        res.owl__kABB.view() == arg_owl__kABB.view(),
{
    owl_secret_kB_message_2 { owl__nB2: arg_owl__nB2, owl__kABB: arg_owl__kABB }
}

impl<'a> owl_secret_kB_message_2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_kB_message_2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_kB_message_2 {
            owl__nB2: SecretBuf::another_ref(&self.owl__nB2),
            owl__kABB: SecretBuf::another_ref(&self.owl__kABB),
        }
    }
}

impl View for owl_secret_kB_message_2<'_> {
    type V = owlSpec_secret_kB_message_2;

    open spec fn view(&self) -> owlSpec_secret_kB_message_2 {
        owlSpec_secret_kB_message_2 {
            owlSpec__nB2: self.owl__nB2.view(),
            owlSpec__kABB: self.owl__kABB.view(),
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
        let (owl__nB2, owl__kABB) = parsed;
        Some(
            owl_secret_kB_message_2 {
                owl__nB2: SecretBuf::from_buf(owl__nB2.another_ref()),
                owl__kABB: SecretBuf::from_buf(owl__kABB.another_ref()),
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
        let (owl__nB2, owl__kABB) = parsed;
        Some(
            owl_secret_kB_message_2 {
                owl__nB2: SecretBuf::another_ref(&owl__nB2),
                owl__kABB: SecretBuf::another_ref(&owl__kABB),
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
    if no_usize_overflows![ arg.owl__nB2.len(), arg.owl__kABB.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_kB_message_2();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__nB2.len() + arg.owl__kABB.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__nB2), SecretBuf::another_ref(&arg.owl__kABB)),
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

pub enum owl_encd_kB_message<'a> {
    owl_mB1_enc(OwlBuf<'a>),
    owl_mB2_enc(OwlBuf<'a>),
}

use owl_encd_kB_message::*;

impl<'a> owl_encd_kB_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_encd_kB_message<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_mB1_enc(x) => owl_mB1_enc(OwlBuf::another_ref(x)),
            owl_mB2_enc(x) => owl_mB2_enc(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_encd_kB_message<'_> {
    type V = owlSpec_encd_kB_message;

    open spec fn view(&self) -> owlSpec_encd_kB_message {
        match self {
            owl_mB1_enc(v) => owlSpec_encd_kB_message::owlSpec_mB1_enc(v.view()),
            owl_mB2_enc(v) => owlSpec_encd_kB_message::owlSpec_mB2_enc(v.view()),
        }
    }
}

#[inline]
pub fn owl_mB1_enc_enumtest(x: &owl_encd_kB_message<'_>) -> (res: bool)
    ensures
        res == mB1_enc_enumtest(x.view()),
{
    match x {
        owl_encd_kB_message::owl_mB1_enc(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl_mB2_enc_enumtest(x: &owl_encd_kB_message<'_>) -> (res: bool)
    ensures
        res == mB2_enc_enumtest(x.view()),
{
    match x {
        owl_encd_kB_message::owl_mB2_enc(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_encd_kB_message<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_encd_kB_message<'a>>)
    ensures
        res is Some ==> parse_owlSpec_encd_kB_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_encd_kB_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_encd_kB_message(arg.view())->Some_0,
{
    reveal(parse_owlSpec_encd_kB_message);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Tail), (Tag::new(U8, 2), Tail));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owl_encd_kB_message::owl_mB1_enc(
                OwlBuf::another_ref(&x),
            ),
            inj_ord_choice_pat!(*, (_,x)) => owl_encd_kB_message::owl_mB2_enc(
                OwlBuf::another_ref(&x),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn serialize_owl_encd_kB_message_inner(arg: &owl_encd_kB_message) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_encd_kB_message_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_encd_kB_message_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_encd_kB_message_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_encd_kB_message(arg: &owl_encd_kB_message) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_encd_kB_message(arg.view()),
{
    reveal(serialize_owlSpec_encd_kB_message);
    let res = serialize_owl_encd_kB_message_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_msg1_AtoB<'a> {
    pub owl_msg1_M: OwlBuf<'a>,
    pub owl_msg1_A: OwlBuf<'a>,
    pub owl_msg1_B: OwlBuf<'a>,
    pub owl_msg1_x: owl_encd_kA_message<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg1_AtoB<'a>(
    arg_owl_msg1_M: OwlBuf<'a>,
    arg_owl_msg1_A: OwlBuf<'a>,
    arg_owl_msg1_B: OwlBuf<'a>,
    arg_owl_msg1_x: owl_encd_kA_message<'a>,
) -> (res: owl_msg1_AtoB<'a>)
    ensures
        res.owl_msg1_M.view() == arg_owl_msg1_M.view(),
        res.owl_msg1_A.view() == arg_owl_msg1_A.view(),
        res.owl_msg1_B.view() == arg_owl_msg1_B.view(),
        res.owl_msg1_x.view() == arg_owl_msg1_x.view(),
{
    owl_msg1_AtoB {
        owl_msg1_M: arg_owl_msg1_M,
        owl_msg1_A: arg_owl_msg1_A,
        owl_msg1_B: arg_owl_msg1_B,
        owl_msg1_x: arg_owl_msg1_x,
    }
}

impl<'a> owl_msg1_AtoB<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg1_AtoB<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg1_AtoB {
            owl_msg1_M: OwlBuf::another_ref(&self.owl_msg1_M),
            owl_msg1_A: OwlBuf::another_ref(&self.owl_msg1_A),
            owl_msg1_B: OwlBuf::another_ref(&self.owl_msg1_B),
            owl_msg1_x: owl_encd_kA_message::another_ref(&self.owl_msg1_x),
        }
    }
}

impl View for owl_msg1_AtoB<'_> {
    type V = owlSpec_msg1_AtoB;

    open spec fn view(&self) -> owlSpec_msg1_AtoB {
        owlSpec_msg1_AtoB {
            owlSpec_msg1_M: self.owl_msg1_M.view(),
            owlSpec_msg1_A: self.owl_msg1_A.view(),
            owlSpec_msg1_B: self.owl_msg1_B.view(),
            owlSpec_msg1_x: self.owl_msg1_x.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_msg1_AtoB<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg1_AtoB<'a>>)
    ensures
        res is Some ==> parse_owlSpec_msg1_AtoB(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg1_AtoB(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg1_AtoB(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_msg1_AtoB_inner<'a>(arg: &owl_msg1_AtoB) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_msg1_AtoB_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg1_AtoB_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_msg1_AtoB<'a>(arg: &owl_msg1_AtoB) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_msg1_AtoB(arg.view()),
{
    unimplemented!()
}

pub struct owl_msg2_BToS<'a> {
    pub owl_msg2_M: OwlBuf<'a>,
    pub owl_msg2_A: OwlBuf<'a>,
    pub owl_msg2_B: OwlBuf<'a>,
    pub owl_msg2_x1: owl_encd_kA_message<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg2_BToS<'a>(
    arg_owl_msg2_M: OwlBuf<'a>,
    arg_owl_msg2_A: OwlBuf<'a>,
    arg_owl_msg2_B: OwlBuf<'a>,
    arg_owl_msg2_x1: owl_encd_kA_message<'a>,
) -> (res: owl_msg2_BToS<'a>)
    ensures
        res.owl_msg2_M.view() == arg_owl_msg2_M.view(),
        res.owl_msg2_A.view() == arg_owl_msg2_A.view(),
        res.owl_msg2_B.view() == arg_owl_msg2_B.view(),
        res.owl_msg2_x1.view() == arg_owl_msg2_x1.view(),
{
    owl_msg2_BToS {
        owl_msg2_M: arg_owl_msg2_M,
        owl_msg2_A: arg_owl_msg2_A,
        owl_msg2_B: arg_owl_msg2_B,
        owl_msg2_x1: arg_owl_msg2_x1,
    }
}

impl<'a> owl_msg2_BToS<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg2_BToS<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg2_BToS {
            owl_msg2_M: OwlBuf::another_ref(&self.owl_msg2_M),
            owl_msg2_A: OwlBuf::another_ref(&self.owl_msg2_A),
            owl_msg2_B: OwlBuf::another_ref(&self.owl_msg2_B),
            owl_msg2_x1: owl_encd_kA_message::another_ref(&self.owl_msg2_x1),
        }
    }
}

impl View for owl_msg2_BToS<'_> {
    type V = owlSpec_msg2_BToS;

    open spec fn view(&self) -> owlSpec_msg2_BToS {
        owlSpec_msg2_BToS {
            owlSpec_msg2_M: self.owl_msg2_M.view(),
            owlSpec_msg2_A: self.owl_msg2_A.view(),
            owlSpec_msg2_B: self.owl_msg2_B.view(),
            owlSpec_msg2_x1: self.owl_msg2_x1.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_msg2_BToS<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg2_BToS<'a>>)
    ensures
        res is Some ==> parse_owlSpec_msg2_BToS(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg2_BToS(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg2_BToS(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_msg2_BToS_inner<'a>(arg: &owl_msg2_BToS) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_msg2_BToS_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg2_BToS_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_msg2_BToS<'a>(arg: &owl_msg2_BToS) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_msg2_BToS(arg.view()),
{
    unimplemented!()
}

pub struct owl_msg3_StoB<'a> {
    pub owl_msg3_M: OwlBuf<'a>,
    pub owl_msg3_x1: OwlBuf<'a>,
    pub owl_msg3_x2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg3_StoB<'a>(
    arg_owl_msg3_M: OwlBuf<'a>,
    arg_owl_msg3_x1: OwlBuf<'a>,
    arg_owl_msg3_x2: OwlBuf<'a>,
) -> (res: owl_msg3_StoB<'a>)
    ensures
        res.owl_msg3_M.view() == arg_owl_msg3_M.view(),
        res.owl_msg3_x1.view() == arg_owl_msg3_x1.view(),
        res.owl_msg3_x2.view() == arg_owl_msg3_x2.view(),
{
    owl_msg3_StoB {
        owl_msg3_M: arg_owl_msg3_M,
        owl_msg3_x1: arg_owl_msg3_x1,
        owl_msg3_x2: arg_owl_msg3_x2,
    }
}

impl<'a> owl_msg3_StoB<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg3_StoB<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg3_StoB {
            owl_msg3_M: OwlBuf::another_ref(&self.owl_msg3_M),
            owl_msg3_x1: OwlBuf::another_ref(&self.owl_msg3_x1),
            owl_msg3_x2: OwlBuf::another_ref(&self.owl_msg3_x2),
        }
    }
}

impl View for owl_msg3_StoB<'_> {
    type V = owlSpec_msg3_StoB;

    open spec fn view(&self) -> owlSpec_msg3_StoB {
        owlSpec_msg3_StoB {
            owlSpec_msg3_M: self.owl_msg3_M.view(),
            owlSpec_msg3_x1: self.owl_msg3_x1.view(),
            owlSpec_msg3_x2: self.owl_msg3_x2.view(),
        }
    }
}

pub exec fn parse_owl_msg3_StoB<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg3_StoB<'a>>)
    ensures
        res is Some ==> parse_owlSpec_msg3_StoB(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg3_StoB(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg3_StoB(arg.view())->Some_0,
{
    reveal(parse_owlSpec_msg3_StoB);
    let exec_comb = exec_combinator_owl_msg3_StoB();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let ((owl_msg3_M, owl_msg3_x1), owl_msg3_x2) = parsed;
        Some(
            owl_msg3_StoB {
                owl_msg3_M: OwlBuf::another_ref(&owl_msg3_M),
                owl_msg3_x1: OwlBuf::another_ref(&owl_msg3_x1),
                owl_msg3_x2: OwlBuf::another_ref(&owl_msg3_x2),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_msg3_StoB_inner<'a>(arg: &owl_msg3_StoB<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_msg3_StoB_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg3_StoB_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_msg3_StoB_inner);
    if no_usize_overflows![ arg.owl_msg3_M.len(), arg.owl_msg3_x1.len(), arg.owl_msg3_x2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_msg3_StoB();
        let mut obuf = vec_u8_of_len(
            arg.owl_msg3_M.len() + arg.owl_msg3_x1.len() + arg.owl_msg3_x2.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (OwlBuf::another_ref(&arg.owl_msg3_M), OwlBuf::another_ref(&arg.owl_msg3_x1)),
                OwlBuf::another_ref(&arg.owl_msg3_x2),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_msg3_StoB_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_msg3_StoB<'a>(arg: &owl_msg3_StoB<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_msg3_StoB(arg.view()),
{
    reveal(serialize_owlSpec_msg3_StoB);
    let res = serialize_owl_msg3_StoB_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_msg4_BtoA<'a> {
    pub owl_msg4_M: OwlBuf<'a>,
    pub owl_msg4_x1: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg4_BtoA<'a>(arg_owl_msg4_M: OwlBuf<'a>, arg_owl_msg4_x1: OwlBuf<'a>) -> (res:
    owl_msg4_BtoA<'a>)
    ensures
        res.owl_msg4_M.view() == arg_owl_msg4_M.view(),
        res.owl_msg4_x1.view() == arg_owl_msg4_x1.view(),
{
    owl_msg4_BtoA { owl_msg4_M: arg_owl_msg4_M, owl_msg4_x1: arg_owl_msg4_x1 }
}

impl<'a> owl_msg4_BtoA<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg4_BtoA<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg4_BtoA {
            owl_msg4_M: OwlBuf::another_ref(&self.owl_msg4_M),
            owl_msg4_x1: OwlBuf::another_ref(&self.owl_msg4_x1),
        }
    }
}

impl View for owl_msg4_BtoA<'_> {
    type V = owlSpec_msg4_BtoA;

    open spec fn view(&self) -> owlSpec_msg4_BtoA {
        owlSpec_msg4_BtoA {
            owlSpec_msg4_M: self.owl_msg4_M.view(),
            owlSpec_msg4_x1: self.owl_msg4_x1.view(),
        }
    }
}

pub exec fn parse_owl_msg4_BtoA<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg4_BtoA<'a>>)
    ensures
        res is Some ==> parse_owlSpec_msg4_BtoA(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg4_BtoA(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg4_BtoA(arg.view())->Some_0,
{
    reveal(parse_owlSpec_msg4_BtoA);
    let exec_comb = exec_combinator_owl_msg4_BtoA();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl_msg4_M, owl_msg4_x1) = parsed;
        Some(
            owl_msg4_BtoA {
                owl_msg4_M: OwlBuf::another_ref(&owl_msg4_M),
                owl_msg4_x1: OwlBuf::another_ref(&owl_msg4_x1),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_msg4_BtoA_inner<'a>(arg: &owl_msg4_BtoA<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_msg4_BtoA_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg4_BtoA_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_msg4_BtoA_inner);
    if no_usize_overflows![ arg.owl_msg4_M.len(), arg.owl_msg4_x1.len(), 0 ] {
        let exec_comb = exec_combinator_owl_msg4_BtoA();
        let mut obuf = vec_u8_of_len(arg.owl_msg4_M.len() + arg.owl_msg4_x1.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl_msg4_M), OwlBuf::another_ref(&arg.owl_msg4_x1)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_msg4_BtoA_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_msg4_BtoA<'a>(arg: &owl_msg4_BtoA<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_msg4_BtoA(arg.view()),
{
    reveal(serialize_owlSpec_msg4_BtoA);
    let res = serialize_owl_msg4_BtoA_inner(arg);
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
            let tmp_owl_kab362 = { SecretBuf::another_ref(&self.owl_KAB) };
            let owl_kab362 = SecretBuf::another_ref(&tmp_owl_kab362);
            let tmp_owl_kA363 = { SecretBuf::another_ref(&self.owl_KA) };
            let owl_kA363 = SecretBuf::another_ref(&tmp_owl_kA363);
            let tmp_owl_kB364 = { SecretBuf::another_ref(&self.owl_KB) };
            let owl_kB364 = SecretBuf::another_ref(&tmp_owl_kB364);
            let (tmp_owl_inp366, owl__365) = {
                effects.owl_input::<((), state_AS)>(Tracked(&mut itree))
            };
            let owl_inp366 = OwlBuf::from_vec(tmp_owl_inp366);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp366);
            if let Some(parseval) = parse_owl_msg2_BToS(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_M370 = OwlBuf::another_ref(&parseval.owl_msg2_M);
                let owl_A369 = OwlBuf::another_ref(&parseval.owl_msg2_A);
                let owl_B368 = OwlBuf::another_ref(&parseval.owl_msg2_B);
                let owl_x1367 = owl_encd_kA_message::another_ref(&parseval.owl_msg2_x1);
                let (tmp_owl_x2372, owl__371) = {
                    effects.owl_input::<((), state_AS)>(Tracked(&mut itree))
                };
                let owl_x2372 = OwlBuf::from_vec(tmp_owl_x2372);
                match owl_encd_kA_message::another_ref(&owl_x1367) {
                    owl_encd_kA_message::owl_mA2_enc(tmp_owl__373) => {
                        let owl__373 = OwlBuf::another_ref(&tmp_owl__373);
                        (owl_unit(), Tracked(itree))
                    },
                    owl_encd_kA_message::owl_mA1_enc(tmp_owl_x1_374) => {
                        let owl_x1_374 = OwlBuf::another_ref(&tmp_owl_x1_374);
                        let tmp_owl_caseval375 = {
                            let tracked owl_declassify_tok376 = consume_itree_declassify::<
                                ((), state_AS),
                                Endpoint,
                            >(&mut itree);
                            owl_dec(
                                SecretBuf::another_ref(&owl_kA363),
                                OwlBuf::another_ref(&owl_x1_374),
                                Tracked(owl_declassify_tok376),
                            )
                        };
                        let owl_caseval375 = SecretBuf::another_ref_option(&tmp_owl_caseval375);
                        match SecretBuf::another_ref_option(&owl_caseval375) {
                            Option::None => { (owl_unit(), Tracked(itree)) },
                            Option::Some(tmp_owl_resA377) => {
                                let owl_resA377 = SecretBuf::another_ref(&tmp_owl_resA377);
                                let tmp_owl_resA_378 = { SecretBuf::another_ref(&owl_resA377) };
                                let owl_resA_378 = SecretBuf::another_ref(&tmp_owl_resA_378);
                                let tmp_owl_resA__379 = { SecretBuf::another_ref(&owl_resA_378) };
                                let owl_resA__379 = SecretBuf::another_ref(&tmp_owl_resA__379);
                                let tracked owl_declassify_tok380 = consume_itree_declassify::<
                                    ((), state_AS),
                                    Endpoint,
                                >(&mut itree);
                                let parseval_tmp = SecretBuf::another_ref(&owl_resA__379);
                                if let Some(parseval) = secret_parse_owl_kA_messages(
                                    SecretBuf::another_ref(&parseval_tmp),
                                    Tracked(owl_declassify_tok380),
                                ) {
                                    let owl_parsed_caseval381 = owl_kA_messages::another_ref(
                                        &parseval,
                                    );
                                    match owl_kA_messages::another_ref(&owl_parsed_caseval381) {
                                        owl_kA_messages::owl_mA1(tmp_owl_msg1A382) => {
                                            let owl_msg1A382 = owl_kA_message_1::another_ref(
                                                &tmp_owl_msg1A382,
                                            );
                                            let parseval_tmp = OwlBuf::another_ref(&owl_x2372);
                                            if let Some(parseval) = parse_owl_encd_kB_message(
                                                OwlBuf::another_ref(&parseval_tmp),
                                            ) {
                                                let owl_parsed_caseval383 =
                                                    owl_encd_kB_message::another_ref(&parseval);
                                                match owl_encd_kB_message::another_ref(
                                                    &owl_parsed_caseval383,
                                                ) {
                                                    owl_encd_kB_message::owl_mB2_enc(
                                                        tmp_owl__384,
                                                    ) => {
                                                        let owl__384 = OwlBuf::another_ref(
                                                            &tmp_owl__384,
                                                        );
                                                        let owl__385 = {
                                                            effects.owl_output::<((), state_AS)>(
                                                                Tracked(&mut itree),
                                                                {
                                                                    let x = mk_vec_u8![];
                                                                    OwlBuf::from_vec(x)
                                                                }.as_slice(),
                                                                Some(&Bob_addr()),
                                                                &AS_addr(),
                                                            );
                                                        };
                                                        (owl_unit(), Tracked(itree))
                                                    },
                                                    owl_encd_kB_message::owl_mB1_enc(
                                                        tmp_owl_c386,
                                                    ) => {
                                                        let owl_c386 = OwlBuf::another_ref(
                                                            &tmp_owl_c386,
                                                        );
                                                        let tmp_owl_caseval387 = {
                                                            let tracked owl_declassify_tok388 =
                                                                consume_itree_declassify::<
                                                                ((), state_AS),
                                                                Endpoint,
                                                            >(&mut itree);
                                                            owl_dec(
                                                                SecretBuf::another_ref(&owl_kB364),
                                                                OwlBuf::another_ref(&owl_c386),
                                                                Tracked(owl_declassify_tok388),
                                                            )
                                                        };
                                                        let owl_caseval387 =
                                                            SecretBuf::another_ref_option(
                                                            &tmp_owl_caseval387,
                                                        );
                                                        match SecretBuf::another_ref_option(
                                                            &owl_caseval387,
                                                        ) {
                                                            Option::None => {
                                                                let owl__389 = {
                                                                    effects.owl_output::<
                                                                        ((), state_AS),
                                                                    >(
                                                                        Tracked(&mut itree),
                                                                        {
                                                                            let x = mk_vec_u8![];
                                                                            OwlBuf::from_vec(x)
                                                                        }.as_slice(),
                                                                        Some(&Bob_addr()),
                                                                        &AS_addr(),
                                                                    );
                                                                };
                                                                (owl_unit(), Tracked(itree))
                                                            },
                                                            Option::Some(tmp_owl_resB390) => {
                                                                let owl_resB390 =
                                                                    SecretBuf::another_ref(
                                                                    &tmp_owl_resB390,
                                                                );
                                                                let tmp_owl_resB_391 = {
                                                                    SecretBuf::another_ref(
                                                                        &owl_resB390,
                                                                    )
                                                                };
                                                                let owl_resB_391 =
                                                                    SecretBuf::another_ref(
                                                                    &tmp_owl_resB_391,
                                                                );
                                                                let tmp_owl_resB__392 = {
                                                                    SecretBuf::another_ref(
                                                                        &owl_resB_391,
                                                                    )
                                                                };
                                                                let owl_resB__392 =
                                                                    SecretBuf::another_ref(
                                                                    &tmp_owl_resB__392,
                                                                );
                                                                let tracked owl_declassify_tok393 =
                                                                    consume_itree_declassify::<
                                                                    ((), state_AS),
                                                                    Endpoint,
                                                                >(&mut itree);
                                                                let parseval_tmp =
                                                                    SecretBuf::another_ref(
                                                                    &owl_resB__392,
                                                                );
                                                                if let Some(parseval) =
                                                                    secret_parse_owl_kB_messages(
                                                                    SecretBuf::another_ref(
                                                                        &parseval_tmp,
                                                                    ),
                                                                    Tracked(owl_declassify_tok393),
                                                                ) {
                                                                    let owl_parsed_caseval394 =
                                                                        owl_kB_messages::another_ref(
                                                                    &parseval);
                                                                    match owl_kB_messages::another_ref(
                                                                    &owl_parsed_caseval394) {
                                                                        owl_kB_messages::owl_mB1(
                                                                            tmp_owl_msg1B395,
                                                                        ) => {
                                                                            let owl_msg1B395 =
                                                                                owl_kB_message_1::another_ref(
                                                                            &tmp_owl_msg1B395);
                                                                            let parseval =
                                                                                owl_kA_message_1::another_ref(
                                                                            &owl_msg1A382);
                                                                            let owl_nA1_399 =
                                                                                SecretBuf::another_ref(
                                                                            &parseval.owl__nA1);
                                                                            let owl__398 =
                                                                                SecretBuf::another_ref(
                                                                            &parseval.owl__mA);
                                                                            let owl__397 =
                                                                                OwlBuf::another_ref(
                                                                                &parseval.owl__AA,
                                                                            );
                                                                            let owl__396 =
                                                                                OwlBuf::another_ref(
                                                                                &parseval.owl__BA,
                                                                            );
                                                                            let parseval =
                                                                                owl_kB_message_1::another_ref(
                                                                            &owl_msg1B395);
                                                                            let owl_nB1_403 =
                                                                                SecretBuf::another_ref(
                                                                            &parseval.owl__nB1);
                                                                            let owl__402 =
                                                                                OwlBuf::another_ref(
                                                                                &parseval.owl__mB,
                                                                            );
                                                                            let owl__401 =
                                                                                OwlBuf::another_ref(
                                                                                &parseval.owl__AB,
                                                                            );
                                                                            let owl__400 =
                                                                                OwlBuf::another_ref(
                                                                                &parseval.owl__BB,
                                                                            );
                                                                            let tmp_owl_m404 = {
                                                                                owl_mA2(
                                                                                    owl_kA_message_2::another_ref(

                                                                                        &owl_kA_message_2(

                                                                                            SecretBuf::another_ref(

                                                                                                &owl_nA1_399,
                                                                                            ),
                                                                                            SecretBuf::another_ref(

                                                                                                &owl_kab362,
                                                                                            ),
                                                                                        ),
                                                                                    ),
                                                                                )
                                                                            };
                                                                            let owl_m404 =
                                                                                owl_kA_messages::another_ref(
                                                                            &tmp_owl_m404);
                                                                            let tmp_owl_encmA405 = {
                                                                                let tmp_owl_coins406 =
                                                                                    effects.owl_sample::<
                                                                                    ((), state_AS),
                                                                                >(
                                                                                    Tracked(
                                                                                        &mut itree,
                                                                                    ),
                                                                                    NONCE_SIZE,
                                                                                );
                                                                                let owl_coins406 =
                                                                                    SecretBuf::another_ref(
                                                                                &tmp_owl_coins406);
                                                                                owl_enc(
                                                                                    SecretBuf::another_ref(
                                                                                    &owl_kA363),
                                                                                    SecretBuf::another_ref(

                                                                                        &OwlBuf::from_vec(

                                                                                            serialize_owl_kA_messages(

                                                                                                &owl_m404,
                                                                                            ),
                                                                                        ).into_secret(),
                                                                                    ),
                                                                                    SecretBuf::another_ref(
                                                                                    &owl_coins406),
                                                                                )
                                                                            };
                                                                            let owl_encmA405 =
                                                                                OwlBuf::from_vec(
                                                                                tmp_owl_encmA405,
                                                                            );
                                                                            let tmp_owl_m407 = {
                                                                                owl_mB2(
                                                                                    owl_kB_message_2::another_ref(

                                                                                        &owl_kB_message_2(

                                                                                            SecretBuf::another_ref(

                                                                                                &owl_nB1_403,
                                                                                            ),
                                                                                            SecretBuf::another_ref(

                                                                                                &owl_kab362,
                                                                                            ),
                                                                                        ),
                                                                                    ),
                                                                                )
                                                                            };
                                                                            let owl_m407 =
                                                                                owl_kB_messages::another_ref(
                                                                            &tmp_owl_m407);
                                                                            let tmp_owl_encmB408 = {
                                                                                let tmp_owl_coins409 =
                                                                                    effects.owl_sample::<
                                                                                    ((), state_AS),
                                                                                >(
                                                                                    Tracked(
                                                                                        &mut itree,
                                                                                    ),
                                                                                    NONCE_SIZE,
                                                                                );
                                                                                let owl_coins409 =
                                                                                    SecretBuf::another_ref(
                                                                                &tmp_owl_coins409);
                                                                                owl_enc(
                                                                                    SecretBuf::another_ref(
                                                                                    &owl_kB364),
                                                                                    SecretBuf::another_ref(

                                                                                        &OwlBuf::from_vec(

                                                                                            serialize_owl_kB_messages(

                                                                                                &owl_m407,
                                                                                            ),
                                                                                        ).into_secret(),
                                                                                    ),
                                                                                    SecretBuf::another_ref(
                                                                                    &owl_coins409),
                                                                                )
                                                                            };
                                                                            let owl_encmB408 =
                                                                                OwlBuf::from_vec(
                                                                                tmp_owl_encmB408,
                                                                            );
                                                                            let owl__410 = {
                                                                                effects.owl_output::<
                                                                                    ((), state_AS),
                                                                                >(
                                                                                    Tracked(
                                                                                        &mut itree,
                                                                                    ),
                                                                                    serialize_owl_msg3_StoB(

                                                                                        &owl_msg3_StoB(

                                                                                            OwlBuf::another_ref(

                                                                                                &owl_M370,
                                                                                            ),
                                                                                            OwlBuf::another_ref(

                                                                                                &owl_encmA405,
                                                                                            ),
                                                                                            OwlBuf::another_ref(

                                                                                                &owl_encmB408,
                                                                                            ),
                                                                                        ),
                                                                                    ).as_slice(),
                                                                                    Some(
                                                                                        &Bob_addr(),
                                                                                    ),
                                                                                    &AS_addr(),
                                                                                );
                                                                            };
                                                                            (
                                                                                owl_unit(),
                                                                                Tracked(itree),
                                                                            )
                                                                        },
                                                                        owl_kB_messages::owl_mB2(
                                                                            tmp_owl__411,
                                                                        ) => {
                                                                            let owl__411 =
                                                                                owl_kB_message_2::another_ref(
                                                                            &tmp_owl__411);
                                                                            let owl__412 = {
                                                                                effects.owl_output::<
                                                                                    ((), state_AS),
                                                                                >(
                                                                                    Tracked(
                                                                                        &mut itree,
                                                                                    ),
                                                                                    {
                                                                                        let x =
                                                                                            mk_vec_u8![];
                                                                                        OwlBuf::from_vec(
                                                                                        x)
                                                                                    }.as_slice(),
                                                                                    Some(
                                                                                        &Bob_addr(),
                                                                                    ),
                                                                                    &AS_addr(),
                                                                                );
                                                                            };
                                                                            (
                                                                                owl_unit(),
                                                                                Tracked(itree),
                                                                            )
                                                                        },
                                                                    }
                                                                } else {
                                                                    (owl_unit(), Tracked(itree))
                                                                }
                                                            },
                                                        }
                                                    },
                                                }
                                            } else {
                                                (owl_unit(), Tracked(itree))
                                            }
                                        },
                                        owl_kA_messages::owl_mA2(tmp_owl__413) => {
                                            let owl__413 = owl_kA_message_2::another_ref(
                                                &tmp_owl__413,
                                            );
                                            let owl__414 = {
                                                effects.owl_output::<((), state_AS)>(
                                                    Tracked(&mut itree),
                                                    {
                                                        let x = mk_vec_u8![];
                                                        OwlBuf::from_vec(x)
                                                    }.as_slice(),
                                                    Some(&Bob_addr()),
                                                    &AS_addr(),
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
                    },
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
    pub owl_A_username: SecretBuf<'Alice>,
    pub owl_NA: SecretBuf<'Alice>,
    pub owl_B_username: SecretBuf<'Alice>,
    pub owl_KA: SecretBuf<'Alice>,
    pub owl_m: SecretBuf<'Alice>,
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
            let tmp_owl_A415 = { SecretBuf::another_ref(&self.owl_A_username) };
            let owl_A415 = SecretBuf::another_ref(&tmp_owl_A415);
            let tmp_owl_B416 = { SecretBuf::another_ref(&self.owl_B_username) };
            let owl_B416 = SecretBuf::another_ref(&tmp_owl_B416);
            let tmp_owl_M417 = { SecretBuf::another_ref(&self.owl_m) };
            let owl_M417 = SecretBuf::another_ref(&tmp_owl_M417);
            let tmp_owl_nA418 = { SecretBuf::another_ref(&self.owl_NA) };
            let owl_nA418 = SecretBuf::another_ref(&tmp_owl_nA418);
            let tmp_owl_kA419 = { SecretBuf::another_ref(&self.owl_KA) };
            let owl_kA419 = SecretBuf::another_ref(&tmp_owl_kA419);
            let owl__420 = { owl_unit() };
            let tmp_owl_declassified_buf157421 = {
                let tracked owl_declassify_tok422 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_A415).declassify(Tracked(owl_declassify_tok422)) }
            };
            let owl_declassified_buf157421 = OwlBuf::another_ref(&tmp_owl_declassified_buf157421);
            let tmp_owl_declassified_buf160423 = {
                let tracked owl_declassify_tok424 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_B416).declassify(Tracked(owl_declassify_tok424)) }
            };
            let owl_declassified_buf160423 = OwlBuf::another_ref(&tmp_owl_declassified_buf160423);
            let tmp_owl_m425 = {
                owl_mA1(
                    owl_kA_message_1::another_ref(
                        &owl_kA_message_1(
                            SecretBuf::another_ref(&owl_nA418),
                            SecretBuf::another_ref(&owl_M417),
                            OwlBuf::another_ref(&owl_declassified_buf157421),
                            OwlBuf::another_ref(&owl_declassified_buf160423),
                        ),
                    ),
                )
            };
            let owl_m425 = owl_kA_messages::another_ref(&tmp_owl_m425);
            let tmp_owl_encm426 = {
                let tmp_owl_coins427 = effects.owl_sample::<(owlSpec_alice_result, state_Alice)>(
                    Tracked(&mut itree),
                    NONCE_SIZE,
                );
                let owl_coins427 = SecretBuf::another_ref(&tmp_owl_coins427);
                owl_enc(
                    SecretBuf::another_ref(&owl_kA419),
                    SecretBuf::another_ref(
                        &OwlBuf::from_vec(serialize_owl_kA_messages(&owl_m425)).into_secret(),
                    ),
                    SecretBuf::another_ref(&owl_coins427),
                )
            };
            let owl_encm426 = OwlBuf::from_vec(tmp_owl_encm426);
            let tmp_owl_declassified_buf166428 = {
                let tracked owl_declassify_tok429 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_M417).declassify(Tracked(owl_declassify_tok429)) }
            };
            let owl_declassified_buf166428 = OwlBuf::another_ref(&tmp_owl_declassified_buf166428);
            let tmp_owl_declassified_buf169430 = {
                let tracked owl_declassify_tok431 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_A415).declassify(Tracked(owl_declassify_tok431)) }
            };
            let owl_declassified_buf169430 = OwlBuf::another_ref(&tmp_owl_declassified_buf169430);
            let tmp_owl_declassified_buf172432 = {
                let tracked owl_declassify_tok433 = consume_itree_declassify::<
                    (owlSpec_alice_result, state_Alice),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_B416).declassify(Tracked(owl_declassify_tok433)) }
            };
            let owl_declassified_buf172432 = OwlBuf::another_ref(&tmp_owl_declassified_buf172432);
            let owl__434 = {
                effects.owl_output::<(owlSpec_alice_result, state_Alice)>(
                    Tracked(&mut itree),
                    serialize_owl_msg1_AtoB(
                        &owl_msg1_AtoB(
                            OwlBuf::another_ref(&owl_declassified_buf166428),
                            OwlBuf::another_ref(&owl_declassified_buf169430),
                            OwlBuf::another_ref(&owl_declassified_buf172432),
                            owl_encd_kA_message::another_ref(
                                &owl_mA1_enc(OwlBuf::another_ref(&owl_encm426)),
                            ),
                        ),
                    ).as_slice(),
                    Some(&Bob_addr()),
                    &Alice_addr(),
                );
            };
            let (tmp_owl_inp436, owl__435) = {
                effects.owl_input::<(owlSpec_alice_result, state_Alice)>(Tracked(&mut itree))
            };
            let owl_inp436 = OwlBuf::from_vec(tmp_owl_inp436);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp436);
            if let Some(parseval) = parse_owl_msg4_BtoA(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_M_438 = OwlBuf::another_ref(&parseval.owl_msg4_M);
                let owl_x1_437 = OwlBuf::another_ref(&parseval.owl_msg4_x1);
                let tmp_owl_caseval439 = {
                    let tracked owl_declassify_tok440 = consume_itree_declassify::<
                        (owlSpec_alice_result, state_Alice),
                        Endpoint,
                    >(&mut itree);
                    owl_dec(
                        SecretBuf::another_ref(&owl_kA419),
                        OwlBuf::another_ref(&owl_x1_437),
                        Tracked(owl_declassify_tok440),
                    )
                };
                let owl_caseval439 = SecretBuf::another_ref_option(&tmp_owl_caseval439);
                match SecretBuf::another_ref_option(&owl_caseval439) {
                    Option::None => {
                        (owl_alice_result::another_ref(&owl_alice_None()), Tracked(itree))
                    },
                    Option::Some(tmp_owl_res441) => {
                        let owl_res441 = SecretBuf::another_ref(&tmp_owl_res441);
                        let tmp_owl_res_442 = { SecretBuf::another_ref(&owl_res441) };
                        let owl_res_442 = SecretBuf::another_ref(&tmp_owl_res_442);
                        let tmp_owl_res__443 = { SecretBuf::another_ref(&owl_res_442) };
                        let owl_res__443 = SecretBuf::another_ref(&tmp_owl_res__443);
                        let tmp_owl_o444 = {
                            let tracked owl_declassify_tok445 = consume_itree_declassify::<
                                (owlSpec_alice_result, state_Alice),
                                Endpoint,
                            >(&mut itree);
                            let parseval_tmp = SecretBuf::another_ref(&owl_res__443);
                            if let Some(parseval) = secret_parse_owl_kA_messages(
                                SecretBuf::another_ref(&parseval_tmp),
                                Tracked(owl_declassify_tok445),
                            ) {
                                let owl_parsed_caseval446 = owl_kA_messages::another_ref(&parseval);
                                match owl_kA_messages::another_ref(&owl_parsed_caseval446) {
                                    owl_kA_messages::owl_mA1(tmp_owl__447) => {
                                        let owl__447 = owl_kA_message_1::another_ref(&tmp_owl__447);
                                        owl_alice_None()
                                    },
                                    owl_kA_messages::owl_mA2(tmp_owl_msg2448) => {
                                        let owl_msg2448 = owl_kA_message_2::another_ref(
                                            &tmp_owl_msg2448,
                                        );
                                        let parseval = owl_kA_message_2::another_ref(&owl_msg2448);
                                        let owl_nA_450 = SecretBuf::another_ref(&parseval.owl__nA2);
                                        let owl_kAB_449 = SecretBuf::another_ref(
                                            &parseval.owl__kABA,
                                        );
                                        let owl_eq_bool208451 = {
                                            let tracked owl_declassify_tok452 =
                                                consume_itree_declassify::<
                                                (owlSpec_alice_result, state_Alice),
                                                Endpoint,
                                            >(&mut itree);
                                            {
                                                SecretBuf::secret_eq(
                                                    &owl_nA_450,
                                                    &owl_nA418,
                                                    Tracked(owl_declassify_tok452),
                                                )
                                            }
                                        };

                                        if owl_eq_bool208451 {
                                            owl_alice_Some(SecretBuf::another_ref(&owl_kAB_449))
                                        } else {
                                            owl_alice_None()
                                        }

                                    },
                                }
                            } else {
                                owl_alice_None()
                            }
                        };
                        let owl_o444 = owl_alice_result::another_ref(&tmp_owl_o444);
                        (owl_alice_result::another_ref(&owl_o444), Tracked(itree))
                    },
                }
            } else {
                (owl_alice_result::another_ref(&owl_alice_None()), Tracked(itree))
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
    pub owl_B_username: SecretBuf<'Bob>,
    pub owl_KB: SecretBuf<'Bob>,
    pub owl_m: SecretBuf<'Bob>,
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
            let tmp_owl_B453 = { SecretBuf::another_ref(&self.owl_B_username) };
            let owl_B453 = SecretBuf::another_ref(&tmp_owl_B453);
            let tmp_owl_nB454 = { SecretBuf::another_ref(&self.owl_NB) };
            let owl_nB454 = SecretBuf::another_ref(&tmp_owl_nB454);
            let tmp_owl_kB455 = { SecretBuf::another_ref(&self.owl_KB) };
            let owl_kB455 = SecretBuf::another_ref(&tmp_owl_kB455);
            let (tmp_owl_inp457, owl__456) = {
                effects.owl_input::<(owlSpec_bob_result, state_Bob)>(Tracked(&mut itree))
            };
            let owl_inp457 = OwlBuf::from_vec(tmp_owl_inp457);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp457);
            if let Some(parseval) = parse_owl_msg1_AtoB(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_M_461 = OwlBuf::another_ref(&parseval.owl_msg1_M);
                let owl_A_460 = OwlBuf::another_ref(&parseval.owl_msg1_A);
                let owl_B_459 = OwlBuf::another_ref(&parseval.owl_msg1_B);
                let owl_encm_458 = owl_encd_kA_message::another_ref(&parseval.owl_msg1_x);
                let owl__462 = { owl_unit() };
                match owl_encd_kA_message::another_ref(&owl_encm_458) {
                    owl_encd_kA_message::owl_mA2_enc(tmp_owl__463) => {
                        let owl__463 = OwlBuf::another_ref(&tmp_owl__463);
                        let owl__464 = {
                            effects.owl_output::<(owlSpec_bob_result, state_Bob)>(
                                Tracked(&mut itree),
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }.as_slice(),
                                Some(&AS_addr()),
                                &Bob_addr(),
                            );
                        };
                        let (tmp_owl__466, owl__465) = {
                            effects.owl_input::<(owlSpec_bob_result, state_Bob)>(
                                Tracked(&mut itree),
                            )
                        };
                        let owl__466 = OwlBuf::from_vec(tmp_owl__466);
                        let owl__467 = {
                            effects.owl_output::<(owlSpec_bob_result, state_Bob)>(
                                Tracked(&mut itree),
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }.as_slice(),
                                Some(&Alice_addr()),
                                &Bob_addr(),
                            );
                        };
                        (owl_bob_result::another_ref(&owl_bob_None()), Tracked(itree))
                    },
                    owl_encd_kA_message::owl_mA1_enc(tmp_owl_v468) => {
                        let owl_v468 = OwlBuf::another_ref(&tmp_owl_v468);
                        let tmp_owl_v_469 = { owl_mA1_enc(OwlBuf::another_ref(&owl_v468)) };
                        let owl_v_469 = owl_encd_kA_message::another_ref(&tmp_owl_v_469);
                        let tmp_owl_declassified_buf238470 = {
                            let tracked owl_declassify_tok471 = consume_itree_declassify::<
                                (owlSpec_bob_result, state_Bob),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_B453).declassify(
                                    Tracked(owl_declassify_tok471),
                                )
                            }
                        };
                        let owl_declassified_buf238470 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf238470,
                        );
                        let tmp_owl_m472 = {
                            owl_mB1(
                                owl_kB_message_1::another_ref(
                                    &owl_kB_message_1(
                                        SecretBuf::another_ref(&owl_nB454),
                                        OwlBuf::another_ref(&owl_M_461),
                                        OwlBuf::another_ref(&owl_A_460),
                                        OwlBuf::another_ref(&owl_declassified_buf238470),
                                    ),
                                ),
                            )
                        };
                        let owl_m472 = owl_kB_messages::another_ref(&tmp_owl_m472);
                        let tmp_owl_encm473 = {
                            let tmp_owl_coins474 = effects.owl_sample::<
                                (owlSpec_bob_result, state_Bob),
                            >(Tracked(&mut itree), NONCE_SIZE);
                            let owl_coins474 = SecretBuf::another_ref(&tmp_owl_coins474);
                            owl_enc(
                                SecretBuf::another_ref(&owl_kB455),
                                SecretBuf::another_ref(
                                    &OwlBuf::from_vec(
                                        serialize_owl_kB_messages(&owl_m472),
                                    ).into_secret(),
                                ),
                                SecretBuf::another_ref(&owl_coins474),
                            )
                        };
                        let owl_encm473 = OwlBuf::from_vec(tmp_owl_encm473);
                        let tmp_owl_declassified_buf244475 = {
                            let tracked owl_declassify_tok476 = consume_itree_declassify::<
                                (owlSpec_bob_result, state_Bob),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_B453).declassify(
                                    Tracked(owl_declassify_tok476),
                                )
                            }
                        };
                        let owl_declassified_buf244475 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf244475,
                        );
                        let owl__477 = {
                            effects.owl_output::<(owlSpec_bob_result, state_Bob)>(
                                Tracked(&mut itree),
                                serialize_owl_msg2_BToS(
                                    &owl_msg2_BToS(
                                        OwlBuf::another_ref(&owl_M_461),
                                        OwlBuf::another_ref(&owl_A_460),
                                        OwlBuf::another_ref(&owl_declassified_buf244475),
                                        owl_encd_kA_message::another_ref(&owl_v_469),
                                    ),
                                ).as_slice(),
                                Some(&AS_addr()),
                                &Bob_addr(),
                            );
                        };
                        let owl__478 = {
                            effects.owl_output::<(owlSpec_bob_result, state_Bob)>(
                                Tracked(&mut itree),
                                OwlBuf::from_vec(
                                    serialize_owl_encd_kB_message(
                                        &owl_mB1_enc(OwlBuf::another_ref(&owl_encm473)),
                                    ),
                                ).as_slice(),
                                Some(&AS_addr()),
                                &Bob_addr(),
                            );
                        };
                        let (tmp_owl_inp2480, owl__479) = {
                            effects.owl_input::<(owlSpec_bob_result, state_Bob)>(
                                Tracked(&mut itree),
                            )
                        };
                        let owl_inp2480 = OwlBuf::from_vec(tmp_owl_inp2480);
                        let parseval_tmp = OwlBuf::another_ref(&owl_inp2480);
                        if let Some(parseval) = parse_owl_msg3_StoB(
                            OwlBuf::another_ref(&parseval_tmp),
                        ) {
                            let owl_M_483 = OwlBuf::another_ref(&parseval.owl_msg3_M);
                            let owl_x1_482 = OwlBuf::another_ref(&parseval.owl_msg3_x1);
                            let owl_x2_481 = OwlBuf::another_ref(&parseval.owl_msg3_x2);
                            let tmp_owl_caseval484 = {
                                let tracked owl_declassify_tok485 = consume_itree_declassify::<
                                    (owlSpec_bob_result, state_Bob),
                                    Endpoint,
                                >(&mut itree);
                                owl_dec(
                                    SecretBuf::another_ref(&owl_kB455),
                                    OwlBuf::another_ref(&owl_x2_481),
                                    Tracked(owl_declassify_tok485),
                                )
                            };
                            let owl_caseval484 = SecretBuf::another_ref_option(&tmp_owl_caseval484);
                            match SecretBuf::another_ref_option(&owl_caseval484) {
                                Option::None => {
                                    let owl__486 = {
                                        effects.owl_output::<(owlSpec_bob_result, state_Bob)>(
                                            Tracked(&mut itree),
                                            {
                                                let x = mk_vec_u8![];
                                                OwlBuf::from_vec(x)
                                            }.as_slice(),
                                            Some(&Alice_addr()),
                                            &Bob_addr(),
                                        );
                                    };
                                    (owl_bob_result::another_ref(&owl_bob_None()), Tracked(itree))
                                },
                                Option::Some(tmp_owl_res487) => {
                                    let owl_res487 = SecretBuf::another_ref(&tmp_owl_res487);
                                    let tmp_owl_res_488 = { SecretBuf::another_ref(&owl_res487) };
                                    let owl_res_488 = SecretBuf::another_ref(&tmp_owl_res_488);
                                    let tmp_owl_res__489 = { SecretBuf::another_ref(&owl_res_488) };
                                    let owl_res__489 = SecretBuf::another_ref(&tmp_owl_res__489);
                                    let tmp_owl_o490 = {
                                        let tracked owl_declassify_tok491 =
                                            consume_itree_declassify::<
                                            (owlSpec_bob_result, state_Bob),
                                            Endpoint,
                                        >(&mut itree);
                                        let parseval_tmp = SecretBuf::another_ref(&owl_res__489);
                                        if let Some(parseval) = secret_parse_owl_kB_messages(
                                            SecretBuf::another_ref(&parseval_tmp),
                                            Tracked(owl_declassify_tok491),
                                        ) {
                                            let owl_parsed_caseval492 =
                                                owl_kB_messages::another_ref(&parseval);
                                            match owl_kB_messages::another_ref(
                                                &owl_parsed_caseval492,
                                            ) {
                                                owl_kB_messages::owl_mB1(tmp_owl__493) => {
                                                    let owl__493 = owl_kB_message_1::another_ref(
                                                        &tmp_owl__493,
                                                    );
                                                    owl_bob_None()
                                                },
                                                owl_kB_messages::owl_mB2(tmp_owl_msg2494) => {
                                                    let owl_msg2494 = owl_kB_message_2::another_ref(
                                                        &tmp_owl_msg2494,
                                                    );
                                                    let parseval = owl_kB_message_2::another_ref(
                                                        &owl_msg2494,
                                                    );
                                                    let owl_nB_496 = SecretBuf::another_ref(
                                                        &parseval.owl__nB2,
                                                    );
                                                    let owl_msg2_495 = SecretBuf::another_ref(
                                                        &parseval.owl__kABB,
                                                    );
                                                    let owl_eq_bool284497 = {
                                                        let tracked owl_declassify_tok498 =
                                                            consume_itree_declassify::<
                                                            (owlSpec_bob_result, state_Bob),
                                                            Endpoint,
                                                        >(&mut itree);
                                                        {
                                                            SecretBuf::secret_eq(
                                                                &owl_nB_496,
                                                                &owl_nB454,
                                                                Tracked(owl_declassify_tok498),
                                                            )
                                                        }
                                                    };

                                                    if owl_eq_bool284497 {
                                                        let owl__499 = {
                                                            effects.owl_output::<
                                                                (owlSpec_bob_result, state_Bob),
                                                            >(
                                                                Tracked(&mut itree),
                                                                serialize_owl_msg4_BtoA(
                                                                    &owl_msg4_BtoA(
                                                                        OwlBuf::another_ref(
                                                                            &owl_M_483,
                                                                        ),
                                                                        OwlBuf::another_ref(
                                                                            &owl_x1_482,
                                                                        ),
                                                                    ),
                                                                ).as_slice(),
                                                                Some(&Alice_addr()),
                                                                &Bob_addr(),
                                                            );
                                                        };
                                                        owl_bob_Some(
                                                            SecretBuf::another_ref(&owl_msg2_495),
                                                        )
                                                    } else {
                                                        owl_bob_None()
                                                    }

                                                },
                                            }
                                        } else {
                                            owl_bob_None()
                                        }
                                    };
                                    let owl_o490 = owl_bob_result::another_ref(&tmp_owl_o490);
                                    (owl_bob_result::another_ref(&owl_o490), Tracked(itree))
                                },
                            }
                        } else {
                            (owl_bob_result::another_ref(&owl_bob_None()), Tracked(itree))
                        }
                    },
                }
            } else {
                {
                    let owl__500 = { owl_unit() };
                    (owl_bob_result::another_ref(&owl_bob_None()), Tracked(itree))
                }
            }
        };
        Ok((owl_bob_result::another_ref(&res_inner), Tracked(itree)))
    }
}

} // verus!
