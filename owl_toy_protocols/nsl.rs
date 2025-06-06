// Extracted verus code from file owl_toy_protocols/nsl.owl:
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
spec fn spec_combinator_owlSpec_nsl_alice_msg3() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_nsl_alice_msg3() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_nsl_alice_msg3(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_nsl_alice_msg3 {
    pub owlSpec__na3A: Seq<u8>,
    pub owlSpec__na3B: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_nsl_alice_msg3(x: Seq<u8>) -> Option<owlSpec_nsl_alice_msg3> {
    let spec_comb = spec_combinator_owlSpec_nsl_alice_msg3();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__na3A, owlSpec__na3B)) = parsed;
        Some(owlSpec_nsl_alice_msg3 { owlSpec__na3A, owlSpec__na3B })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_nsl_alice_msg3_inner(x: owlSpec_nsl_alice_msg3) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__na3A.len(), x.owlSpec__na3B.len() ] {
        let spec_comb = spec_combinator_owlSpec_nsl_alice_msg3();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__na3A, x.owlSpec__na3B))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_nsl_alice_msg3(x: owlSpec_nsl_alice_msg3) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_nsl_alice_msg3_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_nsl_alice_msg3 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_nsl_alice_msg3(self)
    }
}

pub open spec fn nsl_alice_msg3(
    arg_owlSpec__na3A: Seq<u8>,
    arg_owlSpec__na3B: Seq<u8>,
) -> owlSpec_nsl_alice_msg3 {
    owlSpec_nsl_alice_msg3 { owlSpec__na3A: arg_owlSpec__na3A, owlSpec__na3B: arg_owlSpec__na3B }
}

spec fn spec_combinator_owlSpec_secret_nsl_alice_msg3() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_secret_nsl_alice_msg3() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_nsl_alice_msg3(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_secret_nsl_alice_msg3 {
    pub owlSpec__na3A: Seq<u8>,
    pub owlSpec__na3B: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_nsl_alice_msg3(x: Seq<u8>) -> Option<
    owlSpec_secret_nsl_alice_msg3,
> {
    let spec_comb = spec_combinator_owlSpec_secret_nsl_alice_msg3();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__na3A, owlSpec__na3B)) = parsed;
        Some(owlSpec_secret_nsl_alice_msg3 { owlSpec__na3A, owlSpec__na3B })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_nsl_alice_msg3_inner(
    x: owlSpec_secret_nsl_alice_msg3,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__na3A.len(), x.owlSpec__na3B.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_nsl_alice_msg3();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__na3A, x.owlSpec__na3B))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_nsl_alice_msg3(x: owlSpec_secret_nsl_alice_msg3) -> Seq<
    u8,
> {
    if let Some(val) = serialize_owlSpec_secret_nsl_alice_msg3_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_nsl_alice_msg3 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_nsl_alice_msg3(self)
    }
}

pub open spec fn secret_nsl_alice_msg3(
    arg_owlSpec__na3A: Seq<u8>,
    arg_owlSpec__na3B: Seq<u8>,
) -> owlSpec_secret_nsl_alice_msg3 {
    owlSpec_secret_nsl_alice_msg3 {
        owlSpec__na3A: arg_owlSpec__na3A,
        owlSpec__na3B: arg_owlSpec__na3B,
    }
}

pub enum owlSpec_nsl_alice_message {
    owlSpec_Msg1(Seq<u8>),
    owlSpec_Msg3(owlSpec_nsl_alice_msg3),
}

use owlSpec_nsl_alice_message::*;

#[verifier::external_body]
pub closed spec fn parse_owlSpec_nsl_alice_message(x: Seq<u8>) -> Option<
    owlSpec_nsl_alice_message,
> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_nsl_alice_message_inner(
    x: owlSpec_nsl_alice_message,
) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_nsl_alice_message(x: owlSpec_nsl_alice_message) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_nsl_alice_message {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_nsl_alice_message(self)
    }
}

pub open spec fn Msg1(x: Seq<u8>) -> owlSpec_nsl_alice_message {
    crate::owlSpec_nsl_alice_message::owlSpec_Msg1(x)
}

pub open spec fn Msg3(x: owlSpec_nsl_alice_msg3) -> owlSpec_nsl_alice_message {
    crate::owlSpec_nsl_alice_message::owlSpec_Msg3(x)
}

pub open spec fn Msg1_enumtest(x: owlSpec_nsl_alice_message) -> bool {
    match x {
        owlSpec_nsl_alice_message::owlSpec_Msg1(_) => true,
        _ => false,
    }
}

pub open spec fn Msg3_enumtest(x: owlSpec_nsl_alice_message) -> bool {
    match x {
        owlSpec_nsl_alice_message::owlSpec_Msg3(_) => true,
        _ => false,
    }
}

pub struct owlSpec_nsl_bob_message {
    pub owlSpec__nb_cipher: Ghost<()>,
    pub owlSpec__nbA: Seq<u8>,
    pub owlSpec__nbB: Seq<u8>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_nsl_bob_message(x: Seq<u8>) -> Option<owlSpec_nsl_bob_message> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_nsl_bob_message_inner(x: owlSpec_nsl_bob_message) -> Option<
    Seq<u8>,
> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_nsl_bob_message(x: owlSpec_nsl_bob_message) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_nsl_bob_message {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_nsl_bob_message(self)
    }
}

pub open spec fn nsl_bob_message(
    arg_owlSpec__nb_cipher: Ghost<()>,
    arg_owlSpec__nbA: Seq<u8>,
    arg_owlSpec__nbB: Seq<u8>,
) -> owlSpec_nsl_bob_message {
    owlSpec_nsl_bob_message {
        owlSpec__nb_cipher: arg_owlSpec__nb_cipher,
        owlSpec__nbA: arg_owlSpec__nbA,
        owlSpec__nbB: arg_owlSpec__nbB,
    }
}

pub struct owlSpec_secret_nsl_bob_message {
    pub owlSpec__nb_cipher: Ghost<()>,
    pub owlSpec__nbA: Seq<u8>,
    pub owlSpec__nbB: Seq<u8>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_secret_nsl_bob_message(x: Seq<u8>) -> Option<
    owlSpec_secret_nsl_bob_message,
> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_secret_nsl_bob_message_inner(
    x: owlSpec_secret_nsl_bob_message,
) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_secret_nsl_bob_message(
    x: owlSpec_secret_nsl_bob_message,
) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_secret_nsl_bob_message {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_nsl_bob_message(self)
    }
}

pub open spec fn secret_nsl_bob_message(
    arg_owlSpec__nb_cipher: Ghost<()>,
    arg_owlSpec__nbA: Seq<u8>,
    arg_owlSpec__nbB: Seq<u8>,
) -> owlSpec_secret_nsl_bob_message {
    owlSpec_secret_nsl_bob_message {
        owlSpec__nb_cipher: arg_owlSpec__nb_cipher,
        owlSpec__nbA: arg_owlSpec__nbA,
        owlSpec__nbB: arg_owlSpec__nbB,
    }
}

spec fn spec_combinator_owlSpec_nsl_result() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_nsl_result() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_nsl_result(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_nsl_result {
    pub owlSpec__nrA: Seq<u8>,
    pub owlSpec__nrB: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_nsl_result(x: Seq<u8>) -> Option<owlSpec_nsl_result> {
    let spec_comb = spec_combinator_owlSpec_nsl_result();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__nrA, owlSpec__nrB)) = parsed;
        Some(owlSpec_nsl_result { owlSpec__nrA, owlSpec__nrB })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_nsl_result_inner(x: owlSpec_nsl_result) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__nrA.len(), x.owlSpec__nrB.len() ] {
        let spec_comb = spec_combinator_owlSpec_nsl_result();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__nrA, x.owlSpec__nrB))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_nsl_result(x: owlSpec_nsl_result) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_nsl_result_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_nsl_result {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_nsl_result(self)
    }
}

pub open spec fn nsl_result(
    arg_owlSpec__nrA: Seq<u8>,
    arg_owlSpec__nrB: Seq<u8>,
) -> owlSpec_nsl_result {
    owlSpec_nsl_result { owlSpec__nrA: arg_owlSpec__nrA, owlSpec__nrB: arg_owlSpec__nrB }
}

spec fn spec_combinator_owlSpec_secret_nsl_result() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_secret_nsl_result() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_secret_nsl_result(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_secret_nsl_result {
    pub owlSpec__nrA: Seq<u8>,
    pub owlSpec__nrB: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_nsl_result(x: Seq<u8>) -> Option<
    owlSpec_secret_nsl_result,
> {
    let spec_comb = spec_combinator_owlSpec_secret_nsl_result();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__nrA, owlSpec__nrB)) = parsed;
        Some(owlSpec_secret_nsl_result { owlSpec__nrA, owlSpec__nrB })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_nsl_result_inner(
    x: owlSpec_secret_nsl_result,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__nrA.len(), x.owlSpec__nrB.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_nsl_result();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__nrA, x.owlSpec__nrB))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_nsl_result(x: owlSpec_secret_nsl_result) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_secret_nsl_result_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_nsl_result {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_nsl_result(self)
    }
}

pub open spec fn secret_nsl_result(
    arg_owlSpec__nrA: Seq<u8>,
    arg_owlSpec__nrB: Seq<u8>,
) -> owlSpec_secret_nsl_result {
    owlSpec_secret_nsl_result { owlSpec__nrA: arg_owlSpec__nrA, owlSpec__nrB: arg_owlSpec__nrB }
}

pub enum owlSpec_nsl_result_maybe {
    owlSpec_NRNone(),
    owlSpec_NRSome(owlSpec_nsl_result),
}

use owlSpec_nsl_result_maybe::*;

#[verifier::external_body]
pub closed spec fn parse_owlSpec_nsl_result_maybe(x: Seq<u8>) -> Option<owlSpec_nsl_result_maybe> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_nsl_result_maybe_inner(x: owlSpec_nsl_result_maybe) -> Option<
    Seq<u8>,
> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_nsl_result_maybe(x: owlSpec_nsl_result_maybe) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_nsl_result_maybe {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_nsl_result_maybe(self)
    }
}

pub open spec fn NRNone() -> owlSpec_nsl_result_maybe {
    crate::owlSpec_nsl_result_maybe::owlSpec_NRNone()
}

pub open spec fn NRSome(x: owlSpec_nsl_result) -> owlSpec_nsl_result_maybe {
    crate::owlSpec_nsl_result_maybe::owlSpec_NRSome(x)
}

pub open spec fn NRNone_enumtest(x: owlSpec_nsl_result_maybe) -> bool {
    match x {
        owlSpec_nsl_result_maybe::owlSpec_NRNone() => true,
        _ => false,
    }
}

pub open spec fn NRSome_enumtest(x: owlSpec_nsl_result_maybe) -> bool {
    match x {
        owlSpec_nsl_result_maybe::owlSpec_NRSome(_) => true,
        _ => false,
    }
}

#[verifier::opaque]
pub open spec fn alice_main_spec(cfg: cfg_alice, mut_state: state_alice) -> (res: ITree<
    (owlSpec_nsl_result_maybe, state_alice),
    Endpoint,
>) {
    owl_spec!(mut_state, state_alice,
        let pkB = ((ret(cfg.pk_owl_skB.view()))) in
let c = ((ret(pkenc(pkB, serialize_owlSpec_nsl_alice_message(Msg1(cfg.owl_nA.view())))))) in
(output (c) to (Some(Endpoint::Loc_bob))) in
(input(i,_14)) in
let caseval = ((declassify(DeclassifyingOp::PkDec(cfg.owl_skA.view(), i))) in
(ret(pkdec(cfg.owl_skA.view(), i)))) in
(case (caseval) {
| None => {
(ret(NRNone()))
},
| Some(x) => {
(parse (parse_owlSpec_nsl_bob_message(x)) as (owlSpec_nsl_bob_message{owlSpec__nb_cipher : c_orig, owlSpec__nbA : nA_, owlSpec__nbB : nB_}) in {
let eq_bool25 = ((declassify(DeclassifyingOp::EqCheck(cfg.owl_nA.view(), nA_))) in
(ret(cfg.owl_nA.view() == nA_))) in
(if (eq_bool25) then
(let c_ = ((ret(pkenc(pkB, serialize_owlSpec_nsl_alice_message(Msg3(nsl_alice_msg3(cfg.owl_nA.view(), nB_))))))) in
(output (c_) to (Some(Endpoint::Loc_bob))) in
let res = ((ret(NRSome(nsl_result(cfg.owl_nA.view(), nB_))))) in
(ret(res)))
else
(let _assert_58 = ((ret(ghost_unit()))) in
(ret(NRNone()))))
} otherwise ((ret(NRNone()))))
},
}
)
    )
}

#[verifier::opaque]
pub open spec fn bob_main_spec(cfg: cfg_bob, mut_state: state_bob) -> (res: ITree<
    (owlSpec_nsl_result_maybe, state_bob),
    Endpoint,
>) {
    owl_spec!(mut_state, state_bob,
        let pkA = ((ret(cfg.pk_owl_skA.view()))) in
(input(i,_33)) in
let caseval = ((declassify(DeclassifyingOp::PkDec(cfg.owl_skB.view(), i))) in
(ret(pkdec(cfg.owl_skB.view(), i)))) in
(case (caseval) {
| None => {
(ret(NRNone()))
},
| Some(payload) => {
(declassify(DeclassifyingOp::EnumParse(payload))) in
(parse (parse_owlSpec_nsl_alice_message(payload)) as (parsed_caseval : owlSpec_nsl_alice_message) in {
(case (parsed_caseval) {
| owlSpec_Msg1(nA_) => {
(if (length(nA_) == NONCE_SIZE) then
(let p = ((ret(nsl_bob_message(ghost_unit(), nA_, cfg.owl_nB.view())))) in
let c = ((ret(pkenc(pkA, serialize_owlSpec_nsl_bob_message(p))))) in
(output (c) to (Some(Endpoint::Loc_alice))) in
(input(i_,_44)) in
let caseval = ((declassify(DeclassifyingOp::PkDec(cfg.owl_skB.view(), i_))) in
(ret(pkdec(cfg.owl_skB.view(), i_)))) in
(case (caseval) {
| None => {
(ret(NRNone()))
},
| Some(payload2) => {
(declassify(DeclassifyingOp::EnumParse(payload2))) in
(parse (parse_owlSpec_nsl_alice_message(payload2)) as (parsed_caseval : owlSpec_nsl_alice_message) in {
(case (parsed_caseval) {
| owlSpec_Msg1(_unused82) => {
(ret(NRNone()))
},
| owlSpec_Msg3(p) => {
(parse (p) as (owlSpec_nsl_alice_msg3{owlSpec__na3A : nA3A, owlSpec__na3B : nA3B}) in {
let eq_bool57 = ((declassify(DeclassifyingOp::EqCheck(cfg.owl_nB.view(), nA3B))) in
(ret(cfg.owl_nB.view() == nA3B))) in
let b1 = ((ret(eq_bool57))) in
let eq_bool61 = ((declassify(DeclassifyingOp::EqCheck(nA_, nA3A))) in
(ret(nA_ == nA3A))) in
let b2 = ((ret(eq_bool61))) in
(if (andb(b1, b2)) then
(let res = ((ret(NRSome(nsl_result(nA_, cfg.owl_nB.view()))))) in
(ret(res)))
else
((ret(NRNone()))))
} )
},
}
)
} otherwise (ret(NRNone())))
},
}
))
else
((ret(NRNone()))))
},
| owlSpec_Msg3(_unused83) => {
(ret(NRNone()))
},
}
)
} otherwise (ret(NRNone())))
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

pub struct owl_nsl_alice_msg3<'a> {
    pub owl__na3A: SecretBuf<'a>,
    pub owl__na3B: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_nsl_alice_msg3<'a>(arg_owl__na3A: SecretBuf<'a>, arg_owl__na3B: SecretBuf<'a>) -> (res:
    owl_nsl_alice_msg3<'a>)
    ensures
        res.owl__na3A.view() == arg_owl__na3A.view(),
        res.owl__na3B.view() == arg_owl__na3B.view(),
{
    owl_nsl_alice_msg3 { owl__na3A: arg_owl__na3A, owl__na3B: arg_owl__na3B }
}

impl<'a> owl_nsl_alice_msg3<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_nsl_alice_msg3<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_nsl_alice_msg3 {
            owl__na3A: SecretBuf::another_ref(&self.owl__na3A),
            owl__na3B: SecretBuf::another_ref(&self.owl__na3B),
        }
    }
}

impl View for owl_nsl_alice_msg3<'_> {
    type V = owlSpec_nsl_alice_msg3;

    open spec fn view(&self) -> owlSpec_nsl_alice_msg3 {
        owlSpec_nsl_alice_msg3 {
            owlSpec__na3A: self.owl__na3A.view(),
            owlSpec__na3B: self.owl__na3B.view(),
        }
    }
}

pub exec fn parse_owl_nsl_alice_msg3<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_nsl_alice_msg3<'a>>)
    ensures
        res is Some ==> parse_owlSpec_nsl_alice_msg3(arg.view()) is Some,
        res is None ==> parse_owlSpec_nsl_alice_msg3(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nsl_alice_msg3(arg.view())->Some_0,
{
    reveal(parse_owlSpec_nsl_alice_msg3);
    let exec_comb = exec_combinator_owl_nsl_alice_msg3();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__na3A, owl__na3B) = parsed;
        Some(
            owl_nsl_alice_msg3 {
                owl__na3A: SecretBuf::from_buf(owl__na3A.another_ref()),
                owl__na3B: SecretBuf::from_buf(owl__na3B.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_nsl_alice_msg3<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_nsl_alice_msg3<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_nsl_alice_msg3(arg.view()) is Some,
        res is None ==> parse_owlSpec_nsl_alice_msg3(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nsl_alice_msg3(arg.view())->Some_0,
{
    reveal(parse_owlSpec_nsl_alice_msg3);
    let exec_comb = exec_combinator_owl_nsl_alice_msg3();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (owl__na3A, owl__na3B) = parsed;
        Some(
            owl_nsl_alice_msg3 {
                owl__na3A: SecretBuf::another_ref(&owl__na3A),
                owl__na3B: SecretBuf::another_ref(&owl__na3B),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_nsl_alice_msg3_inner<'a>(arg: &owl_nsl_alice_msg3<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_nsl_alice_msg3_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_nsl_alice_msg3_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_nsl_alice_msg3_inner);
    if no_usize_overflows![ arg.owl__na3A.len(), arg.owl__na3B.len(), 0 ] {
        let exec_comb = exec_combinator_owl_nsl_alice_msg3();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__na3A.len() + arg.owl__na3B.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__na3A), SecretBuf::another_ref(&arg.owl__na3B)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_nsl_alice_msg3_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_nsl_alice_msg3<'a>(arg: &owl_nsl_alice_msg3<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_nsl_alice_msg3(arg.view()),
{
    reveal(serialize_owlSpec_nsl_alice_msg3);
    let res = serialize_owl_nsl_alice_msg3_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_nsl_alice_msg3<'a> {
    pub owl__na3A: SecretBuf<'a>,
    pub owl__na3B: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_nsl_alice_msg3<'a>(
    arg_owl__na3A: SecretBuf<'a>,
    arg_owl__na3B: SecretBuf<'a>,
) -> (res: owl_secret_nsl_alice_msg3<'a>)
    ensures
        res.owl__na3A.view() == arg_owl__na3A.view(),
        res.owl__na3B.view() == arg_owl__na3B.view(),
{
    owl_secret_nsl_alice_msg3 { owl__na3A: arg_owl__na3A, owl__na3B: arg_owl__na3B }
}

impl<'a> owl_secret_nsl_alice_msg3<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_nsl_alice_msg3<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_nsl_alice_msg3 {
            owl__na3A: SecretBuf::another_ref(&self.owl__na3A),
            owl__na3B: SecretBuf::another_ref(&self.owl__na3B),
        }
    }
}

impl View for owl_secret_nsl_alice_msg3<'_> {
    type V = owlSpec_secret_nsl_alice_msg3;

    open spec fn view(&self) -> owlSpec_secret_nsl_alice_msg3 {
        owlSpec_secret_nsl_alice_msg3 {
            owlSpec__na3A: self.owl__na3A.view(),
            owlSpec__na3B: self.owl__na3B.view(),
        }
    }
}

pub exec fn parse_owl_secret_nsl_alice_msg3<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_secret_nsl_alice_msg3<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_nsl_alice_msg3(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_nsl_alice_msg3(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_nsl_alice_msg3(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_nsl_alice_msg3);
    let exec_comb = exec_combinator_owl_secret_nsl_alice_msg3();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__na3A, owl__na3B) = parsed;
        Some(
            owl_secret_nsl_alice_msg3 {
                owl__na3A: SecretBuf::from_buf(owl__na3A.another_ref()),
                owl__na3B: SecretBuf::from_buf(owl__na3B.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_nsl_alice_msg3<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_nsl_alice_msg3<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_nsl_alice_msg3(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_nsl_alice_msg3(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_nsl_alice_msg3(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_nsl_alice_msg3);
    let exec_comb = exec_combinator_owl_secret_nsl_alice_msg3();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (owl__na3A, owl__na3B) = parsed;
        Some(
            owl_secret_nsl_alice_msg3 {
                owl__na3A: SecretBuf::another_ref(&owl__na3A),
                owl__na3B: SecretBuf::another_ref(&owl__na3B),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_nsl_alice_msg3_inner<'a>(
    arg: &owl_secret_nsl_alice_msg3<'a>,
) -> (res: Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_secret_nsl_alice_msg3_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_nsl_alice_msg3_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_secret_nsl_alice_msg3_inner);
    if no_usize_overflows![ arg.owl__na3A.len(), arg.owl__na3B.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_nsl_alice_msg3();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__na3A.len() + arg.owl__na3B.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__na3A), SecretBuf::another_ref(&arg.owl__na3B)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_nsl_alice_msg3_inner(
                arg.view(),
            )->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_nsl_alice_msg3<'a>(arg: &owl_secret_nsl_alice_msg3<'a>) -> (res:
    SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_nsl_alice_msg3(arg.view()),
{
    reveal(serialize_owlSpec_secret_nsl_alice_msg3);
    let res = serialize_owl_secret_nsl_alice_msg3_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_nsl_alice_message<'a> {
    owl_Msg1(SecretBuf<'a>),
    owl_Msg3(owl_nsl_alice_msg3<'a>),
}

use owl_nsl_alice_message::*;

impl<'a> owl_nsl_alice_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_nsl_alice_message<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_Msg1(x) => owl_Msg1(SecretBuf::another_ref(x)),
            owl_Msg3(x) => owl_Msg3(owl_nsl_alice_msg3::another_ref(x)),
        }
    }
}

impl View for owl_nsl_alice_message<'_> {
    type V = owlSpec_nsl_alice_message;

    open spec fn view(&self) -> owlSpec_nsl_alice_message {
        match self {
            owl_Msg1(v) => owlSpec_nsl_alice_message::owlSpec_Msg1(v.view()),
            owl_Msg3(v) => owlSpec_nsl_alice_message::owlSpec_Msg3(v.view()),
        }
    }
}

#[inline]
pub fn owl_Msg1_enumtest(x: &owl_nsl_alice_message<'_>) -> (res: bool)
    ensures
        res == Msg1_enumtest(x.view()),
{
    match x {
        owl_nsl_alice_message::owl_Msg1(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl_Msg3_enumtest(x: &owl_nsl_alice_message<'_>) -> (res: bool)
    ensures
        res == Msg3_enumtest(x.view()),
{
    match x {
        owl_nsl_alice_message::owl_Msg3(_) => true,
        _ => false,
    }
}

#[verifier::external_body]
pub exec fn parse_owl_nsl_alice_message<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_nsl_alice_message<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_nsl_alice_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_nsl_alice_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nsl_alice_message(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_nsl_alice_message<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_nsl_alice_message<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_nsl_alice_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_nsl_alice_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nsl_alice_message(arg.view())->Some_0,
{
    reveal(parse_owlSpec_nsl_alice_message);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_nsl_alice_message_inner(arg: &owl_nsl_alice_message) -> (res: Option<
    Vec<u8>,
>)
    ensures
        res is Some ==> serialize_owlSpec_nsl_alice_message_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_nsl_alice_message_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_nsl_alice_message_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_nsl_alice_message(arg: &owl_nsl_alice_message) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_nsl_alice_message(arg.view()),
{
    unimplemented!()
}

pub struct owl_nsl_bob_message<'a> {
    pub owl__nb_cipher: Ghost<()>,
    pub owl__nbA: SecretBuf<'a>,
    pub owl__nbB: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_nsl_bob_message<'a>(
    arg_owl__nb_cipher: Ghost<()>,
    arg_owl__nbA: SecretBuf<'a>,
    arg_owl__nbB: SecretBuf<'a>,
) -> (res: owl_nsl_bob_message<'a>)
    ensures
        res.owl__nb_cipher.view() == arg_owl__nb_cipher.view(),
        res.owl__nbA.view() == arg_owl__nbA.view(),
        res.owl__nbB.view() == arg_owl__nbB.view(),
{
    owl_nsl_bob_message {
        owl__nb_cipher: arg_owl__nb_cipher,
        owl__nbA: arg_owl__nbA,
        owl__nbB: arg_owl__nbB,
    }
}

impl<'a> owl_nsl_bob_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_nsl_bob_message<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_nsl_bob_message {
            owl__nb_cipher: self.owl__nb_cipher,
            owl__nbA: SecretBuf::another_ref(&self.owl__nbA),
            owl__nbB: SecretBuf::another_ref(&self.owl__nbB),
        }
    }
}

impl View for owl_nsl_bob_message<'_> {
    type V = owlSpec_nsl_bob_message;

    open spec fn view(&self) -> owlSpec_nsl_bob_message {
        owlSpec_nsl_bob_message {
            owlSpec__nb_cipher: ghost_unit(),
            owlSpec__nbA: self.owl__nbA.view(),
            owlSpec__nbB: self.owl__nbB.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_nsl_bob_message<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_nsl_bob_message<'a>>)
    ensures
        res is Some ==> parse_owlSpec_nsl_bob_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_nsl_bob_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nsl_bob_message(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn secret_parse_owl_nsl_bob_message<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_nsl_bob_message<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_nsl_bob_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_nsl_bob_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nsl_bob_message(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_nsl_bob_message_inner<'a>(arg: &owl_nsl_bob_message) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_nsl_bob_message_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_nsl_bob_message_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_nsl_bob_message<'a>(arg: &owl_nsl_bob_message) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_nsl_bob_message(arg.view()),
{
    unimplemented!()
}

pub struct owl_secret_nsl_bob_message<'a> {
    pub owl__nb_cipher: Ghost<()>,
    pub owl__nbA: SecretBuf<'a>,
    pub owl__nbB: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_nsl_bob_message<'a>(
    arg_owl__nb_cipher: Ghost<()>,
    arg_owl__nbA: SecretBuf<'a>,
    arg_owl__nbB: SecretBuf<'a>,
) -> (res: owl_secret_nsl_bob_message<'a>)
    ensures
        res.owl__nb_cipher.view() == arg_owl__nb_cipher.view(),
        res.owl__nbA.view() == arg_owl__nbA.view(),
        res.owl__nbB.view() == arg_owl__nbB.view(),
{
    owl_secret_nsl_bob_message {
        owl__nb_cipher: arg_owl__nb_cipher,
        owl__nbA: arg_owl__nbA,
        owl__nbB: arg_owl__nbB,
    }
}

impl<'a> owl_secret_nsl_bob_message<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_nsl_bob_message<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_nsl_bob_message {
            owl__nb_cipher: self.owl__nb_cipher,
            owl__nbA: SecretBuf::another_ref(&self.owl__nbA),
            owl__nbB: SecretBuf::another_ref(&self.owl__nbB),
        }
    }
}

impl View for owl_secret_nsl_bob_message<'_> {
    type V = owlSpec_secret_nsl_bob_message;

    open spec fn view(&self) -> owlSpec_secret_nsl_bob_message {
        owlSpec_secret_nsl_bob_message {
            owlSpec__nb_cipher: ghost_unit(),
            owlSpec__nbA: self.owl__nbA.view(),
            owlSpec__nbB: self.owl__nbB.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_secret_nsl_bob_message<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_secret_nsl_bob_message<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_nsl_bob_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_nsl_bob_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_nsl_bob_message(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn secret_parse_owl_secret_nsl_bob_message<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_nsl_bob_message<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_nsl_bob_message(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_nsl_bob_message(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_nsl_bob_message(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_secret_nsl_bob_message_inner<'a>(
    arg: &owl_secret_nsl_bob_message,
) -> (res: Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_secret_nsl_bob_message_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_nsl_bob_message_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_secret_nsl_bob_message<'a>(arg: &owl_secret_nsl_bob_message) -> (res:
    SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_nsl_bob_message(arg.view()),
{
    unimplemented!()
}

pub struct owl_nsl_result<'a> {
    pub owl__nrA: SecretBuf<'a>,
    pub owl__nrB: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_nsl_result<'a>(arg_owl__nrA: SecretBuf<'a>, arg_owl__nrB: SecretBuf<'a>) -> (res:
    owl_nsl_result<'a>)
    ensures
        res.owl__nrA.view() == arg_owl__nrA.view(),
        res.owl__nrB.view() == arg_owl__nrB.view(),
{
    owl_nsl_result { owl__nrA: arg_owl__nrA, owl__nrB: arg_owl__nrB }
}

impl<'a> owl_nsl_result<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_nsl_result<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_nsl_result {
            owl__nrA: SecretBuf::another_ref(&self.owl__nrA),
            owl__nrB: SecretBuf::another_ref(&self.owl__nrB),
        }
    }
}

impl View for owl_nsl_result<'_> {
    type V = owlSpec_nsl_result;

    open spec fn view(&self) -> owlSpec_nsl_result {
        owlSpec_nsl_result {
            owlSpec__nrA: self.owl__nrA.view(),
            owlSpec__nrB: self.owl__nrB.view(),
        }
    }
}

pub exec fn parse_owl_nsl_result<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_nsl_result<'a>>)
    ensures
        res is Some ==> parse_owlSpec_nsl_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_nsl_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nsl_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_nsl_result);
    let exec_comb = exec_combinator_owl_nsl_result();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__nrA, owl__nrB) = parsed;
        Some(
            owl_nsl_result {
                owl__nrA: SecretBuf::from_buf(owl__nrA.another_ref()),
                owl__nrB: SecretBuf::from_buf(owl__nrB.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_nsl_result<'a>(arg: SecretBuf<'a>) -> (res: Option<owl_nsl_result<'a>>)
    ensures
        res is Some ==> parse_owlSpec_nsl_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_nsl_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nsl_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_nsl_result);
    let exec_comb = exec_combinator_owl_nsl_result();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (owl__nrA, owl__nrB) = parsed;
        Some(
            owl_nsl_result {
                owl__nrA: SecretBuf::another_ref(&owl__nrA),
                owl__nrB: SecretBuf::another_ref(&owl__nrB),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_nsl_result_inner<'a>(arg: &owl_nsl_result<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_nsl_result_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_nsl_result_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_nsl_result_inner);
    if no_usize_overflows![ arg.owl__nrA.len(), arg.owl__nrB.len(), 0 ] {
        let exec_comb = exec_combinator_owl_nsl_result();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__nrA.len() + arg.owl__nrB.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__nrA), SecretBuf::another_ref(&arg.owl__nrB)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_nsl_result_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_nsl_result<'a>(arg: &owl_nsl_result<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_nsl_result(arg.view()),
{
    reveal(serialize_owlSpec_nsl_result);
    let res = serialize_owl_nsl_result_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_nsl_result<'a> {
    pub owl__nrA: SecretBuf<'a>,
    pub owl__nrB: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_nsl_result<'a>(arg_owl__nrA: SecretBuf<'a>, arg_owl__nrB: SecretBuf<'a>) -> (res:
    owl_secret_nsl_result<'a>)
    ensures
        res.owl__nrA.view() == arg_owl__nrA.view(),
        res.owl__nrB.view() == arg_owl__nrB.view(),
{
    owl_secret_nsl_result { owl__nrA: arg_owl__nrA, owl__nrB: arg_owl__nrB }
}

impl<'a> owl_secret_nsl_result<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_nsl_result<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_nsl_result {
            owl__nrA: SecretBuf::another_ref(&self.owl__nrA),
            owl__nrB: SecretBuf::another_ref(&self.owl__nrB),
        }
    }
}

impl View for owl_secret_nsl_result<'_> {
    type V = owlSpec_secret_nsl_result;

    open spec fn view(&self) -> owlSpec_secret_nsl_result {
        owlSpec_secret_nsl_result {
            owlSpec__nrA: self.owl__nrA.view(),
            owlSpec__nrB: self.owl__nrB.view(),
        }
    }
}

pub exec fn parse_owl_secret_nsl_result<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_secret_nsl_result<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_nsl_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_nsl_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_nsl_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_nsl_result);
    let exec_comb = exec_combinator_owl_secret_nsl_result();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__nrA, owl__nrB) = parsed;
        Some(
            owl_secret_nsl_result {
                owl__nrA: SecretBuf::from_buf(owl__nrA.another_ref()),
                owl__nrB: SecretBuf::from_buf(owl__nrB.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_nsl_result<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_nsl_result<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_nsl_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_nsl_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_nsl_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_secret_nsl_result);
    let exec_comb = exec_combinator_owl_secret_nsl_result();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (owl__nrA, owl__nrB) = parsed;
        Some(
            owl_secret_nsl_result {
                owl__nrA: SecretBuf::another_ref(&owl__nrA),
                owl__nrB: SecretBuf::another_ref(&owl__nrB),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_nsl_result_inner<'a>(arg: &owl_secret_nsl_result<'a>) -> (res:
    Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_secret_nsl_result_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_nsl_result_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_secret_nsl_result_inner);
    if no_usize_overflows![ arg.owl__nrA.len(), arg.owl__nrB.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_nsl_result();
        let mut obuf = SecretOutputBuf::new_obuf(arg.owl__nrA.len() + arg.owl__nrB.len() + 0);
        let ser_result = exec_comb.serialize(
            (SecretBuf::another_ref(&arg.owl__nrA), SecretBuf::another_ref(&arg.owl__nrB)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_nsl_result_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_secret_nsl_result<'a>(arg: &owl_secret_nsl_result<'a>) -> (res: SecretBuf<
    'a,
>)
    ensures
        res.view() == serialize_owlSpec_secret_nsl_result(arg.view()),
{
    reveal(serialize_owlSpec_secret_nsl_result);
    let res = serialize_owl_secret_nsl_result_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_nsl_result_maybe<'a> {
    owl_NRNone(),
    owl_NRSome(owl_nsl_result<'a>),
}

use owl_nsl_result_maybe::*;

impl<'a> owl_nsl_result_maybe<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_nsl_result_maybe<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_NRNone() => owl_NRNone(),
            owl_NRSome(x) => owl_NRSome(owl_nsl_result::another_ref(x)),
        }
    }
}

impl View for owl_nsl_result_maybe<'_> {
    type V = owlSpec_nsl_result_maybe;

    open spec fn view(&self) -> owlSpec_nsl_result_maybe {
        match self {
            owl_NRNone() => owlSpec_nsl_result_maybe::owlSpec_NRNone(),
            owl_NRSome(v) => owlSpec_nsl_result_maybe::owlSpec_NRSome(v.view()),
        }
    }
}

#[inline]
pub fn owl_NRNone_enumtest(x: &owl_nsl_result_maybe<'_>) -> (res: bool)
    ensures
        res == NRNone_enumtest(x.view()),
{
    match x {
        owl_nsl_result_maybe::owl_NRNone() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_NRSome_enumtest(x: &owl_nsl_result_maybe<'_>) -> (res: bool)
    ensures
        res == NRSome_enumtest(x.view()),
{
    match x {
        owl_nsl_result_maybe::owl_NRSome(_) => true,
        _ => false,
    }
}

#[verifier::external_body]
pub exec fn parse_owl_nsl_result_maybe<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_nsl_result_maybe<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_nsl_result_maybe(arg.view()) is Some,
        res is None ==> parse_owlSpec_nsl_result_maybe(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nsl_result_maybe(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_nsl_result_maybe<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_nsl_result_maybe<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_nsl_result_maybe(arg.view()) is Some,
        res is None ==> parse_owlSpec_nsl_result_maybe(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_nsl_result_maybe(arg.view())->Some_0,
{
    reveal(parse_owlSpec_nsl_result_maybe);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_nsl_result_maybe_inner(arg: &owl_nsl_result_maybe) -> (res: Option<
    Vec<u8>,
>)
    ensures
        res is Some ==> serialize_owlSpec_nsl_result_maybe_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_nsl_result_maybe_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_nsl_result_maybe_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_nsl_result_maybe(arg: &owl_nsl_result_maybe) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_nsl_result_maybe(arg.view()),
{
    unimplemented!()
}

pub struct state_alice {}

impl state_alice {
    #[verifier::external_body]
    pub fn init_state_alice() -> Self {
        state_alice {  }
    }
}

pub struct cfg_alice<'alice> {
    pub owl_nA: SecretBuf<'alice>,
    pub owl_skA: SecretBuf<'alice>,
    pub pk_owl_skA: OwlBuf<'alice>,
    pub pk_owl_skB: OwlBuf<'alice>,
}

impl cfg_alice<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_alice_main<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_nsl_result_maybe, state_alice), Endpoint>>,
        mut_state: &mut state_alice,
    ) -> (res: Result<
        (
            owl_nsl_result_maybe<'a>,
            Tracked<ITreeToken<(owlSpec_nsl_result_maybe, state_alice), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == alice_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_nsl_result_maybe<'a>,
            Tracked<ITreeToken<(owlSpec_nsl_result_maybe, state_alice), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(alice_main_spec);
            let tmp_owl_pkB84 = { OwlBuf::another_ref(&self.pk_owl_skB) };
            let owl_pkB84 = OwlBuf::another_ref(&tmp_owl_pkB84);
            let tmp_owl_c85 = {
                owl_pkenc(
                    OwlBuf::another_ref(&owl_pkB84),
                    SecretBuf::another_ref(
                        &OwlBuf::from_vec(
                            serialize_owl_nsl_alice_message(
                                &owl_Msg1(
                                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_nA)),
                                ),
                            ),
                        ).into_secret(),
                    ),
                )
            };
            let owl_c85 = OwlBuf::from_vec(tmp_owl_c85);
            let owl__86 = {
                effects.owl_output::<(owlSpec_nsl_result_maybe, state_alice)>(
                    Tracked(&mut itree),
                    owl_c85.as_slice(),
                    Some(&bob_addr()),
                    &alice_addr(),
                );
            };
            let (tmp_owl_i88, owl__87) = {
                effects.owl_input::<(owlSpec_nsl_result_maybe, state_alice)>(Tracked(&mut itree))
            };
            let owl_i88 = OwlBuf::from_vec(tmp_owl_i88);
            let tmp_owl_caseval89 = {
                let tracked owl_declassify_tok90 = consume_itree_declassify::<
                    (owlSpec_nsl_result_maybe, state_alice),
                    Endpoint,
                >(&mut itree);
                owl_pkdec(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skA)),
                    OwlBuf::another_ref(&owl_i88),
                    Tracked(owl_declassify_tok90),
                )
            };
            let owl_caseval89 = SecretBuf::another_ref_option(&tmp_owl_caseval89);
            match SecretBuf::another_ref_option(&owl_caseval89) {
                Option::None => { (owl_nsl_result_maybe::another_ref(&owl_NRNone()), Tracked(itree))
                },
                Option::Some(tmp_owl_x91) => {
                    let owl_x91 = SecretBuf::another_ref(&tmp_owl_x91);
                    let parseval_tmp = SecretBuf::another_ref(&owl_x91);
                    if let Some(parseval) = secret_parse_owl_nsl_bob_message(
                        SecretBuf::another_ref(&parseval_tmp),
                    ) {
                        let owl_c_orig94 = parseval.owl__nb_cipher;
                        let owl_nA_93 = SecretBuf::another_ref(&parseval.owl__nbA);
                        let owl_nB_92 = SecretBuf::another_ref(&parseval.owl__nbB);
                        let owl_eq_bool2595 = {
                            let tracked owl_declassify_tok96 = consume_itree_declassify::<
                                (owlSpec_nsl_result_maybe, state_alice),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::secret_eq(
                                    &SecretBuf::another_ref(&self.owl_nA),
                                    &owl_nA_93,
                                    Tracked(owl_declassify_tok96),
                                )
                            }
                        };

                        if owl_eq_bool2595 {
                            let tmp_owl_c_97 = {
                                owl_pkenc(
                                    OwlBuf::another_ref(&owl_pkB84),
                                    SecretBuf::another_ref(
                                        &OwlBuf::from_vec(
                                            serialize_owl_nsl_alice_message(
                                                &owl_Msg3(
                                                    owl_nsl_alice_msg3::another_ref(
                                                        &owl_nsl_alice_msg3(
                                                            SecretBuf::another_ref(
                                                                &SecretBuf::another_ref(
                                                                    &self.owl_nA,
                                                                ),
                                                            ),
                                                            SecretBuf::another_ref(&owl_nB_92),
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ).into_secret(),
                                    ),
                                )
                            };
                            let owl_c_97 = OwlBuf::from_vec(tmp_owl_c_97);
                            let owl__98 = {
                                effects.owl_output::<(owlSpec_nsl_result_maybe, state_alice)>(
                                    Tracked(&mut itree),
                                    owl_c_97.as_slice(),
                                    Some(&bob_addr()),
                                    &alice_addr(),
                                );
                            };
                            let tmp_owl_res99 = {
                                owl_NRSome(
                                    owl_nsl_result::another_ref(
                                        &owl_nsl_result(
                                            SecretBuf::another_ref(
                                                &SecretBuf::another_ref(&self.owl_nA),
                                            ),
                                            SecretBuf::another_ref(&owl_nB_92),
                                        ),
                                    ),
                                )
                            };
                            let owl_res99 = owl_nsl_result_maybe::another_ref(&tmp_owl_res99);
                            (owl_nsl_result_maybe::another_ref(&owl_res99), Tracked(itree))
                        } else {
                            {
                                let owl__assert_58100 = { owl_ghost_unit() };
                                (owl_nsl_result_maybe::another_ref(&owl_NRNone()), Tracked(itree))
                            }
                        }

                    } else {
                        (owl_nsl_result_maybe::another_ref(&owl_NRNone()), Tracked(itree))
                    }
                },
            }
        };
        Ok((owl_nsl_result_maybe::another_ref(&res_inner), Tracked(itree)))
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
    pub owl_nB: SecretBuf<'bob>,
    pub owl_skB: SecretBuf<'bob>,
    pub pk_owl_skA: OwlBuf<'bob>,
    pub pk_owl_skB: OwlBuf<'bob>,
}

impl cfg_bob<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_bob_main<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_nsl_result_maybe, state_bob), Endpoint>>,
        mut_state: &mut state_bob,
    ) -> (res: Result<
        (
            owl_nsl_result_maybe<'a>,
            Tracked<ITreeToken<(owlSpec_nsl_result_maybe, state_bob), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == bob_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_nsl_result_maybe<'a>,
            Tracked<ITreeToken<(owlSpec_nsl_result_maybe, state_bob), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(bob_main_spec);
            let tmp_owl_pkA101 = { OwlBuf::another_ref(&self.pk_owl_skA) };
            let owl_pkA101 = OwlBuf::another_ref(&tmp_owl_pkA101);
            let (tmp_owl_i103, owl__102) = {
                effects.owl_input::<(owlSpec_nsl_result_maybe, state_bob)>(Tracked(&mut itree))
            };
            let owl_i103 = OwlBuf::from_vec(tmp_owl_i103);
            let tmp_owl_caseval104 = {
                let tracked owl_declassify_tok105 = consume_itree_declassify::<
                    (owlSpec_nsl_result_maybe, state_bob),
                    Endpoint,
                >(&mut itree);
                owl_pkdec(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skB)),
                    OwlBuf::another_ref(&owl_i103),
                    Tracked(owl_declassify_tok105),
                )
            };
            let owl_caseval104 = SecretBuf::another_ref_option(&tmp_owl_caseval104);
            match SecretBuf::another_ref_option(&owl_caseval104) {
                Option::None => { (owl_nsl_result_maybe::another_ref(&owl_NRNone()), Tracked(itree))
                },
                Option::Some(tmp_owl_payload106) => {
                    let owl_payload106 = SecretBuf::another_ref(&tmp_owl_payload106);
                    let tracked owl_declassify_tok107 = consume_itree_declassify::<
                        (owlSpec_nsl_result_maybe, state_bob),
                        Endpoint,
                    >(&mut itree);
                    let parseval_tmp = SecretBuf::another_ref(&owl_payload106);
                    if let Some(parseval) = secret_parse_owl_nsl_alice_message(
                        SecretBuf::another_ref(&parseval_tmp),
                        Tracked(owl_declassify_tok107),
                    ) {
                        let owl_parsed_caseval108 = owl_nsl_alice_message::another_ref(&parseval);
                        match owl_nsl_alice_message::another_ref(&owl_parsed_caseval108) {
                            owl_nsl_alice_message::owl_Msg1(tmp_owl_nA_109) => {
                                let owl_nA_109 = SecretBuf::another_ref(&tmp_owl_nA_109);

                                if owl_nA_109.len() == NONCE_SIZE {
                                    let tmp_owl_p110 = {
                                        owl_nsl_bob_message(
                                            owl_ghost_unit(),
                                            SecretBuf::another_ref(&owl_nA_109),
                                            SecretBuf::another_ref(
                                                &SecretBuf::another_ref(&self.owl_nB),
                                            ),
                                        )
                                    };
                                    let owl_p110 = owl_nsl_bob_message::another_ref(&tmp_owl_p110);
                                    let tmp_owl_c111 = {
                                        owl_pkenc(
                                            OwlBuf::another_ref(&owl_pkA101),
                                            SecretBuf::another_ref(
                                                &serialize_owl_nsl_bob_message(&owl_p110),
                                            ),
                                        )
                                    };
                                    let owl_c111 = OwlBuf::from_vec(tmp_owl_c111);
                                    let owl__112 = {
                                        effects.owl_output::<(owlSpec_nsl_result_maybe, state_bob)>(
                                            Tracked(&mut itree),
                                            owl_c111.as_slice(),
                                            Some(&alice_addr()),
                                            &bob_addr(),
                                        );
                                    };
                                    let (tmp_owl_i_114, owl__113) = {
                                        effects.owl_input::<(owlSpec_nsl_result_maybe, state_bob)>(
                                            Tracked(&mut itree),
                                        )
                                    };
                                    let owl_i_114 = OwlBuf::from_vec(tmp_owl_i_114);
                                    let tmp_owl_caseval115 = {
                                        let tracked owl_declassify_tok116 =
                                            consume_itree_declassify::<
                                            (owlSpec_nsl_result_maybe, state_bob),
                                            Endpoint,
                                        >(&mut itree);
                                        owl_pkdec(
                                            SecretBuf::another_ref(
                                                &SecretBuf::another_ref(&self.owl_skB),
                                            ),
                                            OwlBuf::another_ref(&owl_i_114),
                                            Tracked(owl_declassify_tok116),
                                        )
                                    };
                                    let owl_caseval115 = SecretBuf::another_ref_option(
                                        &tmp_owl_caseval115,
                                    );
                                    match SecretBuf::another_ref_option(&owl_caseval115) {
                                        Option::None => {
                                            (
                                                owl_nsl_result_maybe::another_ref(&owl_NRNone()),
                                                Tracked(itree),
                                            )
                                        },
                                        Option::Some(tmp_owl_payload2117) => {
                                            let owl_payload2117 = SecretBuf::another_ref(
                                                &tmp_owl_payload2117,
                                            );
                                            let tracked owl_declassify_tok118 =
                                                consume_itree_declassify::<
                                                (owlSpec_nsl_result_maybe, state_bob),
                                                Endpoint,
                                            >(&mut itree);
                                            let parseval_tmp = SecretBuf::another_ref(
                                                &owl_payload2117,
                                            );
                                            if let Some(parseval) =
                                                secret_parse_owl_nsl_alice_message(
                                                SecretBuf::another_ref(&parseval_tmp),
                                                Tracked(owl_declassify_tok118),
                                            ) {
                                                let owl_parsed_caseval119 =
                                                    owl_nsl_alice_message::another_ref(&parseval);
                                                match owl_nsl_alice_message::another_ref(
                                                    &owl_parsed_caseval119,
                                                ) {
                                                    owl_nsl_alice_message::owl_Msg1(
                                                        tmp_owl__120,
                                                    ) => {
                                                        let owl__120 = SecretBuf::another_ref(
                                                            &tmp_owl__120,
                                                        );
                                                        (
                                                            owl_nsl_result_maybe::another_ref(
                                                                &owl_NRNone(),
                                                            ),
                                                            Tracked(itree),
                                                        )
                                                    },
                                                    owl_nsl_alice_message::owl_Msg3(
                                                        tmp_owl_p121,
                                                    ) => {
                                                        let owl_p121 =
                                                            owl_nsl_alice_msg3::another_ref(
                                                            &tmp_owl_p121,
                                                        );
                                                        let parseval =
                                                            owl_nsl_alice_msg3::another_ref(
                                                            &owl_p121,
                                                        );
                                                        let owl_nA3A123 = SecretBuf::another_ref(
                                                            &parseval.owl__na3A,
                                                        );
                                                        let owl_nA3B122 = SecretBuf::another_ref(
                                                            &parseval.owl__na3B,
                                                        );
                                                        let owl_eq_bool57124 = {
                                                            let tracked owl_declassify_tok125 =
                                                                consume_itree_declassify::<
                                                                (
                                                                    owlSpec_nsl_result_maybe,
                                                                    state_bob,
                                                                ),
                                                                Endpoint,
                                                            >(&mut itree);
                                                            {
                                                                SecretBuf::secret_eq(
                                                                    &SecretBuf::another_ref(
                                                                        &self.owl_nB,
                                                                    ),
                                                                    &owl_nA3B122,
                                                                    Tracked(owl_declassify_tok125),
                                                                )
                                                            }
                                                        };
                                                        let owl_b1126 = { owl_eq_bool57124 };
                                                        let owl_eq_bool61127 = {
                                                            let tracked owl_declassify_tok128 =
                                                                consume_itree_declassify::<
                                                                (
                                                                    owlSpec_nsl_result_maybe,
                                                                    state_bob,
                                                                ),
                                                                Endpoint,
                                                            >(&mut itree);
                                                            {
                                                                SecretBuf::secret_eq(
                                                                    &owl_nA_109,
                                                                    &owl_nA3A123,
                                                                    Tracked(owl_declassify_tok128),
                                                                )
                                                            }
                                                        };
                                                        let owl_b2129 = { owl_eq_bool61127 };

                                                        if owl_b1126 && owl_b2129 {
                                                            let tmp_owl_res130 = {
                                                                owl_NRSome(
                                                                    owl_nsl_result::another_ref(
                                                                        &owl_nsl_result(
                                                                            SecretBuf::another_ref(
                                                                                &owl_nA_109,
                                                                            ),
                                                                            SecretBuf::another_ref(
                                                                                &SecretBuf::another_ref(
                                                                                &self.owl_nB),
                                                                            ),
                                                                        ),
                                                                    ),
                                                                )
                                                            };
                                                            let owl_res130 =
                                                                owl_nsl_result_maybe::another_ref(
                                                                &tmp_owl_res130,
                                                            );
                                                            (
                                                                owl_nsl_result_maybe::another_ref(
                                                                    &owl_res130,
                                                                ),
                                                                Tracked(itree),
                                                            )
                                                        } else {
                                                            (
                                                                owl_nsl_result_maybe::another_ref(
                                                                    &owl_NRNone(),
                                                                ),
                                                                Tracked(itree),
                                                            )
                                                        }

                                                    },
                                                }
                                            } else {
                                                (
                                                    owl_nsl_result_maybe::another_ref(
                                                        &owl_NRNone(),
                                                    ),
                                                    Tracked(itree),
                                                )
                                            }
                                        },
                                    }
                                } else {
                                    (
                                        owl_nsl_result_maybe::another_ref(&owl_NRNone()),
                                        Tracked(itree),
                                    )
                                }

                            },
                            owl_nsl_alice_message::owl_Msg3(tmp_owl__131) => {
                                let owl__131 = owl_nsl_alice_msg3::another_ref(&tmp_owl__131);
                                (owl_nsl_result_maybe::another_ref(&owl_NRNone()), Tracked(itree))
                            },
                        }
                    } else {
                        (owl_nsl_result_maybe::another_ref(&owl_NRNone()), Tracked(itree))
                    }
                },
            }
        };
        Ok((owl_nsl_result_maybe::another_ref(&res_inner), Tracked(itree)))
    }
}

} // verus!
