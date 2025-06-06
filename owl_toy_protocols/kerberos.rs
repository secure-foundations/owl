// Extracted verus code from file owl_toy_protocols/kerberos.owl:
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
pub enum owlSpec_AKEnum {
    owlSpec_ClientRequest(),
    owlSpec_TicketResponse(Seq<u8>),
}

use owlSpec_AKEnum::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_AKEnum(x: Seq<u8>) -> Option<owlSpec_AKEnum> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(32)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owlSpec_AKEnum::owlSpec_ClientRequest(),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_AKEnum::owlSpec_TicketResponse(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_AKEnum_inner(x: owlSpec_AKEnum) -> Option<Seq<u8>> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(32)));
    match x {
        owlSpec_AKEnum::owlSpec_ClientRequest() => {
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
        owlSpec_AKEnum::owlSpec_TicketResponse(x) => {
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
pub closed spec fn serialize_owlSpec_AKEnum(x: owlSpec_AKEnum) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_AKEnum_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_AKEnum {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_AKEnum(self)
    }
}

pub open spec fn ClientRequest() -> owlSpec_AKEnum {
    crate::owlSpec_AKEnum::owlSpec_ClientRequest()
}

pub open spec fn TicketResponse(x: Seq<u8>) -> owlSpec_AKEnum {
    crate::owlSpec_AKEnum::owlSpec_TicketResponse(x)
}

pub open spec fn ClientRequest_enumtest(x: owlSpec_AKEnum) -> bool {
    match x {
        owlSpec_AKEnum::owlSpec_ClientRequest() => true,
        _ => false,
    }
}

pub open spec fn TicketResponse_enumtest(x: owlSpec_AKEnum) -> bool {
    match x {
        owlSpec_AKEnum::owlSpec_TicketResponse(_) => true,
        _ => false,
    }
}

pub enum owlSpec_CertAuthMsgs {
    owlSpec_AuthCert(Seq<u8>),
    owlSpec_ClientCert(Seq<u8>),
}

use owlSpec_CertAuthMsgs::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_CertAuthMsgs(x: Seq<u8>) -> Option<owlSpec_CertAuthMsgs> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(1219)), (Tag::spec_new(U8, 2), Variable(1219)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owlSpec_CertAuthMsgs::owlSpec_AuthCert(x),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_CertAuthMsgs::owlSpec_ClientCert(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_CertAuthMsgs_inner(x: owlSpec_CertAuthMsgs) -> Option<
    Seq<u8>,
> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(1219)), (Tag::spec_new(U8, 2), Variable(1219)));
    match x {
        owlSpec_CertAuthMsgs::owlSpec_AuthCert(x) => {
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
        owlSpec_CertAuthMsgs::owlSpec_ClientCert(x) => {
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
pub closed spec fn serialize_owlSpec_CertAuthMsgs(x: owlSpec_CertAuthMsgs) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_CertAuthMsgs_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_CertAuthMsgs {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_CertAuthMsgs(self)
    }
}

pub open spec fn AuthCert(x: Seq<u8>) -> owlSpec_CertAuthMsgs {
    crate::owlSpec_CertAuthMsgs::owlSpec_AuthCert(x)
}

pub open spec fn ClientCert(x: Seq<u8>) -> owlSpec_CertAuthMsgs {
    crate::owlSpec_CertAuthMsgs::owlSpec_ClientCert(x)
}

pub open spec fn AuthCert_enumtest(x: owlSpec_CertAuthMsgs) -> bool {
    match x {
        owlSpec_CertAuthMsgs::owlSpec_AuthCert(_) => true,
        _ => false,
    }
}

pub open spec fn ClientCert_enumtest(x: owlSpec_CertAuthMsgs) -> bool {
    match x {
        owlSpec_CertAuthMsgs::owlSpec_ClientCert(_) => true,
        _ => false,
    }
}

spec fn spec_combinator_owlSpec_authserver_msg() -> (Variable, Variable) {
    let field_1 = Variable(48);
    let field_2 = Variable(48);
    (field_1, field_2)
}

exec fn exec_combinator_owl_authserver_msg() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_authserver_msg(),
{
    let field_1 = Variable(48);
    let field_2 = Variable(48);
    (field_1, field_2)
}

pub struct owlSpec_authserver_msg {
    pub owlSpec__authserver_msg_1: Seq<u8>,
    pub owlSpec__authserver_msg_2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_authserver_msg(x: Seq<u8>) -> Option<owlSpec_authserver_msg> {
    let spec_comb = spec_combinator_owlSpec_authserver_msg();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__authserver_msg_1, owlSpec__authserver_msg_2)) = parsed;
        Some(owlSpec_authserver_msg { owlSpec__authserver_msg_1, owlSpec__authserver_msg_2 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_authserver_msg_inner(x: owlSpec_authserver_msg) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__authserver_msg_1.len(), x.owlSpec__authserver_msg_2.len() ] {
        let spec_comb = spec_combinator_owlSpec_authserver_msg();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((x.owlSpec__authserver_msg_1, x.owlSpec__authserver_msg_2)),
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
pub closed spec fn serialize_owlSpec_authserver_msg(x: owlSpec_authserver_msg) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_authserver_msg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_authserver_msg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_authserver_msg(self)
    }
}

pub open spec fn authserver_msg(
    arg_owlSpec__authserver_msg_1: Seq<u8>,
    arg_owlSpec__authserver_msg_2: Seq<u8>,
) -> owlSpec_authserver_msg {
    owlSpec_authserver_msg {
        owlSpec__authserver_msg_1: arg_owlSpec__authserver_msg_1,
        owlSpec__authserver_msg_2: arg_owlSpec__authserver_msg_2,
    }
}

spec fn spec_combinator_owlSpec_client_to_ticketserver_msg() -> (Variable, Variable) {
    let field_1 = Variable(48);
    let field_2 = Variable(32);
    (field_1, field_2)
}

exec fn exec_combinator_owl_client_to_ticketserver_msg() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_client_to_ticketserver_msg(),
{
    let field_1 = Variable(48);
    let field_2 = Variable(32);
    (field_1, field_2)
}

pub struct owlSpec_client_to_ticketserver_msg {
    pub owlSpec__client_to_ticketserver_msg_1: Seq<u8>,
    pub owlSpec__client_to_ticketserver_msg_2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_client_to_ticketserver_msg(x: Seq<u8>) -> Option<
    owlSpec_client_to_ticketserver_msg,
> {
    let spec_comb = spec_combinator_owlSpec_client_to_ticketserver_msg();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__client_to_ticketserver_msg_1, owlSpec__client_to_ticketserver_msg_2)) =
            parsed;
        Some(
            owlSpec_client_to_ticketserver_msg {
                owlSpec__client_to_ticketserver_msg_1,
                owlSpec__client_to_ticketserver_msg_2,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_client_to_ticketserver_msg_inner(
    x: owlSpec_client_to_ticketserver_msg,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__client_to_ticketserver_msg_1.len(), x.owlSpec__client_to_ticketserver_msg_2.len() ] {
        let spec_comb = spec_combinator_owlSpec_client_to_ticketserver_msg();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((x.owlSpec__client_to_ticketserver_msg_1, x.owlSpec__client_to_ticketserver_msg_2)),
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
pub closed spec fn serialize_owlSpec_client_to_ticketserver_msg(
    x: owlSpec_client_to_ticketserver_msg,
) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_client_to_ticketserver_msg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_client_to_ticketserver_msg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_client_to_ticketserver_msg(self)
    }
}

pub open spec fn client_to_ticketserver_msg(
    arg_owlSpec__client_to_ticketserver_msg_1: Seq<u8>,
    arg_owlSpec__client_to_ticketserver_msg_2: Seq<u8>,
) -> owlSpec_client_to_ticketserver_msg {
    owlSpec_client_to_ticketserver_msg {
        owlSpec__client_to_ticketserver_msg_1: arg_owlSpec__client_to_ticketserver_msg_1,
        owlSpec__client_to_ticketserver_msg_2: arg_owlSpec__client_to_ticketserver_msg_2,
    }
}

spec fn spec_combinator_owlSpec_ticketserver_msg() -> (Variable, Variable) {
    let field_1 = Variable(48);
    let field_2 = Variable(64);
    (field_1, field_2)
}

exec fn exec_combinator_owl_ticketserver_msg() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_ticketserver_msg(),
{
    let field_1 = Variable(48);
    let field_2 = Variable(64);
    (field_1, field_2)
}

pub struct owlSpec_ticketserver_msg {
    pub owlSpec__ticketserver_msg_1: Seq<u8>,
    pub owlSpec__ticketserver_msg_2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_ticketserver_msg(x: Seq<u8>) -> Option<owlSpec_ticketserver_msg> {
    let spec_comb = spec_combinator_owlSpec_ticketserver_msg();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__ticketserver_msg_1, owlSpec__ticketserver_msg_2)) = parsed;
        Some(owlSpec_ticketserver_msg { owlSpec__ticketserver_msg_1, owlSpec__ticketserver_msg_2 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_ticketserver_msg_inner(x: owlSpec_ticketserver_msg) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__ticketserver_msg_1.len(), x.owlSpec__ticketserver_msg_2.len() ] {
        let spec_comb = spec_combinator_owlSpec_ticketserver_msg();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((x.owlSpec__ticketserver_msg_1, x.owlSpec__ticketserver_msg_2)),
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
pub closed spec fn serialize_owlSpec_ticketserver_msg(x: owlSpec_ticketserver_msg) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_ticketserver_msg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_ticketserver_msg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_ticketserver_msg(self)
    }
}

pub open spec fn ticketserver_msg(
    arg_owlSpec__ticketserver_msg_1: Seq<u8>,
    arg_owlSpec__ticketserver_msg_2: Seq<u8>,
) -> owlSpec_ticketserver_msg {
    owlSpec_ticketserver_msg {
        owlSpec__ticketserver_msg_1: arg_owlSpec__ticketserver_msg_1,
        owlSpec__ticketserver_msg_2: arg_owlSpec__ticketserver_msg_2,
    }
}

spec fn spec_combinator_owlSpec_client_to_service_msg() -> (Variable, Variable) {
    let field_1 = Variable(48);
    let field_2 = Variable(28);
    (field_1, field_2)
}

exec fn exec_combinator_owl_client_to_service_msg() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_client_to_service_msg(),
{
    let field_1 = Variable(48);
    let field_2 = Variable(28);
    (field_1, field_2)
}

pub struct owlSpec_client_to_service_msg {
    pub owlSpec__client_to_service_msg_1: Seq<u8>,
    pub owlSpec__client_to_service_msg_2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_client_to_service_msg(x: Seq<u8>) -> Option<
    owlSpec_client_to_service_msg,
> {
    let spec_comb = spec_combinator_owlSpec_client_to_service_msg();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__client_to_service_msg_1, owlSpec__client_to_service_msg_2)) = parsed;
        Some(
            owlSpec_client_to_service_msg {
                owlSpec__client_to_service_msg_1,
                owlSpec__client_to_service_msg_2,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_client_to_service_msg_inner(
    x: owlSpec_client_to_service_msg,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__client_to_service_msg_1.len(), x.owlSpec__client_to_service_msg_2.len() ] {
        let spec_comb = spec_combinator_owlSpec_client_to_service_msg();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((x.owlSpec__client_to_service_msg_1, x.owlSpec__client_to_service_msg_2)),
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
pub closed spec fn serialize_owlSpec_client_to_service_msg(x: owlSpec_client_to_service_msg) -> Seq<
    u8,
> {
    if let Some(val) = serialize_owlSpec_client_to_service_msg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_client_to_service_msg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_client_to_service_msg(self)
    }
}

pub open spec fn client_to_service_msg(
    arg_owlSpec__client_to_service_msg_1: Seq<u8>,
    arg_owlSpec__client_to_service_msg_2: Seq<u8>,
) -> owlSpec_client_to_service_msg {
    owlSpec_client_to_service_msg {
        owlSpec__client_to_service_msg_1: arg_owlSpec__client_to_service_msg_1,
        owlSpec__client_to_service_msg_2: arg_owlSpec__client_to_service_msg_2,
    }
}

spec fn spec_combinator_owlSpec_pkinit_client_to_authserver_msg() -> (
    ((Variable, Variable), Variable),
    Variable,
) {
    let field_1 = Variable(64);
    let field_2 = Variable(1219);
    let field_3 = Variable(64);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_pkinit_client_to_authserver_msg() -> (res: (
    ((Variable, Variable), Variable),
    Variable,
))
    ensures
        res.view() == spec_combinator_owlSpec_pkinit_client_to_authserver_msg(),
{
    let field_1 = Variable(64);
    let field_2 = Variable(1219);
    let field_3 = Variable(64);
    let field_4 = Variable(12);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_pkinit_client_to_authserver_msg {
    pub owlSpec__pkinit_client_to_authserver_msg_1: Seq<u8>,
    pub owlSpec__pkinit_client_to_authserver_msg_2: Seq<u8>,
    pub owlSpec__pkinit_client_to_authserver_msg_3: Seq<u8>,
    pub owlSpec__pkinit_client_to_authserver_msg_4: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_pkinit_client_to_authserver_msg(x: Seq<u8>) -> Option<
    owlSpec_pkinit_client_to_authserver_msg,
> {
    let spec_comb = spec_combinator_owlSpec_pkinit_client_to_authserver_msg();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((
            (
                (
                    owlSpec__pkinit_client_to_authserver_msg_1,
                    owlSpec__pkinit_client_to_authserver_msg_2,
                ),
                owlSpec__pkinit_client_to_authserver_msg_3,
            ),
            owlSpec__pkinit_client_to_authserver_msg_4,
        )) = parsed;
        Some(
            owlSpec_pkinit_client_to_authserver_msg {
                owlSpec__pkinit_client_to_authserver_msg_1,
                owlSpec__pkinit_client_to_authserver_msg_2,
                owlSpec__pkinit_client_to_authserver_msg_3,
                owlSpec__pkinit_client_to_authserver_msg_4,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_pkinit_client_to_authserver_msg_inner(
    x: owlSpec_pkinit_client_to_authserver_msg,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__pkinit_client_to_authserver_msg_1.len(), x.owlSpec__pkinit_client_to_authserver_msg_2.len(), x.owlSpec__pkinit_client_to_authserver_msg_3.len(), x.owlSpec__pkinit_client_to_authserver_msg_4.len() ] {
        let spec_comb = spec_combinator_owlSpec_pkinit_client_to_authserver_msg();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((
                (
                    (
                        x.owlSpec__pkinit_client_to_authserver_msg_1,
                        x.owlSpec__pkinit_client_to_authserver_msg_2,
                    ),
                    x.owlSpec__pkinit_client_to_authserver_msg_3,
                ),
                x.owlSpec__pkinit_client_to_authserver_msg_4,
            )),
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
pub closed spec fn serialize_owlSpec_pkinit_client_to_authserver_msg(
    x: owlSpec_pkinit_client_to_authserver_msg,
) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_pkinit_client_to_authserver_msg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_pkinit_client_to_authserver_msg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_pkinit_client_to_authserver_msg(self)
    }
}

pub open spec fn pkinit_client_to_authserver_msg(
    arg_owlSpec__pkinit_client_to_authserver_msg_1: Seq<u8>,
    arg_owlSpec__pkinit_client_to_authserver_msg_2: Seq<u8>,
    arg_owlSpec__pkinit_client_to_authserver_msg_3: Seq<u8>,
    arg_owlSpec__pkinit_client_to_authserver_msg_4: Seq<u8>,
) -> owlSpec_pkinit_client_to_authserver_msg {
    owlSpec_pkinit_client_to_authserver_msg {
        owlSpec__pkinit_client_to_authserver_msg_1: arg_owlSpec__pkinit_client_to_authserver_msg_1,
        owlSpec__pkinit_client_to_authserver_msg_2: arg_owlSpec__pkinit_client_to_authserver_msg_2,
        owlSpec__pkinit_client_to_authserver_msg_3: arg_owlSpec__pkinit_client_to_authserver_msg_3,
        owlSpec__pkinit_client_to_authserver_msg_4: arg_owlSpec__pkinit_client_to_authserver_msg_4,
    }
}

spec fn spec_combinator_owlSpec_ClientPKResponse() -> (((Variable, Variable), Variable), Variable) {
    let field_1 = Variable(64);
    let field_2 = Variable(1219);
    let field_3 = Variable(32);
    let field_4 = Variable(64);
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_ClientPKResponse() -> (res: (
    ((Variable, Variable), Variable),
    Variable,
))
    ensures
        res.view() == spec_combinator_owlSpec_ClientPKResponse(),
{
    let field_1 = Variable(64);
    let field_2 = Variable(1219);
    let field_3 = Variable(32);
    let field_4 = Variable(64);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_ClientPKResponse {
    pub owlSpec__AuthCert: Seq<u8>,
    pub owlSpec__vkA: Seq<u8>,
    pub owlSpec__k: Seq<u8>,
    pub owlSpec__sigofK: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_ClientPKResponse(x: Seq<u8>) -> Option<owlSpec_ClientPKResponse> {
    let spec_comb = spec_combinator_owlSpec_ClientPKResponse();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec__AuthCert, owlSpec__vkA), owlSpec__k), owlSpec__sigofK)) = parsed;
        Some(
            owlSpec_ClientPKResponse {
                owlSpec__AuthCert,
                owlSpec__vkA,
                owlSpec__k,
                owlSpec__sigofK,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_ClientPKResponse_inner(x: owlSpec_ClientPKResponse) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec__AuthCert.len(), x.owlSpec__vkA.len(), x.owlSpec__k.len(), x.owlSpec__sigofK.len() ] {
        let spec_comb = spec_combinator_owlSpec_ClientPKResponse();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec__AuthCert, x.owlSpec__vkA), x.owlSpec__k), x.owlSpec__sigofK)),
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
pub closed spec fn serialize_owlSpec_ClientPKResponse(x: owlSpec_ClientPKResponse) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_ClientPKResponse_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_ClientPKResponse {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_ClientPKResponse(self)
    }
}

pub open spec fn ClientPKResponse(
    arg_owlSpec__AuthCert: Seq<u8>,
    arg_owlSpec__vkA: Seq<u8>,
    arg_owlSpec__k: Seq<u8>,
    arg_owlSpec__sigofK: Seq<u8>,
) -> owlSpec_ClientPKResponse {
    owlSpec_ClientPKResponse {
        owlSpec__AuthCert: arg_owlSpec__AuthCert,
        owlSpec__vkA: arg_owlSpec__vkA,
        owlSpec__k: arg_owlSpec__k,
        owlSpec__sigofK: arg_owlSpec__sigofK,
    }
}

spec fn spec_combinator_owlSpec_secret_ClientPKResponse() -> (
    ((Variable, Variable), Variable),
    Variable,
) {
    let field_1 = Variable(64);
    let field_2 = Variable(1219);
    let field_3 = Variable(32);
    let field_4 = Variable(64);
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_secret_ClientPKResponse() -> (res: (
    ((Variable, Variable), Variable),
    Variable,
))
    ensures
        res.view() == spec_combinator_owlSpec_secret_ClientPKResponse(),
{
    let field_1 = Variable(64);
    let field_2 = Variable(1219);
    let field_3 = Variable(32);
    let field_4 = Variable(64);
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_secret_ClientPKResponse {
    pub owlSpec__AuthCert: Seq<u8>,
    pub owlSpec__vkA: Seq<u8>,
    pub owlSpec__k: Seq<u8>,
    pub owlSpec__sigofK: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_secret_ClientPKResponse(x: Seq<u8>) -> Option<
    owlSpec_secret_ClientPKResponse,
> {
    let spec_comb = spec_combinator_owlSpec_secret_ClientPKResponse();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((((owlSpec__AuthCert, owlSpec__vkA), owlSpec__k), owlSpec__sigofK)) = parsed;
        Some(
            owlSpec_secret_ClientPKResponse {
                owlSpec__AuthCert,
                owlSpec__vkA,
                owlSpec__k,
                owlSpec__sigofK,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_secret_ClientPKResponse_inner(
    x: owlSpec_secret_ClientPKResponse,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__AuthCert.len(), x.owlSpec__vkA.len(), x.owlSpec__k.len(), x.owlSpec__sigofK.len() ] {
        let spec_comb = spec_combinator_owlSpec_secret_ClientPKResponse();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((((x.owlSpec__AuthCert, x.owlSpec__vkA), x.owlSpec__k), x.owlSpec__sigofK)),
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
pub closed spec fn serialize_owlSpec_secret_ClientPKResponse(
    x: owlSpec_secret_ClientPKResponse,
) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_secret_ClientPKResponse_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_secret_ClientPKResponse {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_secret_ClientPKResponse(self)
    }
}

pub open spec fn secret_ClientPKResponse(
    arg_owlSpec__AuthCert: Seq<u8>,
    arg_owlSpec__vkA: Seq<u8>,
    arg_owlSpec__k: Seq<u8>,
    arg_owlSpec__sigofK: Seq<u8>,
) -> owlSpec_secret_ClientPKResponse {
    owlSpec_secret_ClientPKResponse {
        owlSpec__AuthCert: arg_owlSpec__AuthCert,
        owlSpec__vkA: arg_owlSpec__vkA,
        owlSpec__k: arg_owlSpec__k,
        owlSpec__sigofK: arg_owlSpec__sigofK,
    }
}

#[verifier::opaque]
pub open spec fn authserver_pkinit_spec(
    cfg: cfg_authserver,
    mut_state: state_authserver,
    certA: Seq<u8>,
    vkCA: Seq<u8>,
    pkC: Seq<u8>,
) -> (res: ITree<((), state_authserver), Endpoint>) {
    owl_spec!(mut_state, state_authserver,
        (input(i,_19)) in
(parse (parse_owlSpec_pkinit_client_to_authserver_msg(i)) as (owlSpec_pkinit_client_to_authserver_msg{owlSpec__pkinit_client_to_authserver_msg_1 : certC, owlSpec__pkinit_client_to_authserver_msg_2 : vkc, owlSpec__pkinit_client_to_authserver_msg_3 : signed_un, owlSpec__pkinit_client_to_authserver_msg_4 : un}) in {
(parse (parse_owlSpec_CertAuthMsgs(certC)) as (parsed_caseval : owlSpec_CertAuthMsgs) in {
(case (parsed_caseval) {
| owlSpec_ClientCert(certC) => {
let caseval = ((declassify(DeclassifyingOp::SigVrfy(vkCA, certC, vkc))) in
(ret(vrfy(vkCA, certC, vkc)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(vkC) => {
let declassified_buf34 = ((declassify(DeclassifyingOp::ControlFlow(vkC))) in
(ret((vkC)))) in
let caseval = ((declassify(DeclassifyingOp::SigVrfy(declassified_buf34, signed_un, un))) in
(ret(vrfy(declassified_buf34, signed_un, un)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(username) => {
let eq_bool39 = ((declassify(DeclassifyingOp::EqCheck(username, cfg.owl_uname.view()))) in
(ret(username == cfg.owl_uname.view()))) in
(if (eq_bool39) then
(let tgt = ((sample(NONCE_SIZE, enc(cfg.owl_kT.view(), cfg.owl_AK.view())))) in
(output (tgt) to (Some(Endpoint::Loc_client))) in
let enc_ak = ((sample(NONCE_SIZE, enc(cfg.owl_K.view(), cfg.owl_AK.view())))) in
(output (enc_ak) to (Some(Endpoint::Loc_client))) in
let sA = ((ret(cfg.owl_sigkeyA.view()))) in
let k__ = ((ret(cfg.owl_K.view()))) in
let declassified_buf50 = ((declassify(DeclassifyingOp::ControlFlow(k__))) in
(ret((k__)))) in
let signed_k = ((ret(sign(sA, declassified_buf50)))) in
let b = ((ret(length(signed_k) == SIGNATURE_SIZE))) in
(if (b) then
(let field1 = ((ret(certA))) in
let field2 = ((ret(cfg.pk_owl_sigkeyA.view()))) in
let field3 = ((ret(cfg.owl_K.view()))) in
let field4 = ((ret(signed_k))) in
let str = ((ret(ClientPKResponse(field1, field2, field3, field4)))) in
let msg = ((ret(pkenc(pkC, serialize_owlSpec_ClientPKResponse(str))))) in
(output (msg) to (Some(Endpoint::Loc_client))) in
(ret(())))
else
((ret(())))))
else
((ret(()))))
},
}
)
},
}
)
},
| owlSpec_AuthCert(x) => {
(ret(()))
},
}
)
} otherwise (ret(())))
} otherwise ((ret(()))))
    )
}

#[verifier::opaque]
pub open spec fn authserver_main_spec(cfg: cfg_authserver, mut_state: state_authserver) -> (res:
    ITree<((), state_authserver), Endpoint>) {
    owl_spec!(mut_state, state_authserver,
        (input(i,_64)) in
let eq_bool66 = ((declassify(DeclassifyingOp::EqCheck(i, cfg.owl_uname.view()))) in
(ret(i == cfg.owl_uname.view()))) in
(if (eq_bool66) then
(let tgt = ((sample(NONCE_SIZE, enc(cfg.owl_kT.view(), cfg.owl_AK.view())))) in
let m = ((sample(NONCE_SIZE, enc(cfg.owl_kC.view(), cfg.owl_AK.view())))) in
let p = ((ret(authserver_msg(tgt, m)))) in
(output (serialize_owlSpec_authserver_msg(p)) to (Some(Endpoint::Loc_client))) in
(ret(())))
else
((ret(()))))
    )
}

#[verifier::opaque]
pub open spec fn certauth_main_spec(cfg: cfg_certauth, mut_state: state_certauth) -> (res: ITree<
    ((), state_certauth),
    Endpoint,
>) {
    owl_spec!(mut_state, state_certauth,
        (ret(()))
    )
}

#[verifier::opaque]
pub open spec fn client_main_spec(cfg: cfg_client, mut_state: state_client) -> (res: ITree<
    ((), state_client),
    Endpoint,
>) {
    owl_spec!(mut_state, state_client,
        let username = ((ret(cfg.owl_uname.view()))) in
let declassified_buf76 = ((declassify(DeclassifyingOp::ControlFlow(username))) in
(ret((username)))) in
(output (declassified_buf76) to (Some(Endpoint::Loc_authserver))) in
(input(i,_80)) in
(parse (parse_owlSpec_authserver_msg(i)) as (owlSpec_authserver_msg{owlSpec__authserver_msg_1 : tgt, owlSpec__authserver_msg_2 : c}) in {
let caseval = ((declassify(DeclassifyingOp::ADec(cfg.owl_kC.view(), c))) in
(ret(dec(cfg.owl_kC.view(), c)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(ak) => {
let declassified_buf92 = ((declassify(DeclassifyingOp::ControlFlow(username))) in
(ret((username)))) in
call(client_kerberos_spec(cfg, mut_state, ak, tgt, declassified_buf92))
},
}
)
} otherwise ((ret(()))))
    )
}

#[verifier::opaque]
pub open spec fn client_pkinit_spec(
    cfg: cfg_client,
    mut_state: state_client,
    certC: Seq<u8>,
    vkCA: Seq<u8>,
) -> (res: ITree<((), state_client), Endpoint>) {
    owl_spec!(mut_state, state_client,
        let username = ((ret(cfg.owl_uname.view()))) in
let declassified_buf98 = ((declassify(DeclassifyingOp::ControlFlow(username))) in
(ret((username)))) in
let signed_name = ((ret(sign(cfg.owl_sigkeyC.view(), declassified_buf98)))) in
let declassified_buf102 = ((declassify(DeclassifyingOp::ControlFlow(username))) in
(ret((username)))) in
let p = ((ret(pkinit_client_to_authserver_msg(certC, cfg.pk_owl_sigkeyC.view(), signed_name, declassified_buf102)))) in
(output (serialize_owlSpec_pkinit_client_to_authserver_msg(p)) to (Some(Endpoint::Loc_authserver))) in
(input(tgt,_107)) in
(input(enc_ak,_109)) in
(input(msg,_111)) in
let caseval = ((declassify(DeclassifyingOp::PkDec(cfg.owl_seckeyCnew.view(), msg))) in
(ret(pkdec(cfg.owl_seckeyCnew.view(), msg)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(p_) => {
(parse (parse_owlSpec_secret_ClientPKResponse(p_)) as (owlSpec_secret_ClientPKResponse{owlSpec__AuthCert : certA, owlSpec__vkA : vka, owlSpec__k : k, owlSpec__sigofK : ksig}) in {
let declassified_buf124 = ((declassify(DeclassifyingOp::ControlFlow(certA))) in
(ret((certA)))) in
let declassified_buf127 = ((declassify(DeclassifyingOp::ControlFlow(vka))) in
(ret((vka)))) in
let caseval = ((declassify(DeclassifyingOp::SigVrfy(vkCA, declassified_buf124, declassified_buf127))) in
(ret(vrfy(vkCA, declassified_buf124, declassified_buf127)))) in
(case (caseval) {
| Some(res) => {
let declassified_buf151 = ((declassify(DeclassifyingOp::ControlFlow(res))) in
(ret((res)))) in
(parse (parse_owlSpec_CertAuthMsgs(declassified_buf151)) as (parsed_caseval : owlSpec_CertAuthMsgs) in {
(case (parsed_caseval) {
| owlSpec_ClientCert(_unused259) => {
(ret(()))
},
| owlSpec_AuthCert(vkA) => {
let declassified_buf136 = ((declassify(DeclassifyingOp::ControlFlow(ksig))) in
(ret((ksig)))) in
let caseval = ((declassify(DeclassifyingOp::SigVrfy(vkA, k, declassified_buf136))) in
(ret(vrfy(vkA, k, declassified_buf136)))) in
(case (caseval) {
| Some(k) => {
let caseval = ((declassify(DeclassifyingOp::ADec(k, enc_ak))) in
(ret(dec(k, enc_ak)))) in
(case (caseval) {
| Some(ak) => {
let declassified_buf147 = ((declassify(DeclassifyingOp::ControlFlow(username))) in
(ret((username)))) in
call(client_kerberos_tmpcopy_spec(cfg, mut_state, ak, tgt, declassified_buf147))
},
| None => {
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
},
}
)
} otherwise (ret(())))
},
| None => {
(ret(()))
},
}
)
} otherwise ((ret(()))))
},
}
)
    )
}

#[verifier::opaque]
pub open spec fn client_kerberos_tmpcopy_spec(
    cfg: cfg_client,
    mut_state: state_client,
    ak: Seq<u8>,
    tgt: Seq<u8>,
    username: Seq<u8>,
) -> (res: ITree<((), state_client), Endpoint>) {
    owl_spec!(mut_state, state_client,
        let m = ((sample(NONCE_SIZE, enc(ak, serialize_owlSpec_AKEnum(ClientRequest()))))) in
let p = ((ret(client_to_ticketserver_msg(tgt, m)))) in
(output (serialize_owlSpec_client_to_ticketserver_msg(p)) to (Some(Endpoint::Loc_ticketserver))) in
(input(i_,_161)) in
(parse (parse_owlSpec_ticketserver_msg(i_)) as (owlSpec_ticketserver_msg{owlSpec__ticketserver_msg_1 : service_ticket, owlSpec__ticketserver_msg_2 : c}) in {
let caseval = ((declassify(DeclassifyingOp::ADec(ak, c))) in
(ret(dec(ak, c)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(res) => {
(declassify(DeclassifyingOp::EnumParse(res))) in
(parse (parse_owlSpec_AKEnum(res)) as (parsed_caseval : owlSpec_AKEnum) in {
(case (parsed_caseval) {
| owlSpec_ClientRequest() => {
(ret(()))
},
| owlSpec_TicketResponse(sk) => {
let m_ = ((sample(NONCE_SIZE, enc(sk, username)))) in
let p_ = ((ret(client_to_service_msg(service_ticket, m_)))) in
(output (serialize_owlSpec_client_to_service_msg(p_)) to (Some(Endpoint::Loc_service))) in
(input(_unused263,_175)) in
(ret(()))
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
pub open spec fn client_kerberos_spec(
    cfg: cfg_client,
    mut_state: state_client,
    ak: Seq<u8>,
    tgt: Seq<u8>,
    username: Seq<u8>,
) -> (res: ITree<((), state_client), Endpoint>) {
    owl_spec!(mut_state, state_client,
        let m = ((sample(NONCE_SIZE, enc(ak, serialize_owlSpec_AKEnum(ClientRequest()))))) in
let p = ((ret(client_to_ticketserver_msg(tgt, m)))) in
(output (serialize_owlSpec_client_to_ticketserver_msg(p)) to (Some(Endpoint::Loc_ticketserver))) in
(input(i_,_186)) in
(parse (parse_owlSpec_ticketserver_msg(i_)) as (owlSpec_ticketserver_msg{owlSpec__ticketserver_msg_1 : service_ticket, owlSpec__ticketserver_msg_2 : c}) in {
let caseval = ((declassify(DeclassifyingOp::ADec(ak, c))) in
(ret(dec(ak, c)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(res) => {
(declassify(DeclassifyingOp::EnumParse(res))) in
(parse (parse_owlSpec_AKEnum(res)) as (parsed_caseval : owlSpec_AKEnum) in {
(case (parsed_caseval) {
| owlSpec_ClientRequest() => {
(ret(()))
},
| owlSpec_TicketResponse(sk) => {
let m_ = ((sample(NONCE_SIZE, enc(sk, username)))) in
let p_ = ((ret(client_to_service_msg(service_ticket, m_)))) in
(output (serialize_owlSpec_client_to_service_msg(p_)) to (Some(Endpoint::Loc_service))) in
(input(_unused267,_200)) in
(ret(()))
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
pub open spec fn service_main_spec(cfg: cfg_service, mut_state: state_service) -> (res: ITree<
    ((), state_service),
    Endpoint,
>) {
    owl_spec!(mut_state, state_service,
        (input(i,_204)) in
(parse (parse_owlSpec_client_to_service_msg(i)) as (owlSpec_client_to_service_msg{owlSpec__client_to_service_msg_1 : c1, owlSpec__client_to_service_msg_2 : c2}) in {
let caseval = ((declassify(DeclassifyingOp::ADec(cfg.owl_kS.view(), c1))) in
(ret(dec(cfg.owl_kS.view(), c1)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(sk) => {
let caseval = ((declassify(DeclassifyingOp::ADec(sk, c2))) in
(ret(dec(sk, c2)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(u) => {
let eq_bool216 = ((declassify(DeclassifyingOp::EqCheck(u, cfg.owl_uname.view()))) in
(ret(u == cfg.owl_uname.view()))) in
(if (eq_bool216) then
((output (empty_seq_u8()) to (Some(Endpoint::Loc_client))) in
(ret(())))
else
((ret(()))))
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
pub open spec fn ticketserver_main_spec(
    cfg: cfg_ticketserver,
    mut_state: state_ticketserver,
) -> (res: ITree<((), state_ticketserver), Endpoint>) {
    owl_spec!(mut_state, state_ticketserver,
        (input(i,_220)) in
(parse (parse_owlSpec_client_to_ticketserver_msg(i)) as (owlSpec_client_to_ticketserver_msg{owlSpec__client_to_ticketserver_msg_1 : c, owlSpec__client_to_ticketserver_msg_2 : t}) in {
let caseval = ((declassify(DeclassifyingOp::ADec(cfg.owl_kT.view(), c))) in
(ret(dec(cfg.owl_kT.view(), c)))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(ak) => {
let caseval = ((declassify(DeclassifyingOp::ADec(ak, t))) in
(ret(dec(ak, t)))) in
(case (caseval) {
| Some(ClientRequest) => {
let st = ((sample(NONCE_SIZE, enc(cfg.owl_kS.view(), cfg.owl_SK.view())))) in
let m = ((sample(NONCE_SIZE, enc(ak, serialize_owlSpec_AKEnum(TicketResponse(cfg.owl_SK.view())))))) in
let p = ((ret(ticketserver_msg(st, m)))) in
(output (serialize_owlSpec_ticketserver_msg(p)) to (Some(Endpoint::Loc_client))) in
(ret(()))
},
| None => {
(ret(()))
},
}
)
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
    Loc_authserver,
    Loc_certauth,
    Loc_client,
    Loc_service,
    Loc_ticketserver,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier(external_body)]
pub const fn authserver_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_authserver,
{
    "127.0.0.1:9001"
}

#[verifier(external_body)]
pub const fn certauth_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_certauth,
{
    "127.0.0.1:9002"
}

#[verifier(external_body)]
pub const fn client_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_client,
{
    "127.0.0.1:9003"
}

#[verifier(external_body)]
pub const fn service_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_service,
{
    "127.0.0.1:9004"
}

#[verifier(external_body)]
pub const fn ticketserver_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_ticketserver,
{
    "127.0.0.1:9005"
}

pub enum owl_AKEnum<'a> {
    owl_ClientRequest(),
    owl_TicketResponse(SecretBuf<'a>),
}

use owl_AKEnum::*;

impl<'a> owl_AKEnum<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_AKEnum<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_ClientRequest() => owl_ClientRequest(),
            owl_TicketResponse(x) => owl_TicketResponse(SecretBuf::another_ref(x)),
        }
    }
}

impl View for owl_AKEnum<'_> {
    type V = owlSpec_AKEnum;

    open spec fn view(&self) -> owlSpec_AKEnum {
        match self {
            owl_ClientRequest() => owlSpec_AKEnum::owlSpec_ClientRequest(),
            owl_TicketResponse(v) => owlSpec_AKEnum::owlSpec_TicketResponse(v.view()),
        }
    }
}

#[inline]
pub fn owl_ClientRequest_enumtest(x: &owl_AKEnum<'_>) -> (res: bool)
    ensures
        res == ClientRequest_enumtest(x.view()),
{
    match x {
        owl_AKEnum::owl_ClientRequest() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_TicketResponse_enumtest(x: &owl_AKEnum<'_>) -> (res: bool)
    ensures
        res == TicketResponse_enumtest(x.view()),
{
    match x {
        owl_AKEnum::owl_TicketResponse(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_AKEnum<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_AKEnum<'a>>)
    ensures
        res is Some ==> parse_owlSpec_AKEnum(arg.view()) is Some,
        res is None ==> parse_owlSpec_AKEnum(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_AKEnum(arg.view())->Some_0,
{
    reveal(parse_owlSpec_AKEnum);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(0)), (Tag::new(U8, 2), Variable(32)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owl_AKEnum::owl_ClientRequest(),
            inj_ord_choice_pat!(*, (_,x)) => owl_AKEnum::owl_TicketResponse(
                SecretBuf::from_buf(x.another_ref()),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_AKEnum<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_AKEnum<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_AKEnum(arg.view()) is Some,
        res is None ==> parse_owlSpec_AKEnum(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_AKEnum(arg.view())->Some_0,
{
    reveal(parse_owlSpec_AKEnum);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_AKEnum_inner(arg: &owl_AKEnum) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_AKEnum_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_AKEnum_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_AKEnum_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_AKEnum(arg: &owl_AKEnum) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_AKEnum(arg.view()),
{
    reveal(serialize_owlSpec_AKEnum);
    let res = serialize_owl_AKEnum_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_CertAuthMsgs<'a> {
    owl_AuthCert(OwlBuf<'a>),
    owl_ClientCert(OwlBuf<'a>),
}

use owl_CertAuthMsgs::*;

impl<'a> owl_CertAuthMsgs<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_CertAuthMsgs<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_AuthCert(x) => owl_AuthCert(OwlBuf::another_ref(x)),
            owl_ClientCert(x) => owl_ClientCert(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_CertAuthMsgs<'_> {
    type V = owlSpec_CertAuthMsgs;

    open spec fn view(&self) -> owlSpec_CertAuthMsgs {
        match self {
            owl_AuthCert(v) => owlSpec_CertAuthMsgs::owlSpec_AuthCert(v.view()),
            owl_ClientCert(v) => owlSpec_CertAuthMsgs::owlSpec_ClientCert(v.view()),
        }
    }
}

#[inline]
pub fn owl_AuthCert_enumtest(x: &owl_CertAuthMsgs<'_>) -> (res: bool)
    ensures
        res == AuthCert_enumtest(x.view()),
{
    match x {
        owl_CertAuthMsgs::owl_AuthCert(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl_ClientCert_enumtest(x: &owl_CertAuthMsgs<'_>) -> (res: bool)
    ensures
        res == ClientCert_enumtest(x.view()),
{
    match x {
        owl_CertAuthMsgs::owl_ClientCert(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_CertAuthMsgs<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_CertAuthMsgs<'a>>)
    ensures
        res is Some ==> parse_owlSpec_CertAuthMsgs(arg.view()) is Some,
        res is None ==> parse_owlSpec_CertAuthMsgs(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_CertAuthMsgs(arg.view())->Some_0,
{
    reveal(parse_owlSpec_CertAuthMsgs);
    let exec_comb =
        ord_choice!((Tag::new(U8, 1), Variable(1219)), (Tag::new(U8, 2), Variable(1219)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owl_CertAuthMsgs::owl_AuthCert(
                OwlBuf::another_ref(&x),
            ),
            inj_ord_choice_pat!(*, (_,x)) => owl_CertAuthMsgs::owl_ClientCert(
                OwlBuf::another_ref(&x),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn serialize_owl_CertAuthMsgs_inner(arg: &owl_CertAuthMsgs) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_CertAuthMsgs_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_CertAuthMsgs_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_CertAuthMsgs_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_CertAuthMsgs(arg: &owl_CertAuthMsgs) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_CertAuthMsgs(arg.view()),
{
    reveal(serialize_owlSpec_CertAuthMsgs);
    let res = serialize_owl_CertAuthMsgs_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_authserver_msg<'a> {
    pub owl__authserver_msg_1: OwlBuf<'a>,
    pub owl__authserver_msg_2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_authserver_msg<'a>(
    arg_owl__authserver_msg_1: OwlBuf<'a>,
    arg_owl__authserver_msg_2: OwlBuf<'a>,
) -> (res: owl_authserver_msg<'a>)
    ensures
        res.owl__authserver_msg_1.view() == arg_owl__authserver_msg_1.view(),
        res.owl__authserver_msg_2.view() == arg_owl__authserver_msg_2.view(),
{
    owl_authserver_msg {
        owl__authserver_msg_1: arg_owl__authserver_msg_1,
        owl__authserver_msg_2: arg_owl__authserver_msg_2,
    }
}

impl<'a> owl_authserver_msg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_authserver_msg<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_authserver_msg {
            owl__authserver_msg_1: OwlBuf::another_ref(&self.owl__authserver_msg_1),
            owl__authserver_msg_2: OwlBuf::another_ref(&self.owl__authserver_msg_2),
        }
    }
}

impl View for owl_authserver_msg<'_> {
    type V = owlSpec_authserver_msg;

    open spec fn view(&self) -> owlSpec_authserver_msg {
        owlSpec_authserver_msg {
            owlSpec__authserver_msg_1: self.owl__authserver_msg_1.view(),
            owlSpec__authserver_msg_2: self.owl__authserver_msg_2.view(),
        }
    }
}

pub exec fn parse_owl_authserver_msg<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_authserver_msg<'a>>)
    ensures
        res is Some ==> parse_owlSpec_authserver_msg(arg.view()) is Some,
        res is None ==> parse_owlSpec_authserver_msg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_authserver_msg(arg.view())->Some_0,
{
    reveal(parse_owlSpec_authserver_msg);
    let exec_comb = exec_combinator_owl_authserver_msg();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__authserver_msg_1, owl__authserver_msg_2) = parsed;
        Some(
            owl_authserver_msg {
                owl__authserver_msg_1: OwlBuf::another_ref(&owl__authserver_msg_1),
                owl__authserver_msg_2: OwlBuf::another_ref(&owl__authserver_msg_2),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_authserver_msg_inner<'a>(arg: &owl_authserver_msg<'a>) -> (res: Option<
    OwlBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_authserver_msg_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_authserver_msg_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_authserver_msg_inner);
    if no_usize_overflows![ arg.owl__authserver_msg_1.len(), arg.owl__authserver_msg_2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_authserver_msg();
        let mut obuf = vec_u8_of_len(
            arg.owl__authserver_msg_1.len() + arg.owl__authserver_msg_2.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                OwlBuf::another_ref(&arg.owl__authserver_msg_1),
                OwlBuf::another_ref(&arg.owl__authserver_msg_2),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_authserver_msg_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_authserver_msg<'a>(arg: &owl_authserver_msg<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_authserver_msg(arg.view()),
{
    reveal(serialize_owlSpec_authserver_msg);
    let res = serialize_owl_authserver_msg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_client_to_ticketserver_msg<'a> {
    pub owl__client_to_ticketserver_msg_1: OwlBuf<'a>,
    pub owl__client_to_ticketserver_msg_2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_client_to_ticketserver_msg<'a>(
    arg_owl__client_to_ticketserver_msg_1: OwlBuf<'a>,
    arg_owl__client_to_ticketserver_msg_2: OwlBuf<'a>,
) -> (res: owl_client_to_ticketserver_msg<'a>)
    ensures
        res.owl__client_to_ticketserver_msg_1.view()
            == arg_owl__client_to_ticketserver_msg_1.view(),
        res.owl__client_to_ticketserver_msg_2.view()
            == arg_owl__client_to_ticketserver_msg_2.view(),
{
    owl_client_to_ticketserver_msg {
        owl__client_to_ticketserver_msg_1: arg_owl__client_to_ticketserver_msg_1,
        owl__client_to_ticketserver_msg_2: arg_owl__client_to_ticketserver_msg_2,
    }
}

impl<'a> owl_client_to_ticketserver_msg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_client_to_ticketserver_msg<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_client_to_ticketserver_msg {
            owl__client_to_ticketserver_msg_1: OwlBuf::another_ref(
                &self.owl__client_to_ticketserver_msg_1,
            ),
            owl__client_to_ticketserver_msg_2: OwlBuf::another_ref(
                &self.owl__client_to_ticketserver_msg_2,
            ),
        }
    }
}

impl View for owl_client_to_ticketserver_msg<'_> {
    type V = owlSpec_client_to_ticketserver_msg;

    open spec fn view(&self) -> owlSpec_client_to_ticketserver_msg {
        owlSpec_client_to_ticketserver_msg {
            owlSpec__client_to_ticketserver_msg_1: self.owl__client_to_ticketserver_msg_1.view(),
            owlSpec__client_to_ticketserver_msg_2: self.owl__client_to_ticketserver_msg_2.view(),
        }
    }
}

pub exec fn parse_owl_client_to_ticketserver_msg<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_client_to_ticketserver_msg<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_client_to_ticketserver_msg(arg.view()) is Some,
        res is None ==> parse_owlSpec_client_to_ticketserver_msg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_client_to_ticketserver_msg(
            arg.view(),
        )->Some_0,
{
    reveal(parse_owlSpec_client_to_ticketserver_msg);
    let exec_comb = exec_combinator_owl_client_to_ticketserver_msg();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__client_to_ticketserver_msg_1, owl__client_to_ticketserver_msg_2) = parsed;
        Some(
            owl_client_to_ticketserver_msg {
                owl__client_to_ticketserver_msg_1: OwlBuf::another_ref(
                    &owl__client_to_ticketserver_msg_1,
                ),
                owl__client_to_ticketserver_msg_2: OwlBuf::another_ref(
                    &owl__client_to_ticketserver_msg_2,
                ),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_client_to_ticketserver_msg_inner<'a>(
    arg: &owl_client_to_ticketserver_msg<'a>,
) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_client_to_ticketserver_msg_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_client_to_ticketserver_msg_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_client_to_ticketserver_msg_inner);
    if no_usize_overflows![ arg.owl__client_to_ticketserver_msg_1.len(), arg.owl__client_to_ticketserver_msg_2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_client_to_ticketserver_msg();
        let mut obuf = vec_u8_of_len(
            arg.owl__client_to_ticketserver_msg_1.len()
                + arg.owl__client_to_ticketserver_msg_2.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                OwlBuf::another_ref(&arg.owl__client_to_ticketserver_msg_1),
                OwlBuf::another_ref(&arg.owl__client_to_ticketserver_msg_2),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_client_to_ticketserver_msg_inner(
                arg.view(),
            )->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_client_to_ticketserver_msg<'a>(
    arg: &owl_client_to_ticketserver_msg<'a>,
) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_client_to_ticketserver_msg(arg.view()),
{
    reveal(serialize_owlSpec_client_to_ticketserver_msg);
    let res = serialize_owl_client_to_ticketserver_msg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_ticketserver_msg<'a> {
    pub owl__ticketserver_msg_1: OwlBuf<'a>,
    pub owl__ticketserver_msg_2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_ticketserver_msg<'a>(
    arg_owl__ticketserver_msg_1: OwlBuf<'a>,
    arg_owl__ticketserver_msg_2: OwlBuf<'a>,
) -> (res: owl_ticketserver_msg<'a>)
    ensures
        res.owl__ticketserver_msg_1.view() == arg_owl__ticketserver_msg_1.view(),
        res.owl__ticketserver_msg_2.view() == arg_owl__ticketserver_msg_2.view(),
{
    owl_ticketserver_msg {
        owl__ticketserver_msg_1: arg_owl__ticketserver_msg_1,
        owl__ticketserver_msg_2: arg_owl__ticketserver_msg_2,
    }
}

impl<'a> owl_ticketserver_msg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_ticketserver_msg<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_ticketserver_msg {
            owl__ticketserver_msg_1: OwlBuf::another_ref(&self.owl__ticketserver_msg_1),
            owl__ticketserver_msg_2: OwlBuf::another_ref(&self.owl__ticketserver_msg_2),
        }
    }
}

impl View for owl_ticketserver_msg<'_> {
    type V = owlSpec_ticketserver_msg;

    open spec fn view(&self) -> owlSpec_ticketserver_msg {
        owlSpec_ticketserver_msg {
            owlSpec__ticketserver_msg_1: self.owl__ticketserver_msg_1.view(),
            owlSpec__ticketserver_msg_2: self.owl__ticketserver_msg_2.view(),
        }
    }
}

pub exec fn parse_owl_ticketserver_msg<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_ticketserver_msg<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_ticketserver_msg(arg.view()) is Some,
        res is None ==> parse_owlSpec_ticketserver_msg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_ticketserver_msg(arg.view())->Some_0,
{
    reveal(parse_owlSpec_ticketserver_msg);
    let exec_comb = exec_combinator_owl_ticketserver_msg();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__ticketserver_msg_1, owl__ticketserver_msg_2) = parsed;
        Some(
            owl_ticketserver_msg {
                owl__ticketserver_msg_1: OwlBuf::another_ref(&owl__ticketserver_msg_1),
                owl__ticketserver_msg_2: OwlBuf::another_ref(&owl__ticketserver_msg_2),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_ticketserver_msg_inner<'a>(arg: &owl_ticketserver_msg<'a>) -> (res:
    Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_ticketserver_msg_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_ticketserver_msg_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_ticketserver_msg_inner);
    if no_usize_overflows![ arg.owl__ticketserver_msg_1.len(), arg.owl__ticketserver_msg_2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_ticketserver_msg();
        let mut obuf = vec_u8_of_len(
            arg.owl__ticketserver_msg_1.len() + arg.owl__ticketserver_msg_2.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                OwlBuf::another_ref(&arg.owl__ticketserver_msg_1),
                OwlBuf::another_ref(&arg.owl__ticketserver_msg_2),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_ticketserver_msg_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_ticketserver_msg<'a>(arg: &owl_ticketserver_msg<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_ticketserver_msg(arg.view()),
{
    reveal(serialize_owlSpec_ticketserver_msg);
    let res = serialize_owl_ticketserver_msg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_client_to_service_msg<'a> {
    pub owl__client_to_service_msg_1: OwlBuf<'a>,
    pub owl__client_to_service_msg_2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_client_to_service_msg<'a>(
    arg_owl__client_to_service_msg_1: OwlBuf<'a>,
    arg_owl__client_to_service_msg_2: OwlBuf<'a>,
) -> (res: owl_client_to_service_msg<'a>)
    ensures
        res.owl__client_to_service_msg_1.view() == arg_owl__client_to_service_msg_1.view(),
        res.owl__client_to_service_msg_2.view() == arg_owl__client_to_service_msg_2.view(),
{
    owl_client_to_service_msg {
        owl__client_to_service_msg_1: arg_owl__client_to_service_msg_1,
        owl__client_to_service_msg_2: arg_owl__client_to_service_msg_2,
    }
}

impl<'a> owl_client_to_service_msg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_client_to_service_msg<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_client_to_service_msg {
            owl__client_to_service_msg_1: OwlBuf::another_ref(&self.owl__client_to_service_msg_1),
            owl__client_to_service_msg_2: OwlBuf::another_ref(&self.owl__client_to_service_msg_2),
        }
    }
}

impl View for owl_client_to_service_msg<'_> {
    type V = owlSpec_client_to_service_msg;

    open spec fn view(&self) -> owlSpec_client_to_service_msg {
        owlSpec_client_to_service_msg {
            owlSpec__client_to_service_msg_1: self.owl__client_to_service_msg_1.view(),
            owlSpec__client_to_service_msg_2: self.owl__client_to_service_msg_2.view(),
        }
    }
}

pub exec fn parse_owl_client_to_service_msg<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_client_to_service_msg<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_client_to_service_msg(arg.view()) is Some,
        res is None ==> parse_owlSpec_client_to_service_msg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_client_to_service_msg(arg.view())->Some_0,
{
    reveal(parse_owlSpec_client_to_service_msg);
    let exec_comb = exec_combinator_owl_client_to_service_msg();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__client_to_service_msg_1, owl__client_to_service_msg_2) = parsed;
        Some(
            owl_client_to_service_msg {
                owl__client_to_service_msg_1: OwlBuf::another_ref(&owl__client_to_service_msg_1),
                owl__client_to_service_msg_2: OwlBuf::another_ref(&owl__client_to_service_msg_2),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_client_to_service_msg_inner<'a>(
    arg: &owl_client_to_service_msg<'a>,
) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_client_to_service_msg_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_client_to_service_msg_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_client_to_service_msg_inner);
    if no_usize_overflows![ arg.owl__client_to_service_msg_1.len(), arg.owl__client_to_service_msg_2.len(), 0 ] {
        let exec_comb = exec_combinator_owl_client_to_service_msg();
        let mut obuf = vec_u8_of_len(
            arg.owl__client_to_service_msg_1.len() + arg.owl__client_to_service_msg_2.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                OwlBuf::another_ref(&arg.owl__client_to_service_msg_1),
                OwlBuf::another_ref(&arg.owl__client_to_service_msg_2),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_client_to_service_msg_inner(
                arg.view(),
            )->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_client_to_service_msg<'a>(arg: &owl_client_to_service_msg<'a>) -> (res:
    OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_client_to_service_msg(arg.view()),
{
    reveal(serialize_owlSpec_client_to_service_msg);
    let res = serialize_owl_client_to_service_msg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_pkinit_client_to_authserver_msg<'a> {
    pub owl__pkinit_client_to_authserver_msg_1: OwlBuf<'a>,
    pub owl__pkinit_client_to_authserver_msg_2: OwlBuf<'a>,
    pub owl__pkinit_client_to_authserver_msg_3: OwlBuf<'a>,
    pub owl__pkinit_client_to_authserver_msg_4: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_pkinit_client_to_authserver_msg<'a>(
    arg_owl__pkinit_client_to_authserver_msg_1: OwlBuf<'a>,
    arg_owl__pkinit_client_to_authserver_msg_2: OwlBuf<'a>,
    arg_owl__pkinit_client_to_authserver_msg_3: OwlBuf<'a>,
    arg_owl__pkinit_client_to_authserver_msg_4: OwlBuf<'a>,
) -> (res: owl_pkinit_client_to_authserver_msg<'a>)
    ensures
        res.owl__pkinit_client_to_authserver_msg_1.view()
            == arg_owl__pkinit_client_to_authserver_msg_1.view(),
        res.owl__pkinit_client_to_authserver_msg_2.view()
            == arg_owl__pkinit_client_to_authserver_msg_2.view(),
        res.owl__pkinit_client_to_authserver_msg_3.view()
            == arg_owl__pkinit_client_to_authserver_msg_3.view(),
        res.owl__pkinit_client_to_authserver_msg_4.view()
            == arg_owl__pkinit_client_to_authserver_msg_4.view(),
{
    owl_pkinit_client_to_authserver_msg {
        owl__pkinit_client_to_authserver_msg_1: arg_owl__pkinit_client_to_authserver_msg_1,
        owl__pkinit_client_to_authserver_msg_2: arg_owl__pkinit_client_to_authserver_msg_2,
        owl__pkinit_client_to_authserver_msg_3: arg_owl__pkinit_client_to_authserver_msg_3,
        owl__pkinit_client_to_authserver_msg_4: arg_owl__pkinit_client_to_authserver_msg_4,
    }
}

impl<'a> owl_pkinit_client_to_authserver_msg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_pkinit_client_to_authserver_msg<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_pkinit_client_to_authserver_msg {
            owl__pkinit_client_to_authserver_msg_1: OwlBuf::another_ref(
                &self.owl__pkinit_client_to_authserver_msg_1,
            ),
            owl__pkinit_client_to_authserver_msg_2: OwlBuf::another_ref(
                &self.owl__pkinit_client_to_authserver_msg_2,
            ),
            owl__pkinit_client_to_authserver_msg_3: OwlBuf::another_ref(
                &self.owl__pkinit_client_to_authserver_msg_3,
            ),
            owl__pkinit_client_to_authserver_msg_4: OwlBuf::another_ref(
                &self.owl__pkinit_client_to_authserver_msg_4,
            ),
        }
    }
}

impl View for owl_pkinit_client_to_authserver_msg<'_> {
    type V = owlSpec_pkinit_client_to_authserver_msg;

    open spec fn view(&self) -> owlSpec_pkinit_client_to_authserver_msg {
        owlSpec_pkinit_client_to_authserver_msg {
            owlSpec__pkinit_client_to_authserver_msg_1:
                self.owl__pkinit_client_to_authserver_msg_1.view(),
            owlSpec__pkinit_client_to_authserver_msg_2:
                self.owl__pkinit_client_to_authserver_msg_2.view(),
            owlSpec__pkinit_client_to_authserver_msg_3:
                self.owl__pkinit_client_to_authserver_msg_3.view(),
            owlSpec__pkinit_client_to_authserver_msg_4:
                self.owl__pkinit_client_to_authserver_msg_4.view(),
        }
    }
}

pub exec fn parse_owl_pkinit_client_to_authserver_msg<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_pkinit_client_to_authserver_msg<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_pkinit_client_to_authserver_msg(arg.view()) is Some,
        res is None ==> parse_owlSpec_pkinit_client_to_authserver_msg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_pkinit_client_to_authserver_msg(
            arg.view(),
        )->Some_0,
{
    reveal(parse_owlSpec_pkinit_client_to_authserver_msg);
    let exec_comb = exec_combinator_owl_pkinit_client_to_authserver_msg();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (
            (
                (owl__pkinit_client_to_authserver_msg_1, owl__pkinit_client_to_authserver_msg_2),
                owl__pkinit_client_to_authserver_msg_3,
            ),
            owl__pkinit_client_to_authserver_msg_4,
        ) = parsed;
        Some(
            owl_pkinit_client_to_authserver_msg {
                owl__pkinit_client_to_authserver_msg_1: OwlBuf::another_ref(
                    &owl__pkinit_client_to_authserver_msg_1,
                ),
                owl__pkinit_client_to_authserver_msg_2: OwlBuf::another_ref(
                    &owl__pkinit_client_to_authserver_msg_2,
                ),
                owl__pkinit_client_to_authserver_msg_3: OwlBuf::another_ref(
                    &owl__pkinit_client_to_authserver_msg_3,
                ),
                owl__pkinit_client_to_authserver_msg_4: OwlBuf::another_ref(
                    &owl__pkinit_client_to_authserver_msg_4,
                ),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_pkinit_client_to_authserver_msg_inner<'a>(
    arg: &owl_pkinit_client_to_authserver_msg<'a>,
) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_pkinit_client_to_authserver_msg_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_pkinit_client_to_authserver_msg_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_pkinit_client_to_authserver_msg_inner);
    if no_usize_overflows![ arg.owl__pkinit_client_to_authserver_msg_1.len(), arg.owl__pkinit_client_to_authserver_msg_2.len(), arg.owl__pkinit_client_to_authserver_msg_3.len(), arg.owl__pkinit_client_to_authserver_msg_4.len(), 0 ] {
        let exec_comb = exec_combinator_owl_pkinit_client_to_authserver_msg();
        let mut obuf = vec_u8_of_len(
            arg.owl__pkinit_client_to_authserver_msg_1.len()
                + arg.owl__pkinit_client_to_authserver_msg_2.len()
                + arg.owl__pkinit_client_to_authserver_msg_3.len()
                + arg.owl__pkinit_client_to_authserver_msg_4.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        OwlBuf::another_ref(&arg.owl__pkinit_client_to_authserver_msg_1),
                        OwlBuf::another_ref(&arg.owl__pkinit_client_to_authserver_msg_2),
                    ),
                    OwlBuf::another_ref(&arg.owl__pkinit_client_to_authserver_msg_3),
                ),
                OwlBuf::another_ref(&arg.owl__pkinit_client_to_authserver_msg_4),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_pkinit_client_to_authserver_msg_inner(
                arg.view(),
            )->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_pkinit_client_to_authserver_msg<'a>(
    arg: &owl_pkinit_client_to_authserver_msg<'a>,
) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_pkinit_client_to_authserver_msg(arg.view()),
{
    reveal(serialize_owlSpec_pkinit_client_to_authserver_msg);
    let res = serialize_owl_pkinit_client_to_authserver_msg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_ClientPKResponse<'a> {
    pub owl__AuthCert: OwlBuf<'a>,
    pub owl__vkA: OwlBuf<'a>,
    pub owl__k: SecretBuf<'a>,
    pub owl__sigofK: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_ClientPKResponse<'a>(
    arg_owl__AuthCert: OwlBuf<'a>,
    arg_owl__vkA: OwlBuf<'a>,
    arg_owl__k: SecretBuf<'a>,
    arg_owl__sigofK: SecretBuf<'a>,
) -> (res: owl_ClientPKResponse<'a>)
    ensures
        res.owl__AuthCert.view() == arg_owl__AuthCert.view(),
        res.owl__vkA.view() == arg_owl__vkA.view(),
        res.owl__k.view() == arg_owl__k.view(),
        res.owl__sigofK.view() == arg_owl__sigofK.view(),
{
    owl_ClientPKResponse {
        owl__AuthCert: arg_owl__AuthCert,
        owl__vkA: arg_owl__vkA,
        owl__k: arg_owl__k,
        owl__sigofK: arg_owl__sigofK,
    }
}

impl<'a> owl_ClientPKResponse<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_ClientPKResponse<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_ClientPKResponse {
            owl__AuthCert: OwlBuf::another_ref(&self.owl__AuthCert),
            owl__vkA: OwlBuf::another_ref(&self.owl__vkA),
            owl__k: SecretBuf::another_ref(&self.owl__k),
            owl__sigofK: SecretBuf::another_ref(&self.owl__sigofK),
        }
    }
}

impl View for owl_ClientPKResponse<'_> {
    type V = owlSpec_ClientPKResponse;

    open spec fn view(&self) -> owlSpec_ClientPKResponse {
        owlSpec_ClientPKResponse {
            owlSpec__AuthCert: self.owl__AuthCert.view(),
            owlSpec__vkA: self.owl__vkA.view(),
            owlSpec__k: self.owl__k.view(),
            owlSpec__sigofK: self.owl__sigofK.view(),
        }
    }
}

pub exec fn parse_owl_ClientPKResponse<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_ClientPKResponse<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_ClientPKResponse(arg.view()) is Some,
        res is None ==> parse_owlSpec_ClientPKResponse(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_ClientPKResponse(arg.view())->Some_0,
{
    reveal(parse_owlSpec_ClientPKResponse);
    let exec_comb = exec_combinator_owl_ClientPKResponse();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (((owl__AuthCert, owl__vkA), owl__k), owl__sigofK) = parsed;
        Some(
            owl_ClientPKResponse {
                owl__AuthCert: OwlBuf::another_ref(&owl__AuthCert),
                owl__vkA: OwlBuf::another_ref(&owl__vkA),
                owl__k: SecretBuf::from_buf(owl__k.another_ref()),
                owl__sigofK: SecretBuf::from_buf(owl__sigofK.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_ClientPKResponse_inner<'a>(arg: &owl_ClientPKResponse<'a>) -> (res:
    Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_ClientPKResponse_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_ClientPKResponse_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_ClientPKResponse_inner);
    if no_usize_overflows![ arg.owl__AuthCert.len(), arg.owl__vkA.len(), arg.owl__k.len(), arg.owl__sigofK.len(), 0 ] {
        let exec_comb = exec_combinator_owl_ClientPKResponse();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__AuthCert.len() + arg.owl__vkA.len() + arg.owl__k.len() + arg.owl__sigofK.len()
                + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        SecretBuf::from_buf(arg.owl__AuthCert.another_ref()),
                        SecretBuf::from_buf(arg.owl__vkA.another_ref()),
                    ),
                    SecretBuf::another_ref(&arg.owl__k),
                ),
                SecretBuf::another_ref(&arg.owl__sigofK),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_ClientPKResponse_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_ClientPKResponse<'a>(arg: &owl_ClientPKResponse<'a>) -> (res: SecretBuf<
    'a,
>)
    ensures
        res.view() == serialize_owlSpec_ClientPKResponse(arg.view()),
{
    reveal(serialize_owlSpec_ClientPKResponse);
    let res = serialize_owl_ClientPKResponse_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_secret_ClientPKResponse<'a> {
    pub owl__AuthCert: SecretBuf<'a>,
    pub owl__vkA: SecretBuf<'a>,
    pub owl__k: SecretBuf<'a>,
    pub owl__sigofK: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_secret_ClientPKResponse<'a>(
    arg_owl__AuthCert: SecretBuf<'a>,
    arg_owl__vkA: SecretBuf<'a>,
    arg_owl__k: SecretBuf<'a>,
    arg_owl__sigofK: SecretBuf<'a>,
) -> (res: owl_secret_ClientPKResponse<'a>)
    ensures
        res.owl__AuthCert.view() == arg_owl__AuthCert.view(),
        res.owl__vkA.view() == arg_owl__vkA.view(),
        res.owl__k.view() == arg_owl__k.view(),
        res.owl__sigofK.view() == arg_owl__sigofK.view(),
{
    owl_secret_ClientPKResponse {
        owl__AuthCert: arg_owl__AuthCert,
        owl__vkA: arg_owl__vkA,
        owl__k: arg_owl__k,
        owl__sigofK: arg_owl__sigofK,
    }
}

impl<'a> owl_secret_ClientPKResponse<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_secret_ClientPKResponse<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_secret_ClientPKResponse {
            owl__AuthCert: SecretBuf::another_ref(&self.owl__AuthCert),
            owl__vkA: SecretBuf::another_ref(&self.owl__vkA),
            owl__k: SecretBuf::another_ref(&self.owl__k),
            owl__sigofK: SecretBuf::another_ref(&self.owl__sigofK),
        }
    }
}

impl View for owl_secret_ClientPKResponse<'_> {
    type V = owlSpec_secret_ClientPKResponse;

    open spec fn view(&self) -> owlSpec_secret_ClientPKResponse {
        owlSpec_secret_ClientPKResponse {
            owlSpec__AuthCert: self.owl__AuthCert.view(),
            owlSpec__vkA: self.owl__vkA.view(),
            owlSpec__k: self.owl__k.view(),
            owlSpec__sigofK: self.owl__sigofK.view(),
        }
    }
}

pub exec fn parse_owl_secret_ClientPKResponse<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_secret_ClientPKResponse<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_ClientPKResponse(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_ClientPKResponse(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_ClientPKResponse(
            arg.view(),
        )->Some_0,
{
    reveal(parse_owlSpec_secret_ClientPKResponse);
    let exec_comb = exec_combinator_owl_secret_ClientPKResponse();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (((owl__AuthCert, owl__vkA), owl__k), owl__sigofK) = parsed;
        Some(
            owl_secret_ClientPKResponse {
                owl__AuthCert: SecretBuf::from_buf(owl__AuthCert.another_ref()),
                owl__vkA: SecretBuf::from_buf(owl__vkA.another_ref()),
                owl__k: SecretBuf::from_buf(owl__k.another_ref()),
                owl__sigofK: SecretBuf::from_buf(owl__sigofK.another_ref()),
            },
        )
    } else {
        None
    }
}

pub exec fn secret_parse_owl_secret_ClientPKResponse<'a>(arg: SecretBuf<'a>) -> (res: Option<
    owl_secret_ClientPKResponse<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_secret_ClientPKResponse(arg.view()) is Some,
        res is None ==> parse_owlSpec_secret_ClientPKResponse(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_secret_ClientPKResponse(
            arg.view(),
        )->Some_0,
{
    reveal(parse_owlSpec_secret_ClientPKResponse);
    let exec_comb = exec_combinator_owl_secret_ClientPKResponse();
    if let Ok((_, parsed)) = <_ as Combinator<SecretBuf<'_>, SecretOutputBuf>>::parse(
        &exec_comb,
        arg,
    ) {
        let (((owl__AuthCert, owl__vkA), owl__k), owl__sigofK) = parsed;
        Some(
            owl_secret_ClientPKResponse {
                owl__AuthCert: SecretBuf::another_ref(&owl__AuthCert),
                owl__vkA: SecretBuf::another_ref(&owl__vkA),
                owl__k: SecretBuf::another_ref(&owl__k),
                owl__sigofK: SecretBuf::another_ref(&owl__sigofK),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_secret_ClientPKResponse_inner<'a>(
    arg: &owl_secret_ClientPKResponse<'a>,
) -> (res: Option<SecretBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_secret_ClientPKResponse_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_secret_ClientPKResponse_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_secret_ClientPKResponse_inner);
    if no_usize_overflows![ arg.owl__AuthCert.len(), arg.owl__vkA.len(), arg.owl__k.len(), arg.owl__sigofK.len(), 0 ] {
        let exec_comb = exec_combinator_owl_secret_ClientPKResponse();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl__AuthCert.len() + arg.owl__vkA.len() + arg.owl__k.len() + arg.owl__sigofK.len()
                + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        SecretBuf::another_ref(&arg.owl__AuthCert),
                        SecretBuf::another_ref(&arg.owl__vkA),
                    ),
                    SecretBuf::another_ref(&arg.owl__k),
                ),
                SecretBuf::another_ref(&arg.owl__sigofK),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_secret_ClientPKResponse_inner(
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
pub exec fn serialize_owl_secret_ClientPKResponse<'a>(
    arg: &owl_secret_ClientPKResponse<'a>,
) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_secret_ClientPKResponse(arg.view()),
{
    reveal(serialize_owlSpec_secret_ClientPKResponse);
    let res = serialize_owl_secret_ClientPKResponse_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct state_authserver {}

impl state_authserver {
    #[verifier::external_body]
    pub fn init_state_authserver() -> Self {
        state_authserver {  }
    }
}

pub struct cfg_authserver<'authserver> {
    pub owl_K: SecretBuf<'authserver>,
    pub owl_AK: SecretBuf<'authserver>,
    pub owl_sigkeyA: SecretBuf<'authserver>,
    pub owl_kC: SecretBuf<'authserver>,
    pub owl_kT: SecretBuf<'authserver>,
    pub owl_uname: SecretBuf<'authserver>,
    pub pk_owl_seckeyCnew: OwlBuf<'authserver>,
    pub pk_owl_sigkeyCA: OwlBuf<'authserver>,
    pub pk_owl_sigkeyA: OwlBuf<'authserver>,
    pub pk_owl_sigkeyC: OwlBuf<'authserver>,
}

impl cfg_authserver<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_authserver_pkinit<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_authserver), Endpoint>>,
        mut_state: &mut state_authserver,
        owl_certA452: OwlBuf<'a>,
        owl_vkCA453: OwlBuf<'a>,
        owl_pkC454: OwlBuf<'a>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_authserver), Endpoint>>), OwlError>)
        requires
            itree.view() == authserver_pkinit_spec(
                *self,
                *old(mut_state),
                owl_certA452.view(),
                owl_vkCA453.view(),
                owl_pkC454.view(),
            ),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_authserver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(authserver_pkinit_spec);
            let (tmp_owl_i272, owl__271) = {
                effects.owl_input::<((), state_authserver)>(Tracked(&mut itree))
            };
            let owl_i272 = OwlBuf::from_vec(tmp_owl_i272);
            let parseval_tmp = OwlBuf::another_ref(&owl_i272);
            if let Some(parseval) = parse_owl_pkinit_client_to_authserver_msg(
                OwlBuf::another_ref(&parseval_tmp),
            ) {
                let owl_certC276 = OwlBuf::another_ref(
                    &parseval.owl__pkinit_client_to_authserver_msg_1,
                );
                let owl_vkc275 = OwlBuf::another_ref(
                    &parseval.owl__pkinit_client_to_authserver_msg_2,
                );
                let owl_signed_un274 = OwlBuf::another_ref(
                    &parseval.owl__pkinit_client_to_authserver_msg_3,
                );
                let owl_un273 = OwlBuf::another_ref(
                    &parseval.owl__pkinit_client_to_authserver_msg_4,
                );
                {
                    let parseval_tmp = OwlBuf::another_ref(&owl_certC276);
                    if let Some(parseval) = parse_owl_CertAuthMsgs(
                        OwlBuf::another_ref(&parseval_tmp),
                    ) {
                        let owl_parsed_caseval277 = owl_CertAuthMsgs::another_ref(&parseval);
                        match owl_CertAuthMsgs::another_ref(&owl_parsed_caseval277) {
                            owl_CertAuthMsgs::owl_ClientCert(tmp_owl_certC278) => {
                                let owl_certC278 = OwlBuf::another_ref(&tmp_owl_certC278);
                                let tmp_owl_caseval279 = {
                                    let tracked owl_declassify_tok280 = consume_itree_declassify::<
                                        ((), state_authserver),
                                        Endpoint,
                                    >(&mut itree);
                                    owl_vrfy(
                                        OwlBuf::another_ref(&owl_vkCA453),
                                        SecretBuf::another_ref(
                                            &SecretBuf::from_buf(owl_certC278.another_ref()),
                                        ),
                                        OwlBuf::another_ref(&owl_vkc275),
                                        Tracked(owl_declassify_tok280),
                                    )
                                };
                                let owl_caseval279 = SecretBuf::another_ref_option(
                                    &tmp_owl_caseval279,
                                );
                                match SecretBuf::another_ref_option(&owl_caseval279) {
                                    Option::None => { (owl_unit(), Tracked(itree)) },
                                    Option::Some(tmp_owl_vkC281) => {
                                        let owl_vkC281 = SecretBuf::another_ref(&tmp_owl_vkC281);
                                        let tmp_owl_declassified_buf34282 = {
                                            let tracked owl_declassify_tok283 =
                                                consume_itree_declassify::<
                                                ((), state_authserver),
                                                Endpoint,
                                            >(&mut itree);
                                            {
                                                SecretBuf::another_ref(&owl_vkC281).declassify(
                                                    Tracked(owl_declassify_tok283),
                                                )
                                            }
                                        };
                                        let owl_declassified_buf34282 = OwlBuf::another_ref(
                                            &tmp_owl_declassified_buf34282,
                                        );
                                        let tmp_owl_caseval284 = {
                                            let tracked owl_declassify_tok285 =
                                                consume_itree_declassify::<
                                                ((), state_authserver),
                                                Endpoint,
                                            >(&mut itree);
                                            owl_vrfy(
                                                OwlBuf::another_ref(&owl_declassified_buf34282),
                                                SecretBuf::another_ref(
                                                    &SecretBuf::from_buf(
                                                        owl_signed_un274.another_ref(),
                                                    ),
                                                ),
                                                OwlBuf::another_ref(&owl_un273),
                                                Tracked(owl_declassify_tok285),
                                            )
                                        };
                                        let owl_caseval284 = SecretBuf::another_ref_option(
                                            &tmp_owl_caseval284,
                                        );
                                        match SecretBuf::another_ref_option(&owl_caseval284) {
                                            Option::None => { (owl_unit(), Tracked(itree)) },
                                            Option::Some(tmp_owl_username286) => {
                                                let owl_username286 = SecretBuf::another_ref(
                                                    &tmp_owl_username286,
                                                );
                                                let owl_eq_bool39287 = {
                                                    let tracked owl_declassify_tok288 =
                                                        consume_itree_declassify::<
                                                        ((), state_authserver),
                                                        Endpoint,
                                                    >(&mut itree);
                                                    {
                                                        SecretBuf::secret_eq(
                                                            &owl_username286,
                                                            &SecretBuf::another_ref(
                                                                &self.owl_uname,
                                                            ),
                                                            Tracked(owl_declassify_tok288),
                                                        )
                                                    }
                                                };

                                                if owl_eq_bool39287 {
                                                    let tmp_owl_tgt289 = {
                                                        let tmp_owl_coins290 = effects.owl_sample::<
                                                            ((), state_authserver),
                                                        >(Tracked(&mut itree), NONCE_SIZE);
                                                        let owl_coins290 = SecretBuf::another_ref(
                                                            &tmp_owl_coins290,
                                                        );
                                                        owl_enc(
                                                            SecretBuf::another_ref(
                                                                &SecretBuf::another_ref(
                                                                    &self.owl_kT,
                                                                ),
                                                            ),
                                                            SecretBuf::another_ref(
                                                                &SecretBuf::another_ref(
                                                                    &self.owl_AK,
                                                                ),
                                                            ),
                                                            SecretBuf::another_ref(&owl_coins290),
                                                        )
                                                    };
                                                    let owl_tgt289 = OwlBuf::from_vec(
                                                        tmp_owl_tgt289,
                                                    );
                                                    let owl__291 = {
                                                        effects.owl_output::<
                                                            ((), state_authserver),
                                                        >(
                                                            Tracked(&mut itree),
                                                            owl_tgt289.as_slice(),
                                                            Some(&client_addr()),
                                                            &authserver_addr(),
                                                        );
                                                    };
                                                    let tmp_owl_enc_ak292 = {
                                                        let tmp_owl_coins293 = effects.owl_sample::<
                                                            ((), state_authserver),
                                                        >(Tracked(&mut itree), NONCE_SIZE);
                                                        let owl_coins293 = SecretBuf::another_ref(
                                                            &tmp_owl_coins293,
                                                        );
                                                        owl_enc(
                                                            SecretBuf::another_ref(
                                                                &SecretBuf::another_ref(
                                                                    &self.owl_K,
                                                                ),
                                                            ),
                                                            SecretBuf::another_ref(
                                                                &SecretBuf::another_ref(
                                                                    &self.owl_AK,
                                                                ),
                                                            ),
                                                            SecretBuf::another_ref(&owl_coins293),
                                                        )
                                                    };
                                                    let owl_enc_ak292 = OwlBuf::from_vec(
                                                        tmp_owl_enc_ak292,
                                                    );
                                                    let owl__294 = {
                                                        effects.owl_output::<
                                                            ((), state_authserver),
                                                        >(
                                                            Tracked(&mut itree),
                                                            owl_enc_ak292.as_slice(),
                                                            Some(&client_addr()),
                                                            &authserver_addr(),
                                                        );
                                                    };
                                                    let tmp_owl_sA295 = {
                                                        SecretBuf::another_ref(&self.owl_sigkeyA)
                                                    };
                                                    let owl_sA295 = SecretBuf::another_ref(
                                                        &tmp_owl_sA295,
                                                    );
                                                    let tmp_owl_k__296 = {
                                                        SecretBuf::another_ref(&self.owl_K)
                                                    };
                                                    let owl_k__296 = SecretBuf::another_ref(
                                                        &tmp_owl_k__296,
                                                    );
                                                    let tmp_owl_declassified_buf50297 = {
                                                        let tracked owl_declassify_tok298 =
                                                            consume_itree_declassify::<
                                                            ((), state_authserver),
                                                            Endpoint,
                                                        >(&mut itree);
                                                        {
                                                            SecretBuf::another_ref(
                                                                &owl_k__296,
                                                            ).declassify(
                                                                Tracked(owl_declassify_tok298),
                                                            )
                                                        }
                                                    };
                                                    let owl_declassified_buf50297 =
                                                        OwlBuf::another_ref(
                                                        &tmp_owl_declassified_buf50297,
                                                    );
                                                    let tmp_owl_signed_k299 = {
                                                        owl_sign(
                                                            SecretBuf::another_ref(&owl_sA295),
                                                            OwlBuf::another_ref(
                                                                &owl_declassified_buf50297,
                                                            ),
                                                        )
                                                    };
                                                    let owl_signed_k299 = OwlBuf::from_vec(
                                                        tmp_owl_signed_k299,
                                                    );
                                                    let owl_b300 = {
                                                        owl_signed_k299.len() == SIGNATURE_SIZE
                                                    };

                                                    if owl_b300 {
                                                        let tmp_owl_field1301 = {
                                                            OwlBuf::another_ref(&owl_certA452)
                                                        };
                                                        let owl_field1301 = OwlBuf::another_ref(
                                                            &tmp_owl_field1301,
                                                        );
                                                        let tmp_owl_field2302 = {
                                                            OwlBuf::another_ref(
                                                                &self.pk_owl_sigkeyA,
                                                            )
                                                        };
                                                        let owl_field2302 = OwlBuf::another_ref(
                                                            &tmp_owl_field2302,
                                                        );
                                                        let tmp_owl_field3303 = {
                                                            SecretBuf::another_ref(&self.owl_K)
                                                        };
                                                        let owl_field3303 = SecretBuf::another_ref(
                                                            &tmp_owl_field3303,
                                                        );
                                                        let tmp_owl_field4304 = {
                                                            OwlBuf::another_ref(&owl_signed_k299)
                                                        };
                                                        let owl_field4304 = OwlBuf::another_ref(
                                                            &tmp_owl_field4304,
                                                        );
                                                        let tmp_owl_str305 = {
                                                            owl_ClientPKResponse(
                                                                OwlBuf::another_ref(&owl_field1301),
                                                                OwlBuf::another_ref(&owl_field2302),
                                                                SecretBuf::another_ref(
                                                                    &owl_field3303,
                                                                ),
                                                                SecretBuf::another_ref(
                                                                    &SecretBuf::from_buf(
                                                                        owl_field4304.another_ref(),
                                                                    ),
                                                                ),
                                                            )
                                                        };
                                                        let owl_str305 =
                                                            owl_ClientPKResponse::another_ref(
                                                            &tmp_owl_str305,
                                                        );
                                                        let tmp_owl_msg306 = {
                                                            owl_pkenc(
                                                                OwlBuf::another_ref(&owl_pkC454),
                                                                SecretBuf::another_ref(
                                                                    &serialize_owl_ClientPKResponse(
                                                                        &owl_str305,
                                                                    ),
                                                                ),
                                                            )
                                                        };
                                                        let owl_msg306 = OwlBuf::from_vec(
                                                            tmp_owl_msg306,
                                                        );
                                                        let owl__307 = {
                                                            effects.owl_output::<
                                                                ((), state_authserver),
                                                            >(
                                                                Tracked(&mut itree),
                                                                owl_msg306.as_slice(),
                                                                Some(&client_addr()),
                                                                &authserver_addr(),
                                                            );
                                                        };
                                                        (owl_unit(), Tracked(itree))
                                                    } else {
                                                        (owl_unit(), Tracked(itree))
                                                    }

                                                } else {
                                                    (owl_unit(), Tracked(itree))
                                                }

                                            },
                                        }
                                    },
                                }
                            },
                            owl_CertAuthMsgs::owl_AuthCert(tmp_owl_x308) => {
                                let owl_x308 = OwlBuf::another_ref(&tmp_owl_x308);
                                (owl_unit(), Tracked(itree))
                            },
                        }
                    } else {
                        (owl_unit(), Tracked(itree))
                    }
                }
            } else {
                (owl_unit(), Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_authserver_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_authserver), Endpoint>>,
        mut_state: &mut state_authserver,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_authserver), Endpoint>>), OwlError>)
        requires
            itree.view() == authserver_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_authserver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(authserver_main_spec);
            let (tmp_owl_i310, owl__309) = {
                effects.owl_input::<((), state_authserver)>(Tracked(&mut itree))
            };
            let owl_i310 = OwlBuf::from_vec(tmp_owl_i310);
            let owl_eq_bool66311 = {
                let tracked owl_declassify_tok312 = consume_itree_declassify::<
                    ((), state_authserver),
                    Endpoint,
                >(&mut itree);
                {
                    SecretBuf::secret_eq(
                        &SecretBuf::from_buf(owl_i310.another_ref()),
                        &SecretBuf::another_ref(&self.owl_uname),
                        Tracked(owl_declassify_tok312),
                    )
                }
            };

            if owl_eq_bool66311 {
                let tmp_owl_tgt313 = {
                    let tmp_owl_coins314 = effects.owl_sample::<((), state_authserver)>(
                        Tracked(&mut itree),
                        NONCE_SIZE,
                    );
                    let owl_coins314 = SecretBuf::another_ref(&tmp_owl_coins314);
                    owl_enc(
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_kT)),
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_AK)),
                        SecretBuf::another_ref(&owl_coins314),
                    )
                };
                let owl_tgt313 = OwlBuf::from_vec(tmp_owl_tgt313);
                let tmp_owl_m315 = {
                    let tmp_owl_coins316 = effects.owl_sample::<((), state_authserver)>(
                        Tracked(&mut itree),
                        NONCE_SIZE,
                    );
                    let owl_coins316 = SecretBuf::another_ref(&tmp_owl_coins316);
                    owl_enc(
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_kC)),
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_AK)),
                        SecretBuf::another_ref(&owl_coins316),
                    )
                };
                let owl_m315 = OwlBuf::from_vec(tmp_owl_m315);
                let tmp_owl_p317 = {
                    owl_authserver_msg(
                        OwlBuf::another_ref(&owl_tgt313),
                        OwlBuf::another_ref(&owl_m315),
                    )
                };
                let owl_p317 = owl_authserver_msg::another_ref(&tmp_owl_p317);
                let owl__318 = {
                    effects.owl_output::<((), state_authserver)>(
                        Tracked(&mut itree),
                        serialize_owl_authserver_msg(&owl_p317).as_slice(),
                        Some(&client_addr()),
                        &authserver_addr(),
                    );
                };
                (owl_unit(), Tracked(itree))
            } else {
                (owl_unit(), Tracked(itree))
            }

        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub struct state_certauth {}

impl state_certauth {
    #[verifier::external_body]
    pub fn init_state_certauth() -> Self {
        state_certauth {  }
    }
}

pub struct cfg_certauth<'certauth> {
    pub owl_sigkeyCA: SecretBuf<'certauth>,
    pub owl_uname: SecretBuf<'certauth>,
    pub pk_owl_seckeyCnew: OwlBuf<'certauth>,
    pub pk_owl_sigkeyCA: OwlBuf<'certauth>,
    pub pk_owl_sigkeyA: OwlBuf<'certauth>,
    pub pk_owl_sigkeyC: OwlBuf<'certauth>,
}

impl cfg_certauth<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_certauth_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_certauth), Endpoint>>,
        mut_state: &mut state_certauth,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_certauth), Endpoint>>), OwlError>)
        requires
            itree.view() == certauth_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_certauth), Endpoint>>) =
            {
            broadcast use itree_axioms;

            reveal(certauth_main_spec);
            (owl_unit(), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub struct state_client {}

impl state_client {
    #[verifier::external_body]
    pub fn init_state_client() -> Self {
        state_client {  }
    }
}

pub struct cfg_client<'client> {
    pub owl_seckeyCnew: SecretBuf<'client>,
    pub owl_sigkeyC: SecretBuf<'client>,
    pub owl_kC: SecretBuf<'client>,
    pub owl_uname: SecretBuf<'client>,
    pub pk_owl_seckeyCnew: OwlBuf<'client>,
    pub pk_owl_sigkeyCA: OwlBuf<'client>,
    pub pk_owl_sigkeyA: OwlBuf<'client>,
    pub pk_owl_sigkeyC: OwlBuf<'client>,
}

impl cfg_client<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_client_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_client), Endpoint>>,
        mut_state: &mut state_client,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_client), Endpoint>>), OwlError>)
        requires
            itree.view() == client_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_client), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(client_main_spec);
            let tmp_owl_username319 = { SecretBuf::another_ref(&self.owl_uname) };
            let owl_username319 = SecretBuf::another_ref(&tmp_owl_username319);
            let tmp_owl_declassified_buf76320 = {
                let tracked owl_declassify_tok321 = consume_itree_declassify::<
                    ((), state_client),
                    Endpoint,
                >(&mut itree);
                {
                    SecretBuf::another_ref(&owl_username319).declassify(
                        Tracked(owl_declassify_tok321),
                    )
                }
            };
            let owl_declassified_buf76320 = OwlBuf::another_ref(&tmp_owl_declassified_buf76320);
            let owl__322 = {
                effects.owl_output::<((), state_client)>(
                    Tracked(&mut itree),
                    owl_declassified_buf76320.as_slice(),
                    Some(&authserver_addr()),
                    &client_addr(),
                );
            };
            let (tmp_owl_i324, owl__323) = {
                effects.owl_input::<((), state_client)>(Tracked(&mut itree))
            };
            let owl_i324 = OwlBuf::from_vec(tmp_owl_i324);
            let parseval_tmp = OwlBuf::another_ref(&owl_i324);
            if let Some(parseval) = parse_owl_authserver_msg(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_tgt326 = OwlBuf::another_ref(&parseval.owl__authserver_msg_1);
                let owl_c325 = OwlBuf::another_ref(&parseval.owl__authserver_msg_2);
                let tmp_owl_caseval327 = {
                    let tracked owl_declassify_tok328 = consume_itree_declassify::<
                        ((), state_client),
                        Endpoint,
                    >(&mut itree);
                    owl_dec(
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_kC)),
                        OwlBuf::another_ref(&owl_c325),
                        Tracked(owl_declassify_tok328),
                    )
                };
                let owl_caseval327 = SecretBuf::another_ref_option(&tmp_owl_caseval327);
                {
                    match SecretBuf::another_ref_option(&owl_caseval327) {
                        Option::None => { (owl_unit(), Tracked(itree)) },
                        Option::Some(tmp_owl_ak329) => {
                            let owl_ak329 = SecretBuf::another_ref(&tmp_owl_ak329);
                            let tmp_owl_declassified_buf92330 = {
                                let tracked owl_declassify_tok331 = consume_itree_declassify::<
                                    ((), state_client),
                                    Endpoint,
                                >(&mut itree);
                                {
                                    SecretBuf::another_ref(&owl_username319).declassify(
                                        Tracked(owl_declassify_tok331),
                                    )
                                }
                            };
                            let owl_declassified_buf92330 = OwlBuf::another_ref(
                                &tmp_owl_declassified_buf92330,
                            );
                            let tmp_arg1455 = SecretBuf::another_ref(&owl_ak329);
                            let tmp_arg2456 = OwlBuf::another_ref(&owl_tgt326);
                            let tmp_arg3457 = OwlBuf::another_ref(&owl_declassified_buf92330);
                            owl_call_ret_unit!(effects, itree, *mut_state, client_kerberos_spec(*self, *mut_state, tmp_arg1455.view(), tmp_arg2456.view(), tmp_arg3457.view()), self.owl_client_kerberos(mut_state, tmp_arg1455, tmp_arg2456, tmp_arg3457))
                        },
                    }
                }
            } else {
                (owl_unit(), Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_client_pkinit<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_client), Endpoint>>,
        mut_state: &mut state_client,
        owl_certC458: OwlBuf<'a>,
        owl_vkCA459: OwlBuf<'a>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_client), Endpoint>>), OwlError>)
        requires
            itree.view() == client_pkinit_spec(
                *self,
                *old(mut_state),
                owl_certC458.view(),
                owl_vkCA459.view(),
            ),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_client), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(client_pkinit_spec);
            let tmp_owl_username334 = { SecretBuf::another_ref(&self.owl_uname) };
            let owl_username334 = SecretBuf::another_ref(&tmp_owl_username334);
            let tmp_owl_declassified_buf98335 = {
                let tracked owl_declassify_tok336 = consume_itree_declassify::<
                    ((), state_client),
                    Endpoint,
                >(&mut itree);
                {
                    SecretBuf::another_ref(&owl_username334).declassify(
                        Tracked(owl_declassify_tok336),
                    )
                }
            };
            let owl_declassified_buf98335 = OwlBuf::another_ref(&tmp_owl_declassified_buf98335);
            let tmp_owl_signed_name337 = {
                owl_sign(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_sigkeyC)),
                    OwlBuf::another_ref(&owl_declassified_buf98335),
                )
            };
            let owl_signed_name337 = OwlBuf::from_vec(tmp_owl_signed_name337);
            let tmp_owl_declassified_buf102338 = {
                let tracked owl_declassify_tok339 = consume_itree_declassify::<
                    ((), state_client),
                    Endpoint,
                >(&mut itree);
                {
                    SecretBuf::another_ref(&owl_username334).declassify(
                        Tracked(owl_declassify_tok339),
                    )
                }
            };
            let owl_declassified_buf102338 = OwlBuf::another_ref(&tmp_owl_declassified_buf102338);
            let tmp_owl_p340 = {
                owl_pkinit_client_to_authserver_msg(
                    OwlBuf::another_ref(&owl_certC458),
                    OwlBuf::another_ref(&OwlBuf::another_ref(&self.pk_owl_sigkeyC)),
                    OwlBuf::another_ref(&owl_signed_name337),
                    OwlBuf::another_ref(&owl_declassified_buf102338),
                )
            };
            let owl_p340 = owl_pkinit_client_to_authserver_msg::another_ref(&tmp_owl_p340);
            let owl__341 = {
                effects.owl_output::<((), state_client)>(
                    Tracked(&mut itree),
                    serialize_owl_pkinit_client_to_authserver_msg(&owl_p340).as_slice(),
                    Some(&authserver_addr()),
                    &client_addr(),
                );
            };
            let (tmp_owl_tgt343, owl__342) = {
                effects.owl_input::<((), state_client)>(Tracked(&mut itree))
            };
            let owl_tgt343 = OwlBuf::from_vec(tmp_owl_tgt343);
            let (tmp_owl_enc_ak345, owl__344) = {
                effects.owl_input::<((), state_client)>(Tracked(&mut itree))
            };
            let owl_enc_ak345 = OwlBuf::from_vec(tmp_owl_enc_ak345);
            let (tmp_owl_msg347, owl__346) = {
                effects.owl_input::<((), state_client)>(Tracked(&mut itree))
            };
            let owl_msg347 = OwlBuf::from_vec(tmp_owl_msg347);
            let tmp_owl_caseval348 = {
                let tracked owl_declassify_tok349 = consume_itree_declassify::<
                    ((), state_client),
                    Endpoint,
                >(&mut itree);
                owl_pkdec(
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_seckeyCnew)),
                    OwlBuf::another_ref(&owl_msg347),
                    Tracked(owl_declassify_tok349),
                )
            };
            let owl_caseval348 = SecretBuf::another_ref_option(&tmp_owl_caseval348);
            match SecretBuf::another_ref_option(&owl_caseval348) {
                Option::None => { (owl_unit(), Tracked(itree)) },
                Option::Some(tmp_owl_p_350) => {
                    let owl_p_350 = SecretBuf::another_ref(&tmp_owl_p_350);
                    let parseval_tmp = SecretBuf::another_ref(&owl_p_350);
                    if let Some(parseval) = secret_parse_owl_secret_ClientPKResponse(
                        SecretBuf::another_ref(&parseval_tmp),
                    ) {
                        let owl_certA354 = SecretBuf::another_ref(&parseval.owl__AuthCert);
                        let owl_vka353 = SecretBuf::another_ref(&parseval.owl__vkA);
                        let owl_k352 = SecretBuf::another_ref(&parseval.owl__k);
                        let owl_ksig351 = SecretBuf::another_ref(&parseval.owl__sigofK);
                        let tmp_owl_declassified_buf124355 = {
                            let tracked owl_declassify_tok356 = consume_itree_declassify::<
                                ((), state_client),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_certA354).declassify(
                                    Tracked(owl_declassify_tok356),
                                )
                            }
                        };
                        let owl_declassified_buf124355 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf124355,
                        );
                        let tmp_owl_declassified_buf127357 = {
                            let tracked owl_declassify_tok358 = consume_itree_declassify::<
                                ((), state_client),
                                Endpoint,
                            >(&mut itree);
                            {
                                SecretBuf::another_ref(&owl_vka353).declassify(
                                    Tracked(owl_declassify_tok358),
                                )
                            }
                        };
                        let owl_declassified_buf127357 = OwlBuf::another_ref(
                            &tmp_owl_declassified_buf127357,
                        );
                        let tmp_owl_caseval359 = {
                            let tracked owl_declassify_tok360 = consume_itree_declassify::<
                                ((), state_client),
                                Endpoint,
                            >(&mut itree);
                            owl_vrfy(
                                OwlBuf::another_ref(&owl_vkCA459),
                                SecretBuf::another_ref(
                                    &SecretBuf::from_buf(owl_declassified_buf124355.another_ref()),
                                ),
                                OwlBuf::another_ref(&owl_declassified_buf127357),
                                Tracked(owl_declassify_tok360),
                            )
                        };
                        let owl_caseval359 = SecretBuf::another_ref_option(&tmp_owl_caseval359);
                        {
                            match SecretBuf::another_ref_option(&owl_caseval359) {
                                Option::Some(tmp_owl_res361) => {
                                    let owl_res361 = SecretBuf::another_ref(&tmp_owl_res361);
                                    let tmp_owl_declassified_buf151362 = {
                                        let tracked owl_declassify_tok363 =
                                            consume_itree_declassify::<
                                            ((), state_client),
                                            Endpoint,
                                        >(&mut itree);
                                        {
                                            SecretBuf::another_ref(&owl_res361).declassify(
                                                Tracked(owl_declassify_tok363),
                                            )
                                        }
                                    };
                                    let owl_declassified_buf151362 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf151362,
                                    );
                                    let parseval_tmp = OwlBuf::another_ref(
                                        &owl_declassified_buf151362,
                                    );
                                    if let Some(parseval) = parse_owl_CertAuthMsgs(
                                        OwlBuf::another_ref(&parseval_tmp),
                                    ) {
                                        let owl_parsed_caseval364 = owl_CertAuthMsgs::another_ref(
                                            &parseval,
                                        );
                                        match owl_CertAuthMsgs::another_ref(
                                            &owl_parsed_caseval364,
                                        ) {
                                            owl_CertAuthMsgs::owl_ClientCert(tmp_owl__365) => {
                                                let owl__365 = OwlBuf::another_ref(&tmp_owl__365);
                                                (owl_unit(), Tracked(itree))
                                            },
                                            owl_CertAuthMsgs::owl_AuthCert(tmp_owl_vkA366) => {
                                                let owl_vkA366 = OwlBuf::another_ref(
                                                    &tmp_owl_vkA366,
                                                );
                                                let tmp_owl_declassified_buf136367 = {
                                                    let tracked owl_declassify_tok368 =
                                                        consume_itree_declassify::<
                                                        ((), state_client),
                                                        Endpoint,
                                                    >(&mut itree);
                                                    {
                                                        SecretBuf::another_ref(
                                                            &owl_ksig351,
                                                        ).declassify(Tracked(owl_declassify_tok368))
                                                    }
                                                };
                                                let owl_declassified_buf136367 =
                                                    OwlBuf::another_ref(
                                                    &tmp_owl_declassified_buf136367,
                                                );
                                                let tmp_owl_caseval369 = {
                                                    let tracked owl_declassify_tok370 =
                                                        consume_itree_declassify::<
                                                        ((), state_client),
                                                        Endpoint,
                                                    >(&mut itree);
                                                    owl_vrfy(
                                                        OwlBuf::another_ref(&owl_vkA366),
                                                        SecretBuf::another_ref(&owl_k352),
                                                        OwlBuf::another_ref(
                                                            &owl_declassified_buf136367,
                                                        ),
                                                        Tracked(owl_declassify_tok370),
                                                    )
                                                };
                                                let owl_caseval369 = SecretBuf::another_ref_option(
                                                    &tmp_owl_caseval369,
                                                );
                                                match SecretBuf::another_ref_option(
                                                    &owl_caseval369,
                                                ) {
                                                    Option::Some(tmp_owl_k371) => {
                                                        let owl_k371 = SecretBuf::another_ref(
                                                            &tmp_owl_k371,
                                                        );
                                                        let tmp_owl_caseval372 = {
                                                            let tracked owl_declassify_tok373 =
                                                                consume_itree_declassify::<
                                                                ((), state_client),
                                                                Endpoint,
                                                            >(&mut itree);
                                                            owl_dec(
                                                                SecretBuf::another_ref(&owl_k371),
                                                                OwlBuf::another_ref(&owl_enc_ak345),
                                                                Tracked(owl_declassify_tok373),
                                                            )
                                                        };
                                                        let owl_caseval372 =
                                                            SecretBuf::another_ref_option(
                                                            &tmp_owl_caseval372,
                                                        );
                                                        match SecretBuf::another_ref_option(
                                                            &owl_caseval372,
                                                        ) {
                                                            Option::Some(tmp_owl_ak374) => {
                                                                let owl_ak374 =
                                                                    SecretBuf::another_ref(
                                                                    &tmp_owl_ak374,
                                                                );
                                                                let tmp_owl_declassified_buf147375 =
                                                                    {
                                                                    let tracked owl_declassify_tok376 =
                                                                        consume_itree_declassify::<
                                                                        ((), state_client),
                                                                        Endpoint,
                                                                    >(&mut itree);
                                                                    {
                                                                        SecretBuf::another_ref(
                                                                            &owl_username334,
                                                                        ).declassify(
                                                                            Tracked(
                                                                                owl_declassify_tok376,
                                                                            ),
                                                                        )
                                                                    }
                                                                };
                                                                let owl_declassified_buf147375 =
                                                                    OwlBuf::another_ref(
                                                                    &tmp_owl_declassified_buf147375,
                                                                );
                                                                let tmp_arg1460 =
                                                                    SecretBuf::another_ref(
                                                                    &owl_ak374,
                                                                );
                                                                let tmp_arg2461 =
                                                                    OwlBuf::another_ref(
                                                                    &owl_tgt343,
                                                                );
                                                                let tmp_arg3462 =
                                                                    OwlBuf::another_ref(
                                                                    &owl_declassified_buf147375,
                                                                );
                                                                owl_call_ret_unit!(effects, itree, *mut_state, client_kerberos_tmpcopy_spec(*self, *mut_state, tmp_arg1460.view(), tmp_arg2461.view(), tmp_arg3462.view()), self.owl_client_kerberos_tmpcopy(mut_state, tmp_arg1460, tmp_arg2461, tmp_arg3462))
                                                            },
                                                            Option::None => {
                                                                (owl_unit(), Tracked(itree))
                                                            },
                                                        }
                                                    },
                                                    Option::None => { (owl_unit(), Tracked(itree))
                                                    },
                                                }
                                            },
                                        }
                                    } else {
                                        (owl_unit(), Tracked(itree))
                                    }
                                },
                                Option::None => { (owl_unit(), Tracked(itree)) },
                            }
                        }
                    } else {
                        (owl_unit(), Tracked(itree))
                    }
                },
            }
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_client_kerberos_tmpcopy<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_client), Endpoint>>,
        mut_state: &mut state_client,
        owl_ak463: SecretBuf<'_>,
        owl_tgt464: OwlBuf<'a>,
        owl_username465: OwlBuf<'a>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_client), Endpoint>>), OwlError>)
        requires
            itree.view() == client_kerberos_tmpcopy_spec(
                *self,
                *old(mut_state),
                owl_ak463.view(),
                owl_tgt464.view(),
                owl_username465.view(),
            ),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_client), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(client_kerberos_tmpcopy_spec);
            let tmp_owl_m380 = {
                let tmp_owl_coins381 = effects.owl_sample::<((), state_client)>(
                    Tracked(&mut itree),
                    NONCE_SIZE,
                );
                let owl_coins381 = SecretBuf::another_ref(&tmp_owl_coins381);
                owl_enc(
                    SecretBuf::another_ref(&owl_ak463),
                    SecretBuf::another_ref(
                        &OwlBuf::from_vec(serialize_owl_AKEnum(&owl_ClientRequest())).into_secret(),
                    ),
                    SecretBuf::another_ref(&owl_coins381),
                )
            };
            let owl_m380 = OwlBuf::from_vec(tmp_owl_m380);
            let tmp_owl_p382 = {
                owl_client_to_ticketserver_msg(
                    OwlBuf::another_ref(&owl_tgt464),
                    OwlBuf::another_ref(&owl_m380),
                )
            };
            let owl_p382 = owl_client_to_ticketserver_msg::another_ref(&tmp_owl_p382);
            let owl__383 = {
                effects.owl_output::<((), state_client)>(
                    Tracked(&mut itree),
                    serialize_owl_client_to_ticketserver_msg(&owl_p382).as_slice(),
                    Some(&ticketserver_addr()),
                    &client_addr(),
                );
            };
            let (tmp_owl_i_385, owl__384) = {
                effects.owl_input::<((), state_client)>(Tracked(&mut itree))
            };
            let owl_i_385 = OwlBuf::from_vec(tmp_owl_i_385);
            let parseval_tmp = OwlBuf::another_ref(&owl_i_385);
            if let Some(parseval) = parse_owl_ticketserver_msg(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_service_ticket387 = OwlBuf::another_ref(&parseval.owl__ticketserver_msg_1);
                let owl_c386 = OwlBuf::another_ref(&parseval.owl__ticketserver_msg_2);
                let tmp_owl_caseval388 = {
                    let tracked owl_declassify_tok389 = consume_itree_declassify::<
                        ((), state_client),
                        Endpoint,
                    >(&mut itree);
                    owl_dec(
                        SecretBuf::another_ref(&owl_ak463),
                        OwlBuf::another_ref(&owl_c386),
                        Tracked(owl_declassify_tok389),
                    )
                };
                let owl_caseval388 = SecretBuf::another_ref_option(&tmp_owl_caseval388);
                {
                    match SecretBuf::another_ref_option(&owl_caseval388) {
                        Option::None => { (owl_unit(), Tracked(itree)) },
                        Option::Some(tmp_owl_res390) => {
                            let owl_res390 = SecretBuf::another_ref(&tmp_owl_res390);
                            let tracked owl_declassify_tok391 = consume_itree_declassify::<
                                ((), state_client),
                                Endpoint,
                            >(&mut itree);
                            let parseval_tmp = SecretBuf::another_ref(&owl_res390);
                            if let Some(parseval) = secret_parse_owl_AKEnum(
                                SecretBuf::another_ref(&parseval_tmp),
                                Tracked(owl_declassify_tok391),
                            ) {
                                let owl_parsed_caseval392 = owl_AKEnum::another_ref(&parseval);
                                match owl_AKEnum::another_ref(&owl_parsed_caseval392) {
                                    owl_AKEnum::owl_ClientRequest() => {
                                        (owl_unit(), Tracked(itree))
                                    },
                                    owl_AKEnum::owl_TicketResponse(tmp_owl_sk393) => {
                                        let owl_sk393 = SecretBuf::another_ref(&tmp_owl_sk393);
                                        let tmp_owl_m_394 = {
                                            let tmp_owl_coins395 = effects.owl_sample::<
                                                ((), state_client),
                                            >(Tracked(&mut itree), NONCE_SIZE);
                                            let owl_coins395 = SecretBuf::another_ref(
                                                &tmp_owl_coins395,
                                            );
                                            owl_enc(
                                                SecretBuf::another_ref(&owl_sk393),
                                                SecretBuf::another_ref(
                                                    &SecretBuf::from_buf(
                                                        owl_username465.another_ref(),
                                                    ),
                                                ),
                                                SecretBuf::another_ref(&owl_coins395),
                                            )
                                        };
                                        let owl_m_394 = OwlBuf::from_vec(tmp_owl_m_394);
                                        let tmp_owl_p_396 = {
                                            owl_client_to_service_msg(
                                                OwlBuf::another_ref(&owl_service_ticket387),
                                                OwlBuf::another_ref(&owl_m_394),
                                            )
                                        };
                                        let owl_p_396 = owl_client_to_service_msg::another_ref(
                                            &tmp_owl_p_396,
                                        );
                                        let owl__397 = {
                                            effects.owl_output::<((), state_client)>(
                                                Tracked(&mut itree),
                                                serialize_owl_client_to_service_msg(
                                                    &owl_p_396,
                                                ).as_slice(),
                                                Some(&service_addr()),
                                                &client_addr(),
                                            );
                                        };
                                        let (tmp_owl__399, owl__398) = {
                                            effects.owl_input::<((), state_client)>(
                                                Tracked(&mut itree),
                                            )
                                        };
                                        let owl__399 = OwlBuf::from_vec(tmp_owl__399);
                                        (owl_unit(), Tracked(itree))
                                    },
                                }
                            } else {
                                (owl_unit(), Tracked(itree))
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

    #[verifier::spinoff_prover]
    pub fn owl_client_kerberos<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_client), Endpoint>>,
        mut_state: &mut state_client,
        owl_ak466: SecretBuf<'_>,
        owl_tgt467: OwlBuf<'a>,
        owl_username468: OwlBuf<'a>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_client), Endpoint>>), OwlError>)
        requires
            itree.view() == client_kerberos_spec(
                *self,
                *old(mut_state),
                owl_ak466.view(),
                owl_tgt467.view(),
                owl_username468.view(),
            ),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_client), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(client_kerberos_spec);
            let tmp_owl_m403 = {
                let tmp_owl_coins404 = effects.owl_sample::<((), state_client)>(
                    Tracked(&mut itree),
                    NONCE_SIZE,
                );
                let owl_coins404 = SecretBuf::another_ref(&tmp_owl_coins404);
                owl_enc(
                    SecretBuf::another_ref(&owl_ak466),
                    SecretBuf::another_ref(
                        &OwlBuf::from_vec(serialize_owl_AKEnum(&owl_ClientRequest())).into_secret(),
                    ),
                    SecretBuf::another_ref(&owl_coins404),
                )
            };
            let owl_m403 = OwlBuf::from_vec(tmp_owl_m403);
            let tmp_owl_p405 = {
                owl_client_to_ticketserver_msg(
                    OwlBuf::another_ref(&owl_tgt467),
                    OwlBuf::another_ref(&owl_m403),
                )
            };
            let owl_p405 = owl_client_to_ticketserver_msg::another_ref(&tmp_owl_p405);
            let owl__406 = {
                effects.owl_output::<((), state_client)>(
                    Tracked(&mut itree),
                    serialize_owl_client_to_ticketserver_msg(&owl_p405).as_slice(),
                    Some(&ticketserver_addr()),
                    &client_addr(),
                );
            };
            let (tmp_owl_i_408, owl__407) = {
                effects.owl_input::<((), state_client)>(Tracked(&mut itree))
            };
            let owl_i_408 = OwlBuf::from_vec(tmp_owl_i_408);
            let parseval_tmp = OwlBuf::another_ref(&owl_i_408);
            if let Some(parseval) = parse_owl_ticketserver_msg(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_service_ticket410 = OwlBuf::another_ref(&parseval.owl__ticketserver_msg_1);
                let owl_c409 = OwlBuf::another_ref(&parseval.owl__ticketserver_msg_2);
                let tmp_owl_caseval411 = {
                    let tracked owl_declassify_tok412 = consume_itree_declassify::<
                        ((), state_client),
                        Endpoint,
                    >(&mut itree);
                    owl_dec(
                        SecretBuf::another_ref(&owl_ak466),
                        OwlBuf::another_ref(&owl_c409),
                        Tracked(owl_declassify_tok412),
                    )
                };
                let owl_caseval411 = SecretBuf::another_ref_option(&tmp_owl_caseval411);
                {
                    match SecretBuf::another_ref_option(&owl_caseval411) {
                        Option::None => { (owl_unit(), Tracked(itree)) },
                        Option::Some(tmp_owl_res413) => {
                            let owl_res413 = SecretBuf::another_ref(&tmp_owl_res413);
                            let tracked owl_declassify_tok414 = consume_itree_declassify::<
                                ((), state_client),
                                Endpoint,
                            >(&mut itree);
                            let parseval_tmp = SecretBuf::another_ref(&owl_res413);
                            if let Some(parseval) = secret_parse_owl_AKEnum(
                                SecretBuf::another_ref(&parseval_tmp),
                                Tracked(owl_declassify_tok414),
                            ) {
                                let owl_parsed_caseval415 = owl_AKEnum::another_ref(&parseval);
                                match owl_AKEnum::another_ref(&owl_parsed_caseval415) {
                                    owl_AKEnum::owl_ClientRequest() => {
                                        (owl_unit(), Tracked(itree))
                                    },
                                    owl_AKEnum::owl_TicketResponse(tmp_owl_sk416) => {
                                        let owl_sk416 = SecretBuf::another_ref(&tmp_owl_sk416);
                                        let tmp_owl_m_417 = {
                                            let tmp_owl_coins418 = effects.owl_sample::<
                                                ((), state_client),
                                            >(Tracked(&mut itree), NONCE_SIZE);
                                            let owl_coins418 = SecretBuf::another_ref(
                                                &tmp_owl_coins418,
                                            );
                                            owl_enc(
                                                SecretBuf::another_ref(&owl_sk416),
                                                SecretBuf::another_ref(
                                                    &SecretBuf::from_buf(
                                                        owl_username468.another_ref(),
                                                    ),
                                                ),
                                                SecretBuf::another_ref(&owl_coins418),
                                            )
                                        };
                                        let owl_m_417 = OwlBuf::from_vec(tmp_owl_m_417);
                                        let tmp_owl_p_419 = {
                                            owl_client_to_service_msg(
                                                OwlBuf::another_ref(&owl_service_ticket410),
                                                OwlBuf::another_ref(&owl_m_417),
                                            )
                                        };
                                        let owl_p_419 = owl_client_to_service_msg::another_ref(
                                            &tmp_owl_p_419,
                                        );
                                        let owl__420 = {
                                            effects.owl_output::<((), state_client)>(
                                                Tracked(&mut itree),
                                                serialize_owl_client_to_service_msg(
                                                    &owl_p_419,
                                                ).as_slice(),
                                                Some(&service_addr()),
                                                &client_addr(),
                                            );
                                        };
                                        let (tmp_owl__422, owl__421) = {
                                            effects.owl_input::<((), state_client)>(
                                                Tracked(&mut itree),
                                            )
                                        };
                                        let owl__422 = OwlBuf::from_vec(tmp_owl__422);
                                        (owl_unit(), Tracked(itree))
                                    },
                                }
                            } else {
                                (owl_unit(), Tracked(itree))
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

pub struct state_service {}

impl state_service {
    #[verifier::external_body]
    pub fn init_state_service() -> Self {
        state_service {  }
    }
}

pub struct cfg_service<'service> {
    pub owl_kS: SecretBuf<'service>,
    pub owl_uname: SecretBuf<'service>,
    pub pk_owl_seckeyCnew: OwlBuf<'service>,
    pub pk_owl_sigkeyCA: OwlBuf<'service>,
    pub pk_owl_sigkeyA: OwlBuf<'service>,
    pub pk_owl_sigkeyC: OwlBuf<'service>,
}

impl cfg_service<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_service_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_service), Endpoint>>,
        mut_state: &mut state_service,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_service), Endpoint>>), OwlError>)
        requires
            itree.view() == service_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_service), Endpoint>>) =
            {
            broadcast use itree_axioms;

            reveal(service_main_spec);
            let (tmp_owl_i424, owl__423) = {
                effects.owl_input::<((), state_service)>(Tracked(&mut itree))
            };
            let owl_i424 = OwlBuf::from_vec(tmp_owl_i424);
            let parseval_tmp = OwlBuf::another_ref(&owl_i424);
            if let Some(parseval) = parse_owl_client_to_service_msg(
                OwlBuf::another_ref(&parseval_tmp),
            ) {
                let owl_c1426 = OwlBuf::another_ref(&parseval.owl__client_to_service_msg_1);
                let owl_c2425 = OwlBuf::another_ref(&parseval.owl__client_to_service_msg_2);
                let tmp_owl_caseval427 = {
                    let tracked owl_declassify_tok428 = consume_itree_declassify::<
                        ((), state_service),
                        Endpoint,
                    >(&mut itree);
                    owl_dec(
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_kS)),
                        OwlBuf::another_ref(&owl_c1426),
                        Tracked(owl_declassify_tok428),
                    )
                };
                let owl_caseval427 = SecretBuf::another_ref_option(&tmp_owl_caseval427);
                {
                    match SecretBuf::another_ref_option(&owl_caseval427) {
                        Option::None => { (owl_unit(), Tracked(itree)) },
                        Option::Some(tmp_owl_sk429) => {
                            let owl_sk429 = SecretBuf::another_ref(&tmp_owl_sk429);
                            let tmp_owl_caseval430 = {
                                let tracked owl_declassify_tok431 = consume_itree_declassify::<
                                    ((), state_service),
                                    Endpoint,
                                >(&mut itree);
                                owl_dec(
                                    SecretBuf::another_ref(&owl_sk429),
                                    OwlBuf::another_ref(&owl_c2425),
                                    Tracked(owl_declassify_tok431),
                                )
                            };
                            let owl_caseval430 = SecretBuf::another_ref_option(&tmp_owl_caseval430);
                            match SecretBuf::another_ref_option(&owl_caseval430) {
                                Option::None => { (owl_unit(), Tracked(itree)) },
                                Option::Some(tmp_owl_u432) => {
                                    let owl_u432 = SecretBuf::another_ref(&tmp_owl_u432);
                                    let owl_eq_bool216433 = {
                                        let tracked owl_declassify_tok434 =
                                            consume_itree_declassify::<
                                            ((), state_service),
                                            Endpoint,
                                        >(&mut itree);
                                        {
                                            SecretBuf::secret_eq(
                                                &owl_u432,
                                                &SecretBuf::another_ref(&self.owl_uname),
                                                Tracked(owl_declassify_tok434),
                                            )
                                        }
                                    };

                                    if owl_eq_bool216433 {
                                        let owl__435 = {
                                            effects.owl_output::<((), state_service)>(
                                                Tracked(&mut itree),
                                                {
                                                    let x = mk_vec_u8![];
                                                    OwlBuf::from_vec(x)
                                                }.as_slice(),
                                                Some(&client_addr()),
                                                &service_addr(),
                                            );
                                        };
                                        (owl_unit(), Tracked(itree))
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

pub struct state_ticketserver {}

impl state_ticketserver {
    #[verifier::external_body]
    pub fn init_state_ticketserver() -> Self {
        state_ticketserver {  }
    }
}

pub struct cfg_ticketserver<'ticketserver> {
    pub owl_SK: SecretBuf<'ticketserver>,
    pub owl_kS: SecretBuf<'ticketserver>,
    pub owl_kT: SecretBuf<'ticketserver>,
    pub owl_uname: SecretBuf<'ticketserver>,
    pub pk_owl_seckeyCnew: OwlBuf<'ticketserver>,
    pub pk_owl_sigkeyCA: OwlBuf<'ticketserver>,
    pub pk_owl_sigkeyA: OwlBuf<'ticketserver>,
    pub pk_owl_sigkeyC: OwlBuf<'ticketserver>,
}

impl cfg_ticketserver<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_ticketserver_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_ticketserver), Endpoint>>,
        mut_state: &mut state_ticketserver,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_ticketserver), Endpoint>>), OwlError>)
        requires
            itree.view() == ticketserver_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_ticketserver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(ticketserver_main_spec);
            let (tmp_owl_i437, owl__436) = {
                effects.owl_input::<((), state_ticketserver)>(Tracked(&mut itree))
            };
            let owl_i437 = OwlBuf::from_vec(tmp_owl_i437);
            let parseval_tmp = OwlBuf::another_ref(&owl_i437);
            if let Some(parseval) = parse_owl_client_to_ticketserver_msg(
                OwlBuf::another_ref(&parseval_tmp),
            ) {
                let owl_c439 = OwlBuf::another_ref(&parseval.owl__client_to_ticketserver_msg_1);
                let owl_t438 = OwlBuf::another_ref(&parseval.owl__client_to_ticketserver_msg_2);
                let tmp_owl_caseval440 = {
                    let tracked owl_declassify_tok441 = consume_itree_declassify::<
                        ((), state_ticketserver),
                        Endpoint,
                    >(&mut itree);
                    owl_dec(
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_kT)),
                        OwlBuf::another_ref(&owl_c439),
                        Tracked(owl_declassify_tok441),
                    )
                };
                let owl_caseval440 = SecretBuf::another_ref_option(&tmp_owl_caseval440);
                {
                    match SecretBuf::another_ref_option(&owl_caseval440) {
                        Option::None => { (owl_unit(), Tracked(itree)) },
                        Option::Some(tmp_owl_ak442) => {
                            let owl_ak442 = SecretBuf::another_ref(&tmp_owl_ak442);
                            let tmp_owl_caseval443 = {
                                let tracked owl_declassify_tok444 = consume_itree_declassify::<
                                    ((), state_ticketserver),
                                    Endpoint,
                                >(&mut itree);
                                owl_dec(
                                    SecretBuf::another_ref(&owl_ak442),
                                    OwlBuf::another_ref(&owl_t438),
                                    Tracked(owl_declassify_tok444),
                                )
                            };
                            let owl_caseval443 = SecretBuf::another_ref_option(&tmp_owl_caseval443);
                            match SecretBuf::another_ref_option(&owl_caseval443) {
                                Option::Some(tmp_owl_ClientRequest445) => {
                                    let owl_ClientRequest445 = SecretBuf::another_ref(
                                        &tmp_owl_ClientRequest445,
                                    );
                                    let tmp_owl_st446 = {
                                        let tmp_owl_coins447 = effects.owl_sample::<
                                            ((), state_ticketserver),
                                        >(Tracked(&mut itree), NONCE_SIZE);
                                        let owl_coins447 = SecretBuf::another_ref(
                                            &tmp_owl_coins447,
                                        );
                                        owl_enc(
                                            SecretBuf::another_ref(
                                                &SecretBuf::another_ref(&self.owl_kS),
                                            ),
                                            SecretBuf::another_ref(
                                                &SecretBuf::another_ref(&self.owl_SK),
                                            ),
                                            SecretBuf::another_ref(&owl_coins447),
                                        )
                                    };
                                    let owl_st446 = OwlBuf::from_vec(tmp_owl_st446);
                                    let tmp_owl_m448 = {
                                        let tmp_owl_coins449 = effects.owl_sample::<
                                            ((), state_ticketserver),
                                        >(Tracked(&mut itree), NONCE_SIZE);
                                        let owl_coins449 = SecretBuf::another_ref(
                                            &tmp_owl_coins449,
                                        );
                                        owl_enc(
                                            SecretBuf::another_ref(&owl_ak442),
                                            SecretBuf::another_ref(
                                                &OwlBuf::from_vec(
                                                    serialize_owl_AKEnum(
                                                        &owl_TicketResponse(
                                                            SecretBuf::another_ref(
                                                                &SecretBuf::another_ref(
                                                                    &self.owl_SK,
                                                                ),
                                                            ),
                                                        ),
                                                    ),
                                                ).into_secret(),
                                            ),
                                            SecretBuf::another_ref(&owl_coins449),
                                        )
                                    };
                                    let owl_m448 = OwlBuf::from_vec(tmp_owl_m448);
                                    let tmp_owl_p450 = {
                                        owl_ticketserver_msg(
                                            OwlBuf::another_ref(&owl_st446),
                                            OwlBuf::another_ref(&owl_m448),
                                        )
                                    };
                                    let owl_p450 = owl_ticketserver_msg::another_ref(&tmp_owl_p450);
                                    let owl__451 = {
                                        effects.owl_output::<((), state_ticketserver)>(
                                            Tracked(&mut itree),
                                            serialize_owl_ticketserver_msg(&owl_p450).as_slice(),
                                            Some(&client_addr()),
                                            &ticketserver_addr(),
                                        );
                                    };
                                    (owl_unit(), Tracked(itree))
                                },
                                Option::None => { (owl_unit(), Tracked(itree)) },
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

} // verus!
