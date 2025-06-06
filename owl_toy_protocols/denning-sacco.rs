// Extracted verus code from file owl_toy_protocols/denning-sacco.owl:
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
spec fn spec_combinator_owlSpec_addrs() -> (Variable, Variable) {
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

exec fn exec_combinator_owl_addrs() -> (res: (Variable, Variable))
    ensures
        res.view() == spec_combinator_owlSpec_addrs(),
{
    let field_1 = Variable(12);
    let field_2 = Variable(12);
    (field_1, field_2)
}

pub struct owlSpec_addrs {
    pub owlSpec__A: Seq<u8>,
    pub owlSpec__B: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_addrs(x: Seq<u8>) -> Option<owlSpec_addrs> {
    let spec_comb = spec_combinator_owlSpec_addrs();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec__A, owlSpec__B)) = parsed;
        Some(owlSpec_addrs { owlSpec__A, owlSpec__B })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_addrs_inner(x: owlSpec_addrs) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__A.len(), x.owlSpec__B.len() ] {
        let spec_comb = spec_combinator_owlSpec_addrs();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec__A, x.owlSpec__B))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_addrs(x: owlSpec_addrs) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_addrs_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_addrs {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_addrs(self)
    }
}

pub open spec fn addrs(arg_owlSpec__A: Seq<u8>, arg_owlSpec__B: Seq<u8>) -> owlSpec_addrs {
    owlSpec_addrs { owlSpec__A: arg_owlSpec__A, owlSpec__B: arg_owlSpec__B }
}

pub enum owlSpec_pk {
    owlSpec__pkA(Seq<u8>),
    owlSpec__pkB(Seq<u8>),
}

use owlSpec_pk::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_pk(x: Seq<u8>) -> Option<owlSpec_pk> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(1219)), (Tag::spec_new(U8, 2), Variable(1219)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owlSpec_pk::owlSpec__pkA(x),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_pk::owlSpec__pkB(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_pk_inner(x: owlSpec_pk) -> Option<Seq<u8>> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(1219)), (Tag::spec_new(U8, 2), Variable(1219)));
    match x {
        owlSpec_pk::owlSpec__pkA(x) => {
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
        owlSpec_pk::owlSpec__pkB(x) => {
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
pub closed spec fn serialize_owlSpec_pk(x: owlSpec_pk) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_pk_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_pk {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_pk(self)
    }
}

pub open spec fn _pkA(x: Seq<u8>) -> owlSpec_pk {
    crate::owlSpec_pk::owlSpec__pkA(x)
}

pub open spec fn _pkB(x: Seq<u8>) -> owlSpec_pk {
    crate::owlSpec_pk::owlSpec__pkB(x)
}

pub open spec fn _pkA_enumtest(x: owlSpec_pk) -> bool {
    match x {
        owlSpec_pk::owlSpec__pkA(_) => true,
        _ => false,
    }
}

pub open spec fn _pkB_enumtest(x: owlSpec_pk) -> bool {
    match x {
        owlSpec_pk::owlSpec__pkB(_) => true,
        _ => false,
    }
}

pub struct owlSpec_signed_by_pkS {
    pub owlSpec__address: Seq<u8>,
    pub owlSpec__pk: owlSpec_pk,
    pub owlSpec__t: Seq<u8>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_signed_by_pkS(x: Seq<u8>) -> Option<owlSpec_signed_by_pkS> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_signed_by_pkS_inner(x: owlSpec_signed_by_pkS) -> Option<
    Seq<u8>,
> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_signed_by_pkS(x: owlSpec_signed_by_pkS) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_signed_by_pkS {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_signed_by_pkS(self)
    }
}

pub open spec fn signed_by_pkS(
    arg_owlSpec__address: Seq<u8>,
    arg_owlSpec__pk: owlSpec_pk,
    arg_owlSpec__t: Seq<u8>,
) -> owlSpec_signed_by_pkS {
    owlSpec_signed_by_pkS {
        owlSpec__address: arg_owlSpec__address,
        owlSpec__pk: arg_owlSpec__pk,
        owlSpec__t: arg_owlSpec__t,
    }
}

pub struct owlSpec_tickets {
    pub owlSpec__s1: Seq<u8>,
    pub owlSpec__s2: Seq<u8>,
    pub owlSpec__t1: owlSpec_signed_by_pkS,
    pub owlSpec__t2: owlSpec_signed_by_pkS,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_tickets(x: Seq<u8>) -> Option<owlSpec_tickets> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_tickets_inner(x: owlSpec_tickets) -> Option<Seq<u8>> {
    unimplemented!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_tickets(x: owlSpec_tickets) -> Seq<u8> {
    unimplemented!()
}

impl OwlSpecSerialize for owlSpec_tickets {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_tickets(self)
    }
}

pub open spec fn tickets(
    arg_owlSpec__s1: Seq<u8>,
    arg_owlSpec__s2: Seq<u8>,
    arg_owlSpec__t1: owlSpec_signed_by_pkS,
    arg_owlSpec__t2: owlSpec_signed_by_pkS,
) -> owlSpec_tickets {
    owlSpec_tickets {
        owlSpec__s1: arg_owlSpec__s1,
        owlSpec__s2: arg_owlSpec__s2,
        owlSpec__t1: arg_owlSpec__t1,
        owlSpec__t2: arg_owlSpec__t2,
    }
}

pub enum owlSpec_A_result {
    owlSpec_A_No(),
    owlSpec_A_Ok(Seq<u8>),
}

use owlSpec_A_result::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_A_result(x: Seq<u8>) -> Option<owlSpec_A_result> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(1219)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owlSpec_A_result::owlSpec_A_No(),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_A_result::owlSpec_A_Ok(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_A_result_inner(x: owlSpec_A_result) -> Option<Seq<u8>> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(1219)));
    match x {
        owlSpec_A_result::owlSpec_A_No() => {
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
        owlSpec_A_result::owlSpec_A_Ok(x) => {
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
pub closed spec fn serialize_owlSpec_A_result(x: owlSpec_A_result) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_A_result_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_A_result {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_A_result(self)
    }
}

pub open spec fn A_No() -> owlSpec_A_result {
    crate::owlSpec_A_result::owlSpec_A_No()
}

pub open spec fn A_Ok(x: Seq<u8>) -> owlSpec_A_result {
    crate::owlSpec_A_result::owlSpec_A_Ok(x)
}

pub open spec fn A_No_enumtest(x: owlSpec_A_result) -> bool {
    match x {
        owlSpec_A_result::owlSpec_A_No() => true,
        _ => false,
    }
}

pub open spec fn A_Ok_enumtest(x: owlSpec_A_result) -> bool {
    match x {
        owlSpec_A_result::owlSpec_A_Ok(_) => true,
        _ => false,
    }
}

pub enum owlSpec_B_result {
    owlSpec_B_No(),
    owlSpec_B_Ok(Seq<u8>),
}

use owlSpec_B_result::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_B_result(x: Seq<u8>) -> Option<owlSpec_B_result> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(1219)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owlSpec_B_result::owlSpec_B_No(),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_B_result::owlSpec_B_Ok(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_B_result_inner(x: owlSpec_B_result) -> Option<Seq<u8>> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(1219)));
    match x {
        owlSpec_B_result::owlSpec_B_No() => {
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
        owlSpec_B_result::owlSpec_B_Ok(x) => {
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
pub closed spec fn serialize_owlSpec_B_result(x: owlSpec_B_result) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_B_result_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_B_result {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_B_result(self)
    }
}

pub open spec fn B_No() -> owlSpec_B_result {
    crate::owlSpec_B_result::owlSpec_B_No()
}

pub open spec fn B_Ok(x: Seq<u8>) -> owlSpec_B_result {
    crate::owlSpec_B_result::owlSpec_B_Ok(x)
}

pub open spec fn B_No_enumtest(x: owlSpec_B_result) -> bool {
    match x {
        owlSpec_B_result::owlSpec_B_No() => true,
        _ => false,
    }
}

pub open spec fn B_Ok_enumtest(x: owlSpec_B_result) -> bool {
    match x {
        owlSpec_B_result::owlSpec_B_Ok(_) => true,
        _ => false,
    }
}

#[verifier::opaque]
pub open spec fn A_main_spec(cfg: cfg_A, mut_state: state_A) -> (res: ITree<
    (owlSpec_A_result, state_A),
    Endpoint,
>) {
    owl_spec!(mut_state, state_A,
        let a = ((ret(cfg.owl_A_username.view()))) in
let b = ((ret(cfg.owl_B_username.view()))) in
let declassified_buf17 = ((declassify(DeclassifyingOp::ControlFlow(a))) in
(ret((a)))) in
let declassified_buf20 = ((declassify(DeclassifyingOp::ControlFlow(b))) in
(ret((b)))) in
(output (serialize_owlSpec_addrs(addrs(declassified_buf17, declassified_buf20))) to (Some(Endpoint::Loc_S))) in
(input(inp,_24)) in
(parse (parse_owlSpec_tickets(inp)) as (owlSpec_tickets{owlSpec__s1 : s1, owlSpec__s2 : s2, owlSpec__t1 : t1, owlSpec__t2 : t2}) in {
let pkA = ((ret(cfg.pk_owl_skA.view()))) in
let declassified_buf41 = ((declassify(DeclassifyingOp::ControlFlow(a))) in
(ret((a)))) in
let declassified_buf44 = ((declassify(DeclassifyingOp::ControlFlow(cfg.owl_T.view()))) in
(ret((cfg.owl_T.view())))) in
let msg_to_vrfy = ((ret(signed_by_pkS(declassified_buf41, _pkA(pkA), declassified_buf44)))) in
let caseval = ((declassify(DeclassifyingOp::SigVrfy(cfg.pk_owl_skS.view(), serialize_owlSpec_signed_by_pkS(msg_to_vrfy), s1))) in
(ret(vrfy(cfg.pk_owl_skS.view(), serialize_owlSpec_signed_by_pkS(msg_to_vrfy), s1)))) in
(case (caseval) {
| None => {
(ret(A_No()))
},
| Some(s) => {
let caseval = ((declassify(DeclassifyingOp::SigVrfy(cfg.pk_owl_skS.view(), serialize_owlSpec_signed_by_pkS(t2), s2))) in
(ret(vrfy(cfg.pk_owl_skS.view(), serialize_owlSpec_signed_by_pkS(t2), s2)))) in
(case (caseval) {
| None => {
(ret(A_No()))
},
| Some(s) => {
let declassified_buf63 = ((declassify(DeclassifyingOp::ControlFlow(s))) in
(ret((s)))) in
(parse (parse_owlSpec_signed_by_pkS(declassified_buf63)) as (owlSpec_signed_by_pkS{owlSpec__address : addr, owlSpec__pk : pks, owlSpec__t : t_val}) in {
(case (pks) {
| owlSpec__pkA(_unused141) => {
(ret(A_No()))
},
| owlSpec__pkB(o) => {
(output (inp) to (Some(Endpoint::Loc_B))) in
(ret(A_Ok(o)))
},
}
)
} otherwise ((ret(A_No()))))
},
}
)
},
}
)
} otherwise ((ret(A_No()))))
    )
}

#[verifier::opaque]
pub open spec fn B_main_spec(cfg: cfg_B, mut_state: state_B) -> (res: ITree<
    (owlSpec_B_result, state_B),
    Endpoint,
>) {
    owl_spec!(mut_state, state_B,
        let b = ((ret(cfg.owl_B_username.view()))) in
(input(inp,_67)) in
(parse (parse_owlSpec_tickets(inp)) as (owlSpec_tickets{owlSpec__s1 : s1, owlSpec__s2 : s2, owlSpec__t1 : t1, owlSpec__t2 : t2}) in {
let pkB = ((ret(cfg.pk_owl_skB.view()))) in
let declassified_buf84 = ((declassify(DeclassifyingOp::ControlFlow(b))) in
(ret((b)))) in
let declassified_buf87 = ((declassify(DeclassifyingOp::ControlFlow(cfg.owl_T.view()))) in
(ret((cfg.owl_T.view())))) in
let msg_to_vrfy = ((ret(signed_by_pkS(declassified_buf84, _pkB(pkB), declassified_buf87)))) in
let caseval = ((declassify(DeclassifyingOp::SigVrfy(cfg.pk_owl_skS.view(), serialize_owlSpec_signed_by_pkS(msg_to_vrfy), s2))) in
(ret(vrfy(cfg.pk_owl_skS.view(), serialize_owlSpec_signed_by_pkS(msg_to_vrfy), s2)))) in
(case (caseval) {
| None => {
(ret(B_No()))
},
| Some(s) => {
let caseval = ((declassify(DeclassifyingOp::SigVrfy(cfg.pk_owl_skS.view(), serialize_owlSpec_signed_by_pkS(t1), s1))) in
(ret(vrfy(cfg.pk_owl_skS.view(), serialize_owlSpec_signed_by_pkS(t1), s1)))) in
(case (caseval) {
| None => {
(ret(B_No()))
},
| Some(s) => {
let declassified_buf105 = ((declassify(DeclassifyingOp::ControlFlow(s))) in
(ret((s)))) in
(parse (parse_owlSpec_signed_by_pkS(declassified_buf105)) as (owlSpec_signed_by_pkS{owlSpec__address : addr, owlSpec__pk : pks, owlSpec__t : t_val}) in {
(case (pks) {
| owlSpec__pkB(_unused142) => {
(ret(B_No()))
},
| owlSpec__pkA(o) => {
(ret(B_Ok(o)))
},
}
)
} otherwise ((ret(B_No()))))
},
}
)
},
}
)
} otherwise ((ret(B_No()))))
    )
}

#[verifier::opaque]
pub open spec fn S_main_spec(cfg: cfg_S, mut_state: state_S) -> (res: ITree<
    ((), state_S),
    Endpoint,
>) {
    owl_spec!(mut_state, state_S,
        let sigK = ((ret(cfg.owl_skS.view()))) in
(input(inp,_109)) in
(parse (parse_owlSpec_addrs(inp)) as (owlSpec_addrs{owlSpec__A : a, owlSpec__B : b}) in {
let declassified_buf115 = ((declassify(DeclassifyingOp::ControlFlow(cfg.owl_T.view()))) in
(ret((cfg.owl_T.view())))) in
let msg_to_sign_1 = ((ret(signed_by_pkS(a, _pkA(cfg.pk_owl_skA.view()), declassified_buf115)))) in
let declassified_buf119 = ((declassify(DeclassifyingOp::ControlFlow(cfg.owl_T.view()))) in
(ret((cfg.owl_T.view())))) in
let msg_to_sign_2 = ((ret(signed_by_pkS(b, _pkB(cfg.pk_owl_skB.view()), declassified_buf119)))) in
let sig1 = ((ret(sign(sigK, serialize_owlSpec_signed_by_pkS(msg_to_sign_1))))) in
let sig2 = ((ret(sign(sigK, serialize_owlSpec_signed_by_pkS(msg_to_sign_2))))) in
(output (serialize_owlSpec_tickets(tickets(sig1, sig2, msg_to_sign_1, msg_to_sign_2))) to (Some(Endpoint::Loc_A))) in
(ret(()))
} otherwise ((ret(()))))
    )
}

// ------------------------------------
// ---------- IMPLEMENTATIONS ---------
// ------------------------------------
#[derive(Clone,Copy)]
pub enum Endpoint {
    Loc_A,
    Loc_B,
    Loc_S,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier(external_body)]
pub const fn A_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_A,
{
    "127.0.0.1:9001"
}

#[verifier(external_body)]
pub const fn B_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_B,
{
    "127.0.0.1:9002"
}

#[verifier(external_body)]
pub const fn S_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_S,
{
    "127.0.0.1:9003"
}

pub struct owl_addrs<'a> {
    pub owl__A: OwlBuf<'a>,
    pub owl__B: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_addrs<'a>(arg_owl__A: OwlBuf<'a>, arg_owl__B: OwlBuf<'a>) -> (res: owl_addrs<'a>)
    ensures
        res.owl__A.view() == arg_owl__A.view(),
        res.owl__B.view() == arg_owl__B.view(),
{
    owl_addrs { owl__A: arg_owl__A, owl__B: arg_owl__B }
}

impl<'a> owl_addrs<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_addrs<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_addrs {
            owl__A: OwlBuf::another_ref(&self.owl__A),
            owl__B: OwlBuf::another_ref(&self.owl__B),
        }
    }
}

impl View for owl_addrs<'_> {
    type V = owlSpec_addrs;

    open spec fn view(&self) -> owlSpec_addrs {
        owlSpec_addrs { owlSpec__A: self.owl__A.view(), owlSpec__B: self.owl__B.view() }
    }
}

pub exec fn parse_owl_addrs<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_addrs<'a>>)
    ensures
        res is Some ==> parse_owlSpec_addrs(arg.view()) is Some,
        res is None ==> parse_owlSpec_addrs(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_addrs(arg.view())->Some_0,
{
    reveal(parse_owlSpec_addrs);
    let exec_comb = exec_combinator_owl_addrs();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl__A, owl__B) = parsed;
        Some(
            owl_addrs {
                owl__A: OwlBuf::another_ref(&owl__A),
                owl__B: OwlBuf::another_ref(&owl__B),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_addrs_inner<'a>(arg: &owl_addrs<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_addrs_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_addrs_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_addrs_inner);
    if no_usize_overflows![ arg.owl__A.len(), arg.owl__B.len(), 0 ] {
        let exec_comb = exec_combinator_owl_addrs();
        let mut obuf = vec_u8_of_len(arg.owl__A.len() + arg.owl__B.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl__A), OwlBuf::another_ref(&arg.owl__B)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_addrs_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_addrs<'a>(arg: &owl_addrs<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_addrs(arg.view()),
{
    reveal(serialize_owlSpec_addrs);
    let res = serialize_owl_addrs_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_pk<'a> {
    owl__pkA(OwlBuf<'a>),
    owl__pkB(OwlBuf<'a>),
}

use owl_pk::*;

impl<'a> owl_pk<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_pk<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl__pkA(x) => owl__pkA(OwlBuf::another_ref(x)),
            owl__pkB(x) => owl__pkB(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_pk<'_> {
    type V = owlSpec_pk;

    open spec fn view(&self) -> owlSpec_pk {
        match self {
            owl__pkA(v) => owlSpec_pk::owlSpec__pkA(v.view()),
            owl__pkB(v) => owlSpec_pk::owlSpec__pkB(v.view()),
        }
    }
}

#[inline]
pub fn owl__pkA_enumtest(x: &owl_pk<'_>) -> (res: bool)
    ensures
        res == _pkA_enumtest(x.view()),
{
    match x {
        owl_pk::owl__pkA(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl__pkB_enumtest(x: &owl_pk<'_>) -> (res: bool)
    ensures
        res == _pkB_enumtest(x.view()),
{
    match x {
        owl_pk::owl__pkB(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_pk<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_pk<'a>>)
    ensures
        res is Some ==> parse_owlSpec_pk(arg.view()) is Some,
        res is None ==> parse_owlSpec_pk(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_pk(arg.view())->Some_0,
{
    reveal(parse_owlSpec_pk);
    let exec_comb =
        ord_choice!((Tag::new(U8, 1), Variable(1219)), (Tag::new(U8, 2), Variable(1219)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owl_pk::owl__pkA(OwlBuf::another_ref(&x)),
            inj_ord_choice_pat!(*, (_,x)) => owl_pk::owl__pkB(OwlBuf::another_ref(&x)),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn serialize_owl_pk_inner(arg: &owl_pk) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_pk_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_pk_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_pk_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_pk(arg: &owl_pk) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_pk(arg.view()),
{
    reveal(serialize_owlSpec_pk);
    let res = serialize_owl_pk_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_signed_by_pkS<'a> {
    pub owl__address: OwlBuf<'a>,
    pub owl__pk: owl_pk<'a>,
    pub owl__t: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_signed_by_pkS<'a>(
    arg_owl__address: OwlBuf<'a>,
    arg_owl__pk: owl_pk<'a>,
    arg_owl__t: OwlBuf<'a>,
) -> (res: owl_signed_by_pkS<'a>)
    ensures
        res.owl__address.view() == arg_owl__address.view(),
        res.owl__pk.view() == arg_owl__pk.view(),
        res.owl__t.view() == arg_owl__t.view(),
{
    owl_signed_by_pkS { owl__address: arg_owl__address, owl__pk: arg_owl__pk, owl__t: arg_owl__t }
}

impl<'a> owl_signed_by_pkS<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_signed_by_pkS<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_signed_by_pkS {
            owl__address: OwlBuf::another_ref(&self.owl__address),
            owl__pk: owl_pk::another_ref(&self.owl__pk),
            owl__t: OwlBuf::another_ref(&self.owl__t),
        }
    }
}

impl View for owl_signed_by_pkS<'_> {
    type V = owlSpec_signed_by_pkS;

    open spec fn view(&self) -> owlSpec_signed_by_pkS {
        owlSpec_signed_by_pkS {
            owlSpec__address: self.owl__address.view(),
            owlSpec__pk: self.owl__pk.view(),
            owlSpec__t: self.owl__t.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_signed_by_pkS<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_signed_by_pkS<'a>>)
    ensures
        res is Some ==> parse_owlSpec_signed_by_pkS(arg.view()) is Some,
        res is None ==> parse_owlSpec_signed_by_pkS(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_signed_by_pkS(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_signed_by_pkS_inner<'a>(arg: &owl_signed_by_pkS) -> (res: Option<
    OwlBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_signed_by_pkS_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_signed_by_pkS_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_signed_by_pkS<'a>(arg: &owl_signed_by_pkS) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_signed_by_pkS(arg.view()),
{
    unimplemented!()
}

pub struct owl_tickets<'a> {
    pub owl__s1: OwlBuf<'a>,
    pub owl__s2: OwlBuf<'a>,
    pub owl__t1: owl_signed_by_pkS<'a>,
    pub owl__t2: owl_signed_by_pkS<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_tickets<'a>(
    arg_owl__s1: OwlBuf<'a>,
    arg_owl__s2: OwlBuf<'a>,
    arg_owl__t1: owl_signed_by_pkS<'a>,
    arg_owl__t2: owl_signed_by_pkS<'a>,
) -> (res: owl_tickets<'a>)
    ensures
        res.owl__s1.view() == arg_owl__s1.view(),
        res.owl__s2.view() == arg_owl__s2.view(),
        res.owl__t1.view() == arg_owl__t1.view(),
        res.owl__t2.view() == arg_owl__t2.view(),
{
    owl_tickets {
        owl__s1: arg_owl__s1,
        owl__s2: arg_owl__s2,
        owl__t1: arg_owl__t1,
        owl__t2: arg_owl__t2,
    }
}

impl<'a> owl_tickets<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_tickets<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_tickets {
            owl__s1: OwlBuf::another_ref(&self.owl__s1),
            owl__s2: OwlBuf::another_ref(&self.owl__s2),
            owl__t1: owl_signed_by_pkS::another_ref(&self.owl__t1),
            owl__t2: owl_signed_by_pkS::another_ref(&self.owl__t2),
        }
    }
}

impl View for owl_tickets<'_> {
    type V = owlSpec_tickets;

    open spec fn view(&self) -> owlSpec_tickets {
        owlSpec_tickets {
            owlSpec__s1: self.owl__s1.view(),
            owlSpec__s2: self.owl__s2.view(),
            owlSpec__t1: self.owl__t1.view(),
            owlSpec__t2: self.owl__t2.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_tickets<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_tickets<'a>>)
    ensures
        res is Some ==> parse_owlSpec_tickets(arg.view()) is Some,
        res is None ==> parse_owlSpec_tickets(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_tickets(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_tickets_inner<'a>(arg: &owl_tickets) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_tickets_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_tickets_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[verifier::external_body]
pub exec fn serialize_owl_tickets<'a>(arg: &owl_tickets) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_tickets(arg.view()),
{
    unimplemented!()
}

pub enum owl_A_result<'a> {
    owl_A_No(),
    owl_A_Ok(OwlBuf<'a>),
}

use owl_A_result::*;

impl<'a> owl_A_result<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_A_result<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_A_No() => owl_A_No(),
            owl_A_Ok(x) => owl_A_Ok(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_A_result<'_> {
    type V = owlSpec_A_result;

    open spec fn view(&self) -> owlSpec_A_result {
        match self {
            owl_A_No() => owlSpec_A_result::owlSpec_A_No(),
            owl_A_Ok(v) => owlSpec_A_result::owlSpec_A_Ok(v.view()),
        }
    }
}

#[inline]
pub fn owl_A_No_enumtest(x: &owl_A_result<'_>) -> (res: bool)
    ensures
        res == A_No_enumtest(x.view()),
{
    match x {
        owl_A_result::owl_A_No() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_A_Ok_enumtest(x: &owl_A_result<'_>) -> (res: bool)
    ensures
        res == A_Ok_enumtest(x.view()),
{
    match x {
        owl_A_result::owl_A_Ok(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_A_result<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_A_result<'a>>)
    ensures
        res is Some ==> parse_owlSpec_A_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_A_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_A_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_A_result);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(0)), (Tag::new(U8, 2), Variable(1219)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owl_A_result::owl_A_No(),
            inj_ord_choice_pat!(*, (_,x)) => owl_A_result::owl_A_Ok(OwlBuf::another_ref(&x)),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_A_result<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_A_result<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_A_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_A_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_A_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_A_result);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_A_result_inner(arg: &owl_A_result) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_A_result_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_A_result_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_A_result_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_A_result(arg: &owl_A_result) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_A_result(arg.view()),
{
    reveal(serialize_owlSpec_A_result);
    let res = serialize_owl_A_result_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_B_result<'a> {
    owl_B_No(),
    owl_B_Ok(OwlBuf<'a>),
}

use owl_B_result::*;

impl<'a> owl_B_result<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_B_result<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_B_No() => owl_B_No(),
            owl_B_Ok(x) => owl_B_Ok(OwlBuf::another_ref(x)),
        }
    }
}

impl View for owl_B_result<'_> {
    type V = owlSpec_B_result;

    open spec fn view(&self) -> owlSpec_B_result {
        match self {
            owl_B_No() => owlSpec_B_result::owlSpec_B_No(),
            owl_B_Ok(v) => owlSpec_B_result::owlSpec_B_Ok(v.view()),
        }
    }
}

#[inline]
pub fn owl_B_No_enumtest(x: &owl_B_result<'_>) -> (res: bool)
    ensures
        res == B_No_enumtest(x.view()),
{
    match x {
        owl_B_result::owl_B_No() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_B_Ok_enumtest(x: &owl_B_result<'_>) -> (res: bool)
    ensures
        res == B_Ok_enumtest(x.view()),
{
    match x {
        owl_B_result::owl_B_Ok(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_B_result<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_B_result<'a>>)
    ensures
        res is Some ==> parse_owlSpec_B_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_B_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_B_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_B_result);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(0)), (Tag::new(U8, 2), Variable(1219)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owl_B_result::owl_B_No(),
            inj_ord_choice_pat!(*, (_,x)) => owl_B_result::owl_B_Ok(OwlBuf::another_ref(&x)),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_B_result<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_B_result<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_B_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_B_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_B_result(arg.view())->Some_0,
{
    reveal(parse_owlSpec_B_result);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_B_result_inner(arg: &owl_B_result) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_B_result_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_B_result_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_B_result_inner(arg.view())->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_B_result(arg: &owl_B_result) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_B_result(arg.view()),
{
    reveal(serialize_owlSpec_B_result);
    let res = serialize_owl_B_result_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct state_A {}

impl state_A {
    #[verifier::external_body]
    pub fn init_state_A() -> Self {
        state_A {  }
    }
}

pub struct cfg_A<'A> {
    pub owl_B_username: SecretBuf<'A>,
    pub owl_A_username: SecretBuf<'A>,
    pub owl_skA: SecretBuf<'A>,
    pub owl_T: SecretBuf<'A>,
    pub pk_owl_skS: OwlBuf<'A>,
    pub pk_owl_skB: OwlBuf<'A>,
    pub pk_owl_skA: OwlBuf<'A>,
}

impl cfg_A<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_A_main<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_A_result, state_A), Endpoint>>,
        mut_state: &mut state_A,
    ) -> (res: Result<
        (owl_A_result<'a>, Tracked<ITreeToken<(owlSpec_A_result, state_A), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == A_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_A_result<'a>,
            Tracked<ITreeToken<(owlSpec_A_result, state_A), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(A_main_spec);
            let tmp_owl_a143 = { SecretBuf::another_ref(&self.owl_A_username) };
            let owl_a143 = SecretBuf::another_ref(&tmp_owl_a143);
            let tmp_owl_b144 = { SecretBuf::another_ref(&self.owl_B_username) };
            let owl_b144 = SecretBuf::another_ref(&tmp_owl_b144);
            let tmp_owl_declassified_buf17145 = {
                let tracked owl_declassify_tok146 = consume_itree_declassify::<
                    (owlSpec_A_result, state_A),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_a143).declassify(Tracked(owl_declassify_tok146)) }
            };
            let owl_declassified_buf17145 = OwlBuf::another_ref(&tmp_owl_declassified_buf17145);
            let tmp_owl_declassified_buf20147 = {
                let tracked owl_declassify_tok148 = consume_itree_declassify::<
                    (owlSpec_A_result, state_A),
                    Endpoint,
                >(&mut itree);
                { SecretBuf::another_ref(&owl_b144).declassify(Tracked(owl_declassify_tok148)) }
            };
            let owl_declassified_buf20147 = OwlBuf::another_ref(&tmp_owl_declassified_buf20147);
            let owl__149 = {
                effects.owl_output::<(owlSpec_A_result, state_A)>(
                    Tracked(&mut itree),
                    serialize_owl_addrs(
                        &owl_addrs(
                            OwlBuf::another_ref(&owl_declassified_buf17145),
                            OwlBuf::another_ref(&owl_declassified_buf20147),
                        ),
                    ).as_slice(),
                    Some(&S_addr()),
                    &A_addr(),
                );
            };
            let (tmp_owl_inp151, owl__150) = {
                effects.owl_input::<(owlSpec_A_result, state_A)>(Tracked(&mut itree))
            };
            let owl_inp151 = OwlBuf::from_vec(tmp_owl_inp151);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp151);
            if let Some(parseval) = parse_owl_tickets(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_s1155 = OwlBuf::another_ref(&parseval.owl__s1);
                let owl_s2154 = OwlBuf::another_ref(&parseval.owl__s2);
                let owl_t1153 = owl_signed_by_pkS::another_ref(&parseval.owl__t1);
                let owl_t2152 = owl_signed_by_pkS::another_ref(&parseval.owl__t2);
                let tmp_owl_pkA156 = { OwlBuf::another_ref(&self.pk_owl_skA) };
                let owl_pkA156 = OwlBuf::another_ref(&tmp_owl_pkA156);
                let tmp_owl_declassified_buf41157 = {
                    let tracked owl_declassify_tok158 = consume_itree_declassify::<
                        (owlSpec_A_result, state_A),
                        Endpoint,
                    >(&mut itree);
                    { SecretBuf::another_ref(&owl_a143).declassify(Tracked(owl_declassify_tok158)) }
                };
                let owl_declassified_buf41157 = OwlBuf::another_ref(&tmp_owl_declassified_buf41157);
                let tmp_owl_declassified_buf44159 = {
                    let tracked owl_declassify_tok160 = consume_itree_declassify::<
                        (owlSpec_A_result, state_A),
                        Endpoint,
                    >(&mut itree);
                    {
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_T)).declassify(
                            Tracked(owl_declassify_tok160),
                        )
                    }
                };
                let owl_declassified_buf44159 = OwlBuf::another_ref(&tmp_owl_declassified_buf44159);
                let tmp_owl_msg_to_vrfy161 = {
                    owl_signed_by_pkS(
                        OwlBuf::another_ref(&owl_declassified_buf41157),
                        owl_pk::another_ref(&owl__pkA(OwlBuf::another_ref(&owl_pkA156))),
                        OwlBuf::another_ref(&owl_declassified_buf44159),
                    )
                };
                let owl_msg_to_vrfy161 = owl_signed_by_pkS::another_ref(&tmp_owl_msg_to_vrfy161);
                let tmp_owl_caseval162 = {
                    let tracked owl_declassify_tok163 = consume_itree_declassify::<
                        (owlSpec_A_result, state_A),
                        Endpoint,
                    >(&mut itree);
                    owl_vrfy(
                        OwlBuf::another_ref(&OwlBuf::another_ref(&self.pk_owl_skS)),
                        SecretBuf::another_ref(
                            &SecretBuf::from_buf(
                                serialize_owl_signed_by_pkS(&owl_msg_to_vrfy161).another_ref(),
                            ),
                        ),
                        OwlBuf::another_ref(&owl_s1155),
                        Tracked(owl_declassify_tok163),
                    )
                };
                let owl_caseval162 = SecretBuf::another_ref_option(&tmp_owl_caseval162);
                match SecretBuf::another_ref_option(&owl_caseval162) {
                    Option::None => { (owl_A_result::another_ref(&owl_A_No()), Tracked(itree)) },
                    Option::Some(tmp_owl_s164) => {
                        let owl_s164 = SecretBuf::another_ref(&tmp_owl_s164);
                        let tmp_owl_caseval165 = {
                            let tracked owl_declassify_tok166 = consume_itree_declassify::<
                                (owlSpec_A_result, state_A),
                                Endpoint,
                            >(&mut itree);
                            owl_vrfy(
                                OwlBuf::another_ref(&OwlBuf::another_ref(&self.pk_owl_skS)),
                                SecretBuf::another_ref(
                                    &SecretBuf::from_buf(
                                        serialize_owl_signed_by_pkS(&owl_t2152).another_ref(),
                                    ),
                                ),
                                OwlBuf::another_ref(&owl_s2154),
                                Tracked(owl_declassify_tok166),
                            )
                        };
                        let owl_caseval165 = SecretBuf::another_ref_option(&tmp_owl_caseval165);
                        match SecretBuf::another_ref_option(&owl_caseval165) {
                            Option::None => {
                                (owl_A_result::another_ref(&owl_A_No()), Tracked(itree))
                            },
                            Option::Some(tmp_owl_s167) => {
                                let owl_s167 = SecretBuf::another_ref(&tmp_owl_s167);
                                let tmp_owl_declassified_buf63168 = {
                                    let tracked owl_declassify_tok169 = consume_itree_declassify::<
                                        (owlSpec_A_result, state_A),
                                        Endpoint,
                                    >(&mut itree);
                                    {
                                        SecretBuf::another_ref(&owl_s167).declassify(
                                            Tracked(owl_declassify_tok169),
                                        )
                                    }
                                };
                                let owl_declassified_buf63168 = OwlBuf::another_ref(
                                    &tmp_owl_declassified_buf63168,
                                );
                                let parseval_tmp = OwlBuf::another_ref(&owl_declassified_buf63168);
                                if let Some(parseval) = parse_owl_signed_by_pkS(
                                    OwlBuf::another_ref(&parseval_tmp),
                                ) {
                                    let owl_addr172 = OwlBuf::another_ref(&parseval.owl__address);
                                    let owl_pks171 = owl_pk::another_ref(&parseval.owl__pk);
                                    let owl_t_val170 = OwlBuf::another_ref(&parseval.owl__t);
                                    match owl_pk::another_ref(&owl_pks171) {
                                        owl_pk::owl__pkA(tmp_owl__173) => {
                                            let owl__173 = OwlBuf::another_ref(&tmp_owl__173);
                                            (owl_A_result::another_ref(&owl_A_No()), Tracked(itree))
                                        },
                                        owl_pk::owl__pkB(tmp_owl_o174) => {
                                            let owl_o174 = OwlBuf::another_ref(&tmp_owl_o174);
                                            let owl__175 = {
                                                effects.owl_output::<(owlSpec_A_result, state_A)>(
                                                    Tracked(&mut itree),
                                                    owl_inp151.as_slice(),
                                                    Some(&B_addr()),
                                                    &A_addr(),
                                                );
                                            };
                                            (
                                                owl_A_result::another_ref(
                                                    &owl_A_Ok(OwlBuf::another_ref(&owl_o174)),
                                                ),
                                                Tracked(itree),
                                            )
                                        },
                                    }
                                } else {
                                    (owl_A_result::another_ref(&owl_A_No()), Tracked(itree))
                                }
                            },
                        }
                    },
                }
            } else {
                (owl_A_result::another_ref(&owl_A_No()), Tracked(itree))
            }
        };
        Ok((owl_A_result::another_ref(&res_inner), Tracked(itree)))
    }
}

pub struct state_B {}

impl state_B {
    #[verifier::external_body]
    pub fn init_state_B() -> Self {
        state_B {  }
    }
}

pub struct cfg_B<'B> {
    pub owl_B_username: SecretBuf<'B>,
    pub owl_A_username: SecretBuf<'B>,
    pub owl_skB: SecretBuf<'B>,
    pub owl_T: SecretBuf<'B>,
    pub pk_owl_skS: OwlBuf<'B>,
    pub pk_owl_skB: OwlBuf<'B>,
    pub pk_owl_skA: OwlBuf<'B>,
}

impl cfg_B<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_B_main<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_B_result, state_B), Endpoint>>,
        mut_state: &mut state_B,
    ) -> (res: Result<
        (owl_B_result<'a>, Tracked<ITreeToken<(owlSpec_B_result, state_B), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == B_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_B_result<'a>,
            Tracked<ITreeToken<(owlSpec_B_result, state_B), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(B_main_spec);
            let tmp_owl_b176 = { SecretBuf::another_ref(&self.owl_B_username) };
            let owl_b176 = SecretBuf::another_ref(&tmp_owl_b176);
            let (tmp_owl_inp178, owl__177) = {
                effects.owl_input::<(owlSpec_B_result, state_B)>(Tracked(&mut itree))
            };
            let owl_inp178 = OwlBuf::from_vec(tmp_owl_inp178);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp178);
            if let Some(parseval) = parse_owl_tickets(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_s1182 = OwlBuf::another_ref(&parseval.owl__s1);
                let owl_s2181 = OwlBuf::another_ref(&parseval.owl__s2);
                let owl_t1180 = owl_signed_by_pkS::another_ref(&parseval.owl__t1);
                let owl_t2179 = owl_signed_by_pkS::another_ref(&parseval.owl__t2);
                let tmp_owl_pkB183 = { OwlBuf::another_ref(&self.pk_owl_skB) };
                let owl_pkB183 = OwlBuf::another_ref(&tmp_owl_pkB183);
                let tmp_owl_declassified_buf84184 = {
                    let tracked owl_declassify_tok185 = consume_itree_declassify::<
                        (owlSpec_B_result, state_B),
                        Endpoint,
                    >(&mut itree);
                    { SecretBuf::another_ref(&owl_b176).declassify(Tracked(owl_declassify_tok185)) }
                };
                let owl_declassified_buf84184 = OwlBuf::another_ref(&tmp_owl_declassified_buf84184);
                let tmp_owl_declassified_buf87186 = {
                    let tracked owl_declassify_tok187 = consume_itree_declassify::<
                        (owlSpec_B_result, state_B),
                        Endpoint,
                    >(&mut itree);
                    {
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_T)).declassify(
                            Tracked(owl_declassify_tok187),
                        )
                    }
                };
                let owl_declassified_buf87186 = OwlBuf::another_ref(&tmp_owl_declassified_buf87186);
                let tmp_owl_msg_to_vrfy188 = {
                    owl_signed_by_pkS(
                        OwlBuf::another_ref(&owl_declassified_buf84184),
                        owl_pk::another_ref(&owl__pkB(OwlBuf::another_ref(&owl_pkB183))),
                        OwlBuf::another_ref(&owl_declassified_buf87186),
                    )
                };
                let owl_msg_to_vrfy188 = owl_signed_by_pkS::another_ref(&tmp_owl_msg_to_vrfy188);
                let tmp_owl_caseval189 = {
                    let tracked owl_declassify_tok190 = consume_itree_declassify::<
                        (owlSpec_B_result, state_B),
                        Endpoint,
                    >(&mut itree);
                    owl_vrfy(
                        OwlBuf::another_ref(&OwlBuf::another_ref(&self.pk_owl_skS)),
                        SecretBuf::another_ref(
                            &SecretBuf::from_buf(
                                serialize_owl_signed_by_pkS(&owl_msg_to_vrfy188).another_ref(),
                            ),
                        ),
                        OwlBuf::another_ref(&owl_s2181),
                        Tracked(owl_declassify_tok190),
                    )
                };
                let owl_caseval189 = SecretBuf::another_ref_option(&tmp_owl_caseval189);
                match SecretBuf::another_ref_option(&owl_caseval189) {
                    Option::None => { (owl_B_result::another_ref(&owl_B_No()), Tracked(itree)) },
                    Option::Some(tmp_owl_s191) => {
                        let owl_s191 = SecretBuf::another_ref(&tmp_owl_s191);
                        let tmp_owl_caseval192 = {
                            let tracked owl_declassify_tok193 = consume_itree_declassify::<
                                (owlSpec_B_result, state_B),
                                Endpoint,
                            >(&mut itree);
                            owl_vrfy(
                                OwlBuf::another_ref(&OwlBuf::another_ref(&self.pk_owl_skS)),
                                SecretBuf::another_ref(
                                    &SecretBuf::from_buf(
                                        serialize_owl_signed_by_pkS(&owl_t1180).another_ref(),
                                    ),
                                ),
                                OwlBuf::another_ref(&owl_s1182),
                                Tracked(owl_declassify_tok193),
                            )
                        };
                        let owl_caseval192 = SecretBuf::another_ref_option(&tmp_owl_caseval192);
                        match SecretBuf::another_ref_option(&owl_caseval192) {
                            Option::None => {
                                (owl_B_result::another_ref(&owl_B_No()), Tracked(itree))
                            },
                            Option::Some(tmp_owl_s194) => {
                                let owl_s194 = SecretBuf::another_ref(&tmp_owl_s194);
                                let tmp_owl_declassified_buf105195 = {
                                    let tracked owl_declassify_tok196 = consume_itree_declassify::<
                                        (owlSpec_B_result, state_B),
                                        Endpoint,
                                    >(&mut itree);
                                    {
                                        SecretBuf::another_ref(&owl_s194).declassify(
                                            Tracked(owl_declassify_tok196),
                                        )
                                    }
                                };
                                let owl_declassified_buf105195 = OwlBuf::another_ref(
                                    &tmp_owl_declassified_buf105195,
                                );
                                let parseval_tmp = OwlBuf::another_ref(&owl_declassified_buf105195);
                                if let Some(parseval) = parse_owl_signed_by_pkS(
                                    OwlBuf::another_ref(&parseval_tmp),
                                ) {
                                    let owl_addr199 = OwlBuf::another_ref(&parseval.owl__address);
                                    let owl_pks198 = owl_pk::another_ref(&parseval.owl__pk);
                                    let owl_t_val197 = OwlBuf::another_ref(&parseval.owl__t);
                                    match owl_pk::another_ref(&owl_pks198) {
                                        owl_pk::owl__pkB(tmp_owl__200) => {
                                            let owl__200 = OwlBuf::another_ref(&tmp_owl__200);
                                            (owl_B_result::another_ref(&owl_B_No()), Tracked(itree))
                                        },
                                        owl_pk::owl__pkA(tmp_owl_o201) => {
                                            let owl_o201 = OwlBuf::another_ref(&tmp_owl_o201);
                                            (
                                                owl_B_result::another_ref(
                                                    &owl_B_Ok(OwlBuf::another_ref(&owl_o201)),
                                                ),
                                                Tracked(itree),
                                            )
                                        },
                                    }
                                } else {
                                    (owl_B_result::another_ref(&owl_B_No()), Tracked(itree))
                                }
                            },
                        }
                    },
                }
            } else {
                (owl_B_result::another_ref(&owl_B_No()), Tracked(itree))
            }
        };
        Ok((owl_B_result::another_ref(&res_inner), Tracked(itree)))
    }
}

pub struct state_S {}

impl state_S {
    #[verifier::external_body]
    pub fn init_state_S() -> Self {
        state_S {  }
    }
}

pub struct cfg_S<'S> {
    pub owl_skS: SecretBuf<'S>,
    pub owl_T: SecretBuf<'S>,
    pub pk_owl_skS: OwlBuf<'S>,
    pub pk_owl_skB: OwlBuf<'S>,
    pub pk_owl_skA: OwlBuf<'S>,
}

impl cfg_S<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_S_main<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_S), Endpoint>>,
        mut_state: &mut state_S,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_S), Endpoint>>), OwlError>)
        requires
            itree.view() == S_main_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_S), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(S_main_spec);
            let tmp_owl_sigK202 = { SecretBuf::another_ref(&self.owl_skS) };
            let owl_sigK202 = SecretBuf::another_ref(&tmp_owl_sigK202);
            let (tmp_owl_inp204, owl__203) = {
                effects.owl_input::<((), state_S)>(Tracked(&mut itree))
            };
            let owl_inp204 = OwlBuf::from_vec(tmp_owl_inp204);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp204);
            if let Some(parseval) = parse_owl_addrs(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_a206 = OwlBuf::another_ref(&parseval.owl__A);
                let owl_b205 = OwlBuf::another_ref(&parseval.owl__B);
                let tmp_owl_declassified_buf115207 = {
                    let tracked owl_declassify_tok208 = consume_itree_declassify::<
                        ((), state_S),
                        Endpoint,
                    >(&mut itree);
                    {
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_T)).declassify(
                            Tracked(owl_declassify_tok208),
                        )
                    }
                };
                let owl_declassified_buf115207 = OwlBuf::another_ref(
                    &tmp_owl_declassified_buf115207,
                );
                let tmp_owl_msg_to_sign_1209 = {
                    owl_signed_by_pkS(
                        OwlBuf::another_ref(&owl_a206),
                        owl_pk::another_ref(
                            &owl__pkA(OwlBuf::another_ref(&OwlBuf::another_ref(&self.pk_owl_skA))),
                        ),
                        OwlBuf::another_ref(&owl_declassified_buf115207),
                    )
                };
                let owl_msg_to_sign_1209 = owl_signed_by_pkS::another_ref(
                    &tmp_owl_msg_to_sign_1209,
                );
                let tmp_owl_declassified_buf119210 = {
                    let tracked owl_declassify_tok211 = consume_itree_declassify::<
                        ((), state_S),
                        Endpoint,
                    >(&mut itree);
                    {
                        SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_T)).declassify(
                            Tracked(owl_declassify_tok211),
                        )
                    }
                };
                let owl_declassified_buf119210 = OwlBuf::another_ref(
                    &tmp_owl_declassified_buf119210,
                );
                let tmp_owl_msg_to_sign_2212 = {
                    owl_signed_by_pkS(
                        OwlBuf::another_ref(&owl_b205),
                        owl_pk::another_ref(
                            &owl__pkB(OwlBuf::another_ref(&OwlBuf::another_ref(&self.pk_owl_skB))),
                        ),
                        OwlBuf::another_ref(&owl_declassified_buf119210),
                    )
                };
                let owl_msg_to_sign_2212 = owl_signed_by_pkS::another_ref(
                    &tmp_owl_msg_to_sign_2212,
                );
                let tmp_owl_sig1213 = {
                    owl_sign(
                        SecretBuf::another_ref(&owl_sigK202),
                        OwlBuf::another_ref(&serialize_owl_signed_by_pkS(&owl_msg_to_sign_1209)),
                    )
                };
                let owl_sig1213 = OwlBuf::from_vec(tmp_owl_sig1213);
                let tmp_owl_sig2214 = {
                    owl_sign(
                        SecretBuf::another_ref(&owl_sigK202),
                        OwlBuf::another_ref(&serialize_owl_signed_by_pkS(&owl_msg_to_sign_2212)),
                    )
                };
                let owl_sig2214 = OwlBuf::from_vec(tmp_owl_sig2214);
                let owl__215 = {
                    effects.owl_output::<((), state_S)>(
                        Tracked(&mut itree),
                        serialize_owl_tickets(
                            &owl_tickets(
                                OwlBuf::another_ref(&owl_sig1213),
                                OwlBuf::another_ref(&owl_sig2214),
                                owl_signed_by_pkS::another_ref(&owl_msg_to_sign_1209),
                                owl_signed_by_pkS::another_ref(&owl_msg_to_sign_2212),
                            ),
                        ).as_slice(),
                        Some(&A_addr()),
                        &S_addr(),
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

} // verus!
