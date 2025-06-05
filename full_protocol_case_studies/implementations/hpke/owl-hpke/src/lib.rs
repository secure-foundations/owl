// Extracted verus code from file tests/wip/hpke/full.owl:
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]

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
    properties::*, regular::builder::*, regular::bytes::*, regular::bytes_n::*, regular::choice::*,
    regular::tag::*, regular::tail::*, regular::uints::*, regular::*, utils::*,
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


#[derive(Debug)]
pub enum OwlError {
    IntegerOverflow,
}

verus! {

pub spec const SPEC_CIPHER: owl_aead::Mode = crate::owl_aead::Mode::Chacha20Poly1305;

pub spec const SPEC_ENCKEY_SIZE: usize = owl_aead::spec_key_size(CIPHER);

pub spec const SPEC_TAG_SIZE: usize = owl_aead::spec_tag_size(CIPHER);

pub spec const SPEC_NONCE_SIZE: usize = owl_aead::spec_nonce_size(CIPHER);

pub spec const SPEC_HMAC_MODE: owl_hmac::Mode = crate::owl_hmac::Mode::Sha512;

pub spec const SPEC_MACKEY_SIZE: usize = owl_hmac::spec_key_size(HMAC_MODE);

pub spec const SPEC_KDFKEY_SIZE: usize = owl_hkdf::spec_kdfkey_size();

pub spec const SPEC_COUNTER_SIZE: usize = 12usize;

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
    12usize
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

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct TcpListenerWrapper(std::net::TcpListener);

#[verifier(external_type_specification)]
pub struct OwlErrorWrapper(OwlError);

#[verifier(external_body)]
pub fn owl_output<A>(
    Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
    x: &[u8],
    dest_addr: &str,
    ret_addr: &str,
    obuf: &mut [u8]
)
    requires
        old(t).view().is_output(x.view(), endpoint_of_addr(dest_addr.view())),
    ensures
        t.view() == old(t).view().give_output(),
{
    obuf[..x.len()].copy_from_slice(x);
}

#[verifier(external_body)]
pub fn owl_input<A, 'a>(
    Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
    ibuf: &'a [u8],
) -> (ie: (&'a [u8], String))
    requires
        old(t).view().is_input(),
    ensures
        t.view() == old(t).view().take_input(ie.0.view(), endpoint_of_addr(ie.1.view())),
{
    (ibuf, "".to_string())
}

#[verifier(external_body)]
pub fn owl_sample<A, 'a>(Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>, n: usize) -> (res:
    SecretBuf<'a>)
    requires
        old(t).view().is_sample(n),
    ensures
        t.view() == old(t).view().get_sample(res.view()),
        res.len_valid(),
{
    OwlBuf::from_vec(owl_util::gen_rand_bytes(n)).into_secret()
}

#[verifier(external_body)]
pub fn owl_output_serialize_fused<A, I: VestInput, C: View + Combinator<I, Vec<u8>>>(
    Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
    comb: C,
    val: C::Result,
    obuf: &mut Vec<u8>,
    dest_addr: &str,
    ret_addr: &str,
) where <C as View>::V: SecureSpecCombinator<SpecResult = <C::Result as View>::V>
    requires
        comb@.spec_serialize(val.view()) matches Ok(b) ==> old(t).view().is_output(
            b,
            endpoint_of_addr(dest_addr.view()),
        ),
    ensures
        t.view() == old(t).view().give_output(),
        comb@.spec_serialize(val.view()) matches Ok(b) ==> obuf.view() == b,
{
    let ser_result = comb.serialize(val, obuf, 0);
    assume(ser_result.is_ok());
    if let Ok((num_written)) = ser_result {
        // assert(obuf.view() == comb.spec_serialize((arg.view()))->Ok_0);
    } else {
        assert(false);
    }
}

// for debugging purposes, not used by the compiler
#[verifier(external_body)]
pub fn debug_print_bytes(x: &[u8]) {
    println!("debug_print_bytes: {:?}", x);
}

} // verus!
verus! {

// ------------------------------------
// ---------- SPECIFICATIONS ----------
// ------------------------------------
spec fn spec_combinator_owlSpec_hpke_ciphertext() -> (Bytes, Tail) {
    let field_1 = Bytes(32);
    let field_2 = Tail;
    (field_1, field_2)
}

exec fn exec_combinator_owl_hpke_ciphertext() -> (res: (Bytes, Tail))
    ensures
        res.view() == spec_combinator_owlSpec_hpke_ciphertext(),
{
    let field_1 = Bytes(32);
    let field_2 = Tail;
    (field_1, field_2)
}

pub struct owlSpec_hpke_ciphertext {
    pub owlSpec_hc_pk: Seq<u8>,
    pub owlSpec_hc_cipher: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_hpke_ciphertext(x: Seq<u8>) -> Option<owlSpec_hpke_ciphertext> {
    let spec_comb = spec_combinator_owlSpec_hpke_ciphertext();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec_hc_pk, owlSpec_hc_cipher)) = parsed;
        Some(owlSpec_hpke_ciphertext { owlSpec_hc_pk, owlSpec_hc_cipher })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_hpke_ciphertext_inner(x: owlSpec_hpke_ciphertext) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec_hc_pk.len(), x.owlSpec_hc_cipher.len() ] {
        let spec_comb = spec_combinator_owlSpec_hpke_ciphertext();
        if let Ok(serialized) = spec_comb.spec_serialize(((x.owlSpec_hc_pk, x.owlSpec_hc_cipher))) {
            Some(serialized)
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_hpke_ciphertext(x: owlSpec_hpke_ciphertext) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_hpke_ciphertext_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_hpke_ciphertext {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_hpke_ciphertext(self)
    }
}

pub open spec fn hpke_ciphertext(
    arg_owlSpec_hc_pk: Seq<u8>,
    arg_owlSpec_hc_cipher: Seq<u8>,
) -> owlSpec_hpke_ciphertext {
    owlSpec_hpke_ciphertext {
        owlSpec_hc_pk: arg_owlSpec_hc_pk,
        owlSpec_hc_cipher: arg_owlSpec_hc_cipher,
    }
}

spec fn spec_combinator_owlSpec_AuthEncapResult() -> (Bytes, Bytes) {
    let field_1 = Bytes(32);
    let field_2 = Bytes(32);
    (field_1, field_2)
}

exec fn exec_combinator_owl_AuthEncapResult() -> (res: (Bytes, Bytes))
    ensures
        res.view() == spec_combinator_owlSpec_AuthEncapResult(),
{
    let field_1 = Bytes(32);
    let field_2 = Bytes(32);
    (field_1, field_2)
}

pub struct owlSpec_AuthEncapResult {
    pub owlSpec_aer_shared_secret: Seq<u8>,
    pub owlSpec_aer_pke: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_AuthEncapResult(x: Seq<u8>) -> Option<owlSpec_AuthEncapResult> {
    let spec_comb = spec_combinator_owlSpec_AuthEncapResult();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec_aer_shared_secret, owlSpec_aer_pke)) = parsed;
        Some(owlSpec_AuthEncapResult { owlSpec_aer_shared_secret, owlSpec_aer_pke })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_AuthEncapResult_inner(x: owlSpec_AuthEncapResult) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec_aer_shared_secret.len(), x.owlSpec_aer_pke.len() ] {
        let spec_comb = spec_combinator_owlSpec_AuthEncapResult();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((x.owlSpec_aer_shared_secret, x.owlSpec_aer_pke)),
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
pub closed spec fn serialize_owlSpec_AuthEncapResult(x: owlSpec_AuthEncapResult) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_AuthEncapResult_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_AuthEncapResult {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_AuthEncapResult(self)
    }
}

pub open spec fn AuthEncapResult(
    arg_owlSpec_aer_shared_secret: Seq<u8>,
    arg_owlSpec_aer_pke: Seq<u8>,
) -> owlSpec_AuthEncapResult {
    owlSpec_AuthEncapResult {
        owlSpec_aer_shared_secret: arg_owlSpec_aer_shared_secret,
        owlSpec_aer_pke: arg_owlSpec_aer_pke,
    }
}

pub struct owlSpec_ContextS {
    pub owlSpec_ctxtS_ss: Ghost<()>,
    pub owlSpec_ctxtS_base: Seq<u8>,
    pub owlSpec_ctxtS_sk: Seq<u8>,
    pub owlSpec_ctxtS_export: Seq<u8>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_ContextS(x: Seq<u8>) -> Option<owlSpec_ContextS> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_ContextS_inner(x: owlSpec_ContextS) -> Option<Seq<u8>> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_ContextS(x: owlSpec_ContextS) -> Seq<u8> {
    todo!()
}

impl OwlSpecSerialize for owlSpec_ContextS {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_ContextS(self)
    }
}

pub open spec fn ContextS(
    arg_owlSpec_ctxtS_ss: Ghost<()>,
    arg_owlSpec_ctxtS_base: Seq<u8>,
    arg_owlSpec_ctxtS_sk: Seq<u8>,
    arg_owlSpec_ctxtS_export: Seq<u8>,
) -> owlSpec_ContextS {
    owlSpec_ContextS {
        owlSpec_ctxtS_ss: arg_owlSpec_ctxtS_ss,
        owlSpec_ctxtS_base: arg_owlSpec_ctxtS_base,
        owlSpec_ctxtS_sk: arg_owlSpec_ctxtS_sk,
        owlSpec_ctxtS_export: arg_owlSpec_ctxtS_export,
    }
}

pub struct owlSpec_AuthDecapResult {
    pub owlSpec_adr_eph: Ghost<()>,
    pub owlSpec_adr_shared_secret: Seq<u8>,
    pub owlSpec_adr_shared_secret_inj: Ghost<()>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_AuthDecapResult(x: Seq<u8>) -> Option<owlSpec_AuthDecapResult> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_AuthDecapResult_inner(x: owlSpec_AuthDecapResult) -> Option<
    Seq<u8>,
> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_AuthDecapResult(x: owlSpec_AuthDecapResult) -> Seq<u8> {
    todo!()
}

impl OwlSpecSerialize for owlSpec_AuthDecapResult {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_AuthDecapResult(self)
    }
}

pub open spec fn AuthDecapResult(
    arg_owlSpec_adr_eph: Ghost<()>,
    arg_owlSpec_adr_shared_secret: Seq<u8>,
    arg_owlSpec_adr_shared_secret_inj: Ghost<()>,
) -> owlSpec_AuthDecapResult {
    owlSpec_AuthDecapResult {
        owlSpec_adr_eph: arg_owlSpec_adr_eph,
        owlSpec_adr_shared_secret: arg_owlSpec_adr_shared_secret,
        owlSpec_adr_shared_secret_inj: arg_owlSpec_adr_shared_secret_inj,
    }
}

pub struct owlSpec_ContextR {
    pub owlSpec_ctxtR_eph: Ghost<()>,
    pub owlSpec_ctxtR_confirmed: bool,
    pub owlSpec_ctxtR_ss: Ghost<()>,
    pub owlSpec_ctxtR_base: Seq<u8>,
    pub owlSpec_ctxtR_sk: Seq<u8>,
    pub owlSpec_ctxtR_export: Seq<u8>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_ContextR(x: Seq<u8>) -> Option<owlSpec_ContextR> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_ContextR_inner(x: owlSpec_ContextR) -> Option<Seq<u8>> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_ContextR(x: owlSpec_ContextR) -> Seq<u8> {
    todo!()
}

impl OwlSpecSerialize for owlSpec_ContextR {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_ContextR(self)
    }
}

pub open spec fn ContextR(
    arg_owlSpec_ctxtR_eph: Ghost<()>,
    arg_owlSpec_ctxtR_confirmed: bool,
    arg_owlSpec_ctxtR_ss: Ghost<()>,
    arg_owlSpec_ctxtR_base: Seq<u8>,
    arg_owlSpec_ctxtR_sk: Seq<u8>,
    arg_owlSpec_ctxtR_export: Seq<u8>,
) -> owlSpec_ContextR {
    owlSpec_ContextR {
        owlSpec_ctxtR_eph: arg_owlSpec_ctxtR_eph,
        owlSpec_ctxtR_confirmed: arg_owlSpec_ctxtR_confirmed,
        owlSpec_ctxtR_ss: arg_owlSpec_ctxtR_ss,
        owlSpec_ctxtR_base: arg_owlSpec_ctxtR_base,
        owlSpec_ctxtR_sk: arg_owlSpec_ctxtR_sk,
        owlSpec_ctxtR_export: arg_owlSpec_ctxtR_export,
    }
}

pub enum owlSpec_OpenMsg {
    owlSpec_NoMsg(),
    owlSpec_SomeMsg(Seq<u8>),
}

use owlSpec_OpenMsg::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_OpenMsg(x: Seq<u8>) -> Option<owlSpec_OpenMsg> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Bytes(0)), (Tag::spec_new(U8, 2), Tail));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owlSpec_OpenMsg::owlSpec_NoMsg(),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_OpenMsg::owlSpec_SomeMsg(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_OpenMsg_inner(x: owlSpec_OpenMsg) -> Option<Seq<u8>> {
    let spec_comb = ord_choice!((Tag::spec_new(U8, 1), Bytes(0)), (Tag::spec_new(U8, 2), Tail));
    match x {
        owlSpec_OpenMsg::owlSpec_NoMsg() => {
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
        owlSpec_OpenMsg::owlSpec_SomeMsg(x) => {
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
pub closed spec fn serialize_owlSpec_OpenMsg(x: owlSpec_OpenMsg) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_OpenMsg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_OpenMsg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_OpenMsg(self)
    }
}

pub open spec fn NoMsg() -> owlSpec_OpenMsg {
    crate::owlSpec_OpenMsg::owlSpec_NoMsg()
}

pub open spec fn SomeMsg(x: Seq<u8>) -> owlSpec_OpenMsg {
    crate::owlSpec_OpenMsg::owlSpec_SomeMsg(x)
}

pub open spec fn NoMsg_enumtest(x: owlSpec_OpenMsg) -> bool {
    match x {
        owlSpec_OpenMsg::owlSpec_NoMsg() => true,
        _ => false,
    }
}

pub open spec fn SomeMsg_enumtest(x: owlSpec_OpenMsg) -> bool {
    match x {
        owlSpec_OpenMsg::owlSpec_SomeMsg(_) => true,
        _ => false,
    }
}

pub struct owlSpec_OpenResult {
    pub owlSpec_or_ctxt: owlSpec_ContextR,
    pub owlSpec_or_pt: owlSpec_OpenMsg,
    pub owlSpec_or_wf: Ghost<()>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_OpenResult(x: Seq<u8>) -> Option<owlSpec_OpenResult> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_OpenResult_inner(x: owlSpec_OpenResult) -> Option<Seq<u8>> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_OpenResult(x: owlSpec_OpenResult) -> Seq<u8> {
    todo!()
}

impl OwlSpecSerialize for owlSpec_OpenResult {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_OpenResult(self)
    }
}

pub open spec fn OpenResult(
    arg_owlSpec_or_ctxt: owlSpec_ContextR,
    arg_owlSpec_or_pt: owlSpec_OpenMsg,
    arg_owlSpec_or_wf: Ghost<()>,
) -> owlSpec_OpenResult {
    owlSpec_OpenResult {
        owlSpec_or_ctxt: arg_owlSpec_or_ctxt,
        owlSpec_or_pt: arg_owlSpec_or_pt,
        owlSpec_or_wf: arg_owlSpec_or_wf,
    }
}

#[verifier::opaque]
pub open spec fn SingleShotOpen_spec(
    cfg: cfg_receiver,
    mut_state: state_receiver,
    pkS: Seq<u8>,
) -> (res: ITree<(Option<owlSpec_OpenResult>, state_receiver), Endpoint>) {
    owl_spec!(mut_state, state_receiver,
        (input(i,_33)) in
(parse (parse_owlSpec_hpke_ciphertext(i)) as (owlSpec_hpke_ciphertext{owlSpec_hc_pk : eph, owlSpec_hc_cipher : ct}) in {
let oadr = (call(AuthDecap_spec(cfg, mut_state, pkS, eph))) in
let caseval = ((ret(oadr))) in
(case (caseval) {
| Some(adr) => {
let ctxt = (call(KeyScheduleR_spec(cfg, mut_state, adr))) in
let res = (call(Open_spec(cfg, mut_state, ctxt, empty_seq_u8(), ct))) in
(ret(Option::Some(res)))
},
| None => {
(ret(Option::None))
},
}
)
} otherwise ((ret(Option::None))))
    )
}

#[verifier::opaque]
pub open spec fn Open_spec(
    cfg: cfg_receiver,
    mut_state: state_receiver,
    ctxtR: owlSpec_ContextR,
    ct_aad: Seq<u8>,
    ct: Seq<u8>,
) -> (res: ITree<(owlSpec_OpenResult, state_receiver), Endpoint>) {
    owl_spec!(mut_state, state_receiver,
        let ctxtR = ((ret(ctxtR))) in
(parse (ctxtR) as (owlSpec_ContextR{owlSpec_ctxtR_eph : eph, owlSpec_ctxtR_confirmed : confirmed, owlSpec_ctxtR_ss : ss, owlSpec_ctxtR_base : bn, owlSpec_ctxtR_sk : sk, owlSpec_ctxtR_export : exp}) in {
let ctr = ((ret(counter_as_bytes(mut_state.owl_recv_counter)))) in
let iv = ((ret(xor(bn, ctr)))) in
let _unused318 = (((inc_counter(owl_recv_counter)))) in
let caseval = ((declassify(DeclassifyingOp::StAeadDec(sk, ct, iv, ct_aad))) in
(ret(dec_st_aead(sk, ct, iv, ct_aad)))) in
(case (caseval) {
| Some(x) => {
let ctxtR_ = ((ret(ContextR(ghost_unit(), true, ghost_unit(), bn, sk, exp)))) in
let _assert_106 = ((ret(ghost_unit()))) in
let res = ((ret(OpenResult(ctxtR_, SomeMsg(x), ghost_unit())))) in
(ret(res))
},
| None => {
let res = ((ret(OpenResult(ctxtR, NoMsg(), ghost_unit())))) in
(ret(res))
},
}
)
} )
    )
}

#[verifier::opaque]
pub open spec fn KeyScheduleR_spec(
    cfg: cfg_receiver,
    mut_state: state_receiver,
    adr: owlSpec_AuthDecapResult,
) -> (res: ITree<(owlSpec_ContextR, state_receiver), Endpoint>) {
    owl_spec!(mut_state, state_receiver,
        let adr_ = ((ret(adr))) in
(parse (adr_) as (owlSpec_AuthDecapResult{owlSpec_adr_eph : eph, owlSpec_adr_shared_secret : shared_secret, owlSpec_adr_shared_secret_inj : _unused320}) in {
let kdfval156 = ((ret(kdf((0 + COUNTER_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), base_nonce_kdf_info())))) in
let base_nonce = ((ret(Seq::subrange(kdfval156, 0, 0 + COUNTER_SIZE)))) in
let kdfval161 = ((ret(kdf((0 + ENCKEY_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), key_kdf_info())))) in
let sk = ((ret(Seq::subrange(kdfval161, 0, 0 + ENCKEY_SIZE)))) in
let kdfval164 = ((ret(kdf((0 + NONCE_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), export_kdf_info())))) in
let exp = ((ret(Seq::subrange(kdfval164, 0, 0 + NONCE_SIZE)))) in
let res = ((ret(ContextR(ghost_unit(), false, ghost_unit(), base_nonce, sk, exp)))) in
(ret(res))
} )
    )
}

#[verifier::opaque]
pub open spec fn AuthDecap_spec(
    cfg: cfg_receiver,
    mut_state: state_receiver,
    pkS: Seq<u8>,
    eph: Seq<u8>,
) -> (res: ITree<(Option<owlSpec_AuthDecapResult>, state_receiver), Endpoint>) {
    owl_spec!(mut_state, state_receiver,
        (if (is_group_elem(eph)) then
(let dh = ((ret(concat(dh_combine(eph, cfg.owl_skR.view()), dh_combine(pkS, cfg.owl_skR.view()))))) in
let kem_context = ((ret(concat(concat(eph, dhpk(cfg.owl_skR.view())), pkS)))) in
let kdfval173 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, empty_seq_u8(), lbl_ikm(kem_suite_id(), eae_prk(), dh), lbl_info(kem_suite_id(), kdfkey_len(), shared_secret_string(), kem_context))))) in
let shared_secret = ((ret(Seq::subrange(kdfval173, 0, 0 + KDFKEY_SIZE)))) in
let shared_secret_ghost = ((ret(ghost_unit()))) in
let res = ((ret(AuthDecapResult(ghost_unit(), shared_secret, ghost_unit())))) in
let pres = ((ret(res))) in
(ret(Option::Some(pres))))
else
((ret(Option::None))))
    )
}

#[verifier::opaque]
pub open spec fn SingleShotSeal_spec(
    cfg: cfg_sender,
    mut_state: state_sender,
    pkR: Seq<u8>,
    dhpk_skE: Seq<u8>,
    dhpk_skS: Seq<u8>,
    x: Seq<u8>,
) -> (res: ITree<((), state_sender), Endpoint>) {
    owl_spec!(mut_state, state_sender,
        let aer = (call(AuthEncap_spec(cfg, mut_state, pkR, dhpk_skE, dhpk_skS))) in
let context = (call(KeyScheduleS_spec(cfg, mut_state, aer))) in
let c = (call(Seal_spec(cfg, mut_state, context, x))) in
(parse (aer) as (owlSpec_AuthEncapResult{owlSpec_aer_shared_secret : _unused327, owlSpec_aer_pke : pk}) in {
(output (serialize_owlSpec_hpke_ciphertext(hpke_ciphertext(pk, c))) to (Endpoint::Loc_receiver))
} )
    )
}

#[verifier::opaque]
pub open spec fn Seal_spec(
    cfg: cfg_sender,
    mut_state: state_sender,
    ctxt: owlSpec_ContextS,
    x: Seq<u8>,
) -> (res: ITree<(Seq<u8>, state_sender), Endpoint>) {
    owl_spec!(mut_state, state_sender,
        (parse (ctxt) as (owlSpec_ContextS{owlSpec_ctxtS_ss : _unused330, owlSpec_ctxtS_base : base, owlSpec_ctxtS_sk : sk, owlSpec_ctxtS_export : _unused331}) in {
let _unused332 = (call(sent_message_spec(cfg, mut_state, ghost_unit()))) in
let send_counter = ((ret(counter_as_bytes(mut_state.owl_send_counter)))) in
let _unused333 = (((inc_counter(owl_send_counter)))) in
let i = ((ret(xor(send_counter, base)))) in
(ret(enc_st_aead(sk, x, i, empty_seq_u8())))
} )
    )
}

#[verifier::opaque]
pub open spec fn sent_message_spec(cfg: cfg_sender, mut_state: state_sender, x: Ghost<()>) -> (res:
    ITree<((), state_sender), Endpoint>) {
    owl_spec!(mut_state, state_sender,
        (ret(()))
    )
}

#[verifier::opaque]
pub open spec fn KeyScheduleS_spec(
    cfg: cfg_sender,
    mut_state: state_sender,
    aer: owlSpec_AuthEncapResult,
) -> (res: ITree<(owlSpec_ContextS, state_sender), Endpoint>) {
    owl_spec!(mut_state, state_sender,
        (parse (aer) as (owlSpec_AuthEncapResult{owlSpec_aer_shared_secret : shared_secret, owlSpec_aer_pke : pkE}) in {
let kdfval248 = ((ret(kdf((0 + COUNTER_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), base_nonce_kdf_info())))) in
let base_nonce = ((ret(Seq::subrange(kdfval248, 0, 0 + COUNTER_SIZE)))) in
let kdfval251 = ((ret(kdf((0 + ENCKEY_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), key_kdf_info())))) in
let sk = ((ret(Seq::subrange(kdfval251, 0, 0 + ENCKEY_SIZE)))) in
let kdfval254 = ((ret(kdf((0 + NONCE_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), export_kdf_info())))) in
let exp = ((ret(Seq::subrange(kdfval254, 0, 0 + NONCE_SIZE)))) in
(ret(ContextS(ghost_unit(), base_nonce, sk, exp)))
} )
    )
}

#[verifier::opaque]
pub open spec fn AuthEncap_spec(
    cfg: cfg_sender,
    mut_state: state_sender,
    pkR: Seq<u8>,
    dhpk_skE: Seq<u8>,
    dhpk_skS: Seq<u8>,
) -> (res: ITree<(owlSpec_AuthEncapResult, state_sender), Endpoint>) {
    owl_spec!(mut_state, state_sender,
        let dh = ((ret(concat(dh_combine(pkR, cfg.owl_skE.view()), dh_combine(pkR, cfg.owl_skS.view()))))) in
let kem_context = ((ret(concat(concat(dhpk_skE, pkR), dhpk_skS)))) in
let kdfval262 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, empty_seq_u8(), lbl_ikm(kem_suite_id(), eae_prk(), dh), lbl_info(kem_suite_id(), kdfkey_len(), shared_secret_string(), kem_context))))) in
let shared_secret = ((ret(Seq::subrange(kdfval262, 0, 0 + KDFKEY_SIZE)))) in
let res = ((ret(shared_secret))) in
(ret(AuthEncapResult(res, dhpk(cfg.owl_skE.view()))))
    )
}

#[verifier::opaque]
pub closed spec fn base_nonce_kdf_info() -> (res: Seq<u8>) {
    lbl_info(hpke_suite_id(), enckey_len(), base_nonce_string(), key_schedule_context())
}

#[verifier::opaque]
pub closed spec fn base_nonce_string() -> (res: Seq<u8>) {
    seq![0x62u8, 0x61u8, 0x73u8, 0x65u8, 0x5fu8, 0x6eu8, 0x6fu8, 0x6eu8, 0x63u8, 0x65u8, ]
}

#[verifier::opaque]
pub closed spec fn crh_labeled_extract_0salt(lbl: Seq<u8>, ikm: Seq<u8>) -> (res: Seq<u8>) {
    crh(concat(concat(concat(hpke_v1(), hpke_suite_id()), lbl), ikm))
}

#[verifier::opaque]
pub closed spec fn dh_secret_kdf_ikm(psk_: Seq<u8>) -> (res: Seq<u8>) {
    lbl_ikm(hpke_suite_id(), secret_string(), psk_)
}

#[verifier::opaque]
pub closed spec fn eae_prk() -> (res: Seq<u8>) {
    seq![0x65u8, 0x61u8, 0x65u8, 0x5fu8, 0x70u8, 0x72u8, 0x6bu8, ]
}

#[verifier::opaque]
pub closed spec fn enckey_len() -> (res: Seq<u8>) {
    seq![0x00u8, 0x20u8, ]
}

#[verifier::opaque]
pub closed spec fn export_kdf_info() -> (res: Seq<u8>) {
    lbl_info(hpke_suite_id(), enckey_len(), export_string(), key_schedule_context())
}

#[verifier::opaque]
pub closed spec fn export_string() -> (res: Seq<u8>) {
    seq![0x65u8, 0x78u8, 0x70u8, ]
}

#[verifier::opaque]
pub closed spec fn hpke_suite_id() -> (res: Seq<u8>) {
    seq![0x48u8, 0x50u8, 0x4bu8, 0x45u8, 0x00u8, 0x20u8, 0x00u8, 0x01u8, 0x00u8, 0x03u8, ]
}

#[verifier::opaque]
pub closed spec fn hpke_v1() -> (res: Seq<u8>) {
    seq![0x48u8, 0x50u8, 0x4bu8, 0x45u8, 0x2du8, 0x76u8, 0x31u8, ]
}

#[verifier::opaque]
pub closed spec fn info() -> (res: Seq<u8>) {
    empty_seq_u8()
}

#[verifier::opaque]
pub closed spec fn info_hash_string() -> (res: Seq<u8>) {
    seq![0x69u8, 0x6eu8, 0x66u8, 0x6fu8, 0x5fu8, 0x68u8, 0x61u8, 0x73u8, 0x68u8, ]
}

#[verifier::opaque]
pub closed spec fn kdfkey_len() -> (res: Seq<u8>) {
    seq![0x00u8, 0x20u8, ]
}

#[verifier::opaque]
pub closed spec fn kem_suite_id() -> (res: Seq<u8>) {
    seq![0x4bu8, 0x45u8, 0x4du8, 0x00u8, 0x20u8, ]
}

#[verifier::opaque]
pub closed spec fn key_kdf_info() -> (res: Seq<u8>) {
    lbl_info(hpke_suite_id(), enckey_len(), key_string(), key_schedule_context())
}

#[verifier::opaque]
pub closed spec fn key_schedule_context() -> (res: Seq<u8>) {
    seq![0x03u8, 0x43u8, 0x1du8, 0xf6u8, 0xcdu8, 0x95u8, 0xe1u8, 0x1fu8, 0xf4u8, 0x9du8, 0x70u8, 0x13u8, 0x56u8, 0x3bu8, 0xafu8, 0x7fu8, 0x11u8, 0x58u8, 0x8cu8, 0x75u8, 0xa6u8, 0x61u8, 0x1eu8, 0xe2u8, 0xa4u8, 0x40u8, 0x4au8, 0x49u8, 0x30u8, 0x6au8, 0xe4u8, 0xcfu8, 0xc5u8, 0x55u8, 0xe7u8, 0xb3u8, 0x9du8, 0x7au8, 0x73u8, 0x55u8, 0x3cu8, 0x14u8, 0xeeu8, 0xe3u8, 0xb6u8, 0x05u8, 0xf8u8, 0xc4u8, 0x43u8, 0x8fu8, 0xb8u8, 0xc4u8, 0xa5u8, 0xd3u8, 0x2fu8, 0xb2u8, 0xbeu8, 0xf7u8, 0x35u8, 0xf2u8, 0x61u8, 0x28u8, 0xedu8, 0x56u8, 0x95u8, ]
}


#[verifier::opaque]
pub closed spec fn key_string() -> (res: Seq<u8>) {
    seq![0x6bu8, 0x65u8, 0x79u8, ]
}

#[verifier::opaque]
pub closed spec fn lbl_ikm(suite_id: Seq<u8>, lbl: Seq<u8>, ikm: Seq<u8>) -> (res: Seq<u8>) {
    concat(concat(concat(hpke_v1(), suite_id), lbl), ikm)
}

#[verifier::opaque]
pub closed spec fn lbl_info(suite_id: Seq<u8>, len: Seq<u8>, lbl: Seq<u8>, info: Seq<u8>) -> (res:
    Seq<u8>) {
    concat(concat(concat(concat(len, hpke_v1()), suite_id), lbl), info)
}

#[verifier::opaque]
pub closed spec fn mode() -> (res: Seq<u8>) {
    seq![0x03u8, ]
}

#[verifier::opaque]
pub closed spec fn psk_id() -> (res: Seq<u8>) {
    empty_seq_u8()
}

#[verifier::opaque]
pub closed spec fn psk_id_hash_string() -> (res: Seq<u8>) {
    seq![0x70u8, 0x73u8, 0x6bu8, 0x5fu8, 0x69u8, 0x64u8, 0x5fu8, 0x68u8, 0x61u8, 0x73u8, 0x68u8, ]
}

#[verifier::opaque]
pub closed spec fn secret_string() -> (res: Seq<u8>) {
    seq![0x73u8, 0x65u8, 0x63u8, 0x72u8, 0x65u8, 0x74u8, ]
}

#[verifier::opaque]
pub closed spec fn shared_secret_string() -> (res: Seq<u8>) {
    seq![0x73u8, 0x68u8, 0x61u8, 0x72u8, 0x65u8, 0x64u8, 0x5fu8, 0x73u8, 0x65u8, 0x63u8, 0x72u8, 0x65u8, 0x74u8, ]
}

// ------------------------------------
// ---------- IMPLEMENTATIONS ---------
// ------------------------------------
#[derive(Clone,Copy)]
pub enum Endpoint {
    Loc_receiver,
    Loc_sender,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier(external_body)]
pub const fn receiver_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_receiver,
{
    "127.0.0.1:9001"
}

#[verifier(external_body)]
pub const fn sender_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_sender,
{
    "127.0.0.1:9002"
}

pub struct owl_hpke_ciphertext<'a> {
    pub owl_hc_pk: OwlBuf<'a>,
    pub owl_hc_cipher: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_hpke_ciphertext<'a>(arg_owl_hc_pk: OwlBuf<'a>, arg_owl_hc_cipher: OwlBuf<'a>) -> (res:
    owl_hpke_ciphertext<'a>)
    ensures
        res.owl_hc_pk.view() == arg_owl_hc_pk.view(),
        res.owl_hc_cipher.view() == arg_owl_hc_cipher.view(),
{
    owl_hpke_ciphertext { owl_hc_pk: arg_owl_hc_pk, owl_hc_cipher: arg_owl_hc_cipher }
}

impl<'a> owl_hpke_ciphertext<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_hpke_ciphertext<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_hpke_ciphertext {
            owl_hc_pk: OwlBuf::another_ref(&self.owl_hc_pk),
            owl_hc_cipher: OwlBuf::another_ref(&self.owl_hc_cipher),
        }
    }
}

impl View for owl_hpke_ciphertext<'_> {
    type V = owlSpec_hpke_ciphertext;

    open spec fn view(&self) -> owlSpec_hpke_ciphertext {
        owlSpec_hpke_ciphertext {
            owlSpec_hc_pk: self.owl_hc_pk.view(),
            owlSpec_hc_cipher: self.owl_hc_cipher.view(),
        }
    }
}

pub exec fn parse_owl_hpke_ciphertext<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_hpke_ciphertext<'a>>)
    ensures
        res is Some ==> parse_owlSpec_hpke_ciphertext(arg.view()) is Some,
        res is None ==> parse_owlSpec_hpke_ciphertext(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_hpke_ciphertext(arg.view())->Some_0,
{
    reveal(parse_owlSpec_hpke_ciphertext);
    let exec_comb = exec_combinator_owl_hpke_ciphertext();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl_hc_pk, owl_hc_cipher) = parsed;
        Some(
            owl_hpke_ciphertext {
                owl_hc_pk: OwlBuf::another_ref(&owl_hc_pk),
                owl_hc_cipher: OwlBuf::another_ref(&owl_hc_cipher),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_hpke_ciphertext_inner<'a>(arg: &owl_hpke_ciphertext<'a>) -> (res: Option<
    OwlBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_hpke_ciphertext_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_hpke_ciphertext_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_hpke_ciphertext_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_hpke_ciphertext_inner);
    if no_usize_overflows![ arg.owl_hc_pk.len(), arg.owl_hc_cipher.len(), 0 ] {
        let exec_comb = exec_combinator_owl_hpke_ciphertext();
        let mut obuf = vec_u8_of_len(arg.owl_hc_pk.len() + arg.owl_hc_cipher.len() + 0);
        let ser_result = exec_comb.serialize(
            (OwlBuf::another_ref(&arg.owl_hc_pk), OwlBuf::another_ref(&arg.owl_hc_cipher)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_hpke_ciphertext_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_hpke_ciphertext<'a>(arg: &owl_hpke_ciphertext<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_hpke_ciphertext(arg.view()),
{
    reveal(serialize_owlSpec_hpke_ciphertext);
    let res = serialize_owl_hpke_ciphertext_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_AuthEncapResult<'a> {
    pub owl_aer_shared_secret: SecretBuf<'a>,
    pub owl_aer_pke: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_AuthEncapResult<'a>(
    arg_owl_aer_shared_secret: SecretBuf<'a>,
    arg_owl_aer_pke: OwlBuf<'a>,
) -> (res: owl_AuthEncapResult<'a>)
    ensures
        res.owl_aer_shared_secret.view() == arg_owl_aer_shared_secret.view(),
        res.owl_aer_pke.view() == arg_owl_aer_pke.view(),
{
    owl_AuthEncapResult {
        owl_aer_shared_secret: arg_owl_aer_shared_secret,
        owl_aer_pke: arg_owl_aer_pke,
    }
}

impl<'a> owl_AuthEncapResult<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_AuthEncapResult<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_AuthEncapResult {
            owl_aer_shared_secret: SecretBuf::another_ref(&self.owl_aer_shared_secret),
            owl_aer_pke: OwlBuf::another_ref(&self.owl_aer_pke),
        }
    }
}

impl View for owl_AuthEncapResult<'_> {
    type V = owlSpec_AuthEncapResult;

    open spec fn view(&self) -> owlSpec_AuthEncapResult {
        owlSpec_AuthEncapResult {
            owlSpec_aer_shared_secret: self.owl_aer_shared_secret.view(),
            owlSpec_aer_pke: self.owl_aer_pke.view(),
        }
    }
}

pub exec fn parse_owl_AuthEncapResult<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_AuthEncapResult<'a>>)
    ensures
        res is Some ==> parse_owlSpec_AuthEncapResult(arg.view()) is Some,
        res is None ==> parse_owlSpec_AuthEncapResult(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_AuthEncapResult(arg.view())->Some_0,
{
    reveal(parse_owlSpec_AuthEncapResult);
    let exec_comb = exec_combinator_owl_AuthEncapResult();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl_aer_shared_secret, owl_aer_pke) = parsed;
        Some(
            owl_AuthEncapResult {
                owl_aer_shared_secret: SecretBuf::from_buf(owl_aer_shared_secret.another_ref()),
                owl_aer_pke: OwlBuf::another_ref(&owl_aer_pke),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_AuthEncapResult_inner<'a>(arg: &owl_AuthEncapResult<'a>) -> (res: Option<
    SecretBuf<'a>,
>)
    ensures
        res is Some ==> serialize_owlSpec_AuthEncapResult_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_AuthEncapResult_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_AuthEncapResult_inner(
            arg.view(),
        )->Some_0,
{
    reveal(serialize_owlSpec_AuthEncapResult_inner);
    if no_usize_overflows![ arg.owl_aer_shared_secret.len(), arg.owl_aer_pke.len(), 0 ] {
        let exec_comb = exec_combinator_owl_AuthEncapResult();
        let mut obuf = SecretOutputBuf::new_obuf(
            arg.owl_aer_shared_secret.len() + arg.owl_aer_pke.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                SecretBuf::another_ref(&arg.owl_aer_shared_secret),
                SecretBuf::from_buf(arg.owl_aer_pke.another_ref()),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_AuthEncapResult_inner(arg.view())->Some_0);
            Some(obuf.into_secret_buf())
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_AuthEncapResult<'a>(arg: &owl_AuthEncapResult<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_AuthEncapResult(arg.view()),
{
    reveal(serialize_owlSpec_AuthEncapResult);
    let res = serialize_owl_AuthEncapResult_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_ContextS<'a> {
    pub owl_ctxtS_ss: Ghost<()>,
    pub owl_ctxtS_base: SecretBuf<'a>,
    pub owl_ctxtS_sk: SecretBuf<'a>,
    pub owl_ctxtS_export: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_ContextS<'a>(
    arg_owl_ctxtS_ss: Ghost<()>,
    arg_owl_ctxtS_base: SecretBuf<'a>,
    arg_owl_ctxtS_sk: SecretBuf<'a>,
    arg_owl_ctxtS_export: SecretBuf<'a>,
) -> (res: owl_ContextS<'a>)
    ensures
        res.owl_ctxtS_ss.view() == arg_owl_ctxtS_ss.view(),
        res.owl_ctxtS_base.view() == arg_owl_ctxtS_base.view(),
        res.owl_ctxtS_sk.view() == arg_owl_ctxtS_sk.view(),
        res.owl_ctxtS_export.view() == arg_owl_ctxtS_export.view(),
{
    owl_ContextS {
        owl_ctxtS_ss: arg_owl_ctxtS_ss,
        owl_ctxtS_base: arg_owl_ctxtS_base,
        owl_ctxtS_sk: arg_owl_ctxtS_sk,
        owl_ctxtS_export: arg_owl_ctxtS_export,
    }
}

impl<'a> owl_ContextS<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_ContextS<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_ContextS {
            owl_ctxtS_ss: self.owl_ctxtS_ss,
            owl_ctxtS_base: SecretBuf::another_ref(&self.owl_ctxtS_base),
            owl_ctxtS_sk: SecretBuf::another_ref(&self.owl_ctxtS_sk),
            owl_ctxtS_export: SecretBuf::another_ref(&self.owl_ctxtS_export),
        }
    }
}

impl View for owl_ContextS<'_> {
    type V = owlSpec_ContextS;

    open spec fn view(&self) -> owlSpec_ContextS {
        owlSpec_ContextS {
            owlSpec_ctxtS_ss: ghost_unit(),
            owlSpec_ctxtS_base: self.owl_ctxtS_base.view(),
            owlSpec_ctxtS_sk: self.owl_ctxtS_sk.view(),
            owlSpec_ctxtS_export: self.owl_ctxtS_export.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_ContextS<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_ContextS<'a>>)
    ensures
        res is Some ==> parse_owlSpec_ContextS(arg.view()) is Some,
        res is None ==> parse_owlSpec_ContextS(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_ContextS(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_ContextS_inner(arg: &owl_ContextS) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_ContextS_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_ContextS_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_ContextS_inner(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_ContextS(arg: &owl_ContextS) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_ContextS(arg.view()),
{
    todo!()
}

pub struct owl_AuthDecapResult<'a> {
    pub owl_adr_eph: Ghost<()>,
    pub owl_adr_shared_secret: SecretBuf<'a>,
    pub owl_adr_shared_secret_inj: Ghost<()>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_AuthDecapResult<'a>(
    arg_owl_adr_eph: Ghost<()>,
    arg_owl_adr_shared_secret: SecretBuf<'a>,
    arg_owl_adr_shared_secret_inj: Ghost<()>,
) -> (res: owl_AuthDecapResult<'a>)
    ensures
        res.owl_adr_eph.view() == arg_owl_adr_eph.view(),
        res.owl_adr_shared_secret.view() == arg_owl_adr_shared_secret.view(),
        res.owl_adr_shared_secret_inj.view() == arg_owl_adr_shared_secret_inj.view(),
{
    owl_AuthDecapResult {
        owl_adr_eph: arg_owl_adr_eph,
        owl_adr_shared_secret: arg_owl_adr_shared_secret,
        owl_adr_shared_secret_inj: arg_owl_adr_shared_secret_inj,
    }
}

impl<'a> owl_AuthDecapResult<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_AuthDecapResult<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_AuthDecapResult {
            owl_adr_eph: self.owl_adr_eph,
            owl_adr_shared_secret: SecretBuf::another_ref(&self.owl_adr_shared_secret),
            owl_adr_shared_secret_inj: self.owl_adr_shared_secret_inj,
        }
    }
}

impl View for owl_AuthDecapResult<'_> {
    type V = owlSpec_AuthDecapResult;

    open spec fn view(&self) -> owlSpec_AuthDecapResult {
        owlSpec_AuthDecapResult {
            owlSpec_adr_eph: ghost_unit(),
            owlSpec_adr_shared_secret: self.owl_adr_shared_secret.view(),
            owlSpec_adr_shared_secret_inj: ghost_unit(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_AuthDecapResult<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_AuthDecapResult<'a>>)
    ensures
        res is Some ==> parse_owlSpec_AuthDecapResult(arg.view()) is Some,
        res is None ==> parse_owlSpec_AuthDecapResult(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_AuthDecapResult(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_AuthDecapResult_inner(arg: &owl_AuthDecapResult) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_AuthDecapResult_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_AuthDecapResult_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_AuthDecapResult_inner(
            arg.view(),
        )->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_AuthDecapResult(arg: &owl_AuthDecapResult) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_AuthDecapResult(arg.view()),
{
    todo!()
}

pub struct owl_ContextR<'a> {
    pub owl_ctxtR_eph: Ghost<()>,
    pub owl_ctxtR_confirmed: bool,
    pub owl_ctxtR_ss: Ghost<()>,
    pub owl_ctxtR_base: SecretBuf<'a>,
    pub owl_ctxtR_sk: SecretBuf<'a>,
    pub owl_ctxtR_export: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_ContextR<'a>(
    arg_owl_ctxtR_eph: Ghost<()>,
    arg_owl_ctxtR_confirmed: bool,
    arg_owl_ctxtR_ss: Ghost<()>,
    arg_owl_ctxtR_base: SecretBuf<'a>,
    arg_owl_ctxtR_sk: SecretBuf<'a>,
    arg_owl_ctxtR_export: SecretBuf<'a>,
) -> (res: owl_ContextR<'a>)
    ensures
        res.owl_ctxtR_eph.view() == arg_owl_ctxtR_eph.view(),
        res.owl_ctxtR_confirmed.view() == arg_owl_ctxtR_confirmed.view(),
        res.owl_ctxtR_ss.view() == arg_owl_ctxtR_ss.view(),
        res.owl_ctxtR_base.view() == arg_owl_ctxtR_base.view(),
        res.owl_ctxtR_sk.view() == arg_owl_ctxtR_sk.view(),
        res.owl_ctxtR_export.view() == arg_owl_ctxtR_export.view(),
{
    owl_ContextR {
        owl_ctxtR_eph: arg_owl_ctxtR_eph,
        owl_ctxtR_confirmed: arg_owl_ctxtR_confirmed,
        owl_ctxtR_ss: arg_owl_ctxtR_ss,
        owl_ctxtR_base: arg_owl_ctxtR_base,
        owl_ctxtR_sk: arg_owl_ctxtR_sk,
        owl_ctxtR_export: arg_owl_ctxtR_export,
    }
}

impl<'a> owl_ContextR<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_ContextR<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_ContextR {
            owl_ctxtR_eph: self.owl_ctxtR_eph,
            owl_ctxtR_confirmed: self.owl_ctxtR_confirmed,
            owl_ctxtR_ss: self.owl_ctxtR_ss,
            owl_ctxtR_base: SecretBuf::another_ref(&self.owl_ctxtR_base),
            owl_ctxtR_sk: SecretBuf::another_ref(&self.owl_ctxtR_sk),
            owl_ctxtR_export: SecretBuf::another_ref(&self.owl_ctxtR_export),
        }
    }
}

impl View for owl_ContextR<'_> {
    type V = owlSpec_ContextR;

    open spec fn view(&self) -> owlSpec_ContextR {
        owlSpec_ContextR {
            owlSpec_ctxtR_eph: ghost_unit(),
            owlSpec_ctxtR_confirmed: self.owl_ctxtR_confirmed.view(),
            owlSpec_ctxtR_ss: ghost_unit(),
            owlSpec_ctxtR_base: self.owl_ctxtR_base.view(),
            owlSpec_ctxtR_sk: self.owl_ctxtR_sk.view(),
            owlSpec_ctxtR_export: self.owl_ctxtR_export.view(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_ContextR<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_ContextR<'a>>)
    ensures
        res is Some ==> parse_owlSpec_ContextR(arg.view()) is Some,
        res is None ==> parse_owlSpec_ContextR(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_ContextR(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_ContextR_inner(arg: &owl_ContextR) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_ContextR_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_ContextR_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_ContextR_inner(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_ContextR(arg: &owl_ContextR) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_ContextR(arg.view()),
{
    todo!()
}

pub enum owl_OpenMsg<'a> {
    owl_NoMsg(),
    owl_SomeMsg(SecretBuf<'a>),
}

use owl_OpenMsg::*;

impl<'a> owl_OpenMsg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_OpenMsg<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_NoMsg() => owl_NoMsg(),
            owl_SomeMsg(x) => owl_SomeMsg(SecretBuf::another_ref(x)),
        }
    }
}

impl View for owl_OpenMsg<'_> {
    type V = owlSpec_OpenMsg;

    open spec fn view(&self) -> owlSpec_OpenMsg {
        match self {
            owl_NoMsg() => owlSpec_OpenMsg::owlSpec_NoMsg(),
            owl_SomeMsg(v) => owlSpec_OpenMsg::owlSpec_SomeMsg(v.view()),
        }
    }
}

#[inline]
pub fn owl_NoMsg_enumtest(x: &owl_OpenMsg<'_>) -> (res: bool)
    ensures
        res == NoMsg_enumtest(x.view()),
{
    match x {
        owl_OpenMsg::owl_NoMsg() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_SomeMsg_enumtest(x: &owl_OpenMsg<'_>) -> (res: bool)
    ensures
        res == SomeMsg_enumtest(x.view()),
{
    match x {
        owl_OpenMsg::owl_SomeMsg(_) => true,
        _ => false,
    }
}

#[verifier(external_body)]
pub exec fn parse_owl_OpenMsg<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_OpenMsg<'a>>)
    ensures
        res is Some ==> parse_owlSpec_OpenMsg(arg.view()) is Some,
        res is None ==> parse_owlSpec_OpenMsg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_OpenMsg(arg.view())->Some_0,
{
    reveal(parse_owlSpec_OpenMsg);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Tail), (Tag::new(U8, 2), Bytes(0)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owl_OpenMsg::owl_NoMsg(),
            inj_ord_choice_pat!(*, (_,x)) => owl_OpenMsg::owl_SomeMsg(
                SecretBuf::from_buf(x.another_ref()),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn serialize_owl_OpenMsg_inner(arg: &owl_OpenMsg) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_OpenMsg_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_OpenMsg_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_OpenMsg_inner(arg.view())->Some_0,
{
    todo!()/* reveal(serialize_owlSpec_OpenMsg_inner);
    let empty_vec: Vec<u8> = mk_vec_u8![];
    let exec_comb = ord_choice!((Tag::new(U8, 1), Tail), (Tag::new(U8, 2), Bytes(0)));
    match arg {
        owl_OpenMsg::owl_NoMsg() => {
    if no_usize_overflows![ 1, 0 ] {
        let mut obuf = vec_u8_of_len(1 + 0);
        let ser_result = exec_comb.serialize(inj_ord_choice_result!(((), &empty_vec.as_slice()), *), &mut obuf, 0);
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_OpenMsg_inner(arg.view())->Some_0);
            Some(obuf)
        } else {
            None
        }
    } else {
        None
    }
},
owl_OpenMsg::owl_SomeMsg(x) => {
    if no_usize_overflows![ 1, x.len() ] {
        let mut obuf = vec_u8_of_len(1 + x.len());
        let ser_result = exec_comb.serialize(inj_ord_choice_result!(*, ((), x.as_slice())), &mut obuf, 0);
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_OpenMsg_inner(arg.view())->Some_0);
            Some(obuf)
        } else {
            None
        }
    } else {
        None
    }
},
    } */

}

#[inline]
pub exec fn serialize_owl_OpenMsg(arg: &owl_OpenMsg) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_OpenMsg(arg.view()),
{
    reveal(serialize_owlSpec_OpenMsg);
    let res = serialize_owl_OpenMsg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_OpenResult<'a> {
    pub owl_or_ctxt: owl_ContextR<'a>,
    pub owl_or_pt: owl_OpenMsg<'a>,
    pub owl_or_wf: Ghost<()>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_OpenResult<'a>(
    arg_owl_or_ctxt: owl_ContextR<'a>,
    arg_owl_or_pt: owl_OpenMsg<'a>,
    arg_owl_or_wf: Ghost<()>,
) -> (res: owl_OpenResult<'a>)
    ensures
        res.owl_or_ctxt.view() == arg_owl_or_ctxt.view(),
        res.owl_or_pt.view() == arg_owl_or_pt.view(),
        res.owl_or_wf.view() == arg_owl_or_wf.view(),
{
    owl_OpenResult {
        owl_or_ctxt: arg_owl_or_ctxt,
        owl_or_pt: arg_owl_or_pt,
        owl_or_wf: arg_owl_or_wf,
    }
}

impl<'a> owl_OpenResult<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_OpenResult<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_OpenResult {
            owl_or_ctxt: owl_ContextR::another_ref(&self.owl_or_ctxt),
            owl_or_pt: owl_OpenMsg::another_ref(&self.owl_or_pt),
            owl_or_wf: self.owl_or_wf,
        }
    }
}

impl View for owl_OpenResult<'_> {
    type V = owlSpec_OpenResult;

    open spec fn view(&self) -> owlSpec_OpenResult {
        owlSpec_OpenResult {
            owlSpec_or_ctxt: self.owl_or_ctxt.view(),
            owlSpec_or_pt: self.owl_or_pt.view(),
            owlSpec_or_wf: ghost_unit(),
        }
    }
}

#[verifier::external_body]
pub exec fn parse_owl_OpenResult<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_OpenResult<'a>>)
    ensures
        res is Some ==> parse_owlSpec_OpenResult(arg.view()) is Some,
        res is None ==> parse_owlSpec_OpenResult(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_OpenResult(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_OpenResult_inner(arg: &owl_OpenResult) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_OpenResult_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_OpenResult_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_OpenResult_inner(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_OpenResult(arg: &owl_OpenResult) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_OpenResult(arg.view()),
{
    todo!()
}

pub struct state_receiver {
    pub owl_recv_counter: usize,
}

impl state_receiver {
    #[verifier::external_body]
    pub fn init_state_receiver() -> Self {
        state_receiver { owl_recv_counter: 0 }
    }
}

pub struct cfg_receiver<'receiver> {
    pub salt: Vec<u8>,
    pub owl_psk: SecretBuf<'receiver>,
    pub owl_skR: SecretBuf<'receiver>,
    pub pk_owl_skS: OwlBuf<'receiver>,
    pub pk_owl_skE: OwlBuf<'receiver>,
    pub pk_owl_skR: OwlBuf<'receiver>,
}

impl cfg_receiver<'_> {
    pub fn mk_cfg_receiver<'a>(
        salt: Vec<u8>,
        owl_psk: &'a [u8],
        owl_skR: &'a [u8],
        pk_owl_skS: &'a [u8],
        pk_owl_skE: &'a [u8],
        pk_owl_skR: &'a [u8],
    ) -> cfg_receiver<'a> {
        cfg_receiver {
            salt,
            owl_psk: SecretBuf::from_buf(OwlBuf::from_slice(owl_psk)),
            owl_skR: SecretBuf::from_buf(OwlBuf::from_slice(owl_skR)),
            pk_owl_skS: OwlBuf::from_slice(pk_owl_skS),
            pk_owl_skE: OwlBuf::from_slice(pk_owl_skE),
            pk_owl_skR: OwlBuf::from_slice(pk_owl_skR),
        }
    }


    #[verifier::external_body]
    pub fn owl_SingleShotOpen_wrapper<'a>(
        &'a self,
        mut_state: &mut state_receiver,
        owl_pkS379: &'a [u8],
        owl_pkR459: &'a [u8],
        msg: &'a [u8],
    ) -> Option<owl_OpenResult<'a>> {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) = self.owl_SingleShotOpen(
            Tracked(call_token),
            mut_state,
            OwlBuf::from_slice(owl_pkS379),
            OwlBuf::from_slice(owl_pkR459),
            msg
        ).unwrap();
        res
    }


    #[verifier::spinoff_prover]
    pub fn owl_SingleShotOpen<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Option<owlSpec_OpenResult>, state_receiver), Endpoint>>,
        mut_state: &mut state_receiver,
        owl_pkS458: OwlBuf<'a>,
        owl_pkR459: OwlBuf<'a>,
        ibuf: &'a [u8],
    ) -> (res: Result<
        (
            Option<owl_OpenResult<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_OpenResult>, state_receiver), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == SingleShotOpen_spec(
                *self,
                *old(mut_state),
                owl_pkS458.view(),
                owl_pkR459.view(),
            ),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_OpenResult<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_OpenResult>, state_receiver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(SingleShotOpen_spec);
            let (tmp_owl_i371, owl__370) = {
                owl_input::<(Option<owlSpec_OpenResult>, state_receiver)>(
                    Tracked(&mut itree),
                    ibuf
                )
            };
            let owl_i371 = OwlBuf::from_slice(tmp_owl_i371);
            let parseval_tmp = OwlBuf::another_ref(&owl_i371);
            if let Some(parseval) = parse_owl_hpke_ciphertext(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_eph373 = OwlBuf::another_ref(&parseval.owl_hc_pk);
                let owl_ct372 = OwlBuf::another_ref(&parseval.owl_hc_cipher);
                {
                    let (owl_oadr374, Tracked(itree)) = {
                        let tmp_arg1460 = OwlBuf::another_ref(&owl_pkS458);
                        let tmp_arg2461 = OwlBuf::another_ref(&owl_pkR459);
                        let tmp_arg3462 = OwlBuf::another_ref(&owl_eph373);
                        owl_call_ret_option!(itree, *mut_state, AuthDecap_spec(*self, *mut_state, tmp_arg1460.view(), tmp_arg2461.view(), tmp_arg3462.view()), self.owl_AuthDecap(mut_state, tmp_arg1460, tmp_arg2461, tmp_arg3462))
                    };
                    let owl_caseval375 = { owl_oadr374 };
                    match owl_caseval375 {
                        Option::Some(tmp_owl_adr376) => {
                            let owl_adr376 = owl_AuthDecapResult::another_ref(&tmp_owl_adr376);
                            {
                                let (tmp_owl_ctxt377, Tracked(itree)) = {
                                    let tmp_arg1463 = owl_AuthDecapResult::another_ref(&owl_adr376);
                                    owl_call!(itree, *mut_state, KeyScheduleR_spec(*self, *mut_state, tmp_arg1463.view()), self.owl_KeyScheduleR(mut_state, tmp_arg1463))
                                };
                                let owl_ctxt377 = owl_ContextR::another_ref(&tmp_owl_ctxt377);
                                let (tmp_owl_res378, Tracked(itree)) = {
                                    let tmp_arg1464 = owl_ContextR::another_ref(&owl_ctxt377);
                                    let tmp_arg2465 = OwlBuf::another_ref(
                                        &{
                                            let x = mk_vec_u8![];
                                            OwlBuf::from_vec(x)
                                        },
                                    );
                                    let tmp_arg3466 = OwlBuf::another_ref(&owl_ct372);
                                    owl_call!(itree, *mut_state, Open_spec(*self, *mut_state, tmp_arg1464.view(), tmp_arg2465.view(), tmp_arg3466.view()), self.owl_Open(mut_state, tmp_arg1464, tmp_arg2465, tmp_arg3466))
                                };
                                let owl_res378 = owl_OpenResult::another_ref(&tmp_owl_res378);
                                (Some(owl_OpenResult::another_ref(&owl_res378)), Tracked(itree))
                            }
                        },
                        Option::None => { (None, Tracked(itree)) },
                    }
                }
            } else {
                (None, Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_Open<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_OpenResult, state_receiver), Endpoint>>,
        mut_state: &mut state_receiver,
        owl_ctxtR458: owl_ContextR<'a>,
        owl_ct_aad459: OwlBuf<'a>,
        owl_ct460: OwlBuf<'a>,
    ) -> (res: Result<
        (owl_OpenResult<'a>, Tracked<ITreeToken<(owlSpec_OpenResult, state_receiver), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == Open_spec(
                *self,
                *old(mut_state),
                owl_ctxtR458.view(),
                owl_ct_aad459.view(),
                owl_ct460.view(),
            ),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_OpenResult<'a>,
            Tracked<ITreeToken<(owlSpec_OpenResult, state_receiver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(Open_spec);
            let tmp_owl_ctxtR376 = { owl_ContextR::another_ref(&owl_ctxtR458) };
            let owl_ctxtR376 = owl_ContextR::another_ref(&tmp_owl_ctxtR376);
            let parseval = owl_ContextR::another_ref(&owl_ctxtR376);
            let owl_eph382 = parseval.owl_ctxtR_eph;
            let owl_confirmed381 = parseval.owl_ctxtR_confirmed;
            let owl_ss380 = parseval.owl_ctxtR_ss;
            let owl_bn379 = SecretBuf::another_ref(&parseval.owl_ctxtR_base);
            let owl_sk378 = SecretBuf::another_ref(&parseval.owl_ctxtR_sk);
            let owl_exp377 = SecretBuf::another_ref(&parseval.owl_ctxtR_export);
            let tmp_owl_ctr383 = { owl_counter_as_bytes(&mut_state.owl_recv_counter) };
            let owl_ctr383 = OwlBuf::from_slice(&tmp_owl_ctr383);
            let tmp_owl_iv384 = {
                owl_secret_xor(
                    SecretBuf::another_ref(&owl_bn379),
                    SecretBuf::from_buf(owl_ctr383.another_ref()),
                )
            };
            let owl_iv384 = SecretBuf::another_ref(&tmp_owl_iv384);
            let owl__385 = {
                if mut_state.owl_recv_counter > usize::MAX - 1 {
                    return Err(OwlError::IntegerOverflow);
                };
                mut_state.owl_recv_counter = mut_state.owl_recv_counter + 1;
            };
            let tmp_owl_caseval386 = {
                let tracked owl_declassify_tok387 = consume_itree_declassify::<
                    (owlSpec_OpenResult, state_receiver),
                    Endpoint,
                >(&mut itree);
                owl_dec_st_aead(
                    SecretBuf::another_ref(&owl_sk378),
                    OwlBuf::another_ref(&owl_ct460),
                    SecretBuf::another_ref(&owl_iv384),
                    SecretBuf::from_buf(owl_ct_aad459.another_ref()),
                    Tracked(owl_declassify_tok387),
                )
            };
            let owl_caseval386 = SecretBuf::another_ref_option(&tmp_owl_caseval386);
            match SecretBuf::another_ref_option(&owl_caseval386) {
                Option::Some(tmp_owl_x388) => {
                    let owl_x388 = SecretBuf::another_ref(&tmp_owl_x388);
                    let tmp_owl_ctxtR_389 = {
                        owl_ContextR(
                            owl_ghost_unit(),
                            true,
                            owl_ghost_unit(),
                            SecretBuf::another_ref(&owl_bn379),
                            SecretBuf::another_ref(&owl_sk378),
                            SecretBuf::another_ref(&owl_exp377),
                        )
                    };
                    let owl_ctxtR_389 = owl_ContextR::another_ref(&tmp_owl_ctxtR_389);
                    let owl__assert_106390 = { owl_ghost_unit() };
                    let tmp_owl_res391 = {
                        owl_OpenResult(
                            owl_ContextR::another_ref(&owl_ctxtR_389),
                            owl_OpenMsg::another_ref(
                                &owl_OpenMsg::another_ref(
                                    &owl_SomeMsg(SecretBuf::another_ref(&owl_x388)),
                                ),
                            ),
                            owl_ghost_unit(),
                        )
                    };
                    let owl_res391 = owl_OpenResult::another_ref(&tmp_owl_res391);
                    (owl_OpenResult::another_ref(&owl_res391), Tracked(itree))
                },
                Option::None => {
                    let tmp_owl_res392 = {
                        owl_OpenResult(
                            owl_ContextR::another_ref(&owl_ctxtR376),
                            owl_OpenMsg::another_ref(&owl_OpenMsg::another_ref(&owl_NoMsg())),
                            owl_ghost_unit(),
                        )
                    };
                    let owl_res392 = owl_OpenResult::another_ref(&tmp_owl_res392);
                    (owl_OpenResult::another_ref(&owl_res392), Tracked(itree))
                },
            }
        };
        Ok((owl_OpenResult::another_ref(&res_inner), Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_KeyScheduleR<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_ContextR, state_receiver), Endpoint>>,
        mut_state: &mut state_receiver,
        owl_adr461: owl_AuthDecapResult<'a>,
    ) -> (res: Result<
        (owl_ContextR<'a>, Tracked<ITreeToken<(owlSpec_ContextR, state_receiver), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == KeyScheduleR_spec(*self, *old(mut_state), owl_adr461.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_ContextR<'a>,
            Tracked<ITreeToken<(owlSpec_ContextR, state_receiver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(KeyScheduleR_spec);
            let tmp_owl_adr_394 = { owl_AuthDecapResult::another_ref(&owl_adr461) };
            let owl_adr_394 = owl_AuthDecapResult::another_ref(&tmp_owl_adr_394);
            let parseval = owl_AuthDecapResult::another_ref(&owl_adr_394);
            let owl_eph397 = parseval.owl_adr_eph;
            let owl_shared_secret396 = SecretBuf::another_ref(&parseval.owl_adr_shared_secret);
            let owl__395 = parseval.owl_adr_shared_secret_inj;
            let tmp_owl_kdfval156398 = {
                owl_extract_expand_to_len(
                    0 + COUNTER_SIZE,
                    SecretBuf::another_ref(&owl_shared_secret396),
                    SecretBuf::another_ref(
                        &owl_secret_dh_secret_kdf_ikm(
                            SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_psk)),
                        ),
                    ),
                    OwlBuf::another_ref(&owl_public_base_nonce_kdf_info()),
                )
            };
            let owl_kdfval156398 = SecretBuf::another_ref(&tmp_owl_kdfval156398);
            let tmp_owl_base_nonce399 = {
                { SecretBuf::another_ref(&owl_kdfval156398).subrange(0, 0 + COUNTER_SIZE) }
            };
            let owl_base_nonce399 = SecretBuf::another_ref(&tmp_owl_base_nonce399);
            let tmp_owl_kdfval161400 = {
                owl_extract_expand_to_len(
                    0 + ENCKEY_SIZE,
                    SecretBuf::another_ref(&owl_shared_secret396),
                    SecretBuf::another_ref(
                        &owl_secret_dh_secret_kdf_ikm(
                            SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_psk)),
                        ),
                    ),
                    OwlBuf::another_ref(&owl_public_key_kdf_info()),
                )
            };
            let owl_kdfval161400 = SecretBuf::another_ref(&tmp_owl_kdfval161400);
            let tmp_owl_sk401 = {
                { SecretBuf::another_ref(&owl_kdfval161400).subrange(0, 0 + ENCKEY_SIZE) }
            };
            let owl_sk401 = SecretBuf::another_ref(&tmp_owl_sk401);
            let tmp_owl_kdfval164402 = {
                owl_extract_expand_to_len(
                    0 + NONCE_SIZE,
                    SecretBuf::another_ref(&owl_shared_secret396),
                    SecretBuf::another_ref(
                        &owl_secret_dh_secret_kdf_ikm(
                            SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_psk)),
                        ),
                    ),
                    OwlBuf::another_ref(&owl_public_export_kdf_info()),
                )
            };
            let owl_kdfval164402 = SecretBuf::another_ref(&tmp_owl_kdfval164402);
            let tmp_owl_exp403 = {
                { SecretBuf::another_ref(&owl_kdfval164402).subrange(0, 0 + NONCE_SIZE) }
            };
            let owl_exp403 = SecretBuf::another_ref(&tmp_owl_exp403);
            let tmp_owl_res404 = {
                owl_ContextR(
                    owl_ghost_unit(),
                    false,
                    owl_ghost_unit(),
                    SecretBuf::another_ref(&owl_base_nonce399),
                    SecretBuf::another_ref(&owl_sk401),
                    SecretBuf::another_ref(&owl_exp403),
                )
            };
            let owl_res404 = owl_ContextR::another_ref(&tmp_owl_res404);
            (owl_ContextR::another_ref(&owl_res404), Tracked(itree))
        };
        Ok((owl_ContextR::another_ref(&res_inner), Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_AuthDecap<'a>(
        &'a self,
        Tracked(itree): Tracked<
            ITreeToken<(Option<owlSpec_AuthDecapResult>, state_receiver), Endpoint>,
        >,
        mut_state: &mut state_receiver,
        owl_pkS471: OwlBuf<'a>,
        owl_pkR472: OwlBuf<'a>,
        owl_eph473: OwlBuf<'a>,
    ) -> (res: Result<
        (
            Option<owl_AuthDecapResult<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_AuthDecapResult>, state_receiver), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == AuthDecap_spec(
                *self,
                *old(mut_state),
                owl_pkS471.view(),
                owl_pkR472.view(),
                owl_eph473.view(),
            ),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_AuthDecapResult<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_AuthDecapResult>, state_receiver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(AuthDecap_spec);

            if owl_is_group_elem(SecretBuf::from_buf(owl_eph473.another_ref())) {
                let tmp_owl_dh414 = {
                    owl_secret_concat(
                        SecretBuf::another_ref(
                            &owl_dh_combine(
                                SecretBuf::from_buf(owl_eph473.another_ref()),
                                SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skR)),
                            ),
                        ),
                        SecretBuf::another_ref(
                            &owl_dh_combine(
                                SecretBuf::from_buf(owl_pkS471.another_ref()),
                                SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skR)),
                            ),
                        ),
                    )
                };
                let owl_dh414 = SecretBuf::another_ref(&tmp_owl_dh414);
                let tmp_owl_kem_context415 = {
                    owl_concat(
                        owl_concat(owl_eph473.as_slice(), owl_pkR472.as_slice()).as_slice(),
                        owl_pkS471.as_slice(),
                    )
                };
                let owl_kem_context415 = OwlBuf::from_vec(tmp_owl_kem_context415);
                let tmp_owl_kdfval176416 = {
                    owl_extract_expand_to_len(
                        0 + KDFKEY_SIZE,
                        SecretBuf::from_buf(
                            {
                                let x = mk_vec_u8![];
                                OwlBuf::from_vec(x)
                            }.another_ref(),
                        ),
                        SecretBuf::another_ref(
                            &owl_secret_lbl_ikm(
                                SecretBuf::another_ref(
                                    &SecretBuf::from_buf(owl_public_kem_suite_id().another_ref()),
                                ),
                                SecretBuf::another_ref(
                                    &SecretBuf::from_buf(owl_public_eae_prk().another_ref()),
                                ),
                                SecretBuf::another_ref(&owl_dh414),
                            ),
                        ),
                        OwlBuf::another_ref(
                            &owl_public_lbl_info(
                                OwlBuf::another_ref(&owl_public_kem_suite_id()),
                                OwlBuf::another_ref(&owl_public_kdfkey_len()),
                                OwlBuf::another_ref(&owl_public_shared_secret_string()),
                                OwlBuf::another_ref(&owl_kem_context415),
                            ),
                        ),
                    )
                };
                let owl_kdfval176416 = SecretBuf::another_ref(&tmp_owl_kdfval176416);
                let tmp_owl_shared_secret417 = {
                    { SecretBuf::another_ref(&owl_kdfval176416).subrange(0, 0 + KDFKEY_SIZE) }
                };
                let owl_shared_secret417 = SecretBuf::another_ref(&tmp_owl_shared_secret417);
                let owl_shared_secret_ghost418 = { owl_ghost_unit() };
                let tmp_owl_res419 = {
                    owl_AuthDecapResult(
                        owl_ghost_unit(),
                        SecretBuf::another_ref(&owl_shared_secret417),
                        owl_ghost_unit(),
                    )
                };
                let owl_res419 = owl_AuthDecapResult::another_ref(&tmp_owl_res419);
                let tmp_owl_pres420 = { owl_AuthDecapResult::another_ref(&owl_res419) };
                let owl_pres420 = owl_AuthDecapResult::another_ref(&tmp_owl_pres420);
                (Some(owl_AuthDecapResult::another_ref(&owl_pres420)), Tracked(itree))
            } else {
                (None, Tracked(itree))
            }

        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub struct state_sender {
    pub owl_send_counter: usize,
}

impl state_sender {
    #[verifier::external_body]
    pub fn init_state_sender() -> Self {
        state_sender { owl_send_counter: 0 }
    }
}

pub struct cfg_sender<'sender> {
    pub salt: Vec<u8>,
    pub owl_psk: SecretBuf<'sender>,
    pub owl_skS: SecretBuf<'sender>,
    pub owl_skE: SecretBuf<'sender>,
    pub pk_owl_skS: OwlBuf<'sender>,
    pub pk_owl_skE: OwlBuf<'sender>,
    pub pk_owl_skR: OwlBuf<'sender>,
}

impl cfg_sender<'_> {
    pub fn mk_cfg_sender<'a>(
        salt: Vec<u8>,
        owl_psk: &'a [u8],
        owl_skS: &'a [u8],
        owl_skE: &'a [u8],
        pk_owl_skS: &'a [u8],
        pk_owl_skE: &'a [u8],
        pk_owl_skR: &'a [u8],
    ) -> cfg_sender<'a> {
        cfg_sender {
            salt,
            owl_psk: SecretBuf::from_buf(OwlBuf::from_slice(owl_psk)),
            owl_skS: SecretBuf::from_buf(OwlBuf::from_slice(owl_skS)),
            owl_skE: SecretBuf::from_buf(OwlBuf::from_slice(owl_skE)),
            pk_owl_skS: OwlBuf::from_slice(pk_owl_skS),
            pk_owl_skE: OwlBuf::from_slice(pk_owl_skE),
            pk_owl_skR: OwlBuf::from_slice(pk_owl_skR),
        }
    }

    #[verifier::external_body]
    pub fn owl_SingleShotSeal_wrapper<'a>(
        &'a self,
        mut_state: &mut state_sender,
        owl_pkR392: &'a [u8],
        owl_dhpk_skE465: &'a [u8],
        owl_dhpk_skS466: &'a [u8],
        owl_x393: &'a [u8],      
        obuf: &'a mut [u8]  
    ) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) = self.owl_SingleShotSeal(
            Tracked(call_token),
            mut_state,
            OwlBuf::from_slice(owl_pkR392),
            OwlBuf::from_slice(owl_dhpk_skE465),
            OwlBuf::from_slice(owl_dhpk_skS466),
            SecretBuf::from_buf(OwlBuf::from_slice(owl_x393)),
            obuf
        ).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_SingleShotSeal<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<((), state_sender), Endpoint>>,
        mut_state: &mut state_sender,
        owl_pkR464: OwlBuf<'a>,
        owl_dhpk_skE465: OwlBuf<'a>,
        owl_dhpk_skS466: OwlBuf<'a>,
        owl_x467: SecretBuf<'_>,
        obuf: &mut [u8],
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_sender), Endpoint>>), OwlError>)
        requires
            itree.view() == SingleShotSeal_spec(
                *self,
                *old(mut_state),
                owl_pkR464.view(),
                owl_dhpk_skE465.view(),
                owl_dhpk_skS466.view(),
                owl_x467.view(),
            ),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_sender), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(SingleShotSeal_spec);
            let (tmp_owl_aer418, Tracked(itree)) = {
                let tmp_arg1468 = OwlBuf::another_ref(&owl_pkR464);
                let tmp_arg2469 = OwlBuf::another_ref(&owl_dhpk_skE465);
                let tmp_arg3470 = OwlBuf::another_ref(&owl_dhpk_skS466);
                owl_call!(itree, *mut_state, AuthEncap_spec(*self, *mut_state, tmp_arg1468.view(), tmp_arg2469.view(), tmp_arg3470.view()), self.owl_AuthEncap(mut_state, tmp_arg1468, tmp_arg2469, tmp_arg3470))
            };
            let owl_aer418 = owl_AuthEncapResult::another_ref(&tmp_owl_aer418);
            let (tmp_owl_context419, Tracked(itree)) = {
                let tmp_arg1471 = owl_AuthEncapResult::another_ref(&owl_aer418);
                owl_call!(itree, *mut_state, KeyScheduleS_spec(*self, *mut_state, tmp_arg1471.view()), self.owl_KeyScheduleS(mut_state, tmp_arg1471))
            };
            let owl_context419 = owl_ContextS::another_ref(&tmp_owl_context419);
            let (tmp_owl_c420, Tracked(itree)) = {
                let tmp_arg1472 = owl_ContextS::another_ref(&owl_context419);
                let tmp_arg2473 = SecretBuf::another_ref(&owl_x467);
                owl_call!(itree, *mut_state, Seal_spec(*self, *mut_state, tmp_arg1472.view(), tmp_arg2473.view()), self.owl_Seal(mut_state, tmp_arg1472, tmp_arg2473))
            };
            let owl_c420 = OwlBuf::another_ref(&tmp_owl_c420);
            let parseval = owl_AuthEncapResult::another_ref(&owl_aer418);
            let owl__422 = SecretBuf::another_ref(&parseval.owl_aer_shared_secret);
            let owl_pk421 = OwlBuf::another_ref(&parseval.owl_aer_pke);
            owl_output::<((), state_sender)>(
                Tracked(&mut itree),
                serialize_owl_hpke_ciphertext(
                    &owl_hpke_ciphertext(
                        OwlBuf::another_ref(&owl_pk421),
                        OwlBuf::another_ref(&owl_c420),
                    ),
                ).as_slice(),
                &receiver_addr(),
                &sender_addr(),
                obuf
            );
            ((), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_Seal<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_sender), Endpoint>>,
        mut_state: &mut state_sender,
        owl_ctxt474: owl_ContextS<'a>,
        owl_x475: SecretBuf<'_>,
    ) -> (res: Result<
        (OwlBuf<'a>, Tracked<ITreeToken<(Seq<u8>, state_sender), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == Seal_spec(*self, *old(mut_state), owl_ctxt474.view(), owl_x475.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            OwlBuf<'a>,
            Tracked<ITreeToken<(Seq<u8>, state_sender), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(Seal_spec);
            let parseval = owl_ContextS::another_ref(&owl_ctxt474);
            let owl__428 = parseval.owl_ctxtS_ss;
            let owl_base427 = SecretBuf::another_ref(&parseval.owl_ctxtS_base);
            let owl_sk426 = SecretBuf::another_ref(&parseval.owl_ctxtS_sk);
            let owl__425 = SecretBuf::another_ref(&parseval.owl_ctxtS_export);
            let (owl__429, Tracked(itree)) = {
                let tmp_arg1476 = owl_ghost_unit();
                owl_call_ret_unit!(itree, *mut_state, sent_message_spec(*self, *mut_state, tmp_arg1476), self.owl_sent_message(mut_state, tmp_arg1476))
            };
            let tmp_owl_send_counter430 = { owl_counter_as_bytes(&mut_state.owl_send_counter) };
            let owl_send_counter430 = OwlBuf::from_slice(&tmp_owl_send_counter430).into_secret();
            let owl__431 = {
                if mut_state.owl_send_counter > usize::MAX - 1 {
                    return Err(OwlError::IntegerOverflow);
                };
                mut_state.owl_send_counter = mut_state.owl_send_counter + 1;
            };
            let tmp_owl_i432 = {
                owl_secret_xor(
                    SecretBuf::another_ref(&owl_send_counter430),
                    SecretBuf::another_ref(&owl_base427),
                )
            };
            let owl_i432 = SecretBuf::another_ref(&tmp_owl_i432);
            (
                OwlBuf::from_vec(
                    owl_enc_st_aead(
                        SecretBuf::another_ref(&owl_sk426),
                        SecretBuf::another_ref(&owl_x475),
                        SecretBuf::another_ref(&owl_i432),
                        SecretBuf::from_buf(
                            {
                                let x = mk_vec_u8![];
                                OwlBuf::from_vec(x)
                            }.another_ref(),
                        ),
                    ),
                ),
                Tracked(itree),
            )
        };
        Ok((OwlBuf::another_ref(&res_inner), Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_sent_message(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_sender), Endpoint>>,
        mut_state: &mut state_sender,
        owl_x477: Ghost<()>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_sender), Endpoint>>), OwlError>)
        requires
            itree.view() == sent_message_spec(*self, *old(mut_state), owl_x477),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_sender), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(sent_message_spec);
            (owl_unit(), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_KeyScheduleS<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_ContextS, state_sender), Endpoint>>,
        mut_state: &mut state_sender,
        owl_aer478: owl_AuthEncapResult<'a>,
    ) -> (res: Result<
        (owl_ContextS<'a>, Tracked<ITreeToken<(owlSpec_ContextS, state_sender), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == KeyScheduleS_spec(*self, *old(mut_state), owl_aer478.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_ContextS<'a>,
            Tracked<ITreeToken<(owlSpec_ContextS, state_sender), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(KeyScheduleS_spec);
            let parseval = owl_AuthEncapResult::another_ref(&owl_aer478);
            let owl_shared_secret436 = SecretBuf::another_ref(&parseval.owl_aer_shared_secret);
            let owl_pkE435 = OwlBuf::another_ref(&parseval.owl_aer_pke);
            let tmp_owl_kdfval248437 = {
                owl_extract_expand_to_len(
                    0 + COUNTER_SIZE,
                    SecretBuf::another_ref(&owl_shared_secret436),
                    SecretBuf::another_ref(
                        &owl_secret_dh_secret_kdf_ikm(
                            SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_psk)),
                        ),
                    ),
                    OwlBuf::another_ref(&owl_public_base_nonce_kdf_info()),
                )
            };
            let owl_kdfval248437 = SecretBuf::another_ref(&tmp_owl_kdfval248437);
            let tmp_owl_base_nonce438 = {
                { SecretBuf::another_ref(&owl_kdfval248437).subrange(0, 0 + COUNTER_SIZE) }
            };
            let owl_base_nonce438 = SecretBuf::another_ref(&tmp_owl_base_nonce438);
            let tmp_owl_kdfval251439 = {
                owl_extract_expand_to_len(
                    0 + ENCKEY_SIZE,
                    SecretBuf::another_ref(&owl_shared_secret436),
                    SecretBuf::another_ref(
                        &owl_secret_dh_secret_kdf_ikm(
                            SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_psk)),
                        ),
                    ),
                    OwlBuf::another_ref(&owl_public_key_kdf_info()),
                )
            };
            let owl_kdfval251439 = SecretBuf::another_ref(&tmp_owl_kdfval251439);
            let tmp_owl_sk440 = {
                { SecretBuf::another_ref(&owl_kdfval251439).subrange(0, 0 + ENCKEY_SIZE) }
            };
            let owl_sk440 = SecretBuf::another_ref(&tmp_owl_sk440);
            let tmp_owl_kdfval254441 = {
                owl_extract_expand_to_len(
                    0 + NONCE_SIZE,
                    SecretBuf::another_ref(&owl_shared_secret436),
                    SecretBuf::another_ref(
                        &owl_secret_dh_secret_kdf_ikm(
                            SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_psk)),
                        ),
                    ),
                    OwlBuf::another_ref(&owl_public_export_kdf_info()),
                )
            };
            let owl_kdfval254441 = SecretBuf::another_ref(&tmp_owl_kdfval254441);
            let tmp_owl_exp442 = {
                { SecretBuf::another_ref(&owl_kdfval254441).subrange(0, 0 + NONCE_SIZE) }
            };
            let owl_exp442 = SecretBuf::another_ref(&tmp_owl_exp442);
            (
                owl_ContextS::another_ref(
                    &owl_ContextS(
                        owl_ghost_unit(),
                        SecretBuf::another_ref(&owl_base_nonce438),
                        SecretBuf::another_ref(&owl_sk440),
                        SecretBuf::another_ref(&owl_exp442),
                    ),
                ),
                Tracked(itree),
            )
        };
        Ok((owl_ContextS::another_ref(&res_inner), Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_AuthEncap<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_AuthEncapResult, state_sender), Endpoint>>,
        mut_state: &mut state_sender,
        owl_pkR479: OwlBuf<'a>,
        owl_dhpk_skE480: OwlBuf<'a>,
        owl_dhpk_skS481: OwlBuf<'a>,
    ) -> (res: Result<
        (
            owl_AuthEncapResult<'a>,
            Tracked<ITreeToken<(owlSpec_AuthEncapResult, state_sender), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == AuthEncap_spec(
                *self,
                *old(mut_state),
                owl_pkR479.view(),
                owl_dhpk_skE480.view(),
                owl_dhpk_skS481.view(),
            ),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_AuthEncapResult<'a>,
            Tracked<ITreeToken<(owlSpec_AuthEncapResult, state_sender), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(AuthEncap_spec);
            let tmp_owl_dh446 = {
                owl_secret_concat(
                    SecretBuf::another_ref(
                        &owl_dh_combine(
                            SecretBuf::from_buf(owl_pkR479.another_ref()),
                            SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skE)),
                        ),
                    ),
                    SecretBuf::another_ref(
                        &owl_dh_combine(
                            SecretBuf::from_buf(owl_pkR479.another_ref()),
                            SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_skS)),
                        ),
                    ),
                )
            };
            let owl_dh446 = SecretBuf::another_ref(&tmp_owl_dh446);
            let tmp_owl_kem_context447 = {
                owl_concat(
                    owl_concat(owl_dhpk_skE480.as_slice(), owl_pkR479.as_slice()).as_slice(),
                    owl_dhpk_skS481.as_slice(),
                )
            };
            let owl_kem_context447 = OwlBuf::from_vec(tmp_owl_kem_context447);
            let tmp_owl_kdfval262448 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE,
                    SecretBuf::from_buf(
                        {
                            let x = mk_vec_u8![];
                            OwlBuf::from_vec(x)
                        }.another_ref(),
                    ),
                    SecretBuf::another_ref(
                        &owl_secret_lbl_ikm(
                            SecretBuf::another_ref(
                                &SecretBuf::from_buf(owl_public_kem_suite_id().another_ref()),
                            ),
                            SecretBuf::another_ref(
                                &SecretBuf::from_buf(owl_public_eae_prk().another_ref()),
                            ),
                            SecretBuf::another_ref(&owl_dh446),
                        ),
                    ),
                    OwlBuf::another_ref(
                        &owl_public_lbl_info(
                            OwlBuf::another_ref(&owl_public_kem_suite_id()),
                            OwlBuf::another_ref(&owl_public_kdfkey_len()),
                            OwlBuf::another_ref(&owl_public_shared_secret_string()),
                            OwlBuf::another_ref(&owl_kem_context447),
                        ),
                    ),
                )
            };
            let owl_kdfval262448 = SecretBuf::another_ref(&tmp_owl_kdfval262448);
            let tmp_owl_shared_secret449 = {
                { SecretBuf::another_ref(&owl_kdfval262448).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_shared_secret449 = SecretBuf::another_ref(&tmp_owl_shared_secret449);
            let tmp_owl_res450 = { SecretBuf::another_ref(&owl_shared_secret449) };
            let owl_res450 = SecretBuf::another_ref(&tmp_owl_res450);
            (
                owl_AuthEncapResult::another_ref(
                    &owl_AuthEncapResult(
                        SecretBuf::another_ref(&owl_res450),
                        OwlBuf::another_ref(&owl_dhpk_skE480),
                    ),
                ),
                Tracked(itree),
            )
        };
        Ok((owl_AuthEncapResult::another_ref(&res_inner), Tracked(itree)))
    }
}

pub fn owl_secret_base_nonce_kdf_info<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == base_nonce_kdf_info(),
{
    reveal(base_nonce_kdf_info);
    OwlBuf::another_ref(
        &owl_public_lbl_info(
            OwlBuf::another_ref(&owl_public_hpke_suite_id()),
            OwlBuf::another_ref(&owl_public_nonce_len()),
            OwlBuf::another_ref(&owl_public_base_nonce_string()),
            OwlBuf::another_ref(&owl_public_key_schedule_context()),
        ),
    )
}

pub fn owl_public_base_nonce_kdf_info<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == base_nonce_kdf_info(),
{
    reveal(base_nonce_kdf_info);
    OwlBuf::another_ref(
        &owl_public_lbl_info(
            OwlBuf::another_ref(&owl_public_hpke_suite_id()),
            OwlBuf::another_ref(&owl_public_nonce_len()),
            OwlBuf::another_ref(&owl_public_base_nonce_string()),
            OwlBuf::another_ref(&owl_public_key_schedule_context()),
        ),
    )
}

pub fn owl_secret_base_nonce_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == base_nonce_string(),
{
    reveal(base_nonce_string);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x62u8, 0x61u8, 0x73u8, 0x65u8, 0x5fu8, 0x6eu8, 0x6fu8, 0x6eu8, 0x63u8, 0x65u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_base_nonce_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == base_nonce_string(),
{
    reveal(base_nonce_string);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x62u8, 0x61u8, 0x73u8, 0x65u8, 0x5fu8, 0x6eu8, 0x6fu8, 0x6eu8, 0x63u8, 0x65u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_dh_secret_kdf_ikm<'a>(owl_psk_482: SecretBuf<'a>) -> (res: SecretBuf<'a>)
    ensures
        res.view() == dh_secret_kdf_ikm(owl_psk_482.view()),
{
    reveal(dh_secret_kdf_ikm);
    SecretBuf::another_ref(
        &owl_secret_lbl_ikm(
            SecretBuf::another_ref(&SecretBuf::from_buf(owl_public_hpke_suite_id().another_ref())),
            SecretBuf::another_ref(&SecretBuf::from_buf(owl_public_secret_string().another_ref())),
            SecretBuf::another_ref(&owl_psk_482),
        ),
    )
}

pub fn owl_public_dh_secret_kdf_ikm<'a>(owl_psk_483: OwlBuf<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == dh_secret_kdf_ikm(owl_psk_483.view()),
{
    reveal(dh_secret_kdf_ikm);
    OwlBuf::another_ref(
        &owl_public_lbl_ikm(
            OwlBuf::another_ref(&owl_public_hpke_suite_id()),
            OwlBuf::another_ref(&owl_public_secret_string()),
            OwlBuf::another_ref(&owl_psk_483),
        ),
    )
}

pub fn owl_secret_eae_prk<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == eae_prk(),
{
    reveal(eae_prk);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x65u8, 0x61u8, 0x65u8, 0x5fu8, 0x70u8, 0x72u8, 0x6bu8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_eae_prk<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == eae_prk(),
{
    reveal(eae_prk);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x65u8, 0x61u8, 0x65u8, 0x5fu8, 0x70u8, 0x72u8, 0x6bu8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_enckey_len<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == enckey_len(),
{
    reveal(enckey_len);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x00u8, 0x20u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_enckey_len<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == enckey_len(),
{
    reveal(enckey_len);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x00u8, 0x20u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_export_kdf_info<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == export_kdf_info(),
{
    reveal(export_kdf_info);
    OwlBuf::another_ref(
        &owl_public_lbl_info(
            OwlBuf::another_ref(&owl_public_hpke_suite_id()),
            OwlBuf::another_ref(&owl_public_enckey_len()),
            OwlBuf::another_ref(&owl_public_export_string()),
            OwlBuf::another_ref(&owl_public_key_schedule_context()),
        ),
    )
}

pub fn owl_public_export_kdf_info<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == export_kdf_info(),
{
    reveal(export_kdf_info);
    OwlBuf::another_ref(
        &owl_public_lbl_info(
            OwlBuf::another_ref(&owl_public_hpke_suite_id()),
            OwlBuf::another_ref(&owl_public_enckey_len()),
            OwlBuf::another_ref(&owl_public_export_string()),
            OwlBuf::another_ref(&owl_public_key_schedule_context()),
        ),
    )
}

pub fn owl_secret_export_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == export_string(),
{
    reveal(export_string);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x65u8, 0x78u8, 0x70u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_export_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == export_string(),
{
    reveal(export_string);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x65u8, 0x78u8, 0x70u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_hpke_suite_id<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == hpke_suite_id(),
{
    reveal(hpke_suite_id);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x48u8, 0x50u8, 0x4bu8, 0x45u8, 0x00u8, 0x20u8, 0x00u8, 0x01u8, 0x00u8, 0x03u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_hpke_suite_id<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == hpke_suite_id(),
{
    reveal(hpke_suite_id);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x48u8, 0x50u8, 0x4bu8, 0x45u8, 0x00u8, 0x20u8, 0x00u8, 0x01u8, 0x00u8, 0x03u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_hpke_v1<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == hpke_v1(),
{
    reveal(hpke_v1);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x48u8, 0x50u8, 0x4bu8, 0x45u8, 0x2du8, 0x76u8, 0x31u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_hpke_v1<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == hpke_v1(),
{
    reveal(hpke_v1);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x48u8, 0x50u8, 0x4bu8, 0x45u8, 0x2du8, 0x76u8, 0x31u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_kdfkey_len<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == kdfkey_len(),
{
    reveal(kdfkey_len);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x00u8, 0x20u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_kdfkey_len<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == kdfkey_len(),
{
    reveal(kdfkey_len);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x00u8, 0x20u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_kem_suite_id<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == kem_suite_id(),
{
    reveal(kem_suite_id);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x4bu8, 0x45u8, 0x4du8, 0x00u8, 0x20u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_kem_suite_id<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == kem_suite_id(),
{
    reveal(kem_suite_id);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x4bu8, 0x45u8, 0x4du8, 0x00u8, 0x20u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_key_kdf_info<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == key_kdf_info(),
{
    reveal(key_kdf_info);
    OwlBuf::another_ref(
        &owl_public_lbl_info(
            OwlBuf::another_ref(&owl_public_hpke_suite_id()),
            OwlBuf::another_ref(&owl_public_enckey_len()),
            OwlBuf::another_ref(&owl_public_key_string()),
            OwlBuf::another_ref(&owl_public_key_schedule_context()),
        ),
    )
}

pub fn owl_public_key_kdf_info<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == key_kdf_info(),
{
    reveal(key_kdf_info);
    OwlBuf::another_ref(
        &owl_public_lbl_info(
            OwlBuf::another_ref(&owl_public_hpke_suite_id()),
            OwlBuf::another_ref(&owl_public_enckey_len()),
            OwlBuf::another_ref(&owl_public_key_string()),
            OwlBuf::another_ref(&owl_public_key_schedule_context()),
        ),
    )
}

pub fn owl_secret_key_schedule_context<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == key_schedule_context(),
{
    reveal(key_schedule_context);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x03u8, 0x43u8, 0x1du8, 0xf6u8, 0xcdu8, 0x95u8, 0xe1u8, 0x1fu8, 0xf4u8, 0x9du8, 0x70u8, 0x13u8, 0x56u8, 0x3bu8, 0xafu8, 0x7fu8, 0x11u8, 0x58u8, 0x8cu8, 0x75u8, 0xa6u8, 0x61u8, 0x1eu8, 0xe2u8, 0xa4u8, 0x40u8, 0x4au8, 0x49u8, 0x30u8, 0x6au8, 0xe4u8, 0xcfu8, 0xc5u8, 0x55u8, 0xe7u8, 0xb3u8, 0x9du8, 0x7au8, 0x73u8, 0x55u8, 0x3cu8, 0x14u8, 0xeeu8, 0xe3u8, 0xb6u8, 0x05u8, 0xf8u8, 0xc4u8, 0x43u8, 0x8fu8, 0xb8u8, 0xc4u8, 0xa5u8, 0xd3u8, 0x2fu8, 0xb2u8, 0xbeu8, 0xf7u8, 0x35u8, 0xf2u8, 0x61u8, 0x28u8, 0xedu8, 0x56u8, 0x95u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_key_schedule_context<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == key_schedule_context(),
{
    reveal(key_schedule_context);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x03u8, 0x43u8, 0x1du8, 0xf6u8, 0xcdu8, 0x95u8, 0xe1u8, 0x1fu8, 0xf4u8, 0x9du8, 0x70u8, 0x13u8, 0x56u8, 0x3bu8, 0xafu8, 0x7fu8, 0x11u8, 0x58u8, 0x8cu8, 0x75u8, 0xa6u8, 0x61u8, 0x1eu8, 0xe2u8, 0xa4u8, 0x40u8, 0x4au8, 0x49u8, 0x30u8, 0x6au8, 0xe4u8, 0xcfu8, 0xc5u8, 0x55u8, 0xe7u8, 0xb3u8, 0x9du8, 0x7au8, 0x73u8, 0x55u8, 0x3cu8, 0x14u8, 0xeeu8, 0xe3u8, 0xb6u8, 0x05u8, 0xf8u8, 0xc4u8, 0x43u8, 0x8fu8, 0xb8u8, 0xc4u8, 0xa5u8, 0xd3u8, 0x2fu8, 0xb2u8, 0xbeu8, 0xf7u8, 0x35u8, 0xf2u8, 0x61u8, 0x28u8, 0xedu8, 0x56u8, 0x95u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_key_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == key_string(),
{
    reveal(key_string);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x6bu8, 0x65u8, 0x79u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_key_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == key_string(),
{
    reveal(key_string);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x6bu8, 0x65u8, 0x79u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_lbl_ikm<'a>(
    owl_suite_id484: SecretBuf<'a>,
    owl_lbl485: SecretBuf<'a>,
    owl_ikm486: SecretBuf<'a>,
) -> (res: SecretBuf<'a>)
    ensures
        res.view() == lbl_ikm(owl_suite_id484.view(), owl_lbl485.view(), owl_ikm486.view()),
{
    reveal(lbl_ikm);
    SecretBuf::another_ref(
        &owl_secret_concat(
            SecretBuf::another_ref(
                &owl_secret_concat(
                    SecretBuf::another_ref(
                        &owl_secret_concat(
                            SecretBuf::from_buf(owl_public_hpke_v1().another_ref()),
                            SecretBuf::another_ref(&owl_suite_id484),
                        ),
                    ),
                    SecretBuf::another_ref(&owl_lbl485),
                ),
            ),
            SecretBuf::another_ref(&owl_ikm486),
        ),
    )
}

pub fn owl_public_lbl_ikm<'a>(
    owl_suite_id487: OwlBuf<'a>,
    owl_lbl488: OwlBuf<'a>,
    owl_ikm489: OwlBuf<'a>,
) -> (res: OwlBuf<'a>)
    ensures
        res.view() == lbl_ikm(owl_suite_id487.view(), owl_lbl488.view(), owl_ikm489.view()),
{
    reveal(lbl_ikm);
    OwlBuf::from_vec(
        owl_concat(
            owl_concat(
                owl_concat(owl_public_hpke_v1().as_slice(), owl_suite_id487.as_slice()).as_slice(),
                owl_lbl488.as_slice(),
            ).as_slice(),
            owl_ikm489.as_slice(),
        ),
    )
}

pub fn owl_secret_lbl_info<'a>(
    owl_suite_id490: SecretBuf<'a>,
    owl_len491: SecretBuf<'a>,
    owl_lbl492: SecretBuf<'a>,
    owl_info493: SecretBuf<'a>,
) -> (res: SecretBuf<'a>)
    ensures
        res.view() == lbl_info(
            owl_suite_id490.view(),
            owl_len491.view(),
            owl_lbl492.view(),
            owl_info493.view(),
        ),
{
    reveal(lbl_info);
    SecretBuf::another_ref(
        &owl_secret_concat(
            SecretBuf::another_ref(
                &owl_secret_concat(
                    SecretBuf::another_ref(
                        &owl_secret_concat(
                            SecretBuf::another_ref(
                                &owl_secret_concat(
                                    SecretBuf::another_ref(&owl_len491),
                                    SecretBuf::from_buf(owl_public_hpke_v1().another_ref()),
                                ),
                            ),
                            SecretBuf::another_ref(&owl_suite_id490),
                        ),
                    ),
                    SecretBuf::another_ref(&owl_lbl492),
                ),
            ),
            SecretBuf::another_ref(&owl_info493),
        ),
    )
}

pub fn owl_public_lbl_info<'a>(
    owl_suite_id494: OwlBuf<'a>,
    owl_len495: OwlBuf<'a>,
    owl_lbl496: OwlBuf<'a>,
    owl_info497: OwlBuf<'a>,
) -> (res: OwlBuf<'a>)
    ensures
        res.view() == lbl_info(
            owl_suite_id494.view(),
            owl_len495.view(),
            owl_lbl496.view(),
            owl_info497.view(),
        ),
{
    reveal(lbl_info);
    OwlBuf::from_vec(
        owl_concat(
            owl_concat(
                owl_concat(
                    owl_concat(owl_len495.as_slice(), owl_public_hpke_v1().as_slice()).as_slice(),
                    owl_suite_id494.as_slice(),
                ).as_slice(),
                owl_lbl496.as_slice(),
            ).as_slice(),
            owl_info497.as_slice(),
        ),
    )
}

pub fn owl_secret_nonce_len<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == nonce_len(),
{
    reveal(nonce_len);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x00u8, 0x0cu8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_nonce_len<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == nonce_len(),
{
    reveal(nonce_len);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x00u8, 0x0cu8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_secret_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == secret_string(),
{
    reveal(secret_string);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x73u8, 0x65u8, 0x63u8, 0x72u8, 0x65u8, 0x74u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_secret_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == secret_string(),
{
    reveal(secret_string);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x73u8, 0x65u8, 0x63u8, 0x72u8, 0x65u8, 0x74u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_shared_secret_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == shared_secret_string(),
{
    reveal(shared_secret_string);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x73u8, 0x68u8, 0x61u8, 0x72u8, 0x65u8, 0x64u8, 0x5fu8, 0x73u8, 0x65u8, 0x63u8, 0x72u8, 0x65u8, 0x74u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_shared_secret_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == shared_secret_string(),
{
    reveal(shared_secret_string);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x73u8, 0x68u8, 0x61u8, 0x72u8, 0x65u8, 0x64u8, 0x5fu8, 0x73u8, 0x65u8, 0x63u8, 0x72u8, 0x65u8, 0x74u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

} // verus!

