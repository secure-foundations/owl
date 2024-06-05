// Extracted verus code from file tests/wip/hpke/full.owl:
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]

pub use vstd::{modes::*, prelude::*, seq::*, string::*};
pub mod speclib;
pub use crate::speclib::{itree::*, *};
pub mod execlib;
pub use crate::execlib::*;
pub mod owl_aead;
pub mod owl_dhke;
pub mod owl_hkdf;
pub mod owl_hmac;
pub mod owl_pke;
pub mod owl_util;
pub use parsley::{
    properties::*, regular::builder::*, regular::bytes::*, regular::bytes_const::*,
    regular::choice::*, regular::tail::*, regular::uints::*, regular::*, utils::*, *,
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
pub fn owl_input<'a, A>(
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
pub fn owl_sample<A>(Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>, n: usize) -> (res: Vec<u8>)
    requires
        old(t).view().is_sample(n),
    ensures
        t.view() == old(t).view().get_sample(res.view()),
{
    owl_util::gen_rand_bytes(n)
}

#[verifier(external_body)]
pub fn owl_output_serialize_fused<'a, A, C: Combinator<'a> + 'a>(
    Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
    comb: C,
    val: C::Result,
    obuf: &mut Vec<u8>,
    dest_addr: &str,
    ret_addr: &str,
)
    requires
        comb.spec_serialize(val.view()) matches Ok(b) ==> old(t).view().is_output(
            b,
            endpoint_of_addr(dest_addr.view()),
        ),
    ensures
        t.view() == old(t).view().give_output(),
        comb.spec_serialize(val.view()) matches Ok(b) ==> obuf.view() == b,
{
    // let ser_result = comb.serialize(val, obuf, 0);
    // assume(ser_result.is_ok());
    // if let Ok((num_written)) = ser_result {
    //     vec_truncate(obuf, num_written);
    // } else {
    //     assert(false);
    // }
    todo!()
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
    // cant autogenerate vest parser
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_ContextS(x: owlSpec_ContextS) -> Seq<u8> {
    // cant autogenerate vest serializer
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
    // cant autogenerate vest parser
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_AuthDecapResult(x: owlSpec_AuthDecapResult) -> Seq<u8> {
    // cant autogenerate vest serializer
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
    // cant autogenerate vest parser
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_ContextR(x: owlSpec_ContextR) -> Seq<u8> {
    // cant autogenerate vest serializer
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
    owlSpec_SomeMsg((Seq<u8>)),
}

use owlSpec_OpenMsg::*;

#[verifier::external_body]
pub closed spec fn parse_owlSpec_OpenMsg(x: Seq<u8>) -> Option<owlSpec_OpenMsg> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_OpenMsg_inner(x: owlSpec_OpenMsg) -> Option<Seq<u8>> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_OpenMsg(x: owlSpec_OpenMsg) -> Seq<u8> {
    todo!()
}

impl OwlSpecSerialize for owlSpec_OpenMsg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_OpenMsg(self)
    }
}

pub open spec fn NoMsg() -> owlSpec_OpenMsg {
    crate::owlSpec_OpenMsg::owlSpec_NoMsg()
}

pub open spec fn SomeMsg(x: (Seq<u8>)) -> owlSpec_OpenMsg {
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
    // cant autogenerate vest parser
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_OpenResult(x: owlSpec_OpenResult) -> Seq<u8> {
    // cant autogenerate vest serializer
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
let _unused269 = (((inc_counter(owl_recv_counter)))) in
let parseval = ((ret(dec_st_aead(sk, ct, ctr, ct_aad)))) in
let caseval = ((ret(parseval))) in
(case (caseval) {
| Some(x) => {
let ctxtR_ = ((ret(ContextR(ghost_unit(), true, ghost_unit(), bn, sk, exp)))) in
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
(parse (adr_) as (owlSpec_AuthDecapResult{owlSpec_adr_eph : eph, owlSpec_adr_shared_secret : shared_secret, owlSpec_adr_shared_secret_inj : _unused271}) in {
let kdfval134 = ((ret(kdf((0 + COUNTER_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), base_nonce_kdf_info())))) in
let base_nonce = ((ret(Seq::subrange(kdfval134, 0, 0 + COUNTER_SIZE)))) in
let kdfval139 = ((ret(kdf((0 + ENCKEY_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), key_kdf_info())))) in
let sk = ((ret(Seq::subrange(kdfval139, 0, 0 + ENCKEY_SIZE)))) in
let kdfval142 = ((ret(kdf((0 + NONCE_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), export_kdf_info())))) in
let exp = ((ret(Seq::subrange(kdfval142, 0, 0 + NONCE_SIZE)))) in
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
(let dh = ((ret(concat(dh_combine(pkS, cfg.owl_skR.view()), dh_combine(eph, cfg.owl_skR.view()))))) in
let kem_context = ((ret(concat(concat(eph, dhpk(cfg.owl_skR.view())), pkS)))) in
let kdfval151 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, empty_seq_u8(), lbl_ikm(eae_prk(), dh), lbl_info(kdfkey_len(), shared_secret_string(), kem_context))))) in
let shared_secret = ((ret(Seq::subrange(kdfval151, 0, 0 + KDFKEY_SIZE)))) in
let shared_secret_ghost = ((ret(ghost_unit()))) in
(ret(Option::Some(AuthDecapResult(ghost_unit(), shared_secret, ghost_unit())))))
else
((ret(Option::None))))
    )
}

#[verifier::opaque]
pub open spec fn SingleShotSeal_spec(
    cfg: cfg_sender,
    mut_state: state_sender,
    pkR: Seq<u8>,
    x: Seq<u8>,
) -> (res: ITree<((), state_sender), Endpoint>) {
    owl_spec!(mut_state, state_sender,
        let aer = (call(AuthEncap_spec(cfg, mut_state, pkR))) in
let context = (call(KeyScheduleS_spec(cfg, mut_state, aer))) in
let c = (call(Seal_spec(cfg, mut_state, context, x))) in
(parse (aer) as (owlSpec_AuthEncapResult{owlSpec_aer_shared_secret : _unused276, owlSpec_aer_pke : pk}) in {
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
        (parse (ctxt) as (owlSpec_ContextS{owlSpec_ctxtS_ss : _unused279, owlSpec_ctxtS_base : base, owlSpec_ctxtS_sk : sk, owlSpec_ctxtS_export : _unused280}) in {
let send_counter = ((ret(counter_as_bytes(mut_state.owl_send_counter)))) in
let _unused281 = (((inc_counter(owl_send_counter)))) in
let i = ((ret(xor(send_counter, base)))) in
(ret(enc_st_aead(sk, x, i, empty_seq_u8())))
} )
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
let kdfval209 = ((ret(kdf((0 + COUNTER_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), base_nonce_kdf_info())))) in
let base_nonce = ((ret(Seq::subrange(kdfval209, 0, 0 + COUNTER_SIZE)))) in
let kdfval212 = ((ret(kdf((0 + ENCKEY_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), key_kdf_info())))) in
let sk = ((ret(Seq::subrange(kdfval212, 0, 0 + ENCKEY_SIZE)))) in
let kdfval215 = ((ret(kdf((0 + NONCE_SIZE) as usize, shared_secret, dh_secret_kdf_ikm(cfg.owl_psk.view()), export_kdf_info())))) in
let exp = ((ret(Seq::subrange(kdfval215, 0, 0 + NONCE_SIZE)))) in
(ret(ContextS(ghost_unit(), base_nonce, sk, exp)))
} )
    )
}

#[verifier::opaque]
pub open spec fn AuthEncap_spec(cfg: cfg_sender, mut_state: state_sender, pkR: Seq<u8>) -> (res:
    ITree<(owlSpec_AuthEncapResult, state_sender), Endpoint>) {
    owl_spec!(mut_state, state_sender,
        let dh = ((ret(concat(dh_combine(pkR, cfg.owl_skS.view()), dh_combine(pkR, cfg.owl_skE.view()))))) in
let kem_context = ((ret(concat(concat(dhpk(cfg.owl_skE.view()), pkR), dhpk(cfg.owl_skS.view()))))) in
let kdfval221 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, empty_seq_u8(), lbl_ikm(eae_prk(), dh), lbl_info(kdfkey_len(), shared_secret_string(), kem_context))))) in
let shared_secret = ((ret(Seq::subrange(kdfval221, 0, 0 + KDFKEY_SIZE)))) in
let res = ((ret(shared_secret))) in
(ret(AuthEncapResult(res, dhpk(cfg.owl_skE.view()))))
    )
}

#[verifier::opaque]
pub closed spec fn base_nonce_kdf_info() -> (res: Seq<u8>) {
    lbl_info(enckey_len(), base_nonce_string(), key_schedule_context())
}

#[verifier::opaque]
pub closed spec fn base_nonce_string() -> (res: Seq<u8>) {
    seq![0x62u8, 0x61u8, 0x73u8, 0x65u8, 0x5fu8, 0x6eu8, 0x6fu8, 0x6eu8, 0x63u8, 0x65u8, ]
}

#[verifier::opaque]
pub closed spec fn crh_labeled_extract_0salt(lbl: Seq<u8>, ikm: Seq<u8>) -> (res: Seq<u8>) {
    crh(concat(concat(concat(hpke_v1(), suite_id()), lbl), ikm))
}

#[verifier::opaque]
pub closed spec fn dh_secret_kdf_ikm(psk_: Seq<u8>) -> (res: Seq<u8>) {
    lbl_ikm(secret_string(), psk_)
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
    lbl_info(enckey_len(), export_string(), key_schedule_context())
}

#[verifier::opaque]
pub closed spec fn export_string() -> (res: Seq<u8>) {
    seq![0x65u8, 0x78u8, 0x70u8, ]
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
pub closed spec fn key_kdf_info() -> (res: Seq<u8>) {
    lbl_info(enckey_len(), key_string(), key_schedule_context())
}

#[verifier::opaque]
pub closed spec fn key_schedule_context() -> (res: Seq<u8>) {
    concat(
        concat(mode(), crh_labeled_extract_0salt(info_hash_string(), info())),
        crh_labeled_extract_0salt(psk_id_hash_string(), psk_id()),
    )
}

#[verifier::opaque]
pub closed spec fn key_string() -> (res: Seq<u8>) {
    seq![0x6bu8, 0x65u8, 0x79u8, ]
}

#[verifier::opaque]
pub closed spec fn lbl_ikm(lbl: Seq<u8>, ikm: Seq<u8>) -> (res: Seq<u8>) {
    concat(concat(concat(hpke_v1(), suite_id()), lbl), ikm)
}

#[verifier::opaque]
pub closed spec fn lbl_info(len: Seq<u8>, lbl: Seq<u8>, info: Seq<u8>) -> (res: Seq<u8>) {
    concat(concat(concat(concat(len, hpke_v1()), suite_id()), lbl), info)
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

#[verifier::opaque]
pub closed spec fn suite_id() -> (res: Seq<u8>) {
    seq![0x48u8, 0x50u8, 0x4bu8, 0x45u8, 0x00u8, 0x20u8, 0x00u8, 0x01u8, 0x00u8, 0x03u8, ]
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
    requires
        arg_owl_hc_pk.len_valid(),
        arg_owl_hc_cipher.len_valid(),
    ensures
        res.len_valid(),
        res.owl_hc_pk.view() == arg_owl_hc_pk.view(),
        res.owl_hc_cipher.view() == arg_owl_hc_cipher.view(),
{
    owl_hpke_ciphertext { owl_hc_pk: arg_owl_hc_pk, owl_hc_cipher: arg_owl_hc_cipher }
}

impl<'a> owl_hpke_ciphertext<'a> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_hc_pk.len_valid() && self.owl_hc_cipher.len_valid()
    }

    pub fn another_ref<'other>(&'other self) -> (result: owl_hpke_ciphertext<'a>)
        requires
            self.len_valid(),
        ensures
            result.view() == self.view(),
            result.len_valid(),
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
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_hpke_ciphertext(arg.view()) is Some,
        res is None ==> parse_owlSpec_hpke_ciphertext(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_hpke_ciphertext(arg.view())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_hpke_ciphertext);
    let exec_comb = exec_combinator_owl_hpke_ciphertext();
    match arg {
        OwlBuf::Borrowed(s) => {
            if let Ok((_, parsed)) = exec_comb.parse(s) {
                let (owl_hc_pk, owl_hc_cipher) = parsed;
                Some(
                    owl_hpke_ciphertext {
                        owl_hc_pk: OwlBuf::from_slice(&owl_hc_pk),
                        owl_hc_cipher: OwlBuf::from_slice(&owl_hc_cipher),
                    },
                )
            } else {
                None
            }
        },
        OwlBuf::Owned(v, start, len) => {
            reveal(OwlBuf::len_valid);
            if let Ok((_, parsed)) = exec_comb.parse(
                slice_subrange((*v).as_slice(), start, start + len),
            ) {
                let (owl_hc_pk, owl_hc_cipher) = parsed;
                Some(
                    owl_hpke_ciphertext {
                        owl_hc_pk: OwlBuf::from_vec(slice_to_vec(owl_hc_pk)),
                        owl_hc_cipher: OwlBuf::from_vec(slice_to_vec(owl_hc_cipher)),
                    },
                )
            } else {
                None
            }
        },
    }
}

pub exec fn serialize_owl_hpke_ciphertext_inner(arg: &owl_hpke_ciphertext) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
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
            (arg.owl_hc_pk.as_slice(), arg.owl_hc_cipher.as_slice()),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            vec_truncate(&mut obuf, num_written);
            Some(obuf)
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_hpke_ciphertext(arg: &owl_hpke_ciphertext) -> (res: Vec<u8>)
    requires
        arg.len_valid(),
    ensures
        res.view() == serialize_owlSpec_hpke_ciphertext(arg.view()),
{
    reveal(serialize_owlSpec_hpke_ciphertext);
    let res = serialize_owl_hpke_ciphertext_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_AuthEncapResult<'a> {
    pub owl_aer_shared_secret: OwlBuf<'a>,
    pub owl_aer_pke: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_AuthEncapResult<'a>(
    arg_owl_aer_shared_secret: OwlBuf<'a>,
    arg_owl_aer_pke: OwlBuf<'a>,
) -> (res: owl_AuthEncapResult<'a>)
    requires
        arg_owl_aer_shared_secret.len_valid(),
        arg_owl_aer_pke.len_valid(),
    ensures
        res.len_valid(),
        res.owl_aer_shared_secret.view() == arg_owl_aer_shared_secret.view(),
        res.owl_aer_pke.view() == arg_owl_aer_pke.view(),
{
    owl_AuthEncapResult {
        owl_aer_shared_secret: arg_owl_aer_shared_secret,
        owl_aer_pke: arg_owl_aer_pke,
    }
}

impl<'a> owl_AuthEncapResult<'a> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_aer_shared_secret.len_valid() && self.owl_aer_pke.len_valid()
    }

    pub fn another_ref<'other>(&'other self) -> (result: owl_AuthEncapResult<'a>)
        requires
            self.len_valid(),
        ensures
            result.view() == self.view(),
            result.len_valid(),
    {
        owl_AuthEncapResult {
            owl_aer_shared_secret: OwlBuf::another_ref(&self.owl_aer_shared_secret),
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
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_AuthEncapResult(arg.view()) is Some,
        res is None ==> parse_owlSpec_AuthEncapResult(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_AuthEncapResult(arg.view())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_AuthEncapResult);
    let exec_comb = exec_combinator_owl_AuthEncapResult();
    match arg {
        OwlBuf::Borrowed(s) => {
            if let Ok((_, parsed)) = exec_comb.parse(s) {
                let (owl_aer_shared_secret, owl_aer_pke) = parsed;
                Some(
                    owl_AuthEncapResult {
                        owl_aer_shared_secret: OwlBuf::from_slice(&owl_aer_shared_secret),
                        owl_aer_pke: OwlBuf::from_slice(&owl_aer_pke),
                    },
                )
            } else {
                None
            }
        },
        OwlBuf::Owned(v, start, len) => {
            reveal(OwlBuf::len_valid);
            if let Ok((_, parsed)) = exec_comb.parse(
                slice_subrange((*v).as_slice(), start, start + len),
            ) {
                let (owl_aer_shared_secret, owl_aer_pke) = parsed;
                Some(
                    owl_AuthEncapResult {
                        owl_aer_shared_secret: OwlBuf::from_vec(
                            slice_to_vec(owl_aer_shared_secret),
                        ),
                        owl_aer_pke: OwlBuf::from_vec(slice_to_vec(owl_aer_pke)),
                    },
                )
            } else {
                None
            }
        },
    }
}

pub exec fn serialize_owl_AuthEncapResult_inner(arg: &owl_AuthEncapResult) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
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
        let mut obuf = vec_u8_of_len(arg.owl_aer_shared_secret.len() + arg.owl_aer_pke.len() + 0);
        let ser_result = exec_comb.serialize(
            (arg.owl_aer_shared_secret.as_slice(), arg.owl_aer_pke.as_slice()),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            vec_truncate(&mut obuf, num_written);
            Some(obuf)
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_AuthEncapResult(arg: &owl_AuthEncapResult) -> (res: Vec<u8>)
    requires
        arg.len_valid(),
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
    pub owl_ctxtS_base: OwlBuf<'a>,
    pub owl_ctxtS_sk: OwlBuf<'a>,
    pub owl_ctxtS_export: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_ContextS<'a>(
    arg_owl_ctxtS_ss: Ghost<()>,
    arg_owl_ctxtS_base: OwlBuf<'a>,
    arg_owl_ctxtS_sk: OwlBuf<'a>,
    arg_owl_ctxtS_export: OwlBuf<'a>,
) -> (res: owl_ContextS<'a>)
    requires
        arg_owl_ctxtS_base.len_valid(),
        arg_owl_ctxtS_sk.len_valid(),
        arg_owl_ctxtS_export.len_valid(),
    ensures
        res.len_valid(),
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
    pub open spec fn len_valid(&self) -> bool {
        self.owl_ctxtS_base.len_valid() && self.owl_ctxtS_sk.len_valid()
            && self.owl_ctxtS_export.len_valid()
    }

    pub fn another_ref<'other>(&'other self) -> (result: owl_ContextS<'a>)
        requires
            self.len_valid(),
        ensures
            result.view() == self.view(),
            result.len_valid(),
    {
        owl_ContextS {
            owl_ctxtS_ss: self.owl_ctxtS_ss,
            owl_ctxtS_base: OwlBuf::another_ref(&self.owl_ctxtS_base),
            owl_ctxtS_sk: OwlBuf::another_ref(&self.owl_ctxtS_sk),
            owl_ctxtS_export: OwlBuf::another_ref(&self.owl_ctxtS_export),
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

pub struct owl_AuthDecapResult<'a> {
    pub owl_adr_eph: Ghost<()>,
    pub owl_adr_shared_secret: OwlBuf<'a>,
    pub owl_adr_shared_secret_inj: Ghost<()>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_AuthDecapResult<'a>(
    arg_owl_adr_eph: Ghost<()>,
    arg_owl_adr_shared_secret: OwlBuf<'a>,
    arg_owl_adr_shared_secret_inj: Ghost<()>,
) -> (res: owl_AuthDecapResult<'a>)
    requires
        arg_owl_adr_shared_secret.len_valid(),
    ensures
        res.len_valid(),
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
    pub open spec fn len_valid(&self) -> bool {
        self.owl_adr_shared_secret.len_valid()
    }

    pub fn another_ref<'other>(&'other self) -> (result: owl_AuthDecapResult<'a>)
        requires
            self.len_valid(),
        ensures
            result.view() == self.view(),
            result.len_valid(),
    {
        owl_AuthDecapResult {
            owl_adr_eph: self.owl_adr_eph,
            owl_adr_shared_secret: OwlBuf::another_ref(&self.owl_adr_shared_secret),
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

pub struct owl_ContextR<'a> {
    pub owl_ctxtR_eph: Ghost<()>,
    pub owl_ctxtR_confirmed: bool,
    pub owl_ctxtR_ss: Ghost<()>,
    pub owl_ctxtR_base: OwlBuf<'a>,
    pub owl_ctxtR_sk: OwlBuf<'a>,
    pub owl_ctxtR_export: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_ContextR<'a>(
    arg_owl_ctxtR_eph: Ghost<()>,
    arg_owl_ctxtR_confirmed: bool,
    arg_owl_ctxtR_ss: Ghost<()>,
    arg_owl_ctxtR_base: OwlBuf<'a>,
    arg_owl_ctxtR_sk: OwlBuf<'a>,
    arg_owl_ctxtR_export: OwlBuf<'a>,
) -> (res: owl_ContextR<'a>)
    requires
        arg_owl_ctxtR_base.len_valid(),
        arg_owl_ctxtR_sk.len_valid(),
        arg_owl_ctxtR_export.len_valid(),
    ensures
        res.len_valid(),
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
    pub open spec fn len_valid(&self) -> bool {
        self.owl_ctxtR_base.len_valid() && self.owl_ctxtR_sk.len_valid()
            && self.owl_ctxtR_export.len_valid()
    }

    pub fn another_ref<'other>(&'other self) -> (result: owl_ContextR<'a>)
        requires
            self.len_valid(),
        ensures
            result.view() == self.view(),
            result.len_valid(),
    {
        owl_ContextR {
            owl_ctxtR_eph: self.owl_ctxtR_eph,
            owl_ctxtR_confirmed: self.owl_ctxtR_confirmed,
            owl_ctxtR_ss: self.owl_ctxtR_ss,
            owl_ctxtR_base: OwlBuf::another_ref(&self.owl_ctxtR_base),
            owl_ctxtR_sk: OwlBuf::another_ref(&self.owl_ctxtR_sk),
            owl_ctxtR_export: OwlBuf::another_ref(&self.owl_ctxtR_export),
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

pub enum owl_OpenMsg<'a> {
    owl_NoMsg(),
    owl_SomeMsg(OwlBuf<'a>),
}

use owl_OpenMsg::*;

impl<'a> owl_OpenMsg<'a> {
    pub open spec fn len_valid(&self) -> bool {
        match self {
            owl_NoMsg() => true,
            owl_SomeMsg(x) => x.len_valid(),
        }
    }

    pub fn another_ref<'other>(&'other self) -> (result: owl_OpenMsg<'a>)
        requires
            self.len_valid(),
        ensures
            result.view() == self.view(),
            result.len_valid(),
    {
        match self {
            owl_NoMsg() => owl_NoMsg(),
            owl_SomeMsg(x) => owl_SomeMsg(OwlBuf::another_ref(x)),
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
    requires
        arg_owl_or_ctxt.len_valid(),
        arg_owl_or_pt.len_valid(),
    ensures
        res.len_valid(),
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
    pub open spec fn len_valid(&self) -> bool {
        self.owl_or_ctxt.len_valid() && self.owl_or_pt.len_valid()
    }

    pub fn another_ref<'other>(&'other self) -> (result: owl_OpenResult<'a>)
        requires
            self.len_valid(),
        ensures
            result.view() == self.view(),
            result.len_valid(),
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

pub struct state_receiver {
    pub owl_recv_counter: usize,
}

impl state_receiver {
    #[verifier::external_body]
    pub fn init_state_receiver() -> Self {
        state_receiver { owl_recv_counter: 0 }
    }
}

pub struct cfg_receiver {
    pub salt: Vec<u8>,
    pub owl_psk: Vec<u8>,
    pub owl_skR: Vec<u8>,
    pub pk_owl_skS: Vec<u8>,
    pub pk_owl_skE: Vec<u8>,
    pub pk_owl_skR: Vec<u8>,
}

impl cfg_receiver {
    // TODO: library routines for reading configs
    /*
    #[verifier::external_body]
    pub fn init_cfg_receiver(config_path: &StrSlice) -> Self {
        let listener = TcpListener::bind(receiver_addr().into_rust_str()).unwrap();
        let config_str = fs::read_to_string(config_path.into_rust_str()).expect("Config file not found");
        let config = deserialize_cfg_alice_config(&config_str);
        cfg_receiver {
            listener,
            salt: (config.salt),
            owl_psk : (config.owl_psk),
owl_skR : (config.owl_skR),
pk_owl_skS : (config.pk_owl_skS),
pk_owl_skE : (config.pk_owl_skE),
pk_owl_skR : (config.pk_owl_skR)
        }
    }
    */

    #[verifier::external_body]
    pub fn owl_SingleShotOpen_wrapper<'a>(
        &'a self,
        mut_state: &mut state_receiver,
        owl_pkS379: &'a [u8],
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
            msg
        ).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_SingleShotOpen<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Option<owlSpec_OpenResult>, state_receiver), Endpoint>>,
        mut_state: &mut state_receiver,
        owl_pkS379: OwlBuf<'a>,
        ibuf: &'a [u8]
    ) -> (res: Result<
        (
            Option<owl_OpenResult<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_OpenResult>, state_receiver), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == SingleShotOpen_spec(*self, *old(mut_state), owl_pkS379.view()),
            owl_pkS379.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
            res matches Ok((Some(b), _)) ==> b.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_OpenResult<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_OpenResult>, state_receiver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(SingleShotOpen_spec);
            let (tmp_owl_i302, owl__301) = {
                owl_input::<(Option<owlSpec_OpenResult>, state_receiver)>(
                    Tracked(&mut itree),
                    ibuf,
                )
            };
            let owl_i302 = OwlBuf::from_slice(tmp_owl_i302);
            let parseval_tmp = OwlBuf::another_ref(&owl_i302);
            if let Some(parseval) = parse_owl_hpke_ciphertext(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_eph304 = OwlBuf::another_ref(&parseval.owl_hc_pk);
                let owl_ct303 = OwlBuf::another_ref(&parseval.owl_hc_cipher);
                {
                    let (owl_oadr305, Tracked(itree)) = {
                        let tmp_arg1380 = OwlBuf::another_ref(&owl_pkS379);
                        let tmp_arg2381 = OwlBuf::another_ref(&owl_eph304);
                        owl_call_ret_option!(itree, *mut_state, AuthDecap_spec(*self, *mut_state, tmp_arg1380.view(), tmp_arg2381.view()), self.owl_AuthDecap(mut_state, tmp_arg1380, tmp_arg2381))
                    };
                    let owl_caseval306 = { owl_oadr305 };
                    match owl_caseval306 {
                        Option::Some(tmp_owl_adr307) => {
                            let owl_adr307 = owl_AuthDecapResult::another_ref(&tmp_owl_adr307);
                            {
                                let (owl_ctxt308, Tracked(itree)) = {
                                    let tmp_arg1382 = owl_AuthDecapResult::another_ref(&owl_adr307);
                                    owl_call!(itree, *mut_state, KeyScheduleR_spec(*self, *mut_state, tmp_arg1382.view()), self.owl_KeyScheduleR(mut_state, tmp_arg1382))
                                };
                                let (owl_res309, Tracked(itree)) = {
                                    let tmp_arg1383 = owl_ContextR::another_ref(&owl_ctxt308);
                                    let tmp_arg2384 = OwlBuf::another_ref(
                                        &{
                                            let x = mk_vec_u8![];
                                            OwlBuf::from_vec(x)
                                        },
                                    );
                                    let tmp_arg3385 = OwlBuf::another_ref(&owl_ct303);
                                    owl_call!(itree, *mut_state, Open_spec(*self, *mut_state, tmp_arg1383.view(), tmp_arg2384.view(), tmp_arg3385.view()), self.owl_Open(mut_state, tmp_arg1383, tmp_arg2384, tmp_arg3385))
                                };
                                (Some(owl_OpenResult::another_ref(&owl_res309)), Tracked(itree))
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
        owl_ctxtR388: owl_ContextR<'a>,
        owl_ct_aad389: OwlBuf<'a>,
        owl_ct390: OwlBuf<'a>,
    ) -> (res: Result<
        (owl_OpenResult<'a>, Tracked<ITreeToken<(owlSpec_OpenResult, state_receiver), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == Open_spec(
                *self,
                *old(mut_state),
                owl_ctxtR388.view(),
                owl_ct_aad389.view(),
                owl_ct390.view(),
            ),
            owl_ctxtR388.len_valid(),
            owl_ct_aad389.len_valid(),
            owl_ct390.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
            res matches Ok(r) ==> r.0.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_OpenResult<'a>,
            Tracked<ITreeToken<(owlSpec_OpenResult, state_receiver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(Open_spec);
            let owl_ctxtR314 = { owl_ctxtR388 };
            let parseval = owl_ContextR::another_ref(&owl_ctxtR314);
            let owl_eph320 = parseval.owl_ctxtR_eph;
            let owl_confirmed319 = parseval.owl_ctxtR_confirmed;
            let owl_ss318 = parseval.owl_ctxtR_ss;
            let owl_bn317 = OwlBuf::another_ref(&parseval.owl_ctxtR_base);
            let owl_sk316 = OwlBuf::another_ref(&parseval.owl_ctxtR_sk);
            let owl_exp315 = OwlBuf::another_ref(&parseval.owl_ctxtR_export);
            let tmp_owl_ctr321 = { owl_counter_as_bytes(&mut_state.owl_recv_counter) };
            let owl_ctr321 = OwlBuf::from_slice(&tmp_owl_ctr321);
            let tmp_owl_iv322 = { owl_xor(owl_bn317.as_slice(), owl_ctr321.as_slice()) };
            let owl_iv322 = OwlBuf::from_vec(tmp_owl_iv322);
            let owl__323 = {
                if mut_state.owl_recv_counter > usize::MAX - 1 {
                    return Err(OwlError::IntegerOverflow);
                };
                mut_state.owl_recv_counter = mut_state.owl_recv_counter + 1;
            };
            let tmp_owl_parseval324 = {
                owl_dec_st_aead(
                    owl_sk316.as_slice(),
                    owl_ct390.as_slice(),
                    owl_iv322.as_slice(),
                    owl_ct_aad389.as_slice(),
                )
            };
            let owl_parseval324 = OwlBuf::from_vec_option(tmp_owl_parseval324);
            let owl_caseval325 = { owl_parseval324 };
            match owl_caseval325 {
                Option::Some(tmp_owl_x326) => {
                    let owl_x326 = OwlBuf::another_ref(&tmp_owl_x326);
                    let owl_ctxtR_327 = {
                        owl_ContextR(
                            owl_ghost_unit(),
                            true,
                            owl_ghost_unit(),
                            OwlBuf::another_ref(&owl_bn317),
                            OwlBuf::another_ref(&owl_sk316),
                            OwlBuf::another_ref(&owl_exp315),
                        )
                    };
                    let owl_res328 = {
                        owl_OpenResult(
                            owl_ContextR::another_ref(&owl_ctxtR_327),
                            owl_OpenMsg::another_ref(&owl_SomeMsg(OwlBuf::another_ref(&owl_x326))),
                            owl_ghost_unit(),
                        )
                    };
                    (owl_OpenResult::another_ref(&owl_res328), Tracked(itree))
                },
                Option::None => {
                    let owl_res329 = {
                        owl_OpenResult(
                            owl_ContextR::another_ref(&owl_ctxtR314),
                            owl_OpenMsg::another_ref(&owl_NoMsg()),
                            owl_ghost_unit(),
                        )
                    };
                    (owl_OpenResult::another_ref(&owl_res329), Tracked(itree))
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
        owl_adr389: owl_AuthDecapResult<'a>,
    ) -> (res: Result<
        (owl_ContextR<'a>, Tracked<ITreeToken<(owlSpec_ContextR, state_receiver), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == KeyScheduleR_spec(*self, *old(mut_state), owl_adr389.view()),
            owl_adr389.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
            res matches Ok(r) ==> r.0.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_ContextR<'a>,
            Tracked<ITreeToken<(owlSpec_ContextR, state_receiver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(KeyScheduleR_spec);
            let owl_adr_330 = { owl_adr389 };
            let parseval = owl_AuthDecapResult::another_ref(&owl_adr_330);
            let owl_eph333 = parseval.owl_adr_eph;
            let owl_shared_secret332 = OwlBuf::another_ref(&parseval.owl_adr_shared_secret);
            let owl__331 = parseval.owl_adr_shared_secret_inj;
            let tmp_owl_kdfval134334 = {
                owl_extract_expand_to_len(
                    0 + COUNTER_SIZE,
                    owl_shared_secret332.as_slice(),
                    owl_dh_secret_kdf_ikm(
                        OwlBuf::another_ref(&OwlBuf::from_slice(&self.owl_psk.as_slice())),
                    ).as_slice(),
                    owl_base_nonce_kdf_info().as_slice(),
                )
            };
            let owl_kdfval134334 = OwlBuf::from_vec(tmp_owl_kdfval134334);
            let owl_base_nonce335 = {
                { OwlBuf::another_ref(&owl_kdfval134334).subrange(0, 0 + COUNTER_SIZE) }
            };
            let tmp_owl_kdfval139336 = {
                owl_extract_expand_to_len(
                    0 + ENCKEY_SIZE,
                    owl_shared_secret332.as_slice(),
                    owl_dh_secret_kdf_ikm(
                        OwlBuf::another_ref(&OwlBuf::from_slice(&self.owl_psk.as_slice())),
                    ).as_slice(),
                    owl_key_kdf_info().as_slice(),
                )
            };
            let owl_kdfval139336 = OwlBuf::from_vec(tmp_owl_kdfval139336);
            let owl_sk337 = {
                { OwlBuf::another_ref(&owl_kdfval139336).subrange(0, 0 + ENCKEY_SIZE) }
            };
            let tmp_owl_kdfval142338 = {
                owl_extract_expand_to_len(
                    0 + NONCE_SIZE,
                    owl_shared_secret332.as_slice(),
                    owl_dh_secret_kdf_ikm(
                        OwlBuf::another_ref(&OwlBuf::from_slice(&self.owl_psk.as_slice())),
                    ).as_slice(),
                    owl_export_kdf_info().as_slice(),
                )
            };
            let owl_kdfval142338 = OwlBuf::from_vec(tmp_owl_kdfval142338);
            let owl_exp339 = {
                { OwlBuf::another_ref(&owl_kdfval142338).subrange(0, 0 + NONCE_SIZE) }
            };
            let owl_res340 = {
                owl_ContextR(
                    owl_ghost_unit(),
                    false,
                    owl_ghost_unit(),
                    OwlBuf::another_ref(&owl_base_nonce335),
                    OwlBuf::another_ref(&owl_sk337),
                    OwlBuf::another_ref(&owl_exp339),
                )
            };
            (owl_ContextR::another_ref(&owl_res340), Tracked(itree))
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
        owl_pkS390: OwlBuf<'a>,
        owl_eph391: OwlBuf<'a>,
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
                owl_pkS390.view(),
                owl_eph391.view(),
            ),
            owl_pkS390.len_valid(),
            owl_eph391.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
            res matches Ok((Some(b), _)) ==> b.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_AuthDecapResult<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_AuthDecapResult>, state_receiver), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(AuthDecap_spec);
            if owl_is_group_elem(owl_eph391.as_slice()) {
                let tmp_owl_dh343 = {
                    owl_concat(
                        owl_dh_combine(
                            owl_pkS390.as_slice(),
                            OwlBuf::from_slice(&self.owl_skR.as_slice()).as_slice(),
                        ).as_slice(),
                        owl_dh_combine(
                            owl_eph391.as_slice(),
                            OwlBuf::from_slice(&self.owl_skR.as_slice()).as_slice(),
                        ).as_slice(),
                    )
                };
                let owl_dh343 = OwlBuf::from_vec(tmp_owl_dh343);
                let tmp_owl_kem_context344 = {
                    owl_concat(
                        owl_concat(
                            owl_eph391.as_slice(),
                            owl_dhpk(
                                OwlBuf::from_slice(&self.owl_skR.as_slice()).as_slice(),
                            ).as_slice(),
                        ).as_slice(),
                        owl_pkS390.as_slice(),
                    )
                };
                let owl_kem_context344 = OwlBuf::from_vec(tmp_owl_kem_context344);
                let tmp_owl_kdfval151345 = {
                    owl_extract_expand_to_len(
                        0 + KDFKEY_SIZE,
                        {
                            let x = mk_vec_u8![];
                            OwlBuf::from_vec(x)
                        }.as_slice(),
                        owl_lbl_ikm(
                            OwlBuf::another_ref(&owl_eae_prk()),
                            OwlBuf::another_ref(&owl_dh343),
                        ).as_slice(),
                        owl_lbl_info(
                            OwlBuf::another_ref(&owl_kdfkey_len()),
                            OwlBuf::another_ref(&owl_shared_secret_string()),
                            OwlBuf::another_ref(&owl_kem_context344),
                        ).as_slice(),
                    )
                };
                let owl_kdfval151345 = OwlBuf::from_vec(tmp_owl_kdfval151345);
                let owl_shared_secret346 = {
                    { OwlBuf::another_ref(&owl_kdfval151345).subrange(0, 0 + KDFKEY_SIZE) }
                };
                let owl_shared_secret_ghost347 = { owl_ghost_unit() };
                (
                    Some(
                        owl_AuthDecapResult::another_ref(
                            &owl_AuthDecapResult(
                                owl_ghost_unit(),
                                OwlBuf::another_ref(&owl_shared_secret346),
                                owl_ghost_unit(),
                            ),
                        ),
                    ),
                    Tracked(itree),
                )
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

pub struct cfg_sender {
    pub salt: Vec<u8>,
    pub owl_psk: Vec<u8>,
    pub owl_skS: Vec<u8>,
    pub owl_skE: Vec<u8>,
    pub pk_owl_skS: Vec<u8>,
    pub pk_owl_skE: Vec<u8>,
    pub pk_owl_skR: Vec<u8>,
}

impl cfg_sender {
    // TODO: library routines for reading configs
    /*
    #[verifier::external_body]
    pub fn init_cfg_sender(config_path: &StrSlice) -> Self {
        let listener = TcpListener::bind(sender_addr().into_rust_str()).unwrap();
        let config_str = fs::read_to_string(config_path.into_rust_str()).expect("Config file not found");
        let config = deserialize_cfg_alice_config(&config_str);
        cfg_sender {
            listener,
            salt: (config.salt),
            owl_psk : (config.owl_psk),
owl_skS : (config.owl_skS),
owl_skE : (config.owl_skE),
pk_owl_skS : (config.pk_owl_skS),
pk_owl_skE : (config.pk_owl_skE),
pk_owl_skR : (config.pk_owl_skR)
        }
    }
    */

    #[verifier::external_body]
    pub fn owl_SingleShotSeal_wrapper<'a>(
        &'a self,
        mut_state: &mut state_sender,
        owl_pkR392: &'a [u8],
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
            OwlBuf::from_slice(owl_x393),
            obuf
        ).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_SingleShotSeal<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<((), state_sender), Endpoint>>,
        mut_state: &mut state_sender,
        owl_pkR392: OwlBuf<'a>,
        owl_x393: OwlBuf<'a>,
        obuf: &'a mut [u8]
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_sender), Endpoint>>), OwlError>)
        requires
            itree.view() == SingleShotSeal_spec(
                *self,
                *old(mut_state),
                owl_pkR392.view(),
                owl_x393.view(),
            ),
            owl_pkR392.len_valid(),
            owl_x393.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_sender), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(SingleShotSeal_spec);
            let (owl_aer350, Tracked(itree)) = {
                let tmp_arg1394 = OwlBuf::another_ref(&owl_pkR392);
                owl_call!(itree, *mut_state, AuthEncap_spec(*self, *mut_state, tmp_arg1394.view()), self.owl_AuthEncap(mut_state, tmp_arg1394))
            };
            let (owl_context351, Tracked(itree)) = {
                let tmp_arg1395 = owl_AuthEncapResult::another_ref(&owl_aer350);
                owl_call!(itree, *mut_state, KeyScheduleS_spec(*self, *mut_state, tmp_arg1395.view()), self.owl_KeyScheduleS(mut_state, tmp_arg1395))
            };
            let (owl_c352, Tracked(itree)) = {
                let tmp_arg1396 = owl_ContextS::another_ref(&owl_context351);
                let tmp_arg2397 = OwlBuf::another_ref(&owl_x393);
                owl_call!(itree, *mut_state, Seal_spec(*self, *mut_state, tmp_arg1396.view(), tmp_arg2397.view()), self.owl_Seal(mut_state, tmp_arg1396, tmp_arg2397))
            };
            let parseval = owl_AuthEncapResult::another_ref(&owl_aer350);
            let owl__354 = OwlBuf::another_ref(&parseval.owl_aer_shared_secret);
            let owl_pk353 = OwlBuf::another_ref(&parseval.owl_aer_pke);
            owl_output::<((), state_sender)>(
                Tracked(&mut itree),
                serialize_owl_hpke_ciphertext(
                    &owl_hpke_ciphertext(
                        OwlBuf::another_ref(&owl_pk353),
                        OwlBuf::another_ref(&owl_c352),
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
        owl_ctxt398: owl_ContextS<'a>,
        owl_x399: OwlBuf<'a>,
    ) -> (res: Result<
        (OwlBuf<'a>, Tracked<ITreeToken<(Seq<u8>, state_sender), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == Seal_spec(*self, *old(mut_state), owl_ctxt398.view(), owl_x399.view()),
            owl_ctxt398.len_valid(),
            owl_x399.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
            res matches Ok(r) ==> r.0.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            OwlBuf<'a>,
            Tracked<ITreeToken<(Seq<u8>, state_sender), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(Seal_spec);
            let parseval = owl_ContextS::another_ref(&owl_ctxt398);
            let owl__360 = parseval.owl_ctxtS_ss;
            let owl_base359 = OwlBuf::another_ref(&parseval.owl_ctxtS_base);
            let owl_sk358 = OwlBuf::another_ref(&parseval.owl_ctxtS_sk);
            let owl__357 = OwlBuf::another_ref(&parseval.owl_ctxtS_export);
            let tmp_owl_send_counter361 = { owl_counter_as_bytes(&mut_state.owl_send_counter) };
            let owl_send_counter361 = OwlBuf::from_slice(&tmp_owl_send_counter361);
            let owl__362 = {
                if mut_state.owl_send_counter > usize::MAX - 1 {
                    return Err(OwlError::IntegerOverflow);
                };
                mut_state.owl_send_counter = mut_state.owl_send_counter + 1;
            };
            // dbg!(hex::encode(&owl_send_counter361.as_slice()));
            // dbg!(hex::encode(&owl_base359.as_slice()));
            let tmp_owl_i363 = { owl_xor(owl_send_counter361.as_slice(), owl_base359.as_slice()) };
            let owl_i363 = OwlBuf::from_vec(tmp_owl_i363);
            (
                OwlBuf::from_vec(
                    owl_enc_st_aead(
                        owl_sk358.as_slice(),
                        owl_x399.as_slice(),
                        owl_i363.as_slice(),
                        {
                            let x = mk_vec_u8![];
                            OwlBuf::from_vec(x)
                        }.as_slice(),
                    ),
                ),
                Tracked(itree),
            )
        };
        Ok((OwlBuf::another_ref(&res_inner), Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_KeyScheduleS<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_ContextS, state_sender), Endpoint>>,
        mut_state: &mut state_sender,
        owl_aer400: owl_AuthEncapResult<'a>,
    ) -> (res: Result<
        (owl_ContextS<'a>, Tracked<ITreeToken<(owlSpec_ContextS, state_sender), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == KeyScheduleS_spec(*self, *old(mut_state), owl_aer400.view()),
            owl_aer400.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
            res matches Ok(r) ==> r.0.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_ContextS<'a>,
            Tracked<ITreeToken<(owlSpec_ContextS, state_sender), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(KeyScheduleS_spec);
            let parseval = owl_AuthEncapResult::another_ref(&owl_aer400);
            let owl_shared_secret366 = OwlBuf::another_ref(&parseval.owl_aer_shared_secret);
            let owl_pkE365 = OwlBuf::another_ref(&parseval.owl_aer_pke);
            let tmp_owl_kdfval209367 = {
                owl_extract_expand_to_len(
                    0 + COUNTER_SIZE,
                    owl_shared_secret366.as_slice(),
                    owl_dh_secret_kdf_ikm(
                        OwlBuf::another_ref(&OwlBuf::from_slice(&self.owl_psk.as_slice())),
                    ).as_slice(),
                    owl_base_nonce_kdf_info().as_slice(),
                )
            };
            let owl_kdfval209367 = OwlBuf::from_vec(tmp_owl_kdfval209367);
            let owl_base_nonce368 = {
                { OwlBuf::another_ref(&owl_kdfval209367).subrange(0, 0 + COUNTER_SIZE) }
            };
            let tmp_owl_kdfval212369 = {
                owl_extract_expand_to_len(
                    0 + ENCKEY_SIZE,
                    owl_shared_secret366.as_slice(),
                    owl_dh_secret_kdf_ikm(
                        OwlBuf::another_ref(&OwlBuf::from_slice(&self.owl_psk.as_slice())),
                    ).as_slice(),
                    owl_key_kdf_info().as_slice(),
                )
            };
            let owl_kdfval212369 = OwlBuf::from_vec(tmp_owl_kdfval212369);
            let owl_sk370 = {
                { OwlBuf::another_ref(&owl_kdfval212369).subrange(0, 0 + ENCKEY_SIZE) }
            };
            let tmp_owl_kdfval215371 = {
                owl_extract_expand_to_len(
                    0 + NONCE_SIZE,
                    owl_shared_secret366.as_slice(),
                    owl_dh_secret_kdf_ikm(
                        OwlBuf::another_ref(&OwlBuf::from_slice(&self.owl_psk.as_slice())),
                    ).as_slice(),
                    owl_export_kdf_info().as_slice(),
                )
            };
            let owl_kdfval215371 = OwlBuf::from_vec(tmp_owl_kdfval215371);
            let owl_exp372 = {
                { OwlBuf::another_ref(&owl_kdfval215371).subrange(0, 0 + NONCE_SIZE) }
            };
            (
                owl_ContextS::another_ref(
                    &owl_ContextS(
                        owl_ghost_unit(),
                        OwlBuf::another_ref(&owl_base_nonce368),
                        OwlBuf::another_ref(&owl_sk370),
                        OwlBuf::another_ref(&owl_exp372),
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
        owl_pkR401: OwlBuf<'a>,
    ) -> (res: Result<
        (
            owl_AuthEncapResult<'a>,
            Tracked<ITreeToken<(owlSpec_AuthEncapResult, state_sender), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == AuthEncap_spec(*self, *old(mut_state), owl_pkR401.view()),
            owl_pkR401.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
            res matches Ok(r) ==> r.0.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_AuthEncapResult<'a>,
            Tracked<ITreeToken<(owlSpec_AuthEncapResult, state_sender), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(AuthEncap_spec);
            let tmp_owl_dh374 = {
                owl_concat(
                    owl_dh_combine(
                        owl_pkR401.as_slice(),
                        OwlBuf::from_slice(&self.owl_skS.as_slice()).as_slice(),
                    ).as_slice(),
                    owl_dh_combine(
                        owl_pkR401.as_slice(),
                        OwlBuf::from_slice(&self.owl_skE.as_slice()).as_slice(),
                    ).as_slice(),
                )
            };
            let owl_dh374 = OwlBuf::from_vec(tmp_owl_dh374);
            let tmp_owl_kem_context375 = {
                owl_concat(
                    owl_concat(
                        owl_dhpk(
                            OwlBuf::from_slice(&self.owl_skE.as_slice()).as_slice(),
                        ).as_slice(),
                        owl_pkR401.as_slice(),
                    ).as_slice(),
                    owl_dhpk(OwlBuf::from_slice(&self.owl_skS.as_slice()).as_slice()).as_slice(),
                )
            };
            let owl_kem_context375 = OwlBuf::from_vec(tmp_owl_kem_context375);
            let tmp_owl_kdfval221376 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE,
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                    owl_lbl_ikm(
                        OwlBuf::another_ref(&owl_eae_prk()),
                        OwlBuf::another_ref(&owl_dh374),
                    ).as_slice(),
                    owl_lbl_info(
                        OwlBuf::another_ref(&owl_kdfkey_len()),
                        OwlBuf::another_ref(&owl_shared_secret_string()),
                        OwlBuf::another_ref(&owl_kem_context375),
                    ).as_slice(),
                )
            };
            let owl_kdfval221376 = OwlBuf::from_vec(tmp_owl_kdfval221376);
            let owl_shared_secret377 = {
                { OwlBuf::another_ref(&owl_kdfval221376).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_res378 = { owl_shared_secret377 };
            // dbg!(hex::encode(&owl_res378.as_slice()));
            (
                owl_AuthEncapResult::another_ref(
                    &owl_AuthEncapResult(
                        OwlBuf::another_ref(&owl_res378),
                        OwlBuf::from_vec(
                            owl_dhpk(OwlBuf::from_slice(&self.owl_skE.as_slice()).as_slice()),
                        ),
                    ),
                ),
                Tracked(itree),
            )
        };
        Ok((owl_AuthEncapResult::another_ref(&res_inner), Tracked(itree)))
    }
}

pub fn owl_base_nonce_kdf_info<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == base_nonce_kdf_info(),
        res.len_valid(),
{
    reveal(base_nonce_kdf_info);
    OwlBuf::another_ref(
        &owl_lbl_info(
            OwlBuf::another_ref(&owl_enckey_len()),
            OwlBuf::another_ref(&owl_base_nonce_string()),
            OwlBuf::another_ref(&owl_key_schedule_context()),
        ),
    )
}

pub fn owl_base_nonce_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == base_nonce_string(),
        res.len_valid(),
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

pub fn owl_crh_labeled_extract_0salt<'a>(owl_lbl402: OwlBuf<'_>, owl_ikm403: OwlBuf<'_>) -> (res:
    OwlBuf<'a>)
    requires
        owl_lbl402.len_valid(),
        owl_ikm403.len_valid(),
    ensures
        res.view() == crh_labeled_extract_0salt(owl_lbl402.view(), owl_ikm403.view()),
        res.len_valid(),
{
    reveal(crh_labeled_extract_0salt);
    OwlBuf::from_vec(
        owl_crh(
            owl_concat(
                owl_concat(
                    owl_concat(owl_hpke_v1().as_slice(), owl_suite_id().as_slice()).as_slice(),
                    owl_lbl402.as_slice(),
                ).as_slice(),
                owl_ikm403.as_slice(),
            ).as_slice(),
        ),
    )
}

pub fn owl_dh_secret_kdf_ikm<'a>(owl_psk_404: OwlBuf<'_>) -> (res: OwlBuf<'a>)
    requires
        owl_psk_404.len_valid(),
    ensures
        res.view() == dh_secret_kdf_ikm(owl_psk_404.view()),
        res.len_valid(),
{
    reveal(dh_secret_kdf_ikm);
    OwlBuf::another_ref(
        &owl_lbl_ikm(OwlBuf::another_ref(&owl_secret_string()), OwlBuf::another_ref(&owl_psk_404)),
    )
}

pub fn owl_eae_prk<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == eae_prk(),
        res.len_valid(),
{
    reveal(eae_prk);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x65u8, 0x61u8, 0x65u8, 0x5fu8, 0x70u8, 0x72u8, 0x6bu8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_enckey_len<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == enckey_len(),
        res.len_valid(),
{
    reveal(enckey_len);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x00u8, 0x20u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_export_kdf_info<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == export_kdf_info(),
        res.len_valid(),
{
    reveal(export_kdf_info);
    OwlBuf::another_ref(
        &owl_lbl_info(
            OwlBuf::another_ref(&owl_enckey_len()),
            OwlBuf::another_ref(&owl_export_string()),
            OwlBuf::another_ref(&owl_key_schedule_context()),
        ),
    )
}

pub fn owl_export_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == export_string(),
        res.len_valid(),
{
    reveal(export_string);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x65u8, 0x78u8, 0x70u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_hpke_v1<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == hpke_v1(),
        res.len_valid(),
{
    reveal(hpke_v1);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x48u8, 0x50u8, 0x4bu8, 0x45u8, 0x2du8, 0x76u8, 0x31u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_info<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == info(),
        res.len_valid(),
{
    reveal(info);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_info_hash_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == info_hash_string(),
        res.len_valid(),
{
    reveal(info_hash_string);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x69u8, 0x6eu8, 0x66u8, 0x6fu8, 0x5fu8, 0x68u8, 0x61u8, 0x73u8, 0x68u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_kdfkey_len<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == kdfkey_len(),
        res.len_valid(),
{
    reveal(kdfkey_len);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x00u8, 0x20u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_key_kdf_info<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == key_kdf_info(),
        res.len_valid(),
{
    reveal(key_kdf_info);
    OwlBuf::another_ref(
        &owl_lbl_info(
            OwlBuf::another_ref(&owl_enckey_len()),
            OwlBuf::another_ref(&owl_key_string()),
            OwlBuf::another_ref(&owl_key_schedule_context()),
        ),
    )
}

pub fn owl_key_schedule_context<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == key_schedule_context(),
        res.len_valid(),
{
    reveal(key_schedule_context);
    OwlBuf::from_vec(
        owl_concat(
            owl_concat(
                owl_mode().as_slice(),
                owl_crh_labeled_extract_0salt(
                    OwlBuf::another_ref(&owl_info_hash_string()),
                    OwlBuf::another_ref(&owl_info()),
                ).as_slice(),
            ).as_slice(),
            owl_crh_labeled_extract_0salt(
                OwlBuf::another_ref(&owl_psk_id_hash_string()),
                OwlBuf::another_ref(&owl_psk_id()),
            ).as_slice(),
        ),
    )
}

pub fn owl_key_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == key_string(),
        res.len_valid(),
{
    reveal(key_string);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x6bu8, 0x65u8, 0x79u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_lbl_ikm<'a>(owl_lbl405: OwlBuf<'_>, owl_ikm406: OwlBuf<'_>) -> (res: OwlBuf<'a>)
    requires
        owl_lbl405.len_valid(),
        owl_ikm406.len_valid(),
    ensures
        res.view() == lbl_ikm(owl_lbl405.view(), owl_ikm406.view()),
        res.len_valid(),
{
    reveal(lbl_ikm);
    OwlBuf::from_vec(
        owl_concat(
            owl_concat(
                owl_concat(owl_hpke_v1().as_slice(), owl_suite_id().as_slice()).as_slice(),
                owl_lbl405.as_slice(),
            ).as_slice(),
            owl_ikm406.as_slice(),
        ),
    )
}

pub fn owl_lbl_info<'a>(
    owl_len407: OwlBuf<'_>,
    owl_lbl408: OwlBuf<'_>,
    owl_info409: OwlBuf<'_>,
) -> (res: OwlBuf<'a>)
    requires
        owl_len407.len_valid(),
        owl_lbl408.len_valid(),
        owl_info409.len_valid(),
    ensures
        res.view() == lbl_info(owl_len407.view(), owl_lbl408.view(), owl_info409.view()),
        res.len_valid(),
{
    reveal(lbl_info);
    OwlBuf::from_vec(
        owl_concat(
            owl_concat(
                owl_concat(
                    owl_concat(owl_len407.as_slice(), owl_hpke_v1().as_slice()).as_slice(),
                    owl_suite_id().as_slice(),
                ).as_slice(),
                owl_lbl408.as_slice(),
            ).as_slice(),
            owl_info409.as_slice(),
        ),
    )
}

pub fn owl_mode<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == mode(),
        res.len_valid(),
{
    reveal(mode);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x03u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_psk_id<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == psk_id(),
        res.len_valid(),
{
    reveal(psk_id);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_psk_id_hash_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == psk_id_hash_string(),
        res.len_valid(),
{
    reveal(psk_id_hash_string);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x70u8, 0x73u8, 0x6bu8, 0x5fu8, 0x69u8, 0x64u8, 0x5fu8, 0x68u8, 0x61u8, 0x73u8, 0x68u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == secret_string(),
        res.len_valid(),
{
    reveal(secret_string);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x73u8, 0x65u8, 0x63u8, 0x72u8, 0x65u8, 0x74u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_shared_secret_string<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == shared_secret_string(),
        res.len_valid(),
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

pub fn owl_suite_id<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == suite_id(),
        res.len_valid(),
{
    reveal(suite_id);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x48u8, 0x50u8, 0x4bu8, 0x45u8, 0x00u8, 0x20u8, 0x00u8, 0x01u8, 0x00u8, 0x03u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

// ------------------------------------
// ------------ ENTRY POINT -----------
// ------------------------------------
/* no entry point */
} // verus!


