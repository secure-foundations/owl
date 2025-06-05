// Extracted verus code from file echo_server_example/echo_server_example.owl:
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
pub mod server;
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
spec const SPEC_BYTES_CONST_01_ENCMSG: [u8; 1] = [0x01u8];

exec const EXEC_BYTES_CONST_01_ENCMSG: [u8; 1]
    ensures
        EXEC_BYTES_CONST_01_ENCMSG == SPEC_BYTES_CONST_01_ENCMSG,
{
    let arr: [u8; 1] = [0x01u8];
    assert(arr == SPEC_BYTES_CONST_01_ENCMSG);
    arr
}

spec fn spec_combinator_owlSpec_EncMsg() -> (OwlConstBytes<1>, Tail) {
    let field_1 = OwlConstBytes::<1>(SPEC_BYTES_CONST_01_ENCMSG);
    let field_2 = Tail;
    (field_1, field_2)
}

exec fn exec_combinator_owl_EncMsg() -> (res: (OwlConstBytes<1>, Tail))
    ensures
        res.view() == spec_combinator_owlSpec_EncMsg(),
{
    let field_1 = OwlConstBytes::<1>(EXEC_BYTES_CONST_01_ENCMSG);
    let field_2 = Tail;
    (field_1, field_2)
}

pub struct owlSpec_EncMsg {
    pub owlSpec_version_num: (),
    pub owlSpec_cipher: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_EncMsg(x: Seq<u8>) -> Option<owlSpec_EncMsg> {
    let spec_comb = spec_combinator_owlSpec_EncMsg();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((owlSpec_version_num, owlSpec_cipher)) = parsed;
        Some(owlSpec_EncMsg { owlSpec_version_num, owlSpec_cipher })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_EncMsg_inner(x: owlSpec_EncMsg) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ 1, x.owlSpec_cipher.len() ] {
        let spec_comb = spec_combinator_owlSpec_EncMsg();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((x.owlSpec_version_num, x.owlSpec_cipher)),
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
pub closed spec fn serialize_owlSpec_EncMsg(x: owlSpec_EncMsg) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_EncMsg_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_EncMsg {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_EncMsg(self)
    }
}

pub open spec fn EncMsg(
    arg_owlSpec_version_num: (),
    arg_owlSpec_cipher: Seq<u8>,
) -> owlSpec_EncMsg {
    owlSpec_EncMsg {
        owlSpec_version_num: arg_owlSpec_version_num,
        owlSpec_cipher: arg_owlSpec_cipher,
    }
}

pub enum owlSpec_ServerResult {
    owlSpec_SRErr(),
    owlSpec_SROk(Seq<u8>),
}

use owlSpec_ServerResult::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_ServerResult(x: Seq<u8>) -> Option<owlSpec_ServerResult> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(12)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owlSpec_ServerResult::owlSpec_SRErr(),
            inj_ord_choice_pat!(*, (_,x)) => owlSpec_ServerResult::owlSpec_SROk(x),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_ServerResult_inner(x: owlSpec_ServerResult) -> Option<
    Seq<u8>,
> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Variable(0)), (Tag::spec_new(U8, 2), Variable(12)));
    match x {
        owlSpec_ServerResult::owlSpec_SRErr() => {
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
        owlSpec_ServerResult::owlSpec_SROk(x) => {
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
pub closed spec fn serialize_owlSpec_ServerResult(x: owlSpec_ServerResult) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_ServerResult_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_ServerResult {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_ServerResult(self)
    }
}

pub open spec fn SRErr() -> owlSpec_ServerResult {
    crate::owlSpec_ServerResult::owlSpec_SRErr()
}

pub open spec fn SROk(x: Seq<u8>) -> owlSpec_ServerResult {
    crate::owlSpec_ServerResult::owlSpec_SROk(x)
}

pub open spec fn SRErr_enumtest(x: owlSpec_ServerResult) -> bool {
    match x {
        owlSpec_ServerResult::owlSpec_SRErr() => true,
        _ => false,
    }
}

pub open spec fn SROk_enumtest(x: owlSpec_ServerResult) -> bool {
    match x {
        owlSpec_ServerResult::owlSpec_SROk(_) => true,
        _ => false,
    }
}

#[verifier::opaque]
pub open spec fn server_send_spec(cfg: cfg_Server, mut_state: state_Server, m: Seq<u8>) -> (res:
    ITree<((), state_Server), Endpoint>) {
    owl_spec!(mut_state, state_Server,
        let send_key = ((ret(cfg.owl_kS2C.view()))) in
        let enc_msg = ((sample(NONCE_SIZE, enc(send_key, m)))) in
        let msg = ((ret(EncMsg((), enc_msg)))) in
        (output (serialize_owlSpec_EncMsg(msg)) to (Some(Endpoint::Loc_Client)))
    )
}

#[verifier::opaque]
pub open spec fn server_recv_spec(cfg: cfg_Server, mut_state: state_Server) -> (res: ITree<
    (owlSpec_ServerResult, state_Server),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Server,
        (input(p,_10)) in
        (parse (parse_owlSpec_EncMsg(p)) as (owlSpec_EncMsg{owlSpec_version_num : _unused23, owlSpec_cipher : ctxt}) in {
            let recv_key = ((ret(cfg.owl_kC2S.view()))) in
            let caseval = ((declassify(DeclassifyingOp::ADec(recv_key, ctxt))) in
                           (ret(dec(recv_key, ctxt)))) in
            (case (caseval) {
                | Some(ptxt) => {
                    (ret(SROk(ptxt)))
                },
                | None => {
                    (ret(SRErr()))
                },
            })
        } otherwise ((ret(SRErr())))
    ))
}

// ------------------------------------
// ---------- IMPLEMENTATIONS ---------
// ------------------------------------
#[derive(Clone,Copy)]
pub enum Endpoint {
    Loc_Client,
    Loc_Server,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier(external_body)]
pub const fn Client_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_Client,
{
    "127.0.0.1:9001"
}

#[verifier(external_body)]
pub const fn Server_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_Server,
{
    "127.0.0.1:9002"
}

pub struct owl_EncMsg<'a> {
    pub owl_version_num: (),
    pub owl_cipher: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_EncMsg<'a>(arg_owl_version_num: (), arg_owl_cipher: OwlBuf<'a>) -> (res: owl_EncMsg<'a>)
    ensures
        res.owl_version_num.view() == arg_owl_version_num.view(),
        res.owl_cipher.view() == arg_owl_cipher.view(),
{
    owl_EncMsg { owl_version_num: arg_owl_version_num, owl_cipher: arg_owl_cipher }
}

impl<'a> owl_EncMsg<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_EncMsg<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_EncMsg {
            owl_version_num: self.owl_version_num,
            owl_cipher: OwlBuf::another_ref(&self.owl_cipher),
        }
    }
}

impl View for owl_EncMsg<'_> {
    type V = owlSpec_EncMsg;

    open spec fn view(&self) -> owlSpec_EncMsg {
        owlSpec_EncMsg {
            owlSpec_version_num: self.owl_version_num.view(),
            owlSpec_cipher: self.owl_cipher.view(),
        }
    }
}

pub exec fn parse_owl_EncMsg<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_EncMsg<'a>>)
    ensures
        res is Some ==> parse_owlSpec_EncMsg(arg.view()) is Some,
        res is None ==> parse_owlSpec_EncMsg(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_EncMsg(arg.view())->Some_0,
{
    reveal(parse_owlSpec_EncMsg);
    let exec_comb = exec_combinator_owl_EncMsg();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (owl_version_num, owl_cipher) = parsed;
        Some(
            owl_EncMsg {
                owl_version_num: owl_version_num,
                owl_cipher: OwlBuf::another_ref(&owl_cipher),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_EncMsg_inner<'a>(arg: &owl_EncMsg<'a>) -> (res: Option<OwlBuf<'a>>)
    ensures
        res is Some ==> serialize_owlSpec_EncMsg_inner(arg.view()) is Some,
        res matches Some(x) ==> x.view() == serialize_owlSpec_EncMsg_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_EncMsg_inner);
    if no_usize_overflows![ 1, arg.owl_cipher.len(), 0 ] {
        let exec_comb = exec_combinator_owl_EncMsg();
        let mut obuf = vec_u8_of_len(1 + arg.owl_cipher.len() + 0);
        let ser_result = exec_comb.serialize(
            (arg.owl_version_num, OwlBuf::another_ref(&arg.owl_cipher)),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_EncMsg_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_EncMsg<'a>(arg: &owl_EncMsg<'a>) -> (res: OwlBuf<'a>)
    ensures
        res.view() == serialize_owlSpec_EncMsg(arg.view()),
{
    reveal(serialize_owlSpec_EncMsg);
    let res = serialize_owl_EncMsg_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub enum owl_ServerResult<'a> {
    owl_SRErr(),
    owl_SROk(SecretBuf<'a>),
}

use owl_ServerResult::*;

impl<'a> owl_ServerResult<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_ServerResult<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_SRErr() => owl_SRErr(),
            owl_SROk(x) => owl_SROk(SecretBuf::another_ref(x)),
        }
    }
}

impl View for owl_ServerResult<'_> {
    type V = owlSpec_ServerResult;

    open spec fn view(&self) -> owlSpec_ServerResult {
        match self {
            owl_SRErr() => owlSpec_ServerResult::owlSpec_SRErr(),
            owl_SROk(v) => owlSpec_ServerResult::owlSpec_SROk(v.view()),
        }
    }
}

#[inline]
pub fn owl_SRErr_enumtest(x: &owl_ServerResult<'_>) -> (res: bool)
    ensures
        res == SRErr_enumtest(x.view()),
{
    match x {
        owl_ServerResult::owl_SRErr() => true,
        _ => false,
    }
}

#[inline]
pub fn owl_SROk_enumtest(x: &owl_ServerResult<'_>) -> (res: bool)
    ensures
        res == SROk_enumtest(x.view()),
{
    match x {
        owl_ServerResult::owl_SROk(_) => true,
        _ => false,
    }
}

pub exec fn parse_owl_ServerResult<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_ServerResult<'a>>)
    ensures
        res is Some ==> parse_owlSpec_ServerResult(arg.view()) is Some,
        res is None ==> parse_owlSpec_ServerResult(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_ServerResult(arg.view())->Some_0,
{
    reveal(parse_owlSpec_ServerResult);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Variable(0)), (Tag::new(U8, 2), Variable(12)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!(_, *) => owl_ServerResult::owl_SRErr(),
            inj_ord_choice_pat!(*, (_,x)) => owl_ServerResult::owl_SROk(
                SecretBuf::from_buf(x.another_ref()),
            ),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn secret_parse_owl_ServerResult<'a>(
    arg: SecretBuf<'a>,
    Tracked(t): Tracked<DeclassifyingOpToken>,
) -> (res: Option<owl_ServerResult<'a>>)
    requires
        t.view() matches DeclassifyingOp::EnumParse(b) && b == arg.view(),
    ensures
        res is Some ==> parse_owlSpec_ServerResult(arg.view()) is Some,
        res is None ==> parse_owlSpec_ServerResult(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_ServerResult(arg.view())->Some_0,
{
    reveal(parse_owlSpec_ServerResult);
    unimplemented!()
}

#[verifier(external_body)]
pub exec fn serialize_owl_ServerResult_inner(arg: &owl_ServerResult) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_ServerResult_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_ServerResult_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_ServerResult_inner(
            arg.view(),
        )->Some_0,
{
    unimplemented!()
}

#[inline]
pub exec fn serialize_owl_ServerResult(arg: &owl_ServerResult) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_ServerResult(arg.view()),
{
    reveal(serialize_owlSpec_ServerResult);
    let res = serialize_owl_ServerResult_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct state_Client {}

impl state_Client {
    #[verifier::external_body]
    pub fn init_state_Client() -> Self {
        state_Client {  }
    }
}

pub struct cfg_Client<'Client> {
    pub salt: Vec<u8>,
    pub owl_message: SecretBuf<'Client>,
    pub owl_kS2C: SecretBuf<'Client>,
    pub owl_kC2S: SecretBuf<'Client>,
}

impl cfg_Client<'_> {

}

pub struct state_Server {}

impl state_Server {
    #[verifier::external_body]
    pub fn init_state_Server() -> Self {
        state_Server {  }
    }
}

pub struct cfg_Server<'Server> {
    pub salt: Vec<u8>,
    pub owl_kS2C: SecretBuf<'Server>,
    pub owl_kC2S: SecretBuf<'Server>,
}

impl cfg_Server<'_> {
    #[verifier::spinoff_prover]
    pub fn owl_server_send<E: OwlEffects>(
        &self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<((), state_Server), Endpoint>>,
        mut_state: &mut state_Server,
        owl_m40: SecretBuf<'_>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Server), Endpoint>>), OwlError>)
        requires
            itree.view() == server_send_spec(*self, *old(mut_state), owl_m40.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_Server), Endpoint>>) = {
            broadcast use itree_axioms;

            reveal(server_send_spec);
            let tmp_owl_send_key27 = { SecretBuf::another_ref(&self.owl_kS2C) };
            let owl_send_key27 = SecretBuf::another_ref(&tmp_owl_send_key27);
            let tmp_owl_enc_msg28 = {
                let tmp_owl_coins29 = effects.owl_sample::<((), state_Server)>(
                    Tracked(&mut itree),
                    NONCE_SIZE,
                );
                let owl_coins29 = SecretBuf::another_ref(&tmp_owl_coins29);
                owl_enc(
                    SecretBuf::another_ref(&owl_send_key27),
                    SecretBuf::another_ref(&owl_m40),
                    SecretBuf::another_ref(&owl_coins29),
                )
            };
            let owl_enc_msg28 = OwlBuf::from_vec(tmp_owl_enc_msg28);
            let tmp_owl_msg30 = { owl_EncMsg((), OwlBuf::another_ref(&owl_enc_msg28)) };
            let owl_msg30 = owl_EncMsg::another_ref(&tmp_owl_msg30);
            effects.owl_output::<((), state_Server)>(
                Tracked(&mut itree),
                serialize_owl_EncMsg(&owl_msg30).as_slice(),
                Some(&Client_addr()),
                &Server_addr(),
            );
            ((), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_server_recv<'a, E: OwlEffects>(
        &'a self,
        effects: &mut E,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_ServerResult, state_Server), Endpoint>>,
        mut_state: &mut state_Server,
    ) -> (res: Result<
        (owl_ServerResult<'a>, Tracked<ITreeToken<(owlSpec_ServerResult, state_Server), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == server_recv_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_ServerResult<'a>,
            Tracked<ITreeToken<(owlSpec_ServerResult, state_Server), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(server_recv_spec);
            let (tmp_owl_p32, owl__31) = {
                effects.owl_input::<(owlSpec_ServerResult, state_Server)>(Tracked(&mut itree))
            };
            let owl_p32 = OwlBuf::from_vec(tmp_owl_p32);
            let parseval_tmp = OwlBuf::another_ref(&owl_p32);
            if let Some(parseval) = parse_owl_EncMsg(OwlBuf::another_ref(&parseval_tmp)) {
                let owl__34 = parseval.owl_version_num;
                let owl_ctxt33 = OwlBuf::another_ref(&parseval.owl_cipher);
                {
                    let tmp_owl_recv_key35 = { SecretBuf::another_ref(&self.owl_kC2S) };
                    let owl_recv_key35 = SecretBuf::another_ref(&tmp_owl_recv_key35);
                    let tmp_owl_caseval36 = {
                        let tracked owl_declassify_tok37 = consume_itree_declassify::<
                            (owlSpec_ServerResult, state_Server),
                            Endpoint,
                        >(&mut itree);
                        owl_dec(
                            SecretBuf::another_ref(&owl_recv_key35),
                            OwlBuf::another_ref(&owl_ctxt33),
                            Tracked(owl_declassify_tok37),
                        )
                    };
                    let owl_caseval36 = SecretBuf::another_ref_option(&tmp_owl_caseval36);
                    match SecretBuf::another_ref_option(&owl_caseval36) {
                        Option::Some(tmp_owl_ptxt38) => {
                            let owl_ptxt38 = SecretBuf::another_ref(&tmp_owl_ptxt38);
                            (
                                owl_ServerResult::another_ref(
                                    &owl_SROk(SecretBuf::another_ref(&owl_ptxt38)),
                                ),
                                Tracked(itree),
                            )
                        },
                        Option::None => {
                            (owl_ServerResult::another_ref(&owl_SRErr()), Tracked(itree))
                        },
                    }
                }
            } else {
                (owl_ServerResult::another_ref(&owl_SRErr()), Tracked(itree))
            }
        };
        Ok((owl_ServerResult::another_ref(&res_inner), Tracked(itree)))
    }
}

// ------------------------------------
// ------------ ENTRY POINT -----------
// ------------------------------------
} // verus!
