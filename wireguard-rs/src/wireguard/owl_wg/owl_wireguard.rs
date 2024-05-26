// Extracted verus code from file tests/wip/wg/transp.owl:
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]




pub use vstd::{modes::*, prelude::*, seq::*, string::*};
pub use crate::wireguard::owl_wg::speclib::{*, itree::*};
pub use crate::wireguard::owl_wg::execlib::{*};
pub use crate::wireguard::owl_wg::*;
use crate::wireguard::handshake::device::Device;

pub use parsley::{
    regular::builder::*,
    properties::*, regular::bytes::*, regular::bytes_const::*, regular::choice::*,
    regular::tail::*, regular::uints::*, regular::*, utils::*, *,
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

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct TcpListenerWrapper(std::net::TcpListener);

#[verifier(external_type_specification)]
pub struct OwlErrorWrapper(OwlError);

#[verifier(external_body)]
pub fn owl_output<A>(
    Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
    x: &[u8],
    dest_addr: &StrSlice,
    ret_addr: &StrSlice,
    obuf: &mut [u8]
)
    requires
        old(t).view().is_output(x.view(), endpoint_of_addr(dest_addr.view())),
    ensures
        t.view() == old(t).view().give_output(),
{
    // todo!()
    // dbg!(x.len());
    // dbg!(obuf.len());
    // let len = std::cmp::min(x.len(), obuf.len());
    // dbg!(len);
    obuf[..x.len()].copy_from_slice(x);
}

#[verifier(external_body)]
pub fn owl_input<A, 'a>(
    Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
    ibuf: &'a [u8]
) -> (ie: (&'a [u8], String))
    requires
        old(t).view().is_input(),
    ensures
        t.view() == old(t).view().take_input(ie.0.view(), endpoint_of_addr(ie.1.view())),
{
    (ibuf, String::from_rust_string("".to_string())) // Specific to Wireguard---we never use the endpoints
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
pub enum owlSpec_PSKMode {
    owlSpec_HasPSK((Seq<u8>)),
    owlSpec_NoPSK(),
}

use owlSpec_PSKMode::*;

#[verifier::external_body]
pub closed spec fn parse_owlSpec_PSKMode(x: Seq<u8>) -> Option<owlSpec_PSKMode> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_PSKMode_inner(x: owlSpec_PSKMode) -> Option<Seq<u8>> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_PSKMode(x: owlSpec_PSKMode) -> Seq<u8> {
    todo!()
}

impl OwlSpecSerialize for owlSpec_PSKMode {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_PSKMode(self)
    }
}

pub open spec fn HasPSK(x: (Seq<u8>)) -> owlSpec_PSKMode {
    crate::owlSpec_PSKMode::owlSpec_HasPSK(x)
}

pub open spec fn NoPSK() -> owlSpec_PSKMode {
    crate::owlSpec_PSKMode::owlSpec_NoPSK()
}

pub open spec fn HasPSK_enumtest(x: owlSpec_PSKMode) -> bool {
    match x {
        owlSpec_PSKMode::owlSpec_HasPSK(_) => true,
        _ => false,
    }
}

pub open spec fn NoPSK_enumtest(x: owlSpec_PSKMode) -> bool {
    match x {
        owlSpec_PSKMode::owlSpec_NoPSK() => true,
        _ => false,
    }
}

spec const SPEC_BYTES_CONST_01000000_MSG1: Seq<u8> = seq![0x01u8, 0x00u8, 0x00u8, 0x00u8, ];

spec const SPEC_BYTES_CONST_00000000000000000000000000000000_MSG1: Seq<u8> =
    seq![0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, ];

exec const EXEC_BYTES_CONST_01000000_MSG1: [u8; 4]
    ensures
        EXEC_BYTES_CONST_01000000_MSG1.view() == SPEC_BYTES_CONST_01000000_MSG1,
{
    let arr: [u8; 4] = [0x01u8, 0x00u8, 0x00u8, 0x00u8];
    assert(arr.view() == SPEC_BYTES_CONST_01000000_MSG1);
    arr
}

exec const EXEC_BYTES_CONST_00000000000000000000000000000000_MSG1: [u8; 16]
    ensures
        EXEC_BYTES_CONST_00000000000000000000000000000000_MSG1.view()
            == SPEC_BYTES_CONST_00000000000000000000000000000000_MSG1,
{
    let arr: [u8; 16] = [
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
    ];
    assert(arr.view() == SPEC_BYTES_CONST_00000000000000000000000000000000_MSG1);
    arr
}

spec fn spec_combinator_owlSpec_msg1() -> (
    (((((SpecConstBytes, Bytes), Bytes), Bytes), Bytes), Bytes),
    SpecConstBytes,
) {
    let field_1 = SpecConstBytes(SPEC_BYTES_CONST_01000000_MSG1);
    let field_2 = Bytes(4);
    let field_3 = Bytes(32);
    let field_4 = Bytes(48);
    let field_5 = Bytes(28);
    let field_6 = Bytes(16);
    let field_7 = SpecConstBytes(SPEC_BYTES_CONST_00000000000000000000000000000000_MSG1);
    ((((((field_1, field_2), field_3), field_4), field_5), field_6), field_7)
}

exec fn exec_combinator_owl_msg1() -> (res: (
    (((((ConstBytes<4>, Bytes), Bytes), Bytes), Bytes), Bytes),
    ConstBytes<16>,
))
    ensures
        res.view() == spec_combinator_owlSpec_msg1(),
{
    let field_1 = ConstBytes(EXEC_BYTES_CONST_01000000_MSG1);
    let field_2 = Bytes(4);
    let field_3 = Bytes(32);
    let field_4 = Bytes(48);
    let field_5 = Bytes(28);
    let field_6 = Bytes(16);
    let field_7 = ConstBytes(EXEC_BYTES_CONST_00000000000000000000000000000000_MSG1);
    ((((((field_1, field_2), field_3), field_4), field_5), field_6), field_7)
}

pub struct owlSpec_msg1 {
    pub owlSpec__msg1_tag: (),
    pub owlSpec__msg1_sender: Seq<u8>,
    pub owlSpec__msg1_ephemeral: Seq<u8>,
    pub owlSpec__msg1_static: Seq<u8>,
    pub owlSpec__msg1_timestamp: Seq<u8>,
    pub owlSpec__msg1_mac1: Seq<u8>,
    pub owlSpec__msg1_mac2: (),
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_msg1(x: Seq<u8>) -> Option<owlSpec_msg1> {
    let spec_comb = spec_combinator_owlSpec_msg1();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((
            (
                (
                    (
                        ((owlSpec__msg1_tag, owlSpec__msg1_sender), owlSpec__msg1_ephemeral),
                        owlSpec__msg1_static,
                    ),
                    owlSpec__msg1_timestamp,
                ),
                owlSpec__msg1_mac1,
            ),
            owlSpec__msg1_mac2,
        )) = parsed;
        Some(
            owlSpec_msg1 {
                owlSpec__msg1_tag,
                owlSpec__msg1_sender,
                owlSpec__msg1_ephemeral,
                owlSpec__msg1_static,
                owlSpec__msg1_timestamp,
                owlSpec__msg1_mac1,
                owlSpec__msg1_mac2,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_msg1_inner(x: owlSpec_msg1) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ 4, x.owlSpec__msg1_sender.len(), x.owlSpec__msg1_ephemeral.len(), x.owlSpec__msg1_static.len(), x.owlSpec__msg1_timestamp.len(), x.owlSpec__msg1_mac1.len(), 16 ] {
        let spec_comb = spec_combinator_owlSpec_msg1();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((
                (
                    (
                        (
                            (
                                (x.owlSpec__msg1_tag, x.owlSpec__msg1_sender),
                                x.owlSpec__msg1_ephemeral,
                            ),
                            x.owlSpec__msg1_static,
                        ),
                        x.owlSpec__msg1_timestamp,
                    ),
                    x.owlSpec__msg1_mac1,
                ),
                x.owlSpec__msg1_mac2,
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
pub closed spec fn serialize_owlSpec_msg1(x: owlSpec_msg1) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_msg1_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_msg1 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg1(self)
    }
}

pub open spec fn msg1(
    arg_owlSpec__msg1_tag: (),
    arg_owlSpec__msg1_sender: Seq<u8>,
    arg_owlSpec__msg1_ephemeral: Seq<u8>,
    arg_owlSpec__msg1_static: Seq<u8>,
    arg_owlSpec__msg1_timestamp: Seq<u8>,
    arg_owlSpec__msg1_mac1: Seq<u8>,
    arg_owlSpec__msg1_mac2: (),
) -> owlSpec_msg1 {
    owlSpec_msg1 {
        owlSpec__msg1_tag: arg_owlSpec__msg1_tag,
        owlSpec__msg1_sender: arg_owlSpec__msg1_sender,
        owlSpec__msg1_ephemeral: arg_owlSpec__msg1_ephemeral,
        owlSpec__msg1_static: arg_owlSpec__msg1_static,
        owlSpec__msg1_timestamp: arg_owlSpec__msg1_timestamp,
        owlSpec__msg1_mac1: arg_owlSpec__msg1_mac1,
        owlSpec__msg1_mac2: arg_owlSpec__msg1_mac2,
    }
}

spec const SPEC_BYTES_CONST_02000000_MSG2: Seq<u8> = seq![0x02u8, 0x00u8, 0x00u8, 0x00u8, ];

spec const SPEC_BYTES_CONST_00000000000000000000000000000000_MSG2: Seq<u8> =
    seq![0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, ];

exec const EXEC_BYTES_CONST_02000000_MSG2: [u8; 4]
    ensures
        EXEC_BYTES_CONST_02000000_MSG2.view() == SPEC_BYTES_CONST_02000000_MSG2,
{
    let arr: [u8; 4] = [0x02u8, 0x00u8, 0x00u8, 0x00u8];
    assert(arr.view() == SPEC_BYTES_CONST_02000000_MSG2);
    arr
}

exec const EXEC_BYTES_CONST_00000000000000000000000000000000_MSG2: [u8; 16]
    ensures
        EXEC_BYTES_CONST_00000000000000000000000000000000_MSG2.view()
            == SPEC_BYTES_CONST_00000000000000000000000000000000_MSG2,
{
    let arr: [u8; 16] = [
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
        0x00u8,
    ];
    assert(arr.view() == SPEC_BYTES_CONST_00000000000000000000000000000000_MSG2);
    arr
}

spec fn spec_combinator_owlSpec_msg2() -> (
    (((((SpecConstBytes, Bytes), Bytes), Bytes), Bytes), Bytes),
    SpecConstBytes,
) {
    let field_1 = SpecConstBytes(SPEC_BYTES_CONST_02000000_MSG2);
    let field_2 = Bytes(4);
    let field_3 = Bytes(4);
    let field_4 = Bytes(32);
    let field_5 = Bytes(16);
    let field_6 = Bytes(16);
    let field_7 = SpecConstBytes(SPEC_BYTES_CONST_00000000000000000000000000000000_MSG2);
    ((((((field_1, field_2), field_3), field_4), field_5), field_6), field_7)
}

exec fn exec_combinator_owl_msg2() -> (res: (
    (((((ConstBytes<4>, Bytes), Bytes), Bytes), Bytes), Bytes),
    ConstBytes<16>,
))
    ensures
        res.view() == spec_combinator_owlSpec_msg2(),
{
    let field_1 = ConstBytes(EXEC_BYTES_CONST_02000000_MSG2);
    let field_2 = Bytes(4);
    let field_3 = Bytes(4);
    let field_4 = Bytes(32);
    let field_5 = Bytes(16);
    let field_6 = Bytes(16);
    let field_7 = ConstBytes(EXEC_BYTES_CONST_00000000000000000000000000000000_MSG2);
    ((((((field_1, field_2), field_3), field_4), field_5), field_6), field_7)
}

pub struct owlSpec_msg2 {
    pub owlSpec__msg2_tag: (),
    pub owlSpec__msg2_sender: Seq<u8>,
    pub owlSpec__msg2_receiver: Seq<u8>,
    pub owlSpec__msg2_ephemeral: Seq<u8>,
    pub owlSpec__msg2_empty: Seq<u8>,
    pub owlSpec__msg2_mac1: Seq<u8>,
    pub owlSpec__msg2_mac2: (),
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_msg2(x: Seq<u8>) -> Option<owlSpec_msg2> {
    let spec_comb = spec_combinator_owlSpec_msg2();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((
            (
                (
                    (
                        ((owlSpec__msg2_tag, owlSpec__msg2_sender), owlSpec__msg2_receiver),
                        owlSpec__msg2_ephemeral,
                    ),
                    owlSpec__msg2_empty,
                ),
                owlSpec__msg2_mac1,
            ),
            owlSpec__msg2_mac2,
        )) = parsed;
        Some(
            owlSpec_msg2 {
                owlSpec__msg2_tag,
                owlSpec__msg2_sender,
                owlSpec__msg2_receiver,
                owlSpec__msg2_ephemeral,
                owlSpec__msg2_empty,
                owlSpec__msg2_mac1,
                owlSpec__msg2_mac2,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_msg2_inner(x: owlSpec_msg2) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ 4, x.owlSpec__msg2_sender.len(), x.owlSpec__msg2_receiver.len(), x.owlSpec__msg2_ephemeral.len(), x.owlSpec__msg2_empty.len(), x.owlSpec__msg2_mac1.len(), 16 ] {
        let spec_comb = spec_combinator_owlSpec_msg2();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((
                (
                    (
                        (
                            (
                                (x.owlSpec__msg2_tag, x.owlSpec__msg2_sender),
                                x.owlSpec__msg2_receiver,
                            ),
                            x.owlSpec__msg2_ephemeral,
                        ),
                        x.owlSpec__msg2_empty,
                    ),
                    x.owlSpec__msg2_mac1,
                ),
                x.owlSpec__msg2_mac2,
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
pub closed spec fn serialize_owlSpec_msg2(x: owlSpec_msg2) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_msg2_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_msg2 {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_msg2(self)
    }
}

pub open spec fn msg2(
    arg_owlSpec__msg2_tag: (),
    arg_owlSpec__msg2_sender: Seq<u8>,
    arg_owlSpec__msg2_receiver: Seq<u8>,
    arg_owlSpec__msg2_ephemeral: Seq<u8>,
    arg_owlSpec__msg2_empty: Seq<u8>,
    arg_owlSpec__msg2_mac1: Seq<u8>,
    arg_owlSpec__msg2_mac2: (),
) -> owlSpec_msg2 {
    owlSpec_msg2 {
        owlSpec__msg2_tag: arg_owlSpec__msg2_tag,
        owlSpec__msg2_sender: arg_owlSpec__msg2_sender,
        owlSpec__msg2_receiver: arg_owlSpec__msg2_receiver,
        owlSpec__msg2_ephemeral: arg_owlSpec__msg2_ephemeral,
        owlSpec__msg2_empty: arg_owlSpec__msg2_empty,
        owlSpec__msg2_mac1: arg_owlSpec__msg2_mac1,
        owlSpec__msg2_mac2: arg_owlSpec__msg2_mac2,
    }
}

spec const SPEC_BYTES_CONST_04000000_TRANSP: Seq<u8> = seq![0x04u8, 0x00u8, 0x00u8, 0x00u8, ];

exec const EXEC_BYTES_CONST_04000000_TRANSP: [u8; 4]
    ensures
        EXEC_BYTES_CONST_04000000_TRANSP.view() == SPEC_BYTES_CONST_04000000_TRANSP,
{
    let arr: [u8; 4] = [0x04u8, 0x00u8, 0x00u8, 0x00u8];
    assert(arr.view() == SPEC_BYTES_CONST_04000000_TRANSP);
    arr
}

spec fn spec_combinator_owlSpec_transp() -> (((SpecConstBytes, Bytes), Bytes), Tail) {
    let field_1 = SpecConstBytes(SPEC_BYTES_CONST_04000000_TRANSP);
    let field_2 = Bytes(4);
    let field_3 = Bytes(8);
    let field_4 = Tail;
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_transp() -> (res: (((ConstBytes<4>, Bytes), Bytes), Tail))
    ensures
        res.view() == spec_combinator_owlSpec_transp(),
{
    let field_1 = ConstBytes(EXEC_BYTES_CONST_04000000_TRANSP);
    let field_2 = Bytes(4);
    let field_3 = Bytes(8);
    let field_4 = Tail;
    (((field_1, field_2), field_3), field_4)
}

pub struct owlSpec_transp {
    pub owlSpec__transp_tag: (),
    pub owlSpec__transp_receiver: Seq<u8>,
    pub owlSpec__transp_counter: Seq<u8>,
    pub owlSpec__transp_packet: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_transp(x: Seq<u8>) -> Option<owlSpec_transp> {
    let spec_comb = spec_combinator_owlSpec_transp();
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let ((
            ((owlSpec__transp_tag, owlSpec__transp_receiver), owlSpec__transp_counter),
            owlSpec__transp_packet,
        )) = parsed;
        Some(
            owlSpec_transp {
                owlSpec__transp_tag,
                owlSpec__transp_receiver,
                owlSpec__transp_counter,
                owlSpec__transp_packet,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_transp_inner(x: owlSpec_transp) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ 4, x.owlSpec__transp_receiver.len(), x.owlSpec__transp_counter.len(), x.owlSpec__transp_packet.len() ] {
        let spec_comb = spec_combinator_owlSpec_transp();
        if let Ok(serialized) = spec_comb.spec_serialize(
            ((
                ((x.owlSpec__transp_tag, x.owlSpec__transp_receiver), x.owlSpec__transp_counter),
                x.owlSpec__transp_packet,
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
pub closed spec fn serialize_owlSpec_transp(x: owlSpec_transp) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_transp_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_transp {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_transp(self)
    }
}

pub open spec fn transp(
    arg_owlSpec__transp_tag: (),
    arg_owlSpec__transp_receiver: Seq<u8>,
    arg_owlSpec__transp_counter: Seq<u8>,
    arg_owlSpec__transp_packet: Seq<u8>,
) -> owlSpec_transp {
    owlSpec_transp {
        owlSpec__transp_tag: arg_owlSpec__transp_tag,
        owlSpec__transp_receiver: arg_owlSpec__transp_receiver,
        owlSpec__transp_counter: arg_owlSpec__transp_counter,
        owlSpec__transp_packet: arg_owlSpec__transp_packet,
    }
}

pub struct owlSpec_transp_keys_init {
    pub owlSpec_tki_msg2_receiver: Seq<u8>,
    pub owlSpec_tki_msg2_sender: Seq<u8>,
    pub owlSpec_tki_has_psk: bool,
    pub owlSpec_tki_eph: Ghost<()>,
    pub owlSpec_tki_c7: Ghost<()>,
    pub owlSpec_tki_k_init_send: Seq<u8>,
    pub owlSpec_tki_k_resp_send: Seq<u8>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_transp_keys_init(x: Seq<u8>) -> Option<owlSpec_transp_keys_init> {
    // cant autogenerate vest parser
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_transp_keys_init(x: owlSpec_transp_keys_init) -> Seq<u8> {
    // cant autogenerate vest serializer
    todo!()
}

impl OwlSpecSerialize for owlSpec_transp_keys_init {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_transp_keys_init(self)
    }
}

pub open spec fn transp_keys_init(
    arg_owlSpec_tki_msg2_receiver: Seq<u8>,
    arg_owlSpec_tki_msg2_sender: Seq<u8>,
    arg_owlSpec_tki_has_psk: bool,
    arg_owlSpec_tki_eph: Ghost<()>,
    arg_owlSpec_tki_c7: Ghost<()>,
    arg_owlSpec_tki_k_init_send: Seq<u8>,
    arg_owlSpec_tki_k_resp_send: Seq<u8>,
) -> owlSpec_transp_keys_init {
    owlSpec_transp_keys_init {
        owlSpec_tki_msg2_receiver: arg_owlSpec_tki_msg2_receiver,
        owlSpec_tki_msg2_sender: arg_owlSpec_tki_msg2_sender,
        owlSpec_tki_has_psk: arg_owlSpec_tki_has_psk,
        owlSpec_tki_eph: arg_owlSpec_tki_eph,
        owlSpec_tki_c7: arg_owlSpec_tki_c7,
        owlSpec_tki_k_init_send: arg_owlSpec_tki_k_init_send,
        owlSpec_tki_k_resp_send: arg_owlSpec_tki_k_resp_send,
    }
}

pub struct owlSpec_transp_keys_resp {
    pub owlSpec_tkr_msg2_receiver: Seq<u8>,
    pub owlSpec_tkr_msg2_sender: Seq<u8>,
    pub owlSpec_tkr_has_psk: bool,
    pub owlSpec_tkr_eph: Ghost<()>,
    pub owlSpec_tkr_c7: Ghost<()>,
    pub owlSpec_tkr_recvd: bool,
    pub owlSpec_tkr_k_init_send: Seq<u8>,
    pub owlSpec_tkr_k_resp_send: Seq<u8>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_transp_keys_resp(x: Seq<u8>) -> Option<owlSpec_transp_keys_resp> {
    // cant autogenerate vest parser
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_transp_keys_resp(x: owlSpec_transp_keys_resp) -> Seq<u8> {
    // cant autogenerate vest serializer
    todo!()
}

impl OwlSpecSerialize for owlSpec_transp_keys_resp {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_transp_keys_resp(self)
    }
}

pub open spec fn transp_keys_resp(
    arg_owlSpec_tkr_msg2_receiver: Seq<u8>,
    arg_owlSpec_tkr_msg2_sender: Seq<u8>,
    arg_owlSpec_tkr_has_psk: bool,
    arg_owlSpec_tkr_eph: Ghost<()>,
    arg_owlSpec_tkr_c7: Ghost<()>,
    arg_owlSpec_tkr_recvd: bool,
    arg_owlSpec_tkr_k_init_send: Seq<u8>,
    arg_owlSpec_tkr_k_resp_send: Seq<u8>,
) -> owlSpec_transp_keys_resp {
    owlSpec_transp_keys_resp {
        owlSpec_tkr_msg2_receiver: arg_owlSpec_tkr_msg2_receiver,
        owlSpec_tkr_msg2_sender: arg_owlSpec_tkr_msg2_sender,
        owlSpec_tkr_has_psk: arg_owlSpec_tkr_has_psk,
        owlSpec_tkr_eph: arg_owlSpec_tkr_eph,
        owlSpec_tkr_c7: arg_owlSpec_tkr_c7,
        owlSpec_tkr_recvd: arg_owlSpec_tkr_recvd,
        owlSpec_tkr_k_init_send: arg_owlSpec_tkr_k_init_send,
        owlSpec_tkr_k_resp_send: arg_owlSpec_tkr_k_resp_send,
    }
}

pub struct owlSpec_resp_transp_recv_result {
    pub owlSpec_rr_st: owlSpec_transp_keys_resp,
    pub owlSpec_rr_msg: Seq<u8>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_resp_transp_recv_result(x: Seq<u8>) -> Option<
    owlSpec_resp_transp_recv_result,
> {
    // cant autogenerate vest parser
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_resp_transp_recv_result(
    x: owlSpec_resp_transp_recv_result,
) -> Seq<u8> {
    // cant autogenerate vest serializer
    todo!()
}

impl OwlSpecSerialize for owlSpec_resp_transp_recv_result {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_resp_transp_recv_result(self)
    }
}

pub open spec fn resp_transp_recv_result(
    arg_owlSpec_rr_st: owlSpec_transp_keys_resp,
    arg_owlSpec_rr_msg: Seq<u8>,
) -> owlSpec_resp_transp_recv_result {
    owlSpec_resp_transp_recv_result {
        owlSpec_rr_st: arg_owlSpec_rr_st,
        owlSpec_rr_msg: arg_owlSpec_rr_msg,
    }
}

#[verifier::opaque]
pub open spec fn init_send_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    tki: owlSpec_transp_keys_init,
    msg: Seq<u8>,
) -> (res: ITree<((), state_Initiator), Endpoint>) {
    owl_spec!(mut_state, state_Initiator,
        (parse (tki) as (owlSpec_transp_keys_init{owlSpec_tki_msg2_receiver : init, owlSpec_tki_msg2_sender : resp, owlSpec_tki_has_psk : haspsk, owlSpec_tki_eph : eph, owlSpec_tki_c7 : c7, owlSpec_tki_k_init_send : init_send, owlSpec_tki_k_resp_send : resp_send}) in {
let transp_counter = ((ret(counter_as_bytes(mut_state.owl_N_init_send)))) in
let c = ((ret(enc_st_aead(init_send, msg, owl_N_init_send, empty_seq_u8())))) in
let transp_tag = ((ret(transp_tag_value()))) in
let o = ((ret(transp((), init, transp_counter, c)))) in
(output (serialize_owlSpec_transp(o)) to (Endpoint::Loc_Responder))
} )
    )
}

#[verifier::opaque]
pub open spec fn init_recv_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    tki: owlSpec_transp_keys_init,
) -> (res: ITree<(Option<Seq<u8>>, state_Initiator), Endpoint>) {
    owl_spec!(mut_state, state_Initiator,
        (input(i,_104)) in
(parse (tki) as (owlSpec_transp_keys_init{owlSpec_tki_msg2_receiver : init, owlSpec_tki_msg2_sender : resp, owlSpec_tki_has_psk : haspsk, owlSpec_tki_eph : eph, owlSpec_tki_c7 : c7, owlSpec_tki_k_init_send : init_send, owlSpec_tki_k_resp_send : resp_send}) in {
(parse (parse_owlSpec_transp(i)) as (owlSpec_transp{owlSpec__transp_tag : tag, owlSpec__transp_receiver : from, owlSpec__transp_counter : ctr, owlSpec__transp_packet : pkt}) in {
(if (from == resp) then (let p = ((ret(dec_st_aead(resp_send, pkt, ctr, empty_seq_u8())))) in
(ret(p))) else ((ret(Option::None))))
} otherwise ((ret(Option::None))))
} )
    )
}

#[verifier::opaque]
pub open spec fn timestamp_i_spec(cfg: cfg_Initiator, mut_state: state_Initiator) -> (res: ITree<
    (Seq<u8>, state_Initiator),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Initiator,
        (ret(timestamp_i_pure()))
    )
}

#[verifier(external_body)]
pub closed spec fn timestamp_i_pure() -> Seq<u8> {
    unimplemented!()
}

#[verifier::opaque]
pub open spec fn get_sender_i_spec(cfg: cfg_Initiator, mut_state: state_Initiator) -> (res: ITree<
    (Seq<u8>, state_Initiator),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Initiator,
        (ret(get_sender_i_pure()))
    )
}

#[verifier(external_body)]
pub closed spec fn get_sender_i_pure() -> Seq<u8> {
    unimplemented!()
}

#[verifier::opaque]
pub open spec fn resp_send_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    tki: owlSpec_transp_keys_resp,
    msg: Seq<u8>,
) -> (res: ITree<(Option<()>, state_Responder), Endpoint>) {
    owl_spec!(mut_state, state_Responder,
        let tki_ = ((ret(tki))) in
(parse (tki_) as (owlSpec_transp_keys_resp{owlSpec_tkr_msg2_receiver : init, owlSpec_tkr_msg2_sender : resp, owlSpec_tkr_has_psk : haspsk, owlSpec_tkr_eph : eph, owlSpec_tkr_c7 : c7, owlSpec_tkr_recvd : b, owlSpec_tkr_k_init_send : init_send, owlSpec_tkr_k_resp_send : resp_send}) in {
(if (b) then (let _unused330 = (let _unused331 = (let _assert_91 = ((ret(ghost_unit()))) in
(ret(ghost_unit()))) in
(ret(ghost_unit()))) in
let transp_counter = ((ret(counter_as_bytes(mut_state.owl_N_resp_send)))) in
let c = ((ret(enc_st_aead(resp_send, msg, owl_N_resp_send, empty_seq_u8())))) in
let transp_tag = ((ret(transp_tag_value()))) in
let o = ((ret(transp((), resp, transp_counter, c)))) in
(output (serialize_owlSpec_transp(o)) to (Endpoint::Loc_Initiator)) in
(ret(Option::Some(())))) else ((ret(Option::None))))
} )
    )
}

#[verifier::opaque]
pub open spec fn resp_recv_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    tki: owlSpec_transp_keys_resp,
) -> (res: ITree<(Option<owlSpec_resp_transp_recv_result>, state_Responder), Endpoint>) {
    owl_spec!(mut_state, state_Responder,
        (input(i,_191)) in
let tki_ = ((ret(tki))) in
(parse (tki_) as (owlSpec_transp_keys_resp{owlSpec_tkr_msg2_receiver : init, owlSpec_tkr_msg2_sender : resp, owlSpec_tkr_has_psk : haspsk, owlSpec_tkr_eph : eph, owlSpec_tkr_c7 : c7, owlSpec_tkr_recvd : _unused333, owlSpec_tkr_k_init_send : init_send, owlSpec_tkr_k_resp_send : resp_send}) in {
(parse (parse_owlSpec_transp(i)) as (owlSpec_transp{owlSpec__transp_tag : tag, owlSpec__transp_receiver : from, owlSpec__transp_counter : ctr, owlSpec__transp_packet : pkt}) in {
(if (from == init) then (let caseval = ((ret(dec_st_aead(init_send, pkt, ctr, empty_seq_u8())))) in
(case (caseval) {
| Some(x) => {
let st_ = ((ret(transp_keys_resp(init, resp, haspsk, ghost_unit(), ghost_unit(), true, init_send, resp_send)))) in
let ret = ((ret(resp_transp_recv_result(st_, x)))) in
(ret(Option::Some(ret)))
},
| None => {
(ret(Option::None))
},
}
)) else ((ret(Option::None))))
} otherwise ((ret(Option::None))))
} )
    )
}

#[verifier::opaque]
pub open spec fn timestamp_r_spec(cfg: cfg_Responder, mut_state: state_Responder) -> (res: ITree<
    (Seq<u8>, state_Responder),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Responder,
        (ret(timestamp_r_pure()))
    )
}

#[verifier(external_body)]
pub closed spec fn timestamp_r_pure() -> Seq<u8> {
    unimplemented!()
}

#[verifier::opaque]
pub open spec fn get_sender_r_spec(cfg: cfg_Responder, mut_state: state_Responder) -> (res: ITree<
    (Seq<u8>, state_Responder),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Responder,
        (ret(get_sender_r_pure()))
    )
}

#[verifier(external_body)]
pub closed spec fn get_sender_r_pure() -> Seq<u8> {
    unimplemented!()
}

#[verifier::opaque]
pub closed spec fn transp_tag_value() -> (res: Seq<u8>) {
    seq![0x04u8, 0x00u8, 0x00u8, 0x00u8, ]
}

// ------------------------------------
// ---------- IMPLEMENTATIONS ---------
// ------------------------------------
#[derive(Clone,Copy)]
pub enum Endpoint {
    Loc_Initiator,
    Loc_Responder,
    Loc_nobody,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier(external_body)]
pub const fn Initiator_addr() -> (a: StrSlice<'static>)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_Initiator,
{
    new_strlit("127.0.0.1:9001")
}

#[verifier(external_body)]
pub const fn Responder_addr() -> (a: StrSlice<'static>)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_Responder,
{
    new_strlit("127.0.0.1:9002")
}

#[verifier(external_body)]
pub const fn nobody_addr() -> (a: StrSlice<'static>)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_nobody,
{
    new_strlit("127.0.0.1:9003")
}

pub enum owl_PSKMode<'a> {
    owl_HasPSK(OwlBuf<'a>),
    owl_NoPSK(),
}

use owl_PSKMode::*;

impl owl_PSKMode<'_> {
    pub open spec fn len_valid(&self) -> bool {
        match self {
            owl_HasPSK(x) => x.len_valid(),
            owl_NoPSK() => true,
        }
    }
}

impl View for owl_PSKMode<'_> {
    type V = owlSpec_PSKMode;

    open spec fn view(&self) -> owlSpec_PSKMode {
        match self {
            owl_HasPSK(v) => owlSpec_PSKMode::owlSpec_HasPSK(v.view()),
            owl_NoPSK() => owlSpec_PSKMode::owlSpec_NoPSK(),
        }
    }
}

#[inline]
pub fn owl_HasPSK_enumtest(x: &owl_PSKMode<'_>) -> (res: bool)
    ensures
        res == HasPSK_enumtest(x.view()),
{
    match x {
        owl_PSKMode::owl_HasPSK(_) => true,
        _ => false,
    }
}

#[inline]
pub fn owl_NoPSK_enumtest(x: &owl_PSKMode<'_>) -> (res: bool)
    ensures
        res == NoPSK_enumtest(x.view()),
{
    match x {
        owl_PSKMode::owl_NoPSK() => true,
        _ => false,
    }
}

pub struct owl_msg1<'a> {
    pub owl__msg1_tag: (),
    pub owl__msg1_sender: OwlBuf<'a>,
    pub owl__msg1_ephemeral: OwlBuf<'a>,
    pub owl__msg1_static: OwlBuf<'a>,
    pub owl__msg1_timestamp: OwlBuf<'a>,
    pub owl__msg1_mac1: OwlBuf<'a>,
    pub owl__msg1_mac2: (),
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg1<'a>(
    arg_owl__msg1_tag: (),
    arg_owl__msg1_sender: OwlBuf<'a>,
    arg_owl__msg1_ephemeral: OwlBuf<'a>,
    arg_owl__msg1_static: OwlBuf<'a>,
    arg_owl__msg1_timestamp: OwlBuf<'a>,
    arg_owl__msg1_mac1: OwlBuf<'a>,
    arg_owl__msg1_mac2: (),
) -> (res: owl_msg1<'a>)
    requires
        arg_owl__msg1_sender.len_valid(),
        arg_owl__msg1_ephemeral.len_valid(),
        arg_owl__msg1_static.len_valid(),
        arg_owl__msg1_timestamp.len_valid(),
        arg_owl__msg1_mac1.len_valid(),
    ensures
        res.len_valid(),
        res.owl__msg1_tag.view() == arg_owl__msg1_tag.view(),
        res.owl__msg1_sender.view() == arg_owl__msg1_sender.view(),
        res.owl__msg1_ephemeral.view() == arg_owl__msg1_ephemeral.view(),
        res.owl__msg1_static.view() == arg_owl__msg1_static.view(),
        res.owl__msg1_timestamp.view() == arg_owl__msg1_timestamp.view(),
        res.owl__msg1_mac1.view() == arg_owl__msg1_mac1.view(),
        res.owl__msg1_mac2.view() == arg_owl__msg1_mac2.view(),
{
    owl_msg1 {
        owl__msg1_tag: arg_owl__msg1_tag,
        owl__msg1_sender: arg_owl__msg1_sender,
        owl__msg1_ephemeral: arg_owl__msg1_ephemeral,
        owl__msg1_static: arg_owl__msg1_static,
        owl__msg1_timestamp: arg_owl__msg1_timestamp,
        owl__msg1_mac1: arg_owl__msg1_mac1,
        owl__msg1_mac2: arg_owl__msg1_mac2,
    }
}

impl owl_msg1<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl__msg1_sender.len_valid() && self.owl__msg1_ephemeral.len_valid()
            && self.owl__msg1_static.len_valid() && self.owl__msg1_timestamp.len_valid()
            && self.owl__msg1_mac1.len_valid()
    }
}

impl View for owl_msg1<'_> {
    type V = owlSpec_msg1;

    open spec fn view(&self) -> owlSpec_msg1 {
        owlSpec_msg1 {
            owlSpec__msg1_tag: self.owl__msg1_tag.view(),
            owlSpec__msg1_sender: self.owl__msg1_sender.view(),
            owlSpec__msg1_ephemeral: self.owl__msg1_ephemeral.view(),
            owlSpec__msg1_static: self.owl__msg1_static.view(),
            owlSpec__msg1_timestamp: self.owl__msg1_timestamp.view(),
            owlSpec__msg1_mac1: self.owl__msg1_mac1.view(),
            owlSpec__msg1_mac2: self.owl__msg1_mac2.view(),
        }
    }
}

pub exec fn parse_owl_msg1<'a>(arg: &'a [u8]) -> (res: Option<
    owl_msg1<'a>,
>)
// requires arg.len_valid()

    ensures
        res is Some ==> parse_owlSpec_msg1(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg1(arg.view())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_msg1);
    let exec_comb = exec_combinator_owl_msg1();
    if let Ok((_, parsed)) = exec_comb.parse(arg) {
        let (
            (
                (
                    (((owl__msg1_tag, owl__msg1_sender), owl__msg1_ephemeral), owl__msg1_static),
                    owl__msg1_timestamp,
                ),
                owl__msg1_mac1,
            ),
            owl__msg1_mac2,
        ) = parsed;
        Some(
            owl_msg1 {
                owl__msg1_tag: (),
                owl__msg1_sender: OwlBuf::from_slice(&owl__msg1_sender),
                owl__msg1_ephemeral: OwlBuf::from_slice(&owl__msg1_ephemeral),
                owl__msg1_static: OwlBuf::from_slice(&owl__msg1_static),
                owl__msg1_timestamp: OwlBuf::from_slice(&owl__msg1_timestamp),
                owl__msg1_mac1: OwlBuf::from_slice(&owl__msg1_mac1),
                owl__msg1_mac2: (),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_msg1_inner(arg: &owl_msg1) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> serialize_owlSpec_msg1_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_msg1_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg1_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_msg1_inner);
    if no_usize_overflows![ 4, arg.owl__msg1_sender.len(), arg.owl__msg1_ephemeral.len(), arg.owl__msg1_static.len(), arg.owl__msg1_timestamp.len(), arg.owl__msg1_mac1.len(), 16, 0 ] {
        let exec_comb = exec_combinator_owl_msg1();
        let mut obuf = vec_u8_of_len(
            4 + arg.owl__msg1_sender.len() + arg.owl__msg1_ephemeral.len()
                + arg.owl__msg1_static.len() + arg.owl__msg1_timestamp.len()
                + arg.owl__msg1_mac1.len() + 16 + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        (
                            (
                                (arg.owl__msg1_tag, arg.owl__msg1_sender.as_slice()),
                                arg.owl__msg1_ephemeral.as_slice(),
                            ),
                            arg.owl__msg1_static.as_slice(),
                        ),
                        arg.owl__msg1_timestamp.as_slice(),
                    ),
                    arg.owl__msg1_mac1.as_slice(),
                ),
                arg.owl__msg1_mac2,
            ),
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

pub exec fn serialize_owl_msg1(arg: &owl_msg1) -> (res: Vec<u8>)
    requires
        arg.len_valid(),
    ensures
        res.view() == serialize_owlSpec_msg1(arg.view()),
{
    reveal(serialize_owlSpec_msg1);
    let res = serialize_owl_msg1_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_msg2<'a> {
    pub owl__msg2_tag: (),
    pub owl__msg2_sender: OwlBuf<'a>,
    pub owl__msg2_receiver: OwlBuf<'a>,
    pub owl__msg2_ephemeral: OwlBuf<'a>,
    pub owl__msg2_empty: OwlBuf<'a>,
    pub owl__msg2_mac1: OwlBuf<'a>,
    pub owl__msg2_mac2: (),
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg2<'a>(
    arg_owl__msg2_tag: (),
    arg_owl__msg2_sender: OwlBuf<'a>,
    arg_owl__msg2_receiver: OwlBuf<'a>,
    arg_owl__msg2_ephemeral: OwlBuf<'a>,
    arg_owl__msg2_empty: OwlBuf<'a>,
    arg_owl__msg2_mac1: OwlBuf<'a>,
    arg_owl__msg2_mac2: (),
) -> (res: owl_msg2<'a>)
    requires
        arg_owl__msg2_sender.len_valid(),
        arg_owl__msg2_receiver.len_valid(),
        arg_owl__msg2_ephemeral.len_valid(),
        arg_owl__msg2_empty.len_valid(),
        arg_owl__msg2_mac1.len_valid(),
    ensures
        res.len_valid(),
        res.owl__msg2_tag.view() == arg_owl__msg2_tag.view(),
        res.owl__msg2_sender.view() == arg_owl__msg2_sender.view(),
        res.owl__msg2_receiver.view() == arg_owl__msg2_receiver.view(),
        res.owl__msg2_ephemeral.view() == arg_owl__msg2_ephemeral.view(),
        res.owl__msg2_empty.view() == arg_owl__msg2_empty.view(),
        res.owl__msg2_mac1.view() == arg_owl__msg2_mac1.view(),
        res.owl__msg2_mac2.view() == arg_owl__msg2_mac2.view(),
{
    owl_msg2 {
        owl__msg2_tag: arg_owl__msg2_tag,
        owl__msg2_sender: arg_owl__msg2_sender,
        owl__msg2_receiver: arg_owl__msg2_receiver,
        owl__msg2_ephemeral: arg_owl__msg2_ephemeral,
        owl__msg2_empty: arg_owl__msg2_empty,
        owl__msg2_mac1: arg_owl__msg2_mac1,
        owl__msg2_mac2: arg_owl__msg2_mac2,
    }
}

impl owl_msg2<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl__msg2_sender.len_valid() && self.owl__msg2_receiver.len_valid()
            && self.owl__msg2_ephemeral.len_valid() && self.owl__msg2_empty.len_valid()
            && self.owl__msg2_mac1.len_valid()
    }
}

impl View for owl_msg2<'_> {
    type V = owlSpec_msg2;

    open spec fn view(&self) -> owlSpec_msg2 {
        owlSpec_msg2 {
            owlSpec__msg2_tag: self.owl__msg2_tag.view(),
            owlSpec__msg2_sender: self.owl__msg2_sender.view(),
            owlSpec__msg2_receiver: self.owl__msg2_receiver.view(),
            owlSpec__msg2_ephemeral: self.owl__msg2_ephemeral.view(),
            owlSpec__msg2_empty: self.owl__msg2_empty.view(),
            owlSpec__msg2_mac1: self.owl__msg2_mac1.view(),
            owlSpec__msg2_mac2: self.owl__msg2_mac2.view(),
        }
    }
}

pub exec fn parse_owl_msg2<'a>(arg: &'a [u8]) -> (res: Option<
    owl_msg2<'a>,
>)
// requires arg.len_valid()

    ensures
        res is Some ==> parse_owlSpec_msg2(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg2(arg.view())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_msg2);
    let exec_comb = exec_combinator_owl_msg2();
    if let Ok((_, parsed)) = exec_comb.parse(arg) {
        let (
            (
                (
                    (((owl__msg2_tag, owl__msg2_sender), owl__msg2_receiver), owl__msg2_ephemeral),
                    owl__msg2_empty,
                ),
                owl__msg2_mac1,
            ),
            owl__msg2_mac2,
        ) = parsed;
        Some(
            owl_msg2 {
                owl__msg2_tag: (),
                owl__msg2_sender: OwlBuf::from_slice(&owl__msg2_sender),
                owl__msg2_receiver: OwlBuf::from_slice(&owl__msg2_receiver),
                owl__msg2_ephemeral: OwlBuf::from_slice(&owl__msg2_ephemeral),
                owl__msg2_empty: OwlBuf::from_slice(&owl__msg2_empty),
                owl__msg2_mac1: OwlBuf::from_slice(&owl__msg2_mac1),
                owl__msg2_mac2: (),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_msg2_inner(arg: &owl_msg2) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> serialize_owlSpec_msg2_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_msg2_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_msg2_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_msg2_inner);
    if no_usize_overflows![ 4, arg.owl__msg2_sender.len(), arg.owl__msg2_receiver.len(), arg.owl__msg2_ephemeral.len(), arg.owl__msg2_empty.len(), arg.owl__msg2_mac1.len(), 16, 0 ] {
        let exec_comb = exec_combinator_owl_msg2();
        let mut obuf = vec_u8_of_len(
            4 + arg.owl__msg2_sender.len() + arg.owl__msg2_receiver.len()
                + arg.owl__msg2_ephemeral.len() + arg.owl__msg2_empty.len()
                + arg.owl__msg2_mac1.len() + 16 + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (
                        (
                            (
                                (arg.owl__msg2_tag, arg.owl__msg2_sender.as_slice()),
                                arg.owl__msg2_receiver.as_slice(),
                            ),
                            arg.owl__msg2_ephemeral.as_slice(),
                        ),
                        arg.owl__msg2_empty.as_slice(),
                    ),
                    arg.owl__msg2_mac1.as_slice(),
                ),
                arg.owl__msg2_mac2,
            ),
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

pub exec fn serialize_owl_msg2(arg: &owl_msg2) -> (res: Vec<u8>)
    requires
        arg.len_valid(),
    ensures
        res.view() == serialize_owlSpec_msg2(arg.view()),
{
    reveal(serialize_owlSpec_msg2);
    let res = serialize_owl_msg2_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_transp<'a> {
    pub owl__transp_tag: (),
    pub owl__transp_receiver: OwlBuf<'a>,
    pub owl__transp_counter: OwlBuf<'a>,
    pub owl__transp_packet: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_transp<'a>(
    arg_owl__transp_tag: (),
    arg_owl__transp_receiver: OwlBuf<'a>,
    arg_owl__transp_counter: OwlBuf<'a>,
    arg_owl__transp_packet: OwlBuf<'a>,
) -> (res: owl_transp<'a>)
    requires
        arg_owl__transp_receiver.len_valid(),
        arg_owl__transp_counter.len_valid(),
        arg_owl__transp_packet.len_valid(),
    ensures
        res.len_valid(),
        res.owl__transp_tag.view() == arg_owl__transp_tag.view(),
        res.owl__transp_receiver.view() == arg_owl__transp_receiver.view(),
        res.owl__transp_counter.view() == arg_owl__transp_counter.view(),
        res.owl__transp_packet.view() == arg_owl__transp_packet.view(),
{
    owl_transp {
        owl__transp_tag: arg_owl__transp_tag,
        owl__transp_receiver: arg_owl__transp_receiver,
        owl__transp_counter: arg_owl__transp_counter,
        owl__transp_packet: arg_owl__transp_packet,
    }
}

impl owl_transp<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl__transp_receiver.len_valid() && self.owl__transp_counter.len_valid()
            && self.owl__transp_packet.len_valid()
    }
}

impl View for owl_transp<'_> {
    type V = owlSpec_transp;

    open spec fn view(&self) -> owlSpec_transp {
        owlSpec_transp {
            owlSpec__transp_tag: self.owl__transp_tag.view(),
            owlSpec__transp_receiver: self.owl__transp_receiver.view(),
            owlSpec__transp_counter: self.owl__transp_counter.view(),
            owlSpec__transp_packet: self.owl__transp_packet.view(),
        }
    }
}

pub exec fn parse_owl_transp<'a>(arg: &'a [u8]) -> (res: Option<
    owl_transp<'a>,
>)
// requires arg.len_valid()

    ensures
        res is Some ==> parse_owlSpec_transp(arg.view()) is Some,
        res is None ==> parse_owlSpec_transp(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_transp(arg.view())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_transp);
    let exec_comb = exec_combinator_owl_transp();
    if let Ok((_, parsed)) = exec_comb.parse(arg) {
        let (((owl__transp_tag, owl__transp_receiver), owl__transp_counter), owl__transp_packet) =
            parsed;
        Some(
            owl_transp {
                owl__transp_tag: (),
                owl__transp_receiver: OwlBuf::from_slice(&owl__transp_receiver),
                owl__transp_counter: OwlBuf::from_slice(&owl__transp_counter),
                owl__transp_packet: OwlBuf::from_slice(&owl__transp_packet),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_transp_inner(arg: &owl_transp) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> serialize_owlSpec_transp_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_transp_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_transp_inner(arg.view())->Some_0,
{
    reveal(serialize_owlSpec_transp_inner);
    if no_usize_overflows![ 4, arg.owl__transp_receiver.len(), arg.owl__transp_counter.len(), arg.owl__transp_packet.len(), 0 ] {
        let exec_comb = exec_combinator_owl_transp();
        let mut obuf = vec_u8_of_len(
            4 + arg.owl__transp_receiver.len() + arg.owl__transp_counter.len()
                + arg.owl__transp_packet.len() + 0,
        );
        let ser_result = exec_comb.serialize(
            (
                (
                    (arg.owl__transp_tag, arg.owl__transp_receiver.as_slice()),
                    arg.owl__transp_counter.as_slice(),
                ),
                arg.owl__transp_packet.as_slice(),
            ),
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

pub exec fn serialize_owl_transp(arg: &owl_transp) -> (res: Vec<u8>)
    requires
        arg.len_valid(),
    ensures
        res.view() == serialize_owlSpec_transp(arg.view()),
{
    reveal(serialize_owlSpec_transp);
    let res = serialize_owl_transp_inner(arg);
    assume(res is Some);
    res.unwrap()
}

pub struct owl_transp_keys_init<'a> {
    pub owl_tki_msg2_receiver: OwlBuf<'a>,
    pub owl_tki_msg2_sender: OwlBuf<'a>,
    pub owl_tki_has_psk: bool,
    pub owl_tki_eph: Ghost<()>,
    pub owl_tki_c7: Ghost<()>,
    pub owl_tki_k_init_send: OwlBuf<'a>,
    pub owl_tki_k_resp_send: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_transp_keys_init<'a>(
    arg_owl_tki_msg2_receiver: OwlBuf<'a>,
    arg_owl_tki_msg2_sender: OwlBuf<'a>,
    arg_owl_tki_has_psk: bool,
    arg_owl_tki_eph: Ghost<()>,
    arg_owl_tki_c7: Ghost<()>,
    arg_owl_tki_k_init_send: OwlBuf<'a>,
    arg_owl_tki_k_resp_send: OwlBuf<'a>,
) -> (res: owl_transp_keys_init<'a>)
    requires
        arg_owl_tki_msg2_receiver.len_valid(),
        arg_owl_tki_msg2_sender.len_valid(),
        arg_owl_tki_k_init_send.len_valid(),
        arg_owl_tki_k_resp_send.len_valid(),
    ensures
        res.len_valid(),
        res.owl_tki_msg2_receiver.view() == arg_owl_tki_msg2_receiver.view(),
        res.owl_tki_msg2_sender.view() == arg_owl_tki_msg2_sender.view(),
        res.owl_tki_has_psk.view() == arg_owl_tki_has_psk.view(),
        res.owl_tki_eph.view() == arg_owl_tki_eph.view(),
        res.owl_tki_c7.view() == arg_owl_tki_c7.view(),
        res.owl_tki_k_init_send.view() == arg_owl_tki_k_init_send.view(),
        res.owl_tki_k_resp_send.view() == arg_owl_tki_k_resp_send.view(),
{
    owl_transp_keys_init {
        owl_tki_msg2_receiver: arg_owl_tki_msg2_receiver,
        owl_tki_msg2_sender: arg_owl_tki_msg2_sender,
        owl_tki_has_psk: arg_owl_tki_has_psk,
        owl_tki_eph: arg_owl_tki_eph,
        owl_tki_c7: arg_owl_tki_c7,
        owl_tki_k_init_send: arg_owl_tki_k_init_send,
        owl_tki_k_resp_send: arg_owl_tki_k_resp_send,
    }
}

impl owl_transp_keys_init<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_tki_msg2_receiver.len_valid() && self.owl_tki_msg2_sender.len_valid()
            && self.owl_tki_k_init_send.len_valid() && self.owl_tki_k_resp_send.len_valid()
    }
}

impl View for owl_transp_keys_init<'_> {
    type V = owlSpec_transp_keys_init;

    open spec fn view(&self) -> owlSpec_transp_keys_init {
        owlSpec_transp_keys_init {
            owlSpec_tki_msg2_receiver: self.owl_tki_msg2_receiver.view(),
            owlSpec_tki_msg2_sender: self.owl_tki_msg2_sender.view(),
            owlSpec_tki_has_psk: self.owl_tki_has_psk.view(),
            owlSpec_tki_eph: ghost_unit(),
            owlSpec_tki_c7: ghost_unit(),
            owlSpec_tki_k_init_send: self.owl_tki_k_init_send.view(),
            owlSpec_tki_k_resp_send: self.owl_tki_k_resp_send.view(),
        }
    }
}

pub struct owl_transp_keys_resp<'a> {
    pub owl_tkr_msg2_receiver: OwlBuf<'a>,
    pub owl_tkr_msg2_sender: OwlBuf<'a>,
    pub owl_tkr_has_psk: bool,
    pub owl_tkr_eph: Ghost<()>,
    pub owl_tkr_c7: Ghost<()>,
    pub owl_tkr_recvd: bool,
    pub owl_tkr_k_init_send: OwlBuf<'a>,
    pub owl_tkr_k_resp_send: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_transp_keys_resp<'a>(
    arg_owl_tkr_msg2_receiver: OwlBuf<'a>,
    arg_owl_tkr_msg2_sender: OwlBuf<'a>,
    arg_owl_tkr_has_psk: bool,
    arg_owl_tkr_eph: Ghost<()>,
    arg_owl_tkr_c7: Ghost<()>,
    arg_owl_tkr_recvd: bool,
    arg_owl_tkr_k_init_send: OwlBuf<'a>,
    arg_owl_tkr_k_resp_send: OwlBuf<'a>,
) -> (res: owl_transp_keys_resp<'a>)
    requires
        arg_owl_tkr_msg2_receiver.len_valid(),
        arg_owl_tkr_msg2_sender.len_valid(),
        arg_owl_tkr_k_init_send.len_valid(),
        arg_owl_tkr_k_resp_send.len_valid(),
    ensures
        res.len_valid(),
        res.owl_tkr_msg2_receiver.view() == arg_owl_tkr_msg2_receiver.view(),
        res.owl_tkr_msg2_sender.view() == arg_owl_tkr_msg2_sender.view(),
        res.owl_tkr_has_psk.view() == arg_owl_tkr_has_psk.view(),
        res.owl_tkr_eph.view() == arg_owl_tkr_eph.view(),
        res.owl_tkr_c7.view() == arg_owl_tkr_c7.view(),
        res.owl_tkr_recvd.view() == arg_owl_tkr_recvd.view(),
        res.owl_tkr_k_init_send.view() == arg_owl_tkr_k_init_send.view(),
        res.owl_tkr_k_resp_send.view() == arg_owl_tkr_k_resp_send.view(),
{
    owl_transp_keys_resp {
        owl_tkr_msg2_receiver: arg_owl_tkr_msg2_receiver,
        owl_tkr_msg2_sender: arg_owl_tkr_msg2_sender,
        owl_tkr_has_psk: arg_owl_tkr_has_psk,
        owl_tkr_eph: arg_owl_tkr_eph,
        owl_tkr_c7: arg_owl_tkr_c7,
        owl_tkr_recvd: arg_owl_tkr_recvd,
        owl_tkr_k_init_send: arg_owl_tkr_k_init_send,
        owl_tkr_k_resp_send: arg_owl_tkr_k_resp_send,
    }
}

impl owl_transp_keys_resp<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_tkr_msg2_receiver.len_valid() && self.owl_tkr_msg2_sender.len_valid()
            && self.owl_tkr_k_init_send.len_valid() && self.owl_tkr_k_resp_send.len_valid()
    }
}

impl View for owl_transp_keys_resp<'_> {
    type V = owlSpec_transp_keys_resp;

    open spec fn view(&self) -> owlSpec_transp_keys_resp {
        owlSpec_transp_keys_resp {
            owlSpec_tkr_msg2_receiver: self.owl_tkr_msg2_receiver.view(),
            owlSpec_tkr_msg2_sender: self.owl_tkr_msg2_sender.view(),
            owlSpec_tkr_has_psk: self.owl_tkr_has_psk.view(),
            owlSpec_tkr_eph: ghost_unit(),
            owlSpec_tkr_c7: ghost_unit(),
            owlSpec_tkr_recvd: self.owl_tkr_recvd.view(),
            owlSpec_tkr_k_init_send: self.owl_tkr_k_init_send.view(),
            owlSpec_tkr_k_resp_send: self.owl_tkr_k_resp_send.view(),
        }
    }
}

pub struct owl_resp_transp_recv_result<'a> {
    pub owl_rr_st: owl_transp_keys_resp<'a>,
    pub owl_rr_msg: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_resp_transp_recv_result<'a>(
    arg_owl_rr_st: owl_transp_keys_resp<'a>,
    arg_owl_rr_msg: OwlBuf<'a>,
) -> (res: owl_resp_transp_recv_result<'a>)
    requires
        arg_owl_rr_st.len_valid(),
        arg_owl_rr_msg.len_valid(),
    ensures
        res.len_valid(),
        res.owl_rr_st.view() == arg_owl_rr_st.view(),
        res.owl_rr_msg.view() == arg_owl_rr_msg.view(),
{
    owl_resp_transp_recv_result { owl_rr_st: arg_owl_rr_st, owl_rr_msg: arg_owl_rr_msg }
}

impl owl_resp_transp_recv_result<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_rr_st.len_valid() && self.owl_rr_msg.len_valid()
    }
}

impl View for owl_resp_transp_recv_result<'_> {
    type V = owlSpec_resp_transp_recv_result;

    open spec fn view(&self) -> owlSpec_resp_transp_recv_result {
        owlSpec_resp_transp_recv_result {
            owlSpec_rr_st: self.owl_rr_st.view(),
            owlSpec_rr_msg: self.owl_rr_msg.view(),
        }
    }
}

pub struct state_Initiator {
    pub owl_aead_counter_msg1_C2: usize,
    pub owl_aead_counter_msg1_C3: usize,
    pub owl_N_init_recv: usize,
    pub owl_N_init_send: usize,
}

impl state_Initiator {
    #[verifier::external_body]
    pub fn init_state_Initiator() -> Self {
        state_Initiator {
            owl_aead_counter_msg1_C2: 0,
            owl_aead_counter_msg1_C3: 0,
            owl_N_init_recv: 0,
            owl_N_init_send: 0,
        }
    }
}

pub struct cfg_Initiator<O> {
    pub salt: Vec<u8>,
    pub owl_S_init: Vec<u8>,
    pub owl_E_init: Vec<u8>,
    pub pk_owl_S_resp: Vec<u8>,
    pub pk_owl_S_init: Vec<u8>,
    pub pk_owl_E_resp: Vec<u8>,
    pub pk_owl_E_init: Vec<u8>,
    pub device: Option<crate::wireguard::handshake::device::DeviceInner<O>>,
}

impl<O> cfg_Initiator<O> {    
    pub exec fn owl_transp_send_init_wrapper<'a>(
        &'a self,         
        mut_state: &mut state_Initiator,
        owl_plaintext: &'a [u8],
        obuf: &mut Vec<u8>,
        owl_tki_msg2_receiver: &'a [u8],
        owl_tki_msg2_sender: &'a [u8],
        owl_tki_k_init_send: &'a [u8],
        owl_tki_k_resp_send: &'a [u8],
    ) -> () {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let owl_transp_keys_val = owl_transp_keys_init {
            owl_tki_msg2_receiver: OwlBuf::from_slice(owl_tki_msg2_receiver),
            owl_tki_msg2_sender: OwlBuf::from_slice(owl_tki_msg2_sender),
            owl_tki_has_psk: false,
            owl_tki_eph: Ghost(()),
            owl_tki_c7: Ghost(()),
            owl_tki_k_init_send: OwlBuf::from_slice(owl_tki_k_init_send),
            owl_tki_k_resp_send: OwlBuf::from_slice(owl_tki_k_resp_send),
        };
        let (res, _) =
            self.owl_init_send(Tracked(call_token), mut_state, owl_transp_keys_val, OwlBuf::from_slice(owl_plaintext), obuf).unwrap();
        res
    }


    #[verifier::spinoff_prover]
    pub fn owl_init_send<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_tki401: owl_transp_keys_init<'a>,
        owl_msg402: OwlBuf<'a>,
        obuf: &mut Vec<u8>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Initiator), Endpoint>>), OwlError>)
        requires
            itree.view() == init_send_spec(
                *self,
                *old(mut_state),
                owl_tki401.view(),
                owl_msg402.view(),
            ),
            owl_tki401.len_valid(),
            owl_msg402.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(init_send_spec);
            let parseval = owl_tki401;
            let owl_init342 = OwlBuf::another_ref(&parseval.owl_tki_msg2_receiver);
            let owl_resp341 = OwlBuf::another_ref(&parseval.owl_tki_msg2_sender);
            let owl_haspsk340 = parseval.owl_tki_has_psk;
            let owl_eph339 = parseval.owl_tki_eph;
            let owl_c7338 = parseval.owl_tki_c7;
            let owl_init_send337 = OwlBuf::another_ref(&parseval.owl_tki_k_init_send);
            let owl_resp_send336 = OwlBuf::another_ref(&parseval.owl_tki_k_resp_send);
            let tmp_owl_transp_counter343 = { owl_counter_as_bytes(&mut_state.owl_N_init_send) };
            let owl_transp_counter343 = OwlBuf::from_slice(&tmp_owl_transp_counter343);
            let x = mk_vec_u8![];
            let owl_c344 = {
                {
                    match owl_enc_st_aead_builder(
                        owl_init_send337.as_slice(),
                        owl_msg402.as_slice(),
                        &mut mut_state.owl_N_init_send,
                        x.as_slice(),
                    ) {
                        Ok(b) => { b },
                        Err(e) => { return Err(e) },
                    }
                }
            };
            let owl_transp_tag345 = { owl_transp_tag_value() };

            let field_1 = ConstBytes(EXEC_BYTES_CONST_04000000_TRANSP);
            let field_2 = Bytes(4);
            let field_3 = Bytes(8);
            let field_4 = BuilderCombinator(owl_c344);
            let exec_comb = (((field_1, field_2), field_3), field_4);

            let mut ser_buf = vec_u8_of_len(
                4 + owl_init342.len() + owl_transp_counter343.len()
                    + owl_msg402.len() + tag_size() + 0,
            );
            let ser_result = exec_comb.serialize(
                (
                    (
                        ((), owl_init342.as_slice()),
                        owl_transp_counter343.as_slice(),
                    ),
                    ()
                ),
                &mut ser_buf,
                0,
            );
            if let Ok((num_written)) = ser_result {
                vec_truncate(&mut ser_buf, num_written);
            } else {
                panic!();
            }

            owl_output::<((), state_Initiator)>(
                Tracked(&mut itree),
                ser_buf.as_slice(),
                &Responder_addr(),
                &Initiator_addr(),
                obuf
            );
            ((), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    pub exec fn owl_transp_recv_init_wrapper<'a>(
        &'a self,         
        mut_state: &mut state_Initiator,
        ibuf: &'a [u8],
        owl_tki_msg2_receiver: &'a [u8],
        owl_tki_msg2_sender: &'a [u8],
        owl_tki_k_init_send: &'a [u8],
        owl_tki_k_resp_send: &'a [u8],
    ) -> (Option<OwlBuf<'a>>) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let owl_tki = owl_transp_keys_init {
            owl_tki_msg2_receiver: OwlBuf::from_slice(owl_tki_msg2_receiver),
            owl_tki_msg2_sender: OwlBuf::from_slice(owl_tki_msg2_sender),
            owl_tki_has_psk: false,
            owl_tki_eph: Ghost(()),
            owl_tki_c7: Ghost(()),
            owl_tki_k_init_send: OwlBuf::from_slice(owl_tki_k_init_send),
            owl_tki_k_resp_send: OwlBuf::from_slice(owl_tki_k_resp_send),
        };
        let (res, _) =
            self.owl_init_recv(Tracked(call_token), mut_state, owl_tki, ibuf).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_init_recv<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_tki403: owl_transp_keys_init<'a>,
        ibuf: &'a [u8],
    ) -> (res: Result<
        (Option<OwlBuf<'a>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == init_recv_spec(*self, *old(mut_state), owl_tki403.view()),
            owl_tki403.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
            res matches Ok((Some(b), _)) ==> b.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<OwlBuf<'a>>,
            Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(init_recv_spec);
            let (tmp_owl_i349, owl__348) = {
                owl_input::<(Option<Seq<u8>>, state_Initiator)>(Tracked(&mut itree), ibuf)
            };
            let owl_i349 = OwlBuf::from_slice(tmp_owl_i349);
            let parseval = owl_tki403;
            let owl_init356 = OwlBuf::another_ref(&parseval.owl_tki_msg2_receiver);
            let owl_resp355 = OwlBuf::another_ref(&parseval.owl_tki_msg2_sender);
            let owl_haspsk354 = parseval.owl_tki_has_psk;
            let owl_eph353 = parseval.owl_tki_eph;
            let owl_c7352 = parseval.owl_tki_c7;
            let owl_init_send351 = OwlBuf::another_ref(&parseval.owl_tki_k_init_send);
            let owl_resp_send350 = OwlBuf::another_ref(&parseval.owl_tki_k_resp_send);
            let parseval_tmp = OwlBuf::another_ref(&owl_i349);
            if let Some(parseval) = parse_owl_transp(parseval_tmp.as_slice()) {
                let owl_tag360 = parseval.owl__transp_tag;
                let owl_from359 = OwlBuf::another_ref(&parseval.owl__transp_receiver);
                let owl_ctr358 = OwlBuf::another_ref(&parseval.owl__transp_counter);
                let owl_pkt357 = OwlBuf::another_ref(&parseval.owl__transp_packet);
                {
                    if { slice_eq(owl_from359.as_slice(), owl_resp355.as_slice()) } {
                        let tmp_owl_p361 = {
                            owl_dec_st_aead(
                                owl_resp_send350.as_slice(),
                                owl_pkt357.as_slice(),
                                owl_ctr358.as_slice(),
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }.as_slice(),
                            )
                        };
                        let owl_p361 = OwlBuf::from_vec_option(tmp_owl_p361);
                        (owl_p361, Tracked(itree))
                    } else {
                        (None, Tracked(itree))
                    }
                }
            } else {
                (None, Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier(external_body)]
    #[verifier::spinoff_prover]
    pub fn owl_timestamp_i(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
    ) -> (res: Result<
        (OwlBuf, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == timestamp_i_spec(*self, *old(mut_state)),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview(), *mut_state),
            ),
            res.is_Ok() ==> res.get_Ok_0().0.len_valid(),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let t = crate::wireguard::handshake::timestamp::now().to_vec();
            (OwlBuf::from_vec(t), Tracked(itree))
        };
        Ok(res_inner)
    }

    #[verifier(external_body)]
    #[verifier::spinoff_prover]
    pub fn owl_get_sender_i(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
    ) -> (res: Result<
        (OwlBuf, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == get_sender_i_spec(*self, *old(mut_state)),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview(), *mut_state),
            ),
            res.is_Ok() ==> res.get_Ok_0().0.len_valid(),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let v = self.device.as_ref().unwrap().get_singleton_id();
            (OwlBuf::from_vec(v.to_le_bytes().to_vec()), Tracked(itree))
        };
        Ok(res_inner)
    }
}

pub struct state_Responder {
    pub owl_aead_counter_msg2_C7: usize,
    pub owl_N_resp_recv: usize,
    pub owl_N_resp_send: usize,
}

impl state_Responder {
    #[verifier(external_body)]
    pub fn init_state_Responder() -> Self {
        state_Responder { owl_aead_counter_msg2_C7: 0, owl_N_resp_recv: 0, owl_N_resp_send: 0 }
    }
}

pub struct cfg_Responder<O> {
    pub salt: Vec<u8>,
    pub owl_S_resp: Vec<u8>,
    pub owl_E_resp: Vec<u8>,
    pub pk_owl_S_resp: Vec<u8>,
    pub pk_owl_S_init: Vec<u8>,
    pub pk_owl_E_resp: Vec<u8>,
    pub pk_owl_E_init: Vec<u8>,
    pub device: Option<crate::wireguard::handshake::device::DeviceInner<O>>,
}

impl<O> cfg_Responder<O> {
    pub exec fn owl_transp_send_resp_wrapper<'a>(
        &'a self,         
        mut_state: &'a mut state_Responder,
        owl_plaintext: &'a [u8],
        obuf: &'a mut [u8],
        owl_tkr_msg2_receiver: &'a [u8],
        owl_tkr_msg2_sender: &'a [u8],
        owl_tkr_recvd: bool,
        owl_tkr_k_init_send: &'a [u8],
        owl_tkr_k_resp_send: &'a [u8],
    ) -> Option<()> {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let owl_transp_keys_val = owl_transp_keys_resp {
            owl_tkr_msg2_receiver: OwlBuf::from_slice(owl_tkr_msg2_receiver),
            owl_tkr_msg2_sender: OwlBuf::from_slice(owl_tkr_msg2_sender),
            owl_tkr_has_psk: false,
            owl_tkr_eph: Ghost(()),
            owl_tkr_c7: Ghost(()),
            owl_tkr_recvd: owl_tkr_recvd,
            owl_tkr_k_init_send: OwlBuf::from_slice(owl_tkr_k_init_send),
            owl_tkr_k_resp_send: OwlBuf::from_slice(owl_tkr_k_resp_send),
        };
        let (res, _) =
            self.owl_resp_send(Tracked(call_token), mut_state, owl_transp_keys_val, OwlBuf::from_slice(owl_plaintext), obuf).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_resp_send<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_tki404: owl_transp_keys_resp<'a>,
        owl_msg405: OwlBuf<'a>,
        obuf: &'a mut [u8],
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == resp_send_spec(
                *self,
                *old(mut_state),
                owl_tki404.view(),
                owl_msg405.view(),
            ),
            owl_tki404.len_valid(),
            owl_msg405.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<()>,
            Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(resp_send_spec);
            let owl_tki_364 = { owl_tki404 };
            let parseval = owl_tki_364;
            let owl_init372 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_receiver);
            let owl_resp371 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_sender);
            let owl_haspsk370 = parseval.owl_tkr_has_psk;
            let owl_eph369 = parseval.owl_tkr_eph;
            let owl_c7368 = parseval.owl_tkr_c7;
            let owl_b367 = parseval.owl_tkr_recvd;
            let owl_init_send366 = OwlBuf::another_ref(&parseval.owl_tkr_k_init_send);
            let owl_resp_send365 = OwlBuf::another_ref(&parseval.owl_tkr_k_resp_send);
            if owl_b367 {
                {
                    let owl__373 = {
                        let owl__374 = {
                            let owl__assert_91375 = { owl_ghost_unit() };
                            owl_ghost_unit()
                        };
                        owl_ghost_unit()
                    };
                    let tmp_owl_transp_counter376 = {
                        owl_counter_as_bytes(&mut_state.owl_N_resp_send)
                    };
                    let owl_transp_counter376 = OwlBuf::from_slice(&tmp_owl_transp_counter376);
                    let owl_c377 = {
                        {
                            match owl_enc_st_aead(
                                owl_resp_send365.as_slice(),
                                owl_msg405.as_slice(),
                                &mut mut_state.owl_N_resp_send,
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }.as_slice(),
                            ) {
                                Ok(ctxt) => { OwlBuf::from_vec(ctxt) },
                                Err(e) => { return Err(e) },
                            }
                        }
                    };
                    let owl_transp_tag378 = { owl_transp_tag_value() };
                    let owl_o379 = {
                        owl_transp(
                            (),
                            OwlBuf::another_ref(&owl_resp371),
                            OwlBuf::another_ref(&owl_transp_counter376),
                            OwlBuf::another_ref(&owl_c377),
                        )
                    };
                    let owl__380 = {
                        owl_output::<(Option<()>, state_Responder)>(
                            Tracked(&mut itree),
                            serialize_owl_transp(&owl_o379).as_slice(),
                            &Initiator_addr(),
                            &Responder_addr(),
                            obuf
                        );
                    };
                    (Some(owl_unit()), Tracked(itree))
                }
            } else {
                (None, Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }

    pub exec fn owl_transp_recv_resp_wrapper<'a>(
        &'a self,         
        mut_state: &mut state_Responder,
        ibuf: &'a [u8],
        owl_tkr_msg2_receiver: &'a [u8],
        owl_tkr_msg2_sender: &'a [u8],
        owl_tkr_recvd: bool,
        owl_tkr_k_init_send: &'a [u8],
        owl_tkr_k_resp_send: &'a [u8],
    ) -> Option<OwlBuf<'a>> {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_recv_resp_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let owl_transp_keys_val = owl_transp_keys_resp {
            owl_tkr_msg2_receiver: OwlBuf::from_slice(owl_tkr_msg2_receiver),
            owl_tkr_msg2_sender: OwlBuf::from_slice(owl_tkr_msg2_sender),
            owl_tkr_has_psk: false,
            owl_tkr_eph: Ghost(()),
            owl_tkr_c7: Ghost(()),
            owl_tkr_recvd: owl_tkr_recvd,
            owl_tkr_k_init_send: OwlBuf::from_slice(owl_tkr_k_init_send),
            owl_tkr_k_resp_send: OwlBuf::from_slice(owl_tkr_k_resp_send),
        };
        let (res, _) =
            self.owl_resp_recv(Tracked(call_token), mut_state, owl_transp_keys_val, ibuf).unwrap();
        res.map(move |resp_result| resp_result.owl_rr_msg)
    }    

    #[verifier::spinoff_prover]
    pub fn owl_resp_recv<'a>(
        &'a self,
        Tracked(itree): Tracked<
            ITreeToken<(Option<owlSpec_resp_transp_recv_result>, state_Responder), Endpoint>,
        >,
        mut_state: &mut state_Responder,
        owl_tki406: owl_transp_keys_resp<'a>,
        ibuf: &'a [u8],
    ) -> (res: Result<
        (
            Option<owl_resp_transp_recv_result<'a>>,
            Tracked<
                ITreeToken<(Option<owlSpec_resp_transp_recv_result>, state_Responder), Endpoint>,
            >,
        ),
        OwlError,
    >)
        requires
            itree.view() == resp_recv_spec(*self, *old(mut_state), owl_tki406.view()),
            owl_tki406.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
            res matches Ok((Some(b), _)) ==> b.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_resp_transp_recv_result<'a>>,
            Tracked<
                ITreeToken<(Option<owlSpec_resp_transp_recv_result>, state_Responder), Endpoint>,
            >,
        ) = {
            broadcast use itree_axioms;

            reveal(resp_recv_spec);
            let (tmp_owl_i383, owl__382) = {
                owl_input::<(Option<owlSpec_resp_transp_recv_result>, state_Responder)>(
                    Tracked(&mut itree),
                    ibuf
                )
            };
            let owl_i383 = OwlBuf::from_slice(tmp_owl_i383);
            let owl_tki_384 = { owl_tki406 };
            let parseval = owl_tki_384;
            let owl_init392 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_receiver);
            let owl_resp391 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_sender);
            let owl_haspsk390 = parseval.owl_tkr_has_psk;
            let owl_eph389 = parseval.owl_tkr_eph;
            let owl_c7388 = parseval.owl_tkr_c7;
            let owl__387 = parseval.owl_tkr_recvd;
            let owl_init_send386 = OwlBuf::another_ref(&parseval.owl_tkr_k_init_send);
            let owl_resp_send385 = OwlBuf::another_ref(&parseval.owl_tkr_k_resp_send);
            let parseval_tmp = OwlBuf::another_ref(&owl_i383);
            if let Some(parseval) = parse_owl_transp(parseval_tmp.as_slice()) {
                let owl_tag396 = parseval.owl__transp_tag;
                let owl_from395 = OwlBuf::another_ref(&parseval.owl__transp_receiver);
                let owl_ctr394 = OwlBuf::another_ref(&parseval.owl__transp_counter);
                let owl_pkt393 = OwlBuf::another_ref(&parseval.owl__transp_packet);
                {
                    if { slice_eq(owl_from395.as_slice(), owl_init392.as_slice()) } {
                        let tmp_owl_caseval397 = {
                            owl_dec_st_aead(
                                owl_init_send386.as_slice(),
                                owl_pkt393.as_slice(),
                                owl_ctr394.as_slice(),
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }.as_slice(),
                            )
                        };
                        let owl_caseval397 = OwlBuf::from_vec_option(tmp_owl_caseval397);
                        match owl_caseval397 {
                            Option::Some(tmp_owl_x398) => {
                                let owl_x398 = OwlBuf::another_ref(&tmp_owl_x398);
                                let owl_st_399 = {
                                    owl_transp_keys_resp(
                                        OwlBuf::another_ref(&owl_init392),
                                        OwlBuf::another_ref(&owl_resp391),
                                        owl_haspsk390,
                                        owl_ghost_unit(),
                                        owl_ghost_unit(),
                                        true,
                                        OwlBuf::another_ref(&owl_init_send386),
                                        OwlBuf::another_ref(&owl_resp_send385),
                                    )
                                };
                                let owl_ret400 = {
                                    owl_resp_transp_recv_result(
                                        owl_st_399,
                                        OwlBuf::another_ref(&owl_x398),
                                    )
                                };
                                (Some(owl_ret400), Tracked(itree))
                            },
                            Option::None => { (None, Tracked(itree)) },
                        }
                    } else {
                        (None, Tracked(itree))
                    }
                }
            } else {
                (None, Tracked(itree))
            }
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier(external_body)]
    #[verifier::spinoff_prover]
    pub fn owl_timestamp_r(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
    ) -> (res: Result<
        (OwlBuf, Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == timestamp_r_spec(*self, *old(mut_state)),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview(), *mut_state),
            ),
            res.is_Ok() ==> res.get_Ok_0().0.len_valid(),
    {
        let tracked mut itree = itree;
        let res_inner = { todo!(/* implement owl_timestamp_r */) };
        Ok(res_inner)
    }

    #[verifier(external_body)]
    #[verifier::spinoff_prover]
    pub fn owl_get_sender_r(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
    ) -> (res: Result<
        (OwlBuf, Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == get_sender_r_spec(*self, *old(mut_state)),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview(), *mut_state),
            ),
            res.is_Ok() ==> res.get_Ok_0().0.len_valid(),
    {
        let tracked mut itree = itree;
        let res_inner = { todo!(/* implement owl_get_sender_r */) };
        Ok(res_inner)
    }
}


// ------------------------------------
// ------ USER-DEFINED FUNCTIONS ------
// ------------------------------------
#[verifier::opaque]
pub closed spec fn transp_tag_value() -> Seq<u8> {
    seq![0x04u8, 0x00u8, 0x00u8, 0x00u8, ]
}

pub fn owl_transp_tag_value<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.dview() == transp_tag_value(),
        res.len_valid(),
{
    reveal(transp_tag_value);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x04u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

// ------------------------------------
// ------------ ENTRY POINT -----------
// ------------------------------------
// no entry point

} // verus!
