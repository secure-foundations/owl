// Extracted verus code from file tests/wip/wg/transp.owl:
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_braces)]
#![allow(unused_parens)]



use vstd::{modes::*, prelude::*, seq::*, string::*, slice::*};
use crate::wireguard::owl_wg::speclib::{*, itree::*};
use crate::wireguard::owl_wg::execlib::{*};
use crate::wireguard::owl_wg::*;
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
    dest_addr: &str,
    ret_addr: &str,
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
        comb.spec_serialize(val.view()) matches Ok(b) ==> 
            old(t).view().is_output(b, endpoint_of_addr(dest_addr.view())),
    ensures
        t.view() == old(t).view().give_output(),
        comb.spec_serialize(val.view()) matches Ok(b) ==> obuf.view() == b,
{
    let ser_result = comb.serialize(val, obuf, 0);
    assume(ser_result.is_ok());
    if let Ok((num_written)) = ser_result {
        vec_truncate(obuf, num_written);
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

pub struct owlSpec_init_sent_state {
    pub owlSpec_iss_c2: Ghost<()>,
    pub owlSpec_iss_psk: owlSpec_PSKMode,
    pub owlSpec_iss_static_ss: Ghost<()>,
    pub owlSpec_ss_h4: Seq<u8>,
    pub owlSpec_iss_c3: Seq<u8>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_init_sent_state(x: Seq<u8>) -> Option<owlSpec_init_sent_state> {
    // cant autogenerate vest parser
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_init_sent_state(x: owlSpec_init_sent_state) -> Seq<u8> {
    // cant autogenerate vest serializer
    todo!()
}

impl OwlSpecSerialize for owlSpec_init_sent_state {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_init_sent_state(self)
    }
}

pub open spec fn init_sent_state(
    arg_owlSpec_iss_c2: Ghost<()>,
    arg_owlSpec_iss_psk: owlSpec_PSKMode,
    arg_owlSpec_iss_static_ss: Ghost<()>,
    arg_owlSpec_ss_h4: Seq<u8>,
    arg_owlSpec_iss_c3: Seq<u8>,
) -> owlSpec_init_sent_state {
    owlSpec_init_sent_state {
        owlSpec_iss_c2: arg_owlSpec_iss_c2,
        owlSpec_iss_psk: arg_owlSpec_iss_psk,
        owlSpec_iss_static_ss: arg_owlSpec_iss_static_ss,
        owlSpec_ss_h4: arg_owlSpec_ss_h4,
        owlSpec_iss_c3: arg_owlSpec_iss_c3,
    }
}

pub struct owlSpec_init_info {
    pub owlSpec_init_info_ss: Seq<u8>,
    pub owlSpec_init_info_psk: owlSpec_PSKMode,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_init_info(x: Seq<u8>) -> Option<owlSpec_init_info> {
    // cant autogenerate vest parser
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_init_info(x: owlSpec_init_info) -> Seq<u8> {
    // cant autogenerate vest serializer
    todo!()
}

impl OwlSpecSerialize for owlSpec_init_info {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_init_info(self)
    }
}

pub open spec fn init_info(
    arg_owlSpec_init_info_ss: Seq<u8>,
    arg_owlSpec_init_info_psk: owlSpec_PSKMode,
) -> owlSpec_init_info {
    owlSpec_init_info {
        owlSpec_init_info_ss: arg_owlSpec_init_info_ss,
        owlSpec_init_info_psk: arg_owlSpec_init_info_psk,
    }
}

pub struct owlSpec_resp_received_state {
    pub owlSpec_rrs_msg1_sender: Seq<u8>,
    pub owlSpec_rrs_psk: owlSpec_PSKMode,
    pub owlSpec_rrs_dhpk_S_init: Seq<u8>,
    pub owlSpec_rrs_msg1_ephemeral: Seq<u8>,
    pub owlSpec_rrs_c2: Ghost<()>,
    pub owlSpec_rrs_h4: Seq<u8>,
    pub owlSpec_rrs_c3: Seq<u8>,
}

#[verifier::external_body]
pub closed spec fn parse_owlSpec_resp_received_state(x: Seq<u8>) -> Option<
    owlSpec_resp_received_state,
> {
    // cant autogenerate vest parser
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_resp_received_state(x: owlSpec_resp_received_state) -> Seq<
    u8,
> {
    // cant autogenerate vest serializer
    todo!()
}

impl OwlSpecSerialize for owlSpec_resp_received_state {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_resp_received_state(self)
    }
}

pub open spec fn resp_received_state(
    arg_owlSpec_rrs_msg1_sender: Seq<u8>,
    arg_owlSpec_rrs_psk: owlSpec_PSKMode,
    arg_owlSpec_rrs_dhpk_S_init: Seq<u8>,
    arg_owlSpec_rrs_msg1_ephemeral: Seq<u8>,
    arg_owlSpec_rrs_c2: Ghost<()>,
    arg_owlSpec_rrs_h4: Seq<u8>,
    arg_owlSpec_rrs_c3: Seq<u8>,
) -> owlSpec_resp_received_state {
    owlSpec_resp_received_state {
        owlSpec_rrs_msg1_sender: arg_owlSpec_rrs_msg1_sender,
        owlSpec_rrs_psk: arg_owlSpec_rrs_psk,
        owlSpec_rrs_dhpk_S_init: arg_owlSpec_rrs_dhpk_S_init,
        owlSpec_rrs_msg1_ephemeral: arg_owlSpec_rrs_msg1_ephemeral,
        owlSpec_rrs_c2: arg_owlSpec_rrs_c2,
        owlSpec_rrs_h4: arg_owlSpec_rrs_h4,
        owlSpec_rrs_c3: arg_owlSpec_rrs_c3,
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
        (input(i,_133)) in
(parse (tki) as (owlSpec_transp_keys_init{owlSpec_tki_msg2_receiver : init, owlSpec_tki_msg2_sender : resp, owlSpec_tki_has_psk : haspsk, owlSpec_tki_eph : eph, owlSpec_tki_c7 : c7, owlSpec_tki_k_init_send : init_send, owlSpec_tki_k_resp_send : resp_send}) in {
(parse (parse_owlSpec_transp(i)) as (owlSpec_transp{owlSpec__transp_tag : tag, owlSpec__transp_receiver : from, owlSpec__transp_counter : ctr, owlSpec__transp_packet : pkt}) in {
(if (from == resp) then
(let p = ((ret(dec_st_aead(resp_send, pkt, ctr, empty_seq_u8())))) in
(ret(p)))
else
((ret(Option::None))))
} otherwise ((ret(Option::None))))
} )
    )
}

#[verifier::opaque]
pub open spec fn init_dummy_spec(cfg: cfg_Initiator, mut_state: state_Initiator) -> (res: ITree<
    ((), state_Initiator),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Initiator,
        (ret(()))
    )
}

#[verifier::opaque]
pub open spec fn init_stage2_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    st: owlSpec_init_sent_state,
) -> (res: ITree<(Option<owlSpec_transp_keys_init>, state_Initiator), Endpoint>) {
    owl_spec!(mut_state, state_Initiator,
        (parse (st) as (owlSpec_init_sent_state{owlSpec_iss_c2 : c2, owlSpec_iss_psk : opsk, owlSpec_iss_static_ss : static_ss, owlSpec_ss_h4 : h4, owlSpec_iss_c3 : c3}) in {
(input(i,_187)) in
(parse (parse_owlSpec_msg2(i)) as (owlSpec_msg2{owlSpec__msg2_tag : msg2_tag, owlSpec__msg2_sender : msg2_sender, owlSpec__msg2_receiver : msg2_receiver, owlSpec__msg2_ephemeral : msg2_ephemeral, owlSpec__msg2_empty : msg2_empty_enc, owlSpec__msg2_mac1 : msg2_mac1, owlSpec__msg2_mac2 : msg2_mac2}) in {
(if (andb(length(msg2_sender) == 4, length(msg2_receiver) == 4)) then
((if (is_group_elem(msg2_ephemeral)) then
(let e_init = ((ret(cfg.owl_E_init.view()))) in
let kdfval207 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, c3, msg2_ephemeral, empty_seq_u8())))) in
let c4 = ((ret(Seq::subrange(kdfval207, 0, 0 + KDFKEY_SIZE)))) in
let h5 = ((ret(crh(concat(h4, msg2_ephemeral))))) in
let ss = ((ret(dh_combine(msg2_ephemeral, e_init)))) in
let kdfval219 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, c4, ss, empty_seq_u8())))) in
let c5 = ((ret(Seq::subrange(kdfval219, 0, 0 + KDFKEY_SIZE)))) in
let kdfval232 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, c5, dh_combine(msg2_ephemeral, cfg.owl_S_init.view()), empty_seq_u8())))) in
let c6 = ((ret(Seq::subrange(kdfval232, 0, 0 + KDFKEY_SIZE)))) in
let psk = (let caseval = ((ret(opsk))) in
(case (caseval) {
| owlSpec_HasPSK(v) => {
(ret(v))
},
| owlSpec_NoPSK() => {
(ret(zeros_32()))
},
}
)) in
let kdfval241 = ((ret(kdf((0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE) as usize, c6, psk, empty_seq_u8())))) in
let c7 = ((ret(Seq::subrange(kdfval241, 0, 0 + KDFKEY_SIZE)))) in
let tau = ((ret(Seq::subrange(kdfval241, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + NONCE_SIZE)))) in
let k0 = ((ret(Seq::subrange(kdfval241, 0 + KDFKEY_SIZE + NONCE_SIZE, 0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE)))) in
let h6 = ((ret(crh(concat(h5, tau))))) in
let parseval = ((ret(dec_st_aead(k0, msg2_empty_enc, empty_seq_u8(), h6)))) in
let caseval = ((ret(parseval))) in
(case (caseval) {
| None => {
(ret(Option::None))
},
| Some(x) => {
let kdfval250 = ((ret(kdf((0 + ENCKEY_SIZE + ENCKEY_SIZE) as usize, c7, empty_seq_u8(), empty_seq_u8())))) in
let k1 = ((ret(Seq::subrange(kdfval250, 0, 0 + ENCKEY_SIZE)))) in
let k2 = ((ret(Seq::subrange(kdfval250, 0 + ENCKEY_SIZE, 0 + ENCKEY_SIZE + ENCKEY_SIZE)))) in
(ret(Option::Some(transp_keys_init(msg2_receiver, msg2_sender, HasPSK_enumtest(opsk), ghost_unit(), ghost_unit(), k1, k2))))
},
}
))
else
((ret(Option::None)))))
else
((ret(Option::None))))
} otherwise ((ret(Option::None))))
} )
    )
}

#[verifier::opaque]
pub open spec fn init_stage1_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    dhpk_S_resp: Seq<u8>,
    dhpk_S_init: Seq<u8>,
    ss_S_resp_S_init: Seq<u8>,
    psk: owlSpec_PSKMode,
) -> (res: ITree<(owlSpec_init_sent_state, state_Initiator), Endpoint>) {
    owl_spec!(mut_state, state_Initiator,
        let C0 = ((ret(crh(construction())))) in
let H0 = ((ret(crh(concat(C0, identifier()))))) in
let H1 = ((ret(crh(concat(H0, dhpk_S_resp))))) in
let e_init = ((ret(dhpk(cfg.owl_E_init.view())))) in
let kdfval266 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, C0, e_init, empty_seq_u8())))) in
let C1 = ((ret(Seq::subrange(kdfval266, 0, 0 + KDFKEY_SIZE)))) in
let H2 = ((ret(crh(concat(H1, e_init))))) in
let ss_S_resp_E_init = ((ret(dh_combine(dhpk_S_resp, cfg.owl_E_init.view())))) in
let kdfval271 = ((ret(kdf((0 + KDFKEY_SIZE + ENCKEY_SIZE) as usize, C1, ss_S_resp_E_init, empty_seq_u8())))) in
let C2 = ((ret(Seq::subrange(kdfval271, 0, 0 + KDFKEY_SIZE)))) in
let k0 = ((ret(Seq::subrange(kdfval271, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + ENCKEY_SIZE)))) in
let msg1_static = ((ret(enc_st_aead(k0, dhpk_S_init, owl_aead_counter_msg1_C2, H2)))) in
let H3 = ((ret(crh(concat(H2, msg1_static))))) in
let kdfval277 = ((ret(kdf((0 + KDFKEY_SIZE + ENCKEY_SIZE) as usize, C2, ss_S_resp_S_init, empty_seq_u8())))) in
let c3 = ((ret(Seq::subrange(kdfval277, 0, 0 + KDFKEY_SIZE)))) in
let k1 = ((ret(Seq::subrange(kdfval277, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + ENCKEY_SIZE)))) in
let timestamp = (call(timestamp_i_spec(cfg, mut_state))) in
let msg1_timestamp = ((ret(enc_st_aead(k1, timestamp, owl_aead_counter_msg1_C3, H3)))) in
let h4 = ((ret(crh(concat(H3, msg1_timestamp))))) in
let msg1_sender = (call(get_sender_i_spec(cfg, mut_state))) in
let msg1_tag = ((ret(msg1_tag_value()))) in
let msg1_mac1_k = ((ret(crh(concat(mac1(), dhpk_S_resp))))) in
let msg1_mac1 = ((ret(mac(msg1_mac1_k, concat(concat(concat(concat(msg1_tag, msg1_sender), e_init), msg1_static), msg1_timestamp))))) in
let msg1_mac2 = ((ret(zeros_16()))) in
let msg1_output = ((ret(msg1((), msg1_sender, e_init, msg1_static, msg1_timestamp, msg1_mac1, ())))) in
(output (serialize_owlSpec_msg1(msg1_output)) to (Endpoint::Loc_Responder)) in
(ret(init_sent_state(ghost_unit(), psk, ghost_unit(), h4, c3)))
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
(if (b) then
(let transp_counter = ((ret(counter_as_bytes(mut_state.owl_N_resp_send)))) in
let c = ((ret(enc_st_aead(resp_send, msg, owl_N_resp_send, empty_seq_u8())))) in
let transp_tag = ((ret(transp_tag_value()))) in
let o = ((ret(transp((), resp, transp_counter, c)))) in
(output (serialize_owlSpec_transp(o)) to (Endpoint::Loc_Initiator)) in
(ret(Option::Some(()))))
else
((ret(Option::None))))
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
        (input(i,_352)) in
let tki_ = ((ret(tki))) in
(parse (tki_) as (owlSpec_transp_keys_resp{owlSpec_tkr_msg2_receiver : init, owlSpec_tkr_msg2_sender : resp, owlSpec_tkr_has_psk : haspsk, owlSpec_tkr_eph : eph, owlSpec_tkr_c7 : c7, owlSpec_tkr_recvd : _unused713, owlSpec_tkr_k_init_send : init_send, owlSpec_tkr_k_resp_send : resp_send}) in {
(parse (parse_owlSpec_transp(i)) as (owlSpec_transp{owlSpec__transp_tag : tag, owlSpec__transp_receiver : from, owlSpec__transp_counter : ctr, owlSpec__transp_packet : pkt}) in {
(if (from == init) then
(let caseval = ((ret(dec_st_aead(init_send, pkt, ctr, empty_seq_u8())))) in
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
))
else
((ret(Option::None))))
} otherwise ((ret(Option::None))))
} )
    )
}

#[verifier::opaque]
pub open spec fn resp_dummy_spec(cfg: cfg_Responder, mut_state: state_Responder) -> (res: ITree<
    ((), state_Responder),
    Endpoint,
>) {
    owl_spec!(mut_state, state_Responder,
        (ret(()))
    )
}

#[verifier::opaque]
pub open spec fn resp_stage2_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    st: owlSpec_resp_received_state,
) -> (res: ITree<(Option<owlSpec_transp_keys_resp>, state_Responder), Endpoint>) {
    owl_spec!(mut_state, state_Responder,
        let st_ = ((ret(st))) in
let st__ = ((ret(st_))) in
(parse (st__) as (owlSpec_resp_received_state{owlSpec_rrs_msg1_sender : msg2_receiver, owlSpec_rrs_psk : psk, owlSpec_rrs_dhpk_S_init : dhpk_S_init, owlSpec_rrs_msg1_ephemeral : msg1_ephemeral, owlSpec_rrs_c2 : C2, owlSpec_rrs_h4 : H4, owlSpec_rrs_c3 : C3}) in {
let e_resp_pk = ((ret(dhpk(cfg.owl_E_resp.view())))) in
let kdfval471 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, C3, e_resp_pk, empty_seq_u8())))) in
let c4 = ((ret(Seq::subrange(kdfval471, 0, 0 + KDFKEY_SIZE)))) in
let h5 = ((ret(crh(concat(H4, e_resp_pk))))) in
let ss = ((ret(dh_combine(msg1_ephemeral, cfg.owl_E_resp.view())))) in
let kdfval484 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, c4, ss, empty_seq_u8())))) in
let c5 = ((ret(Seq::subrange(kdfval484, 0, 0 + KDFKEY_SIZE)))) in
let kdfval491 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, c5, dh_combine(dhpk_S_init, cfg.owl_E_resp.view()), empty_seq_u8())))) in
let c6 = ((ret(Seq::subrange(kdfval491, 0, 0 + KDFKEY_SIZE)))) in
let psk_val = (let caseval = ((ret(psk))) in
(case (caseval) {
| owlSpec_HasPSK(v) => {
(ret(v))
},
| owlSpec_NoPSK() => {
(ret(zeros_32()))
},
}
)) in
let kdfval500 = ((ret(kdf((0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE) as usize, c6, psk_val, empty_seq_u8())))) in
let c7 = ((ret(Seq::subrange(kdfval500, 0, 0 + KDFKEY_SIZE)))) in
let tau = ((ret(Seq::subrange(kdfval500, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + NONCE_SIZE)))) in
let k0 = ((ret(Seq::subrange(kdfval500, 0 + KDFKEY_SIZE + NONCE_SIZE, 0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE)))) in
let msg2_tag = ((ret(msg2_tag_value()))) in
let msg2_sender = (call(get_sender_r_spec(cfg, mut_state))) in
let msg2_mac1_k = ((ret(crh(concat(mac1(), dhpk_S_init))))) in
let msg2_receiver = ((ret(seq![0x00u8, 0x00u8, 0x00u8, 0x00u8, ]))) in
let h6 = ((ret(crh(concat(h5, tau))))) in
let msg2_empty = ((ret(enc_st_aead(k0, empty_seq_u8(), owl_aead_counter_msg2_C7, h6)))) in
let msg2_mac1 = ((ret(mac(msg2_mac1_k, concat(concat(concat(concat(msg2_tag, msg2_sender), msg2_receiver), e_resp_pk), msg2_empty))))) in
let _assert_267 = ((ret(ghost_unit()))) in
let msg2_mac2 = ((ret(zeros_16()))) in
let msg2_output = ((ret(msg2((), msg2_sender, msg2_receiver, e_resp_pk, msg2_empty, msg2_mac1, ())))) in
(output (serialize_owlSpec_msg2(msg2_output)) to (Endpoint::Loc_Initiator)) in
let kdfval517 = ((ret(kdf((0 + ENCKEY_SIZE + ENCKEY_SIZE) as usize, c7, empty_seq_u8(), empty_seq_u8())))) in
let tk1 = ((ret(Seq::subrange(kdfval517, 0, 0 + ENCKEY_SIZE)))) in
let tk2 = ((ret(Seq::subrange(kdfval517, 0 + ENCKEY_SIZE, 0 + ENCKEY_SIZE + ENCKEY_SIZE)))) in
let ret = ((ret(transp_keys_resp(msg2_receiver, msg2_sender, HasPSK_enumtest(psk), ghost_unit(), ghost_unit(), false, tk1, tk2)))) in
(ret(Option::Some(ret)))
} )
    )
}

#[verifier::opaque]
pub open spec fn resp_stage1_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    dhpk_S_resp: Seq<u8>,
) -> (res: ITree<(Option<owlSpec_resp_received_state>, state_Responder), Endpoint>) {
    owl_spec!(mut_state, state_Responder,
        (input(inp,_523)) in
(parse (parse_owlSpec_msg1(inp)) as (owlSpec_msg1{owlSpec__msg1_tag : msg1_tag, owlSpec__msg1_sender : msg1_sender, owlSpec__msg1_ephemeral : msg1_ephemeral, owlSpec__msg1_static : msg1_static, owlSpec__msg1_timestamp : msg1_timestamp, owlSpec__msg1_mac1 : msg1_mac1, owlSpec__msg1_mac2 : msg1_mac2}) in {
(if (length(msg1_sender) == 4) then
((if (is_group_elem(msg1_ephemeral)) then
(let C0 = ((ret(crh(construction())))) in
let H0 = ((ret(crh(concat(C0, identifier()))))) in
let H1 = ((ret(crh(concat(H0, dhpk_S_resp))))) in
let kdfval545 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, C0, msg1_ephemeral, empty_seq_u8())))) in
let C1 = ((ret(Seq::subrange(kdfval545, 0, 0 + KDFKEY_SIZE)))) in
let H2 = ((ret(crh(concat(H1, msg1_ephemeral))))) in
let ss_msg1_ephemeral_S_resp = ((ret(dh_combine(msg1_ephemeral, cfg.owl_S_resp.view())))) in
let kdfval555 = ((ret(kdf((0 + KDFKEY_SIZE + ENCKEY_SIZE) as usize, C1, ss_msg1_ephemeral_S_resp, empty_seq_u8())))) in
let C2 = ((ret(Seq::subrange(kdfval555, 0, 0 + KDFKEY_SIZE)))) in
let k0 = ((ret(Seq::subrange(kdfval555, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + ENCKEY_SIZE)))) in
let parseval = ((ret(dec_st_aead(k0, msg1_static, empty_seq_u8(), H2)))) in
let caseval = ((ret(parseval))) in
(case (caseval) {
| None => {
(ret(Option::None))
},
| Some(msg1_static_dec) => {
let oinfo = (call(get_pk_info_spec(cfg, mut_state, msg1_static_dec))) in
let caseval = ((ret(oinfo))) in
(case (caseval) {
| None => {
(ret(Option::None))
},
| Some(info) => {
let info = ((ret(info))) in
(parse (info) as (owlSpec_init_info{owlSpec_init_info_ss : ss, owlSpec_init_info_psk : psk}) in {
let H3 = ((ret(crh(concat(H2, msg1_static))))) in
let dhpk_S_init = ((ret(msg1_static_dec))) in
let kdfval589 = ((ret(kdf((0 + KDFKEY_SIZE + ENCKEY_SIZE) as usize, C2, ss, empty_seq_u8())))) in
let C3 = ((ret(Seq::subrange(kdfval589, 0, 0 + KDFKEY_SIZE)))) in
let k1 = ((ret(Seq::subrange(kdfval589, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + ENCKEY_SIZE)))) in
let parseval = ((ret(dec_st_aead(k1, msg1_timestamp, empty_seq_u8(), H3)))) in
let caseval = ((ret(parseval))) in
(case (caseval) {
| None => {
(ret(Option::None))
},
| Some(msg1_timestamp_dec) => {
let H4 = ((ret(crh(concat(H3, msg1_timestamp))))) in
let st = ((ret(resp_received_state(msg1_sender, psk, dhpk_S_init, msg1_ephemeral, ghost_unit(), H4, C3)))) in
let y = ((ret(st))) in
(ret(Option::Some(y)))
},
}
)
} )
},
}
)
},
}
))
else
((ret(Option::None)))))
else
((ret(Option::None))))
} otherwise ((ret(Option::None))))
    )
}

#[verifier::opaque]
pub open spec fn get_pk_info_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    pk: Seq<u8>,
) -> (res: ITree<(Option<owlSpec_init_info>, state_Responder), Endpoint>) {
    owl_spec!(mut_state, state_Responder,
        (ret(get_pk_info_pure(pk)))
    )
}

#[verifier(external_body)]
pub closed spec fn get_pk_info_pure(pk: Seq<u8>) -> Option<owlSpec_init_info> {
    unimplemented!()
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
pub closed spec fn construction() -> (res: Seq<u8>) {
    seq![0x4eu8, 0x6fu8, 0x69u8, 0x73u8, 0x65u8, 0x5fu8, 0x49u8, 0x4bu8, 0x70u8, 0x73u8, 0x6bu8, 0x32u8, 0x5fu8, 0x32u8, 0x35u8, 0x35u8, 0x31u8, 0x39u8, 0x5fu8, 0x43u8, 0x68u8, 0x61u8, 0x43u8, 0x68u8, 0x61u8, 0x50u8, 0x6fu8, 0x6cu8, 0x79u8, 0x5fu8, 0x42u8, 0x4cu8, 0x41u8, 0x4bu8, 0x45u8, 0x32u8, 0x73u8, ]
}

#[verifier::opaque]
pub closed spec fn honest_c1() -> (res: Ghost<()>) {
    ghost_unit()
}

#[verifier::opaque]
pub closed spec fn honest_c3() -> (res: Ghost<()>) {
    ghost_unit()
}

#[verifier::opaque]
pub closed spec fn honest_c4() -> (res: Ghost<()>) {
    ghost_unit()
}

#[verifier::opaque]
pub closed spec fn identifier() -> (res: Seq<u8>) {
    seq![0x57u8, 0x69u8, 0x72u8, 0x65u8, 0x47u8, 0x75u8, 0x61u8, 0x72u8, 0x64u8, 0x20u8, 0x76u8, 0x31u8, 0x20u8, 0x7au8, 0x78u8, 0x32u8, 0x63u8, 0x34u8, 0x20u8, 0x4au8, 0x61u8, 0x73u8, 0x6fu8, 0x6eu8, 0x40u8, 0x7au8, 0x78u8, 0x32u8, 0x63u8, 0x34u8, 0x2eu8, 0x63u8, 0x6fu8, 0x6du8, ]
}

#[verifier::opaque]
pub closed spec fn mac1() -> (res: Seq<u8>) {
    seq![0x6du8, 0x61u8, 0x63u8, 0x31u8, 0x2du8, 0x2du8, 0x2du8, 0x2du8, ]
}

#[verifier::opaque]
pub closed spec fn msg1_tag_value() -> (res: Seq<u8>) {
    seq![0x01u8, 0x00u8, 0x00u8, 0x00u8, ]
}

#[verifier::opaque]
pub closed spec fn msg2_tag_value() -> (res: Seq<u8>) {
    seq![0x02u8, 0x00u8, 0x00u8, 0x00u8, ]
}

#[verifier::opaque]
pub closed spec fn transp_tag_value() -> (res: Seq<u8>) {
    seq![0x04u8, 0x00u8, 0x00u8, 0x00u8, ]
}

#[verifier::opaque]
pub closed spec fn zeros_16() -> (res: Seq<u8>) {
    seq![0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, ]
}

#[verifier::opaque]
pub closed spec fn zeros_32() -> (res: Seq<u8>) {
    seq![0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, ]
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
pub const fn Initiator_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_Initiator,
{
    "127.0.0.1:9001"
}

#[verifier(external_body)]
pub const fn Responder_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_Responder,
{
    "127.0.0.1:9002"
}

#[verifier(external_body)]
pub const fn nobody_addr() -> (a: &'static str)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_nobody,
{
    "127.0.0.1:9003"
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

pub exec fn parse_owl_msg1<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg1<'a>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_msg1(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg1(arg.view())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_msg1);
    let exec_comb = exec_combinator_owl_msg1();
    match arg {
        OwlBuf::Borrowed(s) => {
            if let Ok((_, parsed)) = exec_comb.parse(s) {
                let (
                    (
                        (
                            (
                                ((owl__msg1_tag, owl__msg1_sender), owl__msg1_ephemeral),
                                owl__msg1_static,
                            ),
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
        },
        OwlBuf::Owned(v, start, len) => {
            reveal(OwlBuf::len_valid);
            if let Ok((_, parsed)) = exec_comb.parse(
                slice_subrange(v.as_slice(), start, start + len),
            ) {
                let (
                    (
                        (
                            (
                                ((owl__msg1_tag, owl__msg1_sender), owl__msg1_ephemeral),
                                owl__msg1_static,
                            ),
                            owl__msg1_timestamp,
                        ),
                        owl__msg1_mac1,
                    ),
                    owl__msg1_mac2,
                ) = parsed;
                Some(
                    owl_msg1 {
                        owl__msg1_tag: (),
                        owl__msg1_sender: OwlBuf::from_vec(slice_to_vec(owl__msg1_sender)),
                        owl__msg1_ephemeral: OwlBuf::from_vec(slice_to_vec(owl__msg1_ephemeral)),
                        owl__msg1_static: OwlBuf::from_vec(slice_to_vec(owl__msg1_static)),
                        owl__msg1_timestamp: OwlBuf::from_vec(slice_to_vec(owl__msg1_timestamp)),
                        owl__msg1_mac1: OwlBuf::from_vec(slice_to_vec(owl__msg1_mac1)),
                        owl__msg1_mac2: (),
                    },
                )
            } else {
                None
            }
        },
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

pub exec fn parse_owl_msg2<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_msg2<'a>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_msg2(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg2(arg.view())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_msg2);
    let exec_comb = exec_combinator_owl_msg2();
    match arg {
        OwlBuf::Borrowed(s) => {
            if let Ok((_, parsed)) = exec_comb.parse(s) {
                let (
                    (
                        (
                            (
                                ((owl__msg2_tag, owl__msg2_sender), owl__msg2_receiver),
                                owl__msg2_ephemeral,
                            ),
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
        },
        OwlBuf::Owned(v, start, len) => {
            reveal(OwlBuf::len_valid);
            if let Ok((_, parsed)) = exec_comb.parse(
                slice_subrange(v.as_slice(), start, start + len),
            ) {
                let (
                    (
                        (
                            (
                                ((owl__msg2_tag, owl__msg2_sender), owl__msg2_receiver),
                                owl__msg2_ephemeral,
                            ),
                            owl__msg2_empty,
                        ),
                        owl__msg2_mac1,
                    ),
                    owl__msg2_mac2,
                ) = parsed;
                Some(
                    owl_msg2 {
                        owl__msg2_tag: (),
                        owl__msg2_sender: OwlBuf::from_vec(slice_to_vec(owl__msg2_sender)),
                        owl__msg2_receiver: OwlBuf::from_vec(slice_to_vec(owl__msg2_receiver)),
                        owl__msg2_ephemeral: OwlBuf::from_vec(slice_to_vec(owl__msg2_ephemeral)),
                        owl__msg2_empty: OwlBuf::from_vec(slice_to_vec(owl__msg2_empty)),
                        owl__msg2_mac1: OwlBuf::from_vec(slice_to_vec(owl__msg2_mac1)),
                        owl__msg2_mac2: (),
                    },
                )
            } else {
                None
            }
        },
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

pub exec fn parse_owl_transp<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_transp<'a>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_transp(arg.view()) is Some,
        res is None ==> parse_owlSpec_transp(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_transp(arg.view())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_transp);
    let exec_comb = exec_combinator_owl_transp();
    match arg {
        OwlBuf::Borrowed(s) => {
            if let Ok((_, parsed)) = exec_comb.parse(s) {
                let (
                    ((owl__transp_tag, owl__transp_receiver), owl__transp_counter),
                    owl__transp_packet,
                ) = parsed;
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
        },
        OwlBuf::Owned(v, start, len) => {
            reveal(OwlBuf::len_valid);
            if let Ok((_, parsed)) = exec_comb.parse(
                slice_subrange(v.as_slice(), start, start + len),
            ) {
                let (
                    ((owl__transp_tag, owl__transp_receiver), owl__transp_counter),
                    owl__transp_packet,
                ) = parsed;
                Some(
                    owl_transp {
                        owl__transp_tag: (),
                        owl__transp_receiver: OwlBuf::from_vec(slice_to_vec(owl__transp_receiver)),
                        owl__transp_counter: OwlBuf::from_vec(slice_to_vec(owl__transp_counter)),
                        owl__transp_packet: OwlBuf::from_vec(slice_to_vec(owl__transp_packet)),
                    },
                )
            } else {
                None
            }
        },
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

pub struct owl_init_sent_state<'a> {
    pub owl_iss_c2: Ghost<()>,
    pub owl_iss_psk: owl_PSKMode<'a>,
    pub owl_iss_static_ss: Ghost<()>,
    pub owl_ss_h4: OwlBuf<'a>,
    pub owl_iss_c3: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_init_sent_state<'a>(
    arg_owl_iss_c2: Ghost<()>,
    arg_owl_iss_psk: owl_PSKMode<'a>,
    arg_owl_iss_static_ss: Ghost<()>,
    arg_owl_ss_h4: OwlBuf<'a>,
    arg_owl_iss_c3: OwlBuf<'a>,
) -> (res: owl_init_sent_state<'a>)
    requires
        arg_owl_iss_psk.len_valid(),
        arg_owl_ss_h4.len_valid(),
        arg_owl_iss_c3.len_valid(),
    ensures
        res.len_valid(),
        res.owl_iss_c2.view() == arg_owl_iss_c2.view(),
        res.owl_iss_psk.view() == arg_owl_iss_psk.view(),
        res.owl_iss_static_ss.view() == arg_owl_iss_static_ss.view(),
        res.owl_ss_h4.view() == arg_owl_ss_h4.view(),
        res.owl_iss_c3.view() == arg_owl_iss_c3.view(),
{
    owl_init_sent_state {
        owl_iss_c2: arg_owl_iss_c2,
        owl_iss_psk: arg_owl_iss_psk,
        owl_iss_static_ss: arg_owl_iss_static_ss,
        owl_ss_h4: arg_owl_ss_h4,
        owl_iss_c3: arg_owl_iss_c3,
    }
}

impl owl_init_sent_state<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_iss_psk.len_valid() && self.owl_ss_h4.len_valid() && self.owl_iss_c3.len_valid()
    }
}

impl View for owl_init_sent_state<'_> {
    type V = owlSpec_init_sent_state;

    open spec fn view(&self) -> owlSpec_init_sent_state {
        owlSpec_init_sent_state {
            owlSpec_iss_c2: ghost_unit(),
            owlSpec_iss_psk: self.owl_iss_psk.view(),
            owlSpec_iss_static_ss: ghost_unit(),
            owlSpec_ss_h4: self.owl_ss_h4.view(),
            owlSpec_iss_c3: self.owl_iss_c3.view(),
        }
    }
}

pub struct owl_init_info<'a> {
    pub owl_init_info_ss: OwlBuf<'a>,
    pub owl_init_info_psk: owl_PSKMode<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_init_info<'a>(
    arg_owl_init_info_ss: OwlBuf<'a>,
    arg_owl_init_info_psk: owl_PSKMode<'a>,
) -> (res: owl_init_info<'a>)
    requires
        arg_owl_init_info_ss.len_valid(),
        arg_owl_init_info_psk.len_valid(),
    ensures
        res.len_valid(),
        res.owl_init_info_ss.view() == arg_owl_init_info_ss.view(),
        res.owl_init_info_psk.view() == arg_owl_init_info_psk.view(),
{
    owl_init_info {
        owl_init_info_ss: arg_owl_init_info_ss,
        owl_init_info_psk: arg_owl_init_info_psk,
    }
}

impl owl_init_info<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_init_info_ss.len_valid() && self.owl_init_info_psk.len_valid()
    }
}

impl View for owl_init_info<'_> {
    type V = owlSpec_init_info;

    open spec fn view(&self) -> owlSpec_init_info {
        owlSpec_init_info {
            owlSpec_init_info_ss: self.owl_init_info_ss.view(),
            owlSpec_init_info_psk: self.owl_init_info_psk.view(),
        }
    }
}

pub struct owl_resp_received_state<'a> {
    pub owl_rrs_msg1_sender: OwlBuf<'a>,
    pub owl_rrs_psk: owl_PSKMode<'a>,
    pub owl_rrs_dhpk_S_init: OwlBuf<'a>,
    pub owl_rrs_msg1_ephemeral: OwlBuf<'a>,
    pub owl_rrs_c2: Ghost<()>,
    pub owl_rrs_h4: OwlBuf<'a>,
    pub owl_rrs_c3: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_resp_received_state<'a>(
    arg_owl_rrs_msg1_sender: OwlBuf<'a>,
    arg_owl_rrs_psk: owl_PSKMode<'a>,
    arg_owl_rrs_dhpk_S_init: OwlBuf<'a>,
    arg_owl_rrs_msg1_ephemeral: OwlBuf<'a>,
    arg_owl_rrs_c2: Ghost<()>,
    arg_owl_rrs_h4: OwlBuf<'a>,
    arg_owl_rrs_c3: OwlBuf<'a>,
) -> (res: owl_resp_received_state<'a>)
    requires
        arg_owl_rrs_msg1_sender.len_valid(),
        arg_owl_rrs_psk.len_valid(),
        arg_owl_rrs_dhpk_S_init.len_valid(),
        arg_owl_rrs_msg1_ephemeral.len_valid(),
        arg_owl_rrs_h4.len_valid(),
        arg_owl_rrs_c3.len_valid(),
    ensures
        res.len_valid(),
        res.owl_rrs_msg1_sender.view() == arg_owl_rrs_msg1_sender.view(),
        res.owl_rrs_psk.view() == arg_owl_rrs_psk.view(),
        res.owl_rrs_dhpk_S_init.view() == arg_owl_rrs_dhpk_S_init.view(),
        res.owl_rrs_msg1_ephemeral.view() == arg_owl_rrs_msg1_ephemeral.view(),
        res.owl_rrs_c2.view() == arg_owl_rrs_c2.view(),
        res.owl_rrs_h4.view() == arg_owl_rrs_h4.view(),
        res.owl_rrs_c3.view() == arg_owl_rrs_c3.view(),
{
    owl_resp_received_state {
        owl_rrs_msg1_sender: arg_owl_rrs_msg1_sender,
        owl_rrs_psk: arg_owl_rrs_psk,
        owl_rrs_dhpk_S_init: arg_owl_rrs_dhpk_S_init,
        owl_rrs_msg1_ephemeral: arg_owl_rrs_msg1_ephemeral,
        owl_rrs_c2: arg_owl_rrs_c2,
        owl_rrs_h4: arg_owl_rrs_h4,
        owl_rrs_c3: arg_owl_rrs_c3,
    }
}

impl owl_resp_received_state<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_rrs_msg1_sender.len_valid() && self.owl_rrs_psk.len_valid()
            && self.owl_rrs_dhpk_S_init.len_valid() && self.owl_rrs_msg1_ephemeral.len_valid()
            && self.owl_rrs_h4.len_valid() && self.owl_rrs_c3.len_valid()
    }
}

impl View for owl_resp_received_state<'_> {
    type V = owlSpec_resp_received_state;

    open spec fn view(&self) -> owlSpec_resp_received_state {
        owlSpec_resp_received_state {
            owlSpec_rrs_msg1_sender: self.owl_rrs_msg1_sender.view(),
            owlSpec_rrs_psk: self.owl_rrs_psk.view(),
            owlSpec_rrs_dhpk_S_init: self.owl_rrs_dhpk_S_init.view(),
            owlSpec_rrs_msg1_ephemeral: self.owl_rrs_msg1_ephemeral.view(),
            owlSpec_rrs_c2: ghost_unit(),
            owlSpec_rrs_h4: self.owl_rrs_h4.view(),
            owlSpec_rrs_c3: self.owl_rrs_c3.view(),
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

pub struct cfg_Initiator<O,'device> {
    pub salt: Vec<u8>,
    pub owl_S_init: Vec<u8>,
    pub owl_E_init: Vec<u8>,
    pub pk_owl_S_resp: Vec<u8>,
    pub pk_owl_S_init: Vec<u8>,
    pub pk_owl_E_resp: Vec<u8>,
    pub pk_owl_E_init: Vec<u8>,
    pub device: Option<&'device crate::wireguard::handshake::device::DeviceInner<O>>,
}

impl<O, 'device> cfg_Initiator<O, 'device> {    
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
        owl_tki402: owl_transp_keys_init<'a>,
        owl_msg403: OwlBuf<'a>,
        obuf: &mut Vec<u8>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Initiator), Endpoint>>), OwlError>)
        requires
            itree.view() == init_send_spec(
                *self,
                *old(mut_state),
                owl_tki402.view(),
                owl_msg403.view(),
            ),
            owl_tki402.len_valid(),
            owl_msg403.len_valid(),
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
            let parseval = owl_tki402;
            let owl_init342 = OwlBuf::another_ref(&parseval.owl_tki_msg2_receiver);
            let owl_resp341 = OwlBuf::another_ref(&parseval.owl_tki_msg2_sender);
            let owl_haspsk340 = parseval.owl_tki_has_psk;
            let owl_eph339 = parseval.owl_tki_eph;
            let owl_c7338 = parseval.owl_tki_c7;
            let owl_init_send337 = OwlBuf::another_ref(&parseval.owl_tki_k_init_send);
            let owl_resp_send336 = OwlBuf::another_ref(&parseval.owl_tki_k_resp_send);
            let tmp_owl_transp_counter343 = { owl_counter_as_bytes(&mut_state.owl_N_init_send) };
            let owl_transp_counter343 = OwlBuf::from_slice(&tmp_owl_transp_counter343);
            let owl_transp_tag346 = { owl_transp_tag_value() };
            let owl_hexconst345 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_c344 = {
                {
                    match owl_enc_st_aead_builder(
                        owl_init_send337.as_slice(),
                        owl_msg403.as_slice(),
                        &mut mut_state.owl_N_init_send,
                        owl_hexconst345.as_slice(),
                    ) {
                        Ok(ctxt) => { ctxt },
                        Err(e) => { return Err(e) },
                    }
                }
            };
            let exec_comb = (
                ((ConstBytes(EXEC_BYTES_CONST_04000000_TRANSP), Bytes(4)), Bytes(8)),
                BuilderCombinator(owl_c344),
            );
            owl_output_serialize_fused::<
                ((), state_Initiator),
                (((ConstBytes<4>, Bytes), Bytes), BuilderCombinator<OwlStAEADBuilder>),
            >(
                Tracked(&mut itree),
                exec_comb,
                (
                    (
                        ((), OwlBuf::another_ref(&owl_init342).as_slice()),
                        OwlBuf::another_ref(&owl_transp_counter343).as_slice(),
                    ),
                    (),
                ),
                obuf,
                &Responder_addr(),
                &Initiator_addr(),
            );
            ((), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    pub exec fn owl_transp_recv_init_wrapper<'a,'b>(
        &'a self,         
        mut_state: &mut state_Initiator,
        ibuf: &'a [u8],
        owl_tki_msg2_receiver: &'a [u8],
        owl_tki_msg2_sender: &'a [u8],
        owl_tki_k_init_send: &'a [u8],
        owl_tki_k_resp_send: &'a [u8],
    ) -> (Option<OwlBuf<'b>>) {
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
    pub fn owl_init_recv<'a, 'b>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_tki404: owl_transp_keys_init<'a>,
        ibuf: &'a [u8],
    ) -> (res: Result<
        (Option<OwlBuf<'b>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == init_recv_spec(*self, *old(mut_state), owl_tki404.view()),
            owl_tki404.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
            res matches Ok((Some(b), _)) ==> b.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<OwlBuf<'b>>,
            Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(init_recv_spec);
            let (tmp_owl_i350, owl__349) = {
                owl_input::<(Option<Seq<u8>>, state_Initiator)>(Tracked(&mut itree), ibuf)
            };
            let owl_i350 = OwlBuf::from_slice(tmp_owl_i350);
            let parseval = owl_tki404;
            let owl_init357 = OwlBuf::another_ref(&parseval.owl_tki_msg2_receiver);
            let owl_resp356 = OwlBuf::another_ref(&parseval.owl_tki_msg2_sender);
            let owl_haspsk355 = parseval.owl_tki_has_psk;
            let owl_eph354 = parseval.owl_tki_eph;
            let owl_c7353 = parseval.owl_tki_c7;
            let owl_init_send352 = OwlBuf::another_ref(&parseval.owl_tki_k_init_send);
            let owl_resp_send351 = OwlBuf::another_ref(&parseval.owl_tki_k_resp_send);
            let parseval_tmp = OwlBuf::another_ref(&owl_i350);
            if let Some(parseval) = parse_owl_transp(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_tag361 = parseval.owl__transp_tag;
                let owl_from360 = OwlBuf::another_ref(&parseval.owl__transp_receiver);
                let owl_ctr359 = OwlBuf::another_ref(&parseval.owl__transp_counter);
                let owl_pkt358 = OwlBuf::another_ref(&parseval.owl__transp_packet);
                {
                    if { slice_eq(owl_from360.as_slice(), owl_resp356.as_slice()) } {
                        let owl_hexconst363 = {
                            {
                                let x = mk_vec_u8![];
                                OwlBuf::from_vec(x)
                            }
                        };
                        let tmp_owl_p362 = {
                            owl_dec_st_aead(
                                owl_resp_send351.as_slice(),
                                owl_pkt358.as_slice(),
                                owl_ctr359.as_slice(),
                                owl_hexconst363.as_slice(),
                            )
                        };
                        let owl_p362 = OwlBuf::from_vec_option(tmp_owl_p362);
                        (owl_p362, Tracked(itree))
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

    #[verifier::spinoff_prover]
    pub fn owl_init_stage2_wrapper<'a>(
        &'a self,
        mut_state: &mut state_Initiator,
        psk: Option<&'a [u8]>,
        h4: &'a [u8],
        c3: &'a [u8],
        ibuf: &'a [u8]
    ) -> (Option<owl_transp_keys_init<'a>>) {
        let pskmode = match psk {
            Some(psk) => owl_PSKMode::owl_HasPSK(OwlBuf::from_slice(psk)),
            None => owl_PSKMode::owl_NoPSK(),
        };
        let owl_st = owl_init_sent_state {
            owl_iss_c2: Ghost(()),
            owl_iss_psk: pskmode,
            owl_iss_static_ss: Ghost(()),
            owl_ss_h4: OwlBuf::from_slice(h4),
            owl_iss_c3: OwlBuf::from_slice(c3),
        };
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<(), Endpoint>::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            init_stage2_spec(*self, *s, owl_st.view())
        );
        let (res, _) = self.owl_init_stage2(Tracked(call_token), mut_state, owl_st, ibuf).unwrap();
        res
    }


    #[verifier::spinoff_prover]
    pub fn owl_init_stage2<'a>(
        &'a self,
        Tracked(itree): Tracked<
            ITreeToken<(Option<owlSpec_transp_keys_init>, state_Initiator), Endpoint>,
        >,
        mut_state: &mut state_Initiator,
        owl_st934: owl_init_sent_state<'a>,
        ibuf: &'a [u8]
    ) -> (res: Result<
        (
            Option<owl_transp_keys_init<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_transp_keys_init>, state_Initiator), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == init_stage2_spec(*self, *old(mut_state), owl_st934.view()),
            owl_st934.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
            res matches Ok((Some(b), _)) ==> b.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_transp_keys_init<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_transp_keys_init>, state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(init_stage2_spec);
            let parseval = owl_st934;
            let owl_c2750 = parseval.owl_iss_c2;
            let owl_opsk749 = parseval.owl_iss_psk;
            let owl_static_ss748 = parseval.owl_iss_static_ss;
            let owl_h4747 = OwlBuf::another_ref(&parseval.owl_ss_h4);
            let owl_c3746 = OwlBuf::another_ref(&parseval.owl_iss_c3);
            let (tmp_owl_i752, owl__751) = {
                owl_input::<(Option<owlSpec_transp_keys_init>, state_Initiator)>(
                    Tracked(&mut itree),
                    ibuf,
                )
            };
            let owl_i752 = OwlBuf::from_slice(tmp_owl_i752);
            let parseval_tmp = OwlBuf::another_ref(&owl_i752);
            if let Some(parseval) = parse_owl_msg2(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_msg2_tag759 = parseval.owl__msg2_tag;
                let owl_msg2_sender758 = OwlBuf::another_ref(&parseval.owl__msg2_sender);
                let owl_msg2_receiver757 = OwlBuf::another_ref(&parseval.owl__msg2_receiver);
                let owl_msg2_ephemeral756 = OwlBuf::another_ref(&parseval.owl__msg2_ephemeral);
                let owl_msg2_empty_enc755 = OwlBuf::another_ref(&parseval.owl__msg2_empty);
                let owl_msg2_mac1754 = OwlBuf::another_ref(&parseval.owl__msg2_mac1);
                let owl_msg2_mac2753 = parseval.owl__msg2_mac2;
                {
                    if owl_msg2_sender758.len() == 4 && owl_msg2_receiver757.len() == 4 {
                        if owl_is_group_elem(owl_msg2_ephemeral756.as_slice()) {
                            let owl_e_init760 = { OwlBuf::from_slice(&self.owl_E_init.as_slice()) };
                            let tmp_owl_kdfval207761 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE,
                                    owl_c3746.as_slice(),
                                    owl_msg2_ephemeral756.as_slice(),
                                    {
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    }.as_slice(),
                                )
                            };
                            let owl_kdfval207761 = OwlBuf::from_vec(tmp_owl_kdfval207761);
                            let owl_c4762 = {
                                {
                                    OwlBuf::another_ref(&owl_kdfval207761).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let tmp_owl_h5763 = {
                                owl_crh(
                                    owl_concat(
                                        owl_h4747.as_slice(),
                                        owl_msg2_ephemeral756.as_slice(),
                                    ).as_slice(),
                                )
                            };
                            let owl_h5763 = OwlBuf::from_vec(tmp_owl_h5763);
                            let tmp_owl_ss764 = {
                                owl_dh_combine(
                                    owl_msg2_ephemeral756.as_slice(),
                                    owl_e_init760.as_slice(),
                                )
                            };
                            let owl_ss764 = OwlBuf::from_vec(tmp_owl_ss764);
                            let tmp_owl_kdfval219765 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE,
                                    owl_c4762.as_slice(),
                                    owl_ss764.as_slice(),
                                    {
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    }.as_slice(),
                                )
                            };
                            let owl_kdfval219765 = OwlBuf::from_vec(tmp_owl_kdfval219765);
                            let owl_c5766 = {
                                {
                                    OwlBuf::another_ref(&owl_kdfval219765).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let tmp_owl_kdfval232767 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE,
                                    owl_c5766.as_slice(),
                                    owl_dh_combine(
                                        owl_msg2_ephemeral756.as_slice(),
                                        OwlBuf::from_slice(&self.owl_S_init.as_slice()).as_slice(),
                                    ).as_slice(),
                                    {
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    }.as_slice(),
                                )
                            };
                            let owl_kdfval232767 = OwlBuf::from_vec(tmp_owl_kdfval232767);
                            let owl_c6768 = {
                                {
                                    OwlBuf::another_ref(&owl_kdfval232767).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let owl_psk769 = {
                                let owl_caseval770 = { &owl_opsk749 };
                                match owl_caseval770 {
                                    owl_PSKMode::owl_HasPSK(tmp_owl_v771) => {
                                        let owl_v771 = OwlBuf::another_ref(&tmp_owl_v771);
                                        owl_v771
                                    },
                                    owl_PSKMode::owl_NoPSK() => { owl_zeros_32() },
                                }
                            };
                            let tmp_owl_kdfval241772 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE,
                                    owl_c6768.as_slice(),
                                    owl_psk769.as_slice(),
                                    {
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    }.as_slice(),
                                )
                            };
                            let owl_kdfval241772 = OwlBuf::from_vec(tmp_owl_kdfval241772);
                            let owl_c7773 = {
                                {
                                    OwlBuf::another_ref(&owl_kdfval241772).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let owl_tau774 = {
                                {
                                    OwlBuf::another_ref(&owl_kdfval241772).subrange(
                                        0 + KDFKEY_SIZE,
                                        0 + KDFKEY_SIZE + NONCE_SIZE,
                                    )
                                }
                            };
                            let owl_k0775 = {
                                {
                                    OwlBuf::another_ref(&owl_kdfval241772).subrange(
                                        0 + KDFKEY_SIZE + NONCE_SIZE,
                                        0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE,
                                    )
                                }
                            };
                            let tmp_owl_h6776 = {
                                owl_crh(
                                    owl_concat(
                                        owl_h5763.as_slice(),
                                        owl_tau774.as_slice(),
                                    ).as_slice(),
                                )
                            };
                            let owl_h6776 = OwlBuf::from_vec(tmp_owl_h6776);
                            let tmp_owl_parseval777 = {
                                owl_dec_st_aead(
                                    owl_k0775.as_slice(),
                                    owl_msg2_empty_enc755.as_slice(),
                                    {
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    }.as_slice(),
                                    owl_h6776.as_slice(),
                                )
                            };
                            let owl_parseval777 = OwlBuf::from_vec_option(tmp_owl_parseval777);
                            let owl_caseval778 = { owl_parseval777 };
                            match owl_caseval778 {
                                Option::None => { (None, Tracked(itree)) },
                                Option::Some(tmp_owl_x779) => {
                                    let owl_x779 = OwlBuf::another_ref(&tmp_owl_x779);
                                    {
                                        let tmp_owl_kdfval250780 = {
                                            owl_extract_expand_to_len(
                                                0 + ENCKEY_SIZE + ENCKEY_SIZE,
                                                owl_c7773.as_slice(),
                                                {
                                                    let x = mk_vec_u8![];
                                                    OwlBuf::from_vec(x)
                                                }.as_slice(),
                                                {
                                                    let x = mk_vec_u8![];
                                                    OwlBuf::from_vec(x)
                                                }.as_slice(),
                                            )
                                        };
                                        let owl_kdfval250780 = OwlBuf::from_vec(
                                            tmp_owl_kdfval250780,
                                        );
                                        let owl_k1781 = {
                                            {
                                                OwlBuf::another_ref(&owl_kdfval250780).subrange(
                                                    0,
                                                    0 + ENCKEY_SIZE,
                                                )
                                            }
                                        };
                                        let owl_k2782 = {
                                            {
                                                OwlBuf::another_ref(&owl_kdfval250780).subrange(
                                                    0 + ENCKEY_SIZE,
                                                    0 + ENCKEY_SIZE + ENCKEY_SIZE,
                                                )
                                            }
                                        };
                                        (
                                            Some(
                                                owl_transp_keys_init(
                                                    OwlBuf::another_ref(&owl_msg2_receiver757),
                                                    OwlBuf::another_ref(&owl_msg2_sender758),
                                                    owl_HasPSK_enumtest(&owl_opsk749),
                                                    owl_ghost_unit(),
                                                    owl_ghost_unit(),
                                                    OwlBuf::another_ref(&owl_k1781),
                                                    OwlBuf::another_ref(&owl_k2782),
                                                ),
                                            ),
                                            Tracked(itree),
                                        )
                                    }
                                },
                            }
                        } else {
                            (None, Tracked(itree))
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

    pub fn owl_init_stage1_wrapper<'a>(
        &'a self,
        mut_state: &mut state_Initiator,
        owl_dhpk_S_resp: &'a [u8],
        owl_dhpk_S_init: &'a [u8],
        owl_ss_S_resp_S_init: &'a [u8],
        owl_psk: Option<&'a [u8]>,
        obuf: &mut [u8],
    ) -> owl_init_sent_state<'a> {
        let pskmode = match owl_psk {
            Some(psk) => owl_PSKMode::owl_HasPSK(OwlBuf::from_slice(psk)),
            None => owl_PSKMode::owl_NoPSK(),
        };        
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<(), Endpoint>::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            init_stage1_spec(*self, *s, dhpk_S_resp.view(), dhpk_S_init.view(), ss_S_resp_S_init.view(), pskmode.view())
        );
        let (res, _) =
            self.owl_init_stage1(
                Tracked(call_token), 
                mut_state, 
                OwlBuf::from_slice(owl_dhpk_S_resp), 
                OwlBuf::from_slice(owl_dhpk_S_init), 
                OwlBuf::from_slice(owl_ss_S_resp_S_init),
                pskmode,
                obuf).unwrap();
        res
        
    }


    #[verifier::spinoff_prover]
    pub fn owl_init_stage1<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_init_sent_state, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_dhpk_S_resp935: OwlBuf<'a>,
        owl_dhpk_S_init936: OwlBuf<'a>,
        owl_ss_S_resp_S_init937: OwlBuf<'a>,
        owl_psk938: owl_PSKMode<'a>,
        obuf: &mut [u8],
    ) -> (res: Result<
        (
            owl_init_sent_state<'a>,
            Tracked<ITreeToken<(owlSpec_init_sent_state, state_Initiator), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == init_stage1_spec(
                *self,
                *old(mut_state),
                owl_dhpk_S_resp935.view(),
                owl_dhpk_S_init936.view(),
                owl_ss_S_resp_S_init937.view(),
                owl_psk938.view(),
            ),
            owl_dhpk_S_resp935.len_valid(),
            owl_dhpk_S_init936.len_valid(),
            owl_ss_S_resp_S_init937.len_valid(),
            owl_psk938.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
            res matches Ok(r) ==> r.0.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_init_sent_state<'a>,
            Tracked<ITreeToken<(owlSpec_init_sent_state, state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(init_stage1_spec);
            let tmp_owl_C0787 = { owl_crh(owl_construction().as_slice()) };
            let owl_C0787 = OwlBuf::from_vec(tmp_owl_C0787);
            let tmp_owl_H0788 = {
                owl_crh(owl_concat(owl_C0787.as_slice(), owl_identifier().as_slice()).as_slice())
            };
            let owl_H0788 = OwlBuf::from_vec(tmp_owl_H0788);
            let tmp_owl_H1789 = {
                owl_crh(owl_concat(owl_H0788.as_slice(), owl_dhpk_S_resp935.as_slice()).as_slice())
            };
            let owl_H1789 = OwlBuf::from_vec(tmp_owl_H1789);
            let tmp_owl_e_init790 = {
                owl_dhpk(OwlBuf::from_slice(&self.owl_E_init.as_slice()).as_slice())
            };
            let owl_e_init790 = OwlBuf::from_vec(tmp_owl_e_init790);
            let tmp_owl_kdfval266791 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE,
                    owl_C0787.as_slice(),
                    owl_e_init790.as_slice(),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                )
            };
            let owl_kdfval266791 = OwlBuf::from_vec(tmp_owl_kdfval266791);
            let owl_C1792 = {
                { OwlBuf::another_ref(&owl_kdfval266791).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let tmp_owl_H2793 = {
                owl_crh(owl_concat(owl_H1789.as_slice(), owl_e_init790.as_slice()).as_slice())
            };
            let owl_H2793 = OwlBuf::from_vec(tmp_owl_H2793);
            let tmp_owl_ss_S_resp_E_init794 = {
                owl_dh_combine(
                    owl_dhpk_S_resp935.as_slice(),
                    OwlBuf::from_slice(&self.owl_E_init.as_slice()).as_slice(),
                )
            };
            let owl_ss_S_resp_E_init794 = OwlBuf::from_vec(tmp_owl_ss_S_resp_E_init794);
            let tmp_owl_kdfval271795 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE + ENCKEY_SIZE,
                    owl_C1792.as_slice(),
                    owl_ss_S_resp_E_init794.as_slice(),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                )
            };
            let owl_kdfval271795 = OwlBuf::from_vec(tmp_owl_kdfval271795);
            let owl_C2796 = {
                { OwlBuf::another_ref(&owl_kdfval271795).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_k0797 = {
                {
                    OwlBuf::another_ref(&owl_kdfval271795).subrange(
                        0 + KDFKEY_SIZE,
                        0 + KDFKEY_SIZE + ENCKEY_SIZE,
                    )
                }
            };
            let owl_msg1_static798 = {
                {
                    match owl_enc_st_aead(
                        owl_k0797.as_slice(),
                        owl_dhpk_S_init936.as_slice(),
                        &mut mut_state.owl_aead_counter_msg1_C2,
                        owl_H2793.as_slice(),
                    ) {
                        Ok(ctxt) => { OwlBuf::from_vec(ctxt) },
                        Err(e) => { return Err(e) },
                    }
                }
            };
            let tmp_owl_H3799 = {
                owl_crh(owl_concat(owl_H2793.as_slice(), owl_msg1_static798.as_slice()).as_slice())
            };
            let owl_H3799 = OwlBuf::from_vec(tmp_owl_H3799);
            let tmp_owl_kdfval277800 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE + ENCKEY_SIZE,
                    owl_C2796.as_slice(),
                    owl_ss_S_resp_S_init937.as_slice(),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                )
            };
            let owl_kdfval277800 = OwlBuf::from_vec(tmp_owl_kdfval277800);
            let owl_c3801 = {
                { OwlBuf::another_ref(&owl_kdfval277800).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_k1802 = {
                {
                    OwlBuf::another_ref(&owl_kdfval277800).subrange(
                        0 + KDFKEY_SIZE,
                        0 + KDFKEY_SIZE + ENCKEY_SIZE,
                    )
                }
            };
            let (owl_timestamp803, Tracked(itree)) = {
                owl_call!(itree, *mut_state, timestamp_i_spec(*self, *mut_state), self.owl_timestamp_i(mut_state))
            };
            let owl_msg1_timestamp804 = {
                {
                    match owl_enc_st_aead(
                        owl_k1802.as_slice(),
                        owl_timestamp803.as_slice(),
                        &mut mut_state.owl_aead_counter_msg1_C3,
                        owl_H3799.as_slice(),
                    ) {
                        Ok(ctxt) => { OwlBuf::from_vec(ctxt) },
                        Err(e) => { return Err(e) },
                    }
                }
            };
            let tmp_owl_h4805 = {
                owl_crh(
                    owl_concat(owl_H3799.as_slice(), owl_msg1_timestamp804.as_slice()).as_slice(),
                )
            };
            let owl_h4805 = OwlBuf::from_vec(tmp_owl_h4805);
            let (owl_msg1_sender806, Tracked(itree)) = {
                owl_call!(itree, *mut_state, get_sender_i_spec(*self, *mut_state), self.owl_get_sender_i(mut_state))
            };
            let owl_msg1_tag807 = { owl_msg1_tag_value() };
            let tmp_owl_msg1_mac1_k808 = {
                owl_crh(owl_concat(owl_mac1().as_slice(), owl_dhpk_S_resp935.as_slice()).as_slice())
            };
            let owl_msg1_mac1_k808 = OwlBuf::from_vec(tmp_owl_msg1_mac1_k808);
            let tmp_owl_msg1_mac1809 = {
                owl_mac(
                    owl_msg1_mac1_k808.as_slice(),
                    owl_concat(
                        owl_concat(
                            owl_concat(
                                owl_concat(
                                    owl_msg1_tag807.as_slice(),
                                    owl_msg1_sender806.as_slice(),
                                ).as_slice(),
                                owl_e_init790.as_slice(),
                            ).as_slice(),
                            owl_msg1_static798.as_slice(),
                        ).as_slice(),
                        owl_msg1_timestamp804.as_slice(),
                    ).as_slice(),
                )
            };
            let owl_msg1_mac1809 = OwlBuf::from_vec(tmp_owl_msg1_mac1809);
            let owl_msg1_mac2810 = { owl_zeros_16() };
            let owl_msg1_output811 = {
                owl_msg1(
                    (),
                    OwlBuf::another_ref(&owl_msg1_sender806),
                    OwlBuf::another_ref(&owl_e_init790),
                    OwlBuf::another_ref(&owl_msg1_static798),
                    OwlBuf::another_ref(&owl_msg1_timestamp804),
                    OwlBuf::another_ref(&owl_msg1_mac1809),
                    (),
                )
            };
            let owl__812 = {
                owl_output::<(owlSpec_init_sent_state, state_Initiator)>(
                    Tracked(&mut itree),
                    serialize_owl_msg1(&owl_msg1_output811).as_slice(),
                    &Responder_addr(),
                    &Initiator_addr(),
                    obuf,
                );
            };
            (
                owl_init_sent_state(
                    owl_ghost_unit(),
                    owl_psk938,
                    owl_ghost_unit(),
                    OwlBuf::another_ref(&owl_h4805),
                    OwlBuf::another_ref(&owl_c3801),
                ),
                Tracked(itree),
            )
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

pub struct cfg_Responder<O, 'device> {
    pub salt: Vec<u8>,
    pub owl_S_resp: Vec<u8>,
    pub owl_E_resp: Vec<u8>,
    pub pk_owl_S_resp: Vec<u8>,
    pub pk_owl_S_init: Vec<u8>,
    pub pk_owl_E_resp: Vec<u8>,
    pub pk_owl_E_init: Vec<u8>,
    pub device: Option<&'device crate::wireguard::handshake::device::DeviceInner<O>>,
}

impl<O, 'device> cfg_Responder<O, 'device> {
    pub exec fn owl_transp_send_resp_wrapper<'a>(
        &'a self,         
        mut_state: &'a mut state_Responder,
        owl_plaintext: &'a [u8],
        obuf: &mut Vec<u8>,
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
        owl_tki405: owl_transp_keys_resp<'a>,
        owl_msg406: OwlBuf<'a>,
        obuf: &mut Vec<u8>
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == resp_send_spec(
                *self,
                *old(mut_state),
                owl_tki405.view(),
                owl_msg406.view(),
            ),
            owl_tki405.len_valid(),
            owl_msg406.len_valid(),
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
            let owl_tki_366 = { owl_tki405 };
            let parseval = owl_tki_366;
            let owl_init374 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_receiver);
            let owl_resp373 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_sender);
            let owl_haspsk372 = parseval.owl_tkr_has_psk;
            let owl_eph371 = parseval.owl_tkr_eph;
            let owl_c7370 = parseval.owl_tkr_c7;
            let owl_b369 = parseval.owl_tkr_recvd;
            let owl_init_send368 = OwlBuf::another_ref(&parseval.owl_tkr_k_init_send);
            let owl_resp_send367 = OwlBuf::another_ref(&parseval.owl_tkr_k_resp_send);
            if owl_b369 {
                {
                    let tmp_owl_transp_counter375 = {
                        owl_counter_as_bytes(&mut_state.owl_N_resp_send)
                    };
                    let owl_transp_counter375 = OwlBuf::from_slice(&tmp_owl_transp_counter375);
                    let owl_transp_tag378 = { owl_transp_tag_value() };
                    let owl_hexconst377 = {
                        {
                            let x = mk_vec_u8![];
                            OwlBuf::from_vec(x)
                        }
                    };
                    let owl_c376 = {
                        {
                            match owl_enc_st_aead_builder(
                                owl_resp_send367.as_slice(),
                                owl_msg406.as_slice(),
                                &mut mut_state.owl_N_resp_send,
                                owl_hexconst377.as_slice(),
                            ) {
                                Ok(ctxt) => { ctxt },
                                Err(e) => { return Err(e) },
                            }
                        }
                    };
                    let owl__380 = {
                        let exec_comb = (
                            ((ConstBytes(EXEC_BYTES_CONST_04000000_TRANSP), Bytes(4)), Bytes(8)),
                            BuilderCombinator(owl_c376),
                        );
                        owl_output_serialize_fused::<
                            (Option<()>, state_Responder),
                            (((ConstBytes<4>, Bytes), Bytes), BuilderCombinator<OwlStAEADBuilder>),
                        >(
                            Tracked(&mut itree),
                            exec_comb,
                            (
                                (
                                    ((), OwlBuf::another_ref(&owl_resp373).as_slice()),
                                    OwlBuf::another_ref(&owl_transp_counter375).as_slice(),
                                ),
                                (),
                            ),
                            obuf,
                            &Initiator_addr(),
                            &Responder_addr(),
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
        owl_tki407: owl_transp_keys_resp<'a>,
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
            itree.view() == resp_recv_spec(*self, *old(mut_state), owl_tki407.view()),
            owl_tki407.len_valid(),
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
                    ibuf,
                )
            };
            let owl_i383 = OwlBuf::from_slice(tmp_owl_i383);
            let owl_tki_384 = { owl_tki407 };
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
            if let Some(parseval) = parse_owl_transp(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_tag396 = parseval.owl__transp_tag;
                let owl_from395 = OwlBuf::another_ref(&parseval.owl__transp_receiver);
                let owl_ctr394 = OwlBuf::another_ref(&parseval.owl__transp_counter);
                let owl_pkt393 = OwlBuf::another_ref(&parseval.owl__transp_packet);
                {
                    if { slice_eq(owl_from395.as_slice(), owl_init392.as_slice()) } {
                        let owl_hexconst398 = {
                            {
                                let x = mk_vec_u8![];
                                OwlBuf::from_vec(x)
                            }
                        };
                        let tmp_owl_caseval397 = {
                            owl_dec_st_aead(
                                owl_init_send386.as_slice(),
                                owl_pkt393.as_slice(),
                                owl_ctr394.as_slice(),
                                owl_hexconst398.as_slice(),
                            )
                        };
                        let owl_caseval397 = OwlBuf::from_vec_option(tmp_owl_caseval397);
                        match owl_caseval397 {
                            Option::Some(tmp_owl_x399) => {
                                let owl_x399 = OwlBuf::another_ref(&tmp_owl_x399);
                                let owl_st_400 = {
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
                                let owl_ret401 = {
                                    owl_resp_transp_recv_result(
                                        owl_st_400,
                                        OwlBuf::another_ref(&owl_x399),
                                    )
                                };
                                (Some(owl_ret401), Tracked(itree))
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


    pub fn owl_resp_stage2_wrapper<'a>(
        &'a self,
        mut_state: &mut state_Responder,
        owl_st: owl_resp_received_state<'a>,
        obuf: &mut [u8],
    ) -> (res: Option<owl_transp_keys_resp<'a>>) 
    {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<(), Endpoint>::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            resp_stage2_spec(*self, *s, owl_st.view()),
        );
        let (res, _) =
            self.owl_resp_stage2(Tracked(call_token), mut_state, owl_st, obuf).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_resp_stage2<'a>(
        &'a self,
        Tracked(itree): Tracked<
            ITreeToken<(Option<owlSpec_transp_keys_resp>, state_Responder), Endpoint>,
        >,
        mut_state: &mut state_Responder,
        owl_st392: owl_resp_received_state<'a>,
        obuf: &mut [u8],
    ) -> (res: Result<
        (
            Option<owl_transp_keys_resp<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_transp_keys_resp>, state_Responder), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == resp_stage2_spec(*self, *old(mut_state), owl_st392.view()),
            owl_st392.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
            res matches Ok((Some(b), _)) ==> b.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_transp_keys_resp<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_transp_keys_resp>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(resp_stage2_spec);
            let owl_st_312 = { owl_st392 };
            let owl_st__313 = { owl_st_312 };
            let parseval = owl_st__313;
            let owl_msg2_receiver320 = OwlBuf::another_ref(&parseval.owl_rrs_msg1_sender);
            let owl_psk319 = parseval.owl_rrs_psk;
            let owl_dhpk_S_init318 = OwlBuf::another_ref(&parseval.owl_rrs_dhpk_S_init);
            let owl_msg1_ephemeral317 = OwlBuf::another_ref(&parseval.owl_rrs_msg1_ephemeral);
            let owl_C2316 = parseval.owl_rrs_c2;
            let owl_H4315 = OwlBuf::another_ref(&parseval.owl_rrs_h4);
            let owl_C3314 = OwlBuf::another_ref(&parseval.owl_rrs_c3);
            let tmp_owl_e_resp_pk321 = {
                owl_dhpk(OwlBuf::from_slice(&self.owl_E_resp.as_slice()).as_slice())
            };
            let owl_e_resp_pk321 = OwlBuf::from_vec(tmp_owl_e_resp_pk321);
            let tmp_owl_kdfval106322 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE,
                    owl_C3314.as_slice(),
                    owl_e_resp_pk321.as_slice(),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                )
            };
            let owl_kdfval106322 = OwlBuf::from_vec(tmp_owl_kdfval106322);
            let owl_c4323 = {
                { OwlBuf::another_ref(&owl_kdfval106322).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let tmp_owl_h5324 = {
                owl_crh(owl_concat(owl_H4315.as_slice(), owl_e_resp_pk321.as_slice()).as_slice())
            };
            let owl_h5324 = OwlBuf::from_vec(tmp_owl_h5324);
            let tmp_owl_ss325 = {
                owl_dh_combine(
                    owl_msg1_ephemeral317.as_slice(),
                    OwlBuf::from_slice(&self.owl_E_resp.as_slice()).as_slice(),
                )
            };
            let owl_ss325 = OwlBuf::from_vec(tmp_owl_ss325);
            let tmp_owl_kdfval119326 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE,
                    owl_c4323.as_slice(),
                    owl_ss325.as_slice(),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                )
            };
            let owl_kdfval119326 = OwlBuf::from_vec(tmp_owl_kdfval119326);
            let owl_c5327 = {
                { OwlBuf::another_ref(&owl_kdfval119326).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let tmp_owl_kdfval126328 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE,
                    owl_c5327.as_slice(),
                    owl_dh_combine(
                        owl_dhpk_S_init318.as_slice(),
                        OwlBuf::from_slice(&self.owl_E_resp.as_slice()).as_slice(),
                    ).as_slice(),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                )
            };
            let owl_kdfval126328 = OwlBuf::from_vec(tmp_owl_kdfval126328);
            let owl_c6329 = {
                { OwlBuf::another_ref(&owl_kdfval126328).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_psk_val330 = {
                let owl_caseval331 = { &owl_psk319 };
                match owl_caseval331 {
                    owl_PSKMode::owl_HasPSK(tmp_owl_v332) => {
                        let owl_v332 = OwlBuf::another_ref(&tmp_owl_v332);
                        owl_v332
                    },
                    owl_PSKMode::owl_NoPSK() => { owl_zeros_32() },
                }
            };
            let tmp_owl_kdfval135333 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE,
                    owl_c6329.as_slice(),
                    owl_psk_val330.as_slice(),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                )
            };
            let owl_kdfval135333 = OwlBuf::from_vec(tmp_owl_kdfval135333);
            let owl_c7334 = {
                { OwlBuf::another_ref(&owl_kdfval135333).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_tau335 = {
                {
                    OwlBuf::another_ref(&owl_kdfval135333).subrange(
                        0 + KDFKEY_SIZE,
                        0 + KDFKEY_SIZE + NONCE_SIZE,
                    )
                }
            };
            let owl_k0336 = {
                {
                    OwlBuf::another_ref(&owl_kdfval135333).subrange(
                        0 + KDFKEY_SIZE + NONCE_SIZE,
                        0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE,
                    )
                }
            };
            let owl_msg2_tag337 = { owl_msg2_tag_value() };
            let (owl_msg2_sender338, Tracked(itree)) = {
                owl_call!(itree, *mut_state, get_sender_r_spec(*self, *mut_state), self.owl_get_sender_r(mut_state))
            };
            let tmp_owl_msg2_mac1_k339 = {
                owl_crh(owl_concat(owl_mac1().as_slice(), owl_dhpk_S_init318.as_slice()).as_slice())
            };
            let owl_msg2_mac1_k339 = OwlBuf::from_vec(tmp_owl_msg2_mac1_k339);
            let tmp_owl_h6340 = {
                owl_crh(owl_concat(owl_h5324.as_slice(), owl_tau335.as_slice()).as_slice())
            };
            let owl_h6340 = OwlBuf::from_vec(tmp_owl_h6340);
            let owl_msg2_empty341 = {
                {
                    match owl_enc_st_aead(
                        owl_k0336.as_slice(),
                        {
                            let x = mk_vec_u8![];
                            OwlBuf::from_vec(x)
                        }.as_slice(),
                        &mut mut_state.owl_aead_counter_msg2_C7,
                        owl_h6340.as_slice(),
                    ) {
                        Ok(ctxt) => { OwlBuf::from_vec(ctxt) },
                        Err(e) => { return Err(e) },
                    }
                }
            };
            let tmp_owl_msg2_mac1342 = {
                owl_mac(
                    owl_msg2_mac1_k339.as_slice(),
                    owl_concat(
                        owl_concat(
                            owl_concat(
                                owl_concat(
                                    owl_msg2_tag337.as_slice(),
                                    owl_msg2_sender338.as_slice(),
                                ).as_slice(),
                                owl_msg2_receiver320.as_slice(),
                            ).as_slice(),
                            owl_e_resp_pk321.as_slice(),
                        ).as_slice(),
                        owl_msg2_empty341.as_slice(),
                    ).as_slice(),
                )
            };
            let owl_msg2_mac1342 = OwlBuf::from_vec(tmp_owl_msg2_mac1342);
            let owl__assert_266343 = { owl_ghost_unit() };
            let owl_msg2_mac2344 = { owl_zeros_16() };
            let owl_msg2_output345 = {
                owl_msg2(
                    (),
                    OwlBuf::another_ref(&owl_msg2_sender338),
                    OwlBuf::another_ref(&owl_msg2_receiver320),
                    OwlBuf::another_ref(&owl_e_resp_pk321),
                    OwlBuf::another_ref(&owl_msg2_empty341),
                    OwlBuf::another_ref(&owl_msg2_mac1342),
                    (),
                )
            };
            let owl__346 = {
                owl_output::<(Option<owlSpec_transp_keys_resp>, state_Responder)>(
                    Tracked(&mut itree),
                    serialize_owl_msg2(&owl_msg2_output345).as_slice(),
                    &Initiator_addr(),
                    &Responder_addr(),
                    obuf
                );
            };
            let tmp_owl_kdfval151347 = {
                owl_extract_expand_to_len(
                    0 + ENCKEY_SIZE + ENCKEY_SIZE,
                    owl_c7334.as_slice(),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                    {
                        let x = mk_vec_u8![];
                        OwlBuf::from_vec(x)
                    }.as_slice(),
                )
            };
            let owl_kdfval151347 = OwlBuf::from_vec(tmp_owl_kdfval151347);
            let owl_tk1348 = {
                { OwlBuf::another_ref(&owl_kdfval151347).subrange(0, 0 + ENCKEY_SIZE) }
            };
            let owl_tk2349 = {
                {
                    OwlBuf::another_ref(&owl_kdfval151347).subrange(
                        0 + ENCKEY_SIZE,
                        0 + ENCKEY_SIZE + ENCKEY_SIZE,
                    )
                }
            };
            let owl_ret350 = {
                owl_transp_keys_resp(
                    OwlBuf::another_ref(&owl_msg2_receiver320),
                    OwlBuf::another_ref(&owl_msg2_sender338),
                    owl_HasPSK_enumtest(&owl_psk319),
                    owl_ghost_unit(),
                    owl_ghost_unit(),
                    false,
                    OwlBuf::another_ref(&owl_tk1348),
                    OwlBuf::another_ref(&owl_tk2349),
                )
            };
            (Some(owl_ret350), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }
        

    #[verifier::spinoff_prover]
    pub fn owl_resp_stage1_wrapper<'a>(
        &'a self,
        mut_state: &mut state_Responder,
        owl_dhpk_S_resp: &'a [u8],
        ibuf: &'a [u8]
    ) -> Option<owl_resp_received_state<'a>> {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<(), Endpoint>::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            resp_stage1_spec(*self, *s, dhpk_S_resp.view())
        );
        let (res, _) = self.owl_resp_stage1(Tracked(call_token), mut_state, OwlBuf::from_slice(owl_dhpk_S_resp), ibuf).unwrap();
        res
    }


    #[verifier::spinoff_prover]
    pub fn owl_resp_stage1<'a>(
        &'a self,
        Tracked(itree): Tracked<
            ITreeToken<(Option<owlSpec_resp_received_state>, state_Responder), Endpoint>,
        >,
        mut_state: &mut state_Responder,
        owl_dhpk_S_resp943: OwlBuf<'a>,
        ibuf: &'a [u8]
    ) -> (res: Result<
        (
            Option<owl_resp_received_state<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_resp_received_state>, state_Responder), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == resp_stage1_spec(*self, *old(mut_state), owl_dhpk_S_resp943.view()),
            owl_dhpk_S_resp943.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
            res matches Ok((Some(b), _)) ==> b.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_resp_received_state<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_resp_received_state>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(resp_stage1_spec);
            let (tmp_owl_inp892, owl__891) = {
                owl_input::<(Option<owlSpec_resp_received_state>, state_Responder)>(
                    Tracked(&mut itree),
                    ibuf,
                )
            };
            let owl_inp892 = OwlBuf::from_slice(tmp_owl_inp892);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp892);
            if let Some(parseval) = parse_owl_msg1(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_msg1_tag899 = parseval.owl__msg1_tag;
                let owl_msg1_sender898 = OwlBuf::another_ref(&parseval.owl__msg1_sender);
                let owl_msg1_ephemeral897 = OwlBuf::another_ref(&parseval.owl__msg1_ephemeral);
                let owl_msg1_static896 = OwlBuf::another_ref(&parseval.owl__msg1_static);
                let owl_msg1_timestamp895 = OwlBuf::another_ref(&parseval.owl__msg1_timestamp);
                let owl_msg1_mac1894 = OwlBuf::another_ref(&parseval.owl__msg1_mac1);
                let owl_msg1_mac2893 = parseval.owl__msg1_mac2;
                {
                    if owl_msg1_sender898.len() == 4 {
                        if owl_is_group_elem(owl_msg1_ephemeral897.as_slice()) {
                            let tmp_owl_C0900 = { owl_crh(owl_construction().as_slice()) };
                            let owl_C0900 = OwlBuf::from_vec(tmp_owl_C0900);
                            let tmp_owl_H0901 = {
                                owl_crh(
                                    owl_concat(
                                        owl_C0900.as_slice(),
                                        owl_identifier().as_slice(),
                                    ).as_slice(),
                                )
                            };
                            let owl_H0901 = OwlBuf::from_vec(tmp_owl_H0901);
                            let tmp_owl_H1902 = {
                                owl_crh(
                                    owl_concat(
                                        owl_H0901.as_slice(),
                                        owl_dhpk_S_resp943.as_slice(),
                                    ).as_slice(),
                                )
                            };
                            let owl_H1902 = OwlBuf::from_vec(tmp_owl_H1902);
                            let tmp_owl_kdfval545903 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE,
                                    owl_C0900.as_slice(),
                                    owl_msg1_ephemeral897.as_slice(),
                                    {
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    }.as_slice(),
                                )
                            };
                            let owl_kdfval545903 = OwlBuf::from_vec(tmp_owl_kdfval545903);
                            let owl_C1904 = {
                                {
                                    OwlBuf::another_ref(&owl_kdfval545903).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let tmp_owl_H2905 = {
                                owl_crh(
                                    owl_concat(
                                        owl_H1902.as_slice(),
                                        owl_msg1_ephemeral897.as_slice(),
                                    ).as_slice(),
                                )
                            };
                            let owl_H2905 = OwlBuf::from_vec(tmp_owl_H2905);
                            let tmp_owl_ss_msg1_ephemeral_S_resp906 = {
                                owl_dh_combine(
                                    owl_msg1_ephemeral897.as_slice(),
                                    OwlBuf::from_slice(&self.owl_S_resp.as_slice()).as_slice(),
                                )
                            };
                            let owl_ss_msg1_ephemeral_S_resp906 = OwlBuf::from_vec(
                                tmp_owl_ss_msg1_ephemeral_S_resp906,
                            );
                            let tmp_owl_kdfval555907 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE + ENCKEY_SIZE,
                                    owl_C1904.as_slice(),
                                    owl_ss_msg1_ephemeral_S_resp906.as_slice(),
                                    {
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    }.as_slice(),
                                )
                            };
                            let owl_kdfval555907 = OwlBuf::from_vec(tmp_owl_kdfval555907);
                            let owl_C2908 = {
                                {
                                    OwlBuf::another_ref(&owl_kdfval555907).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let owl_k0909 = {
                                {
                                    OwlBuf::another_ref(&owl_kdfval555907).subrange(
                                        0 + KDFKEY_SIZE,
                                        0 + KDFKEY_SIZE + ENCKEY_SIZE,
                                    )
                                }
                            };
                            let tmp_owl_parseval910 = {
                                owl_dec_st_aead(
                                    owl_k0909.as_slice(),
                                    owl_msg1_static896.as_slice(),
                                    {
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    }.as_slice(),
                                    owl_H2905.as_slice(),
                                )
                            };
                            let owl_parseval910 = OwlBuf::from_vec_option(tmp_owl_parseval910);
                            let owl_caseval911 = { owl_parseval910 };
                            match owl_caseval911 {
                                Option::None => { (None, Tracked(itree)) },
                                Option::Some(tmp_owl_msg1_static_dec912) => {
                                    let owl_msg1_static_dec912 = OwlBuf::another_ref(
                                        &tmp_owl_msg1_static_dec912,
                                    );
                                    let (owl_oinfo913, Tracked(itree)) = {
                                        let tmp_arg1944 = OwlBuf::another_ref(
                                            &owl_msg1_static_dec912,
                                        );
                                        owl_call_ret_option!(itree, *mut_state, get_pk_info_spec(*self, *mut_state, tmp_arg1944.view()), self.owl_get_pk_info(mut_state, tmp_arg1944))
                                    };
                                    let owl_caseval914 = { owl_oinfo913 };
                                    match owl_caseval914 {
                                        Option::None => { (None, Tracked(itree)) },
                                        Option::Some(tmp_owl_info915) => {
                                            let owl_info915 = tmp_owl_info915;
                                            let owl_info916 = { owl_info915 };
                                            let parseval = owl_info916;
                                            let owl_ss918 = OwlBuf::another_ref(
                                                &parseval.owl_init_info_ss,
                                            );
                                            let owl_psk917 = parseval.owl_init_info_psk;
                                            let tmp_owl_H3919 = {
                                                owl_crh(
                                                    owl_concat(
                                                        owl_H2905.as_slice(),
                                                        owl_msg1_static896.as_slice(),
                                                    ).as_slice(),
                                                )
                                            };
                                            let owl_H3919 = OwlBuf::from_vec(tmp_owl_H3919);
                                            let owl_dhpk_S_init920 = { owl_msg1_static_dec912 };
                                            let tmp_owl_kdfval589921 = {
                                                owl_extract_expand_to_len(
                                                    0 + KDFKEY_SIZE + ENCKEY_SIZE,
                                                    owl_C2908.as_slice(),
                                                    owl_ss918.as_slice(),
                                                    {
                                                        let x = mk_vec_u8![];
                                                        OwlBuf::from_vec(x)
                                                    }.as_slice(),
                                                )
                                            };
                                            let owl_kdfval589921 = OwlBuf::from_vec(
                                                tmp_owl_kdfval589921,
                                            );
                                            let owl_C3922 = {
                                                {
                                                    OwlBuf::another_ref(&owl_kdfval589921).subrange(
                                                        0,
                                                        0 + KDFKEY_SIZE,
                                                    )
                                                }
                                            };
                                            let owl_k1923 = {
                                                {
                                                    OwlBuf::another_ref(&owl_kdfval589921).subrange(
                                                        0 + KDFKEY_SIZE,
                                                        0 + KDFKEY_SIZE + ENCKEY_SIZE,
                                                    )
                                                }
                                            };
                                            let tmp_owl_parseval924 = {
                                                owl_dec_st_aead(
                                                    owl_k1923.as_slice(),
                                                    owl_msg1_timestamp895.as_slice(),
                                                    {
                                                        let x = mk_vec_u8![];
                                                        OwlBuf::from_vec(x)
                                                    }.as_slice(),
                                                    owl_H3919.as_slice(),
                                                )
                                            };
                                            let owl_parseval924 = OwlBuf::from_vec_option(
                                                tmp_owl_parseval924,
                                            );
                                            let owl_caseval925 = { owl_parseval924 };
                                            match owl_caseval925 {
                                                Option::None => { (None, Tracked(itree)) },
                                                Option::Some(tmp_owl_msg1_timestamp_dec926) => {
                                                    let owl_msg1_timestamp_dec926 =
                                                        OwlBuf::another_ref(
                                                        &tmp_owl_msg1_timestamp_dec926,
                                                    );
                                                    let tmp_owl_H4927 = {
                                                        owl_crh(
                                                            owl_concat(
                                                                owl_H3919.as_slice(),
                                                                owl_msg1_timestamp895.as_slice(),
                                                            ).as_slice(),
                                                        )
                                                    };
                                                    let owl_H4927 = OwlBuf::from_vec(tmp_owl_H4927);
                                                    let owl_st928 = {
                                                        owl_resp_received_state(
                                                            OwlBuf::another_ref(
                                                                &owl_msg1_sender898,
                                                            ),
                                                            owl_psk917,
                                                            OwlBuf::another_ref(
                                                                &owl_dhpk_S_init920,
                                                            ),
                                                            OwlBuf::another_ref(
                                                                &owl_msg1_ephemeral897,
                                                            ),
                                                            owl_ghost_unit(),
                                                            OwlBuf::another_ref(&owl_H4927),
                                                            OwlBuf::another_ref(&owl_C3922),
                                                        )
                                                    };
                                                    let owl_y929 = { owl_st928 };
                                                    (Some(owl_y929), Tracked(itree))
                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        } else {
                            (None, Tracked(itree))
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

    #[verifier::external_body]
    #[verifier::spinoff_prover]
    pub fn owl_get_pk_info<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Option<owlSpec_init_info>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_pk945: OwlBuf<'a>,
    ) -> (res: Result<
        (
            Option<owl_init_info<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_init_info>, state_Responder), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == get_pk_info_spec(*self, *old(mut_state), owl_pk945.view()),
            owl_pk945.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
            res matches Ok((Some(b), _)) ==> b.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_init_info<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_init_info>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(get_pk_info_spec);
            use x25519_dalek::{PublicKey};
            use std::convert::TryInto;

            let pk: [u8; 32] = (&owl_pk945).as_slice().try_into().unwrap();
            let ss = self.device.as_ref().unwrap().get_ss(&pk).map(|ss| ss.to_vec());
            let psk = self.device.as_ref().unwrap().get_psk(&pk).map(|psk| psk.to_vec());
            let res = match (ss, psk) {
                (Some(ss), Some(psk)) => Some(owl_init_info {
                    owl_init_info_ss: OwlBuf::from_vec(ss),
                    owl_init_info_psk: owl_PSKMode::owl_HasPSK(OwlBuf::from_vec(psk)),
                }),
                _ => None,
            };
            (res, Tracked(itree))

        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::external_body]
    #[verifier::spinoff_prover]
    pub fn owl_timestamp_r<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
    ) -> (res: Result<
        (OwlBuf<'a>, Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == timestamp_r_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
            res matches Ok(r) ==> r.0.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            OwlBuf<'a>,
            Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(timestamp_r_spec);
            let t = crate::wireguard::handshake::timestamp::now().to_vec();
            (OwlBuf::from_vec(t), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::external_body]
    #[verifier::spinoff_prover]
    pub fn owl_get_sender_r<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
    ) -> (res: Result<
        (OwlBuf<'a>, Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == get_sender_r_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
            res matches Ok(r) ==> r.0.len_valid(),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            OwlBuf<'a>,
            Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(get_sender_r_spec);
            let v = self.device.as_ref().unwrap().get_singleton_id();
            (OwlBuf::from_vec(v.to_le_bytes().to_vec()), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }
}


// ------------------------------------
// ------ USER-DEFINED FUNCTIONS ------
// ------------------------------------

pub fn owl_construction<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == construction(),
        res.len_valid(),
{
    reveal(construction);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x4eu8, 0x6fu8, 0x69u8, 0x73u8, 0x65u8, 0x5fu8, 0x49u8, 0x4bu8, 0x70u8, 0x73u8, 0x6bu8, 0x32u8, 0x5fu8, 0x32u8, 0x35u8, 0x35u8, 0x31u8, 0x39u8, 0x5fu8, 0x43u8, 0x68u8, 0x61u8, 0x43u8, 0x68u8, 0x61u8, 0x50u8, 0x6fu8, 0x6cu8, 0x79u8, 0x5fu8, 0x42u8, 0x4cu8, 0x41u8, 0x4bu8, 0x45u8, 0x32u8, 0x73u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_honest_c1() -> (res: Ghost<()>)
    ensures
        res.view() == honest_c1(),
{
    reveal(honest_c1);
    owl_ghost_unit()
}

pub fn owl_honest_c3() -> (res: Ghost<()>)
    ensures
        res.view() == honest_c3(),
{
    reveal(honest_c3);
    owl_ghost_unit()
}

pub fn owl_honest_c4() -> (res: Ghost<()>)
    ensures
        res.view() == honest_c4(),
{
    reveal(honest_c4);
    owl_ghost_unit()
}

pub fn owl_identifier<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == identifier(),
        res.len_valid(),
{
    reveal(identifier);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x57u8, 0x69u8, 0x72u8, 0x65u8, 0x47u8, 0x75u8, 0x61u8, 0x72u8, 0x64u8, 0x20u8, 0x76u8, 0x31u8, 0x20u8, 0x7au8, 0x78u8, 0x32u8, 0x63u8, 0x34u8, 0x20u8, 0x4au8, 0x61u8, 0x73u8, 0x6fu8, 0x6eu8, 0x40u8, 0x7au8, 0x78u8, 0x32u8, 0x63u8, 0x34u8, 0x2eu8, 0x63u8, 0x6fu8, 0x6du8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_mac1<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == mac1(),
        res.len_valid(),
{
    reveal(mac1);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x6du8, 0x61u8, 0x63u8, 0x31u8, 0x2du8, 0x2du8, 0x2du8, 0x2du8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_msg1_tag_value<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == msg1_tag_value(),
        res.len_valid(),
{
    reveal(msg1_tag_value);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x01u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_msg2_tag_value<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == msg2_tag_value(),
        res.len_valid(),
{
    reveal(msg2_tag_value);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x02u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_transp_tag_value<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == transp_tag_value(),
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

pub fn owl_zeros_16<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == zeros_16(),
        res.len_valid(),
{
    reveal(zeros_16);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_zeros_32<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == zeros_32(),
        res.len_valid(),
{
    reveal(zeros_32);
    OwlBuf::another_ref(
        &{
            let x =
                mk_vec_u8![0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

// ------------------------------------
// ------------ ENTRY POINT -----------
// ------------------------------------
// no entry point

} // verus!
