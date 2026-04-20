// Extracted verus code from file tests/wip/wg/full.owl:
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::{modes::*, prelude::*, seq::*, string::*, slice::*};
use crate::speclib::{*, itree::*};
use crate::execlib::{*};
use crate::*;
use crate::owl_const_bytes::*;
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
    (ibuf, "".to_string()) // Specific to Wireguard---we never use the endpoints
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
pub enum owlSpec_PSKMode {
    owlSpec_HasPSK(Seq<u8>),
    owlSpec_NoPSK(),
}

use owlSpec_PSKMode::*;

#[verifier::opaque]
pub closed spec fn parse_owlSpec_PSKMode(x: Seq<u8>) -> Option<owlSpec_PSKMode> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Bytes(32)), (Tag::spec_new(U8, 2), Bytes(0)));
    if let Ok((_, parsed)) = spec_comb.spec_parse(x) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owlSpec_PSKMode::owlSpec_HasPSK(x),
            inj_ord_choice_pat!(*, _) => owlSpec_PSKMode::owlSpec_NoPSK(),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_PSKMode_inner(x: owlSpec_PSKMode) -> Option<Seq<u8>> {
    let spec_comb =
        ord_choice!((Tag::spec_new(U8, 1), Bytes(32)), (Tag::spec_new(U8, 2), Bytes(0)));
    match x {
        owlSpec_PSKMode::owlSpec_HasPSK(x) => {
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
        owlSpec_PSKMode::owlSpec_NoPSK() => {
            if no_usize_overflows_spec![ 1, 0 ] {
                if let Ok(serialized) = spec_comb.spec_serialize(
                    inj_ord_choice_result!(*, ((), seq![])),
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
pub closed spec fn serialize_owlSpec_PSKMode(x: owlSpec_PSKMode) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_PSKMode_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_PSKMode {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_PSKMode(self)
    }
}

pub open spec fn HasPSK(x: Seq<u8>) -> owlSpec_PSKMode {
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

spec const SPEC_BYTES_CONST_01000000_MSG1: [u8; 4] = [0x01u8, 0x00u8, 0x00u8, 0x00u8];

spec const SPEC_BYTES_CONST_00000000000000000000000000000000_MSG1: [u8; 16] = [
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

exec const EXEC_BYTES_CONST_01000000_MSG1: [u8; 4]
    ensures
        EXEC_BYTES_CONST_01000000_MSG1 == SPEC_BYTES_CONST_01000000_MSG1,
{
    let arr: [u8; 4] = [0x01u8, 0x00u8, 0x00u8, 0x00u8];
    assert(arr == SPEC_BYTES_CONST_01000000_MSG1);
    arr
}

exec const EXEC_BYTES_CONST_00000000000000000000000000000000_MSG1: [u8; 16]
    ensures
        EXEC_BYTES_CONST_00000000000000000000000000000000_MSG1
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
    assert(arr == SPEC_BYTES_CONST_00000000000000000000000000000000_MSG1);
    arr
}

spec fn spec_combinator_owlSpec_msg1() -> (
    (((((OwlConstBytes<4>, Bytes), Bytes), Bytes), Bytes), Bytes),
    OwlConstBytes<16>,
) {
    let field_1 = OwlConstBytes::<4>(SPEC_BYTES_CONST_01000000_MSG1);
    let field_2 = Bytes(4);
    let field_3 = Bytes(32);
    let field_4 = Bytes(48);
    let field_5 = Bytes(28);
    let field_6 = Bytes(16);
    let field_7 = OwlConstBytes::<16>(SPEC_BYTES_CONST_00000000000000000000000000000000_MSG1);
    ((((((field_1, field_2), field_3), field_4), field_5), field_6), field_7)
}

exec fn exec_combinator_owl_msg1() -> (res: (
    (((((OwlConstBytes<4>, Bytes), Bytes), Bytes), Bytes), Bytes),
    OwlConstBytes<16>,
))
    ensures
        res.view() == spec_combinator_owlSpec_msg1(),
{
    let field_1 = OwlConstBytes::<4>(EXEC_BYTES_CONST_01000000_MSG1);
    let field_2 = Bytes(4);
    let field_3 = Bytes(32);
    let field_4 = Bytes(48);
    let field_5 = Bytes(28);
    let field_6 = Bytes(16);
    let field_7 = OwlConstBytes::<16>(EXEC_BYTES_CONST_00000000000000000000000000000000_MSG1);
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

spec const SPEC_BYTES_CONST_02000000_MSG2: [u8; 4] = [0x02u8, 0x00u8, 0x00u8, 0x00u8];

spec const SPEC_BYTES_CONST_00000000000000000000000000000000_MSG2: [u8; 16] = [
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

exec const EXEC_BYTES_CONST_02000000_MSG2: [u8; 4]
    ensures
        EXEC_BYTES_CONST_02000000_MSG2 == SPEC_BYTES_CONST_02000000_MSG2,
{
    let arr: [u8; 4] = [0x02u8, 0x00u8, 0x00u8, 0x00u8];
    assert(arr == SPEC_BYTES_CONST_02000000_MSG2);
    arr
}

exec const EXEC_BYTES_CONST_00000000000000000000000000000000_MSG2: [u8; 16]
    ensures
        EXEC_BYTES_CONST_00000000000000000000000000000000_MSG2
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
    assert(arr == SPEC_BYTES_CONST_00000000000000000000000000000000_MSG2);
    arr
}

spec fn spec_combinator_owlSpec_msg2() -> (
    (((((OwlConstBytes<4>, Bytes), Bytes), Bytes), Bytes), Bytes),
    OwlConstBytes<16>,
) {
    let field_1 = OwlConstBytes::<4>(SPEC_BYTES_CONST_02000000_MSG2);
    let field_2 = Bytes(4);
    let field_3 = Bytes(4);
    let field_4 = Bytes(32);
    let field_5 = Bytes(16);
    let field_6 = Bytes(16);
    let field_7 = OwlConstBytes::<16>(SPEC_BYTES_CONST_00000000000000000000000000000000_MSG2);
    ((((((field_1, field_2), field_3), field_4), field_5), field_6), field_7)
}

exec fn exec_combinator_owl_msg2() -> (res: (
    (((((OwlConstBytes<4>, Bytes), Bytes), Bytes), Bytes), Bytes),
    OwlConstBytes<16>,
))
    ensures
        res.view() == spec_combinator_owlSpec_msg2(),
{
    let field_1 = OwlConstBytes::<4>(EXEC_BYTES_CONST_02000000_MSG2);
    let field_2 = Bytes(4);
    let field_3 = Bytes(4);
    let field_4 = Bytes(32);
    let field_5 = Bytes(16);
    let field_6 = Bytes(16);
    let field_7 = OwlConstBytes::<16>(EXEC_BYTES_CONST_00000000000000000000000000000000_MSG2);
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

spec const SPEC_BYTES_CONST_04000000_TRANSP: [u8; 4] = [0x04u8, 0x00u8, 0x00u8, 0x00u8];

exec const EXEC_BYTES_CONST_04000000_TRANSP: [u8; 4]
    ensures
        EXEC_BYTES_CONST_04000000_TRANSP == SPEC_BYTES_CONST_04000000_TRANSP,
{
    let arr: [u8; 4] = [0x04u8, 0x00u8, 0x00u8, 0x00u8];
    assert(arr == SPEC_BYTES_CONST_04000000_TRANSP);
    arr
}

spec fn spec_combinator_owlSpec_transp() -> (((OwlConstBytes<4>, Bytes), Bytes), Tail) {
    let field_1 = OwlConstBytes::<4>(SPEC_BYTES_CONST_04000000_TRANSP);
    let field_2 = Bytes(4);
    let field_3 = Bytes(8);
    let field_4 = Tail;
    (((field_1, field_2), field_3), field_4)
}

exec fn exec_combinator_owl_transp() -> (res: (((OwlConstBytes<4>, Bytes), Bytes), Tail))
    ensures
        res.view() == spec_combinator_owlSpec_transp(),
{
    let field_1 = OwlConstBytes::<4>(EXEC_BYTES_CONST_04000000_TRANSP);
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
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_transp_keys_init_inner(x: owlSpec_transp_keys_init) -> Option<
    Seq<u8>,
> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_transp_keys_init(x: owlSpec_transp_keys_init) -> Seq<u8> {
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
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_transp_keys_resp_inner(x: owlSpec_transp_keys_resp) -> Option<
    Seq<u8>,
> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_transp_keys_resp(x: owlSpec_transp_keys_resp) -> Seq<u8> {
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
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_init_sent_state_inner(x: owlSpec_init_sent_state) -> Option<
    Seq<u8>,
> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_init_sent_state(x: owlSpec_init_sent_state) -> Seq<u8> {
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
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_init_info_inner(x: owlSpec_init_info) -> Option<Seq<u8>> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_init_info(x: owlSpec_init_info) -> Seq<u8> {
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
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_resp_received_state_inner(
    x: owlSpec_resp_received_state,
) -> Option<Seq<u8>> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_resp_received_state(x: owlSpec_resp_received_state) -> Seq<
    u8,
> {
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
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_resp_transp_recv_result_inner(
    x: owlSpec_resp_transp_recv_result,
) -> Option<Seq<u8>> {
    todo!()
}

#[verifier::external_body]
pub closed spec fn serialize_owlSpec_resp_transp_recv_result(
    x: owlSpec_resp_transp_recv_result,
) -> Seq<u8> {
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
let _unused798 = (call(init_sent_message_spec(cfg, mut_state, ghost_unit()))) in
let N_init_send = ((ret(counter_as_bytes(mut_state.owl_N_init_send)))) in
let _unused799 = (((inc_counter(owl_N_init_send)))) in
let c = ((ret(enc_st_aead(init_send, msg, N_init_send, empty_seq_u8())))) in
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
        (input(i,_139)) in
(parse (tki) as (owlSpec_transp_keys_init{owlSpec_tki_msg2_receiver : init, owlSpec_tki_msg2_sender : resp, owlSpec_tki_has_psk : haspsk, owlSpec_tki_eph : eph, owlSpec_tki_c7 : c7, owlSpec_tki_k_init_send : init_send, owlSpec_tki_k_resp_send : resp_send}) in {
(parse (parse_owlSpec_transp(i)) as (owlSpec_transp{owlSpec__transp_tag : tag, owlSpec__transp_receiver : from, owlSpec__transp_counter : ctr, owlSpec__transp_packet : pkt}) in {
(if (from == resp) then
(let p = ((declassify(DeclassifyingOp::StAeadDec(resp_send, pkt, ctr, empty_seq_u8()))) in
(ret(dec_st_aead(resp_send, pkt, ctr, empty_seq_u8())))) in
let _unused801 = (let _unused802 = (let caseval = ((ret(p))) in
(case (caseval) {
| None => {
(ret(()))
},
| Some(m) => {
let _assert_21 = ((ret(ghost_unit()))) in
(ret(()))
},
}
)) in
(ret(()))) in
(ret(p)))
else
((ret(Option::None))))
} otherwise ((ret(Option::None))))
} )
    )
}

#[verifier::opaque]
pub open spec fn init_sent_message_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    x: Ghost<()>,
) -> (res: ITree<((), state_Initiator), Endpoint>) {
    owl_spec!(mut_state, state_Initiator,
        (ret(()))
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
(input(i,_200)) in
(parse (parse_owlSpec_msg2(i)) as (owlSpec_msg2{owlSpec__msg2_tag : msg2_tag, owlSpec__msg2_sender : msg2_sender, owlSpec__msg2_receiver : msg2_receiver, owlSpec__msg2_ephemeral : msg2_ephemeral, owlSpec__msg2_empty : msg2_empty_enc, owlSpec__msg2_mac1 : msg2_mac1, owlSpec__msg2_mac2 : msg2_mac2}) in {
(if (andb(length(msg2_sender) == 4, length(msg2_receiver) == 4)) then
((if (is_group_elem(msg2_ephemeral)) then
(let e_init = ((ret(cfg.owl_E_init.view()))) in
let kdfval220 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, c3, msg2_ephemeral, empty_seq_u8())))) in
let c4 = ((ret(Seq::subrange(kdfval220, 0, 0 + KDFKEY_SIZE)))) in
let h5 = ((ret(crh(concat(h4, msg2_ephemeral))))) in
let ss = ((ret(dh_combine(msg2_ephemeral, e_init)))) in
let kdfval254 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, c4, ss, empty_seq_u8())))) in
let c5 = ((ret(Seq::subrange(kdfval254, 0, 0 + KDFKEY_SIZE)))) in
let kdfval267 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, c5, dh_combine(msg2_ephemeral, cfg.owl_S_init.view()), empty_seq_u8())))) in
let c6 = ((ret(Seq::subrange(kdfval267, 0, 0 + KDFKEY_SIZE)))) in
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
let kdfval276 = ((ret(kdf((0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE) as usize, c6, psk, empty_seq_u8())))) in
let c7 = ((ret(Seq::subrange(kdfval276, 0, 0 + KDFKEY_SIZE)))) in
let tau = ((ret(Seq::subrange(kdfval276, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + NONCE_SIZE)))) in
let k0 = ((ret(Seq::subrange(kdfval276, 0 + KDFKEY_SIZE + NONCE_SIZE, 0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE)))) in
let h6 = ((ret(crh(concat(h5, tau))))) in
let caseval = ((declassify(DeclassifyingOp::StAeadDec(k0, msg2_empty_enc, empty_seq_u8(), h6))) in
(ret(dec_st_aead(k0, msg2_empty_enc, empty_seq_u8(), h6)))) in
(case (caseval) {
| None => {
(ret(Option::None))
},
| Some(x) => {
let kdfval286 = ((ret(kdf((0 + ENCKEY_SIZE + ENCKEY_SIZE) as usize, c7, empty_seq_u8(), empty_seq_u8())))) in
let k1 = ((ret(Seq::subrange(kdfval286, 0, 0 + ENCKEY_SIZE)))) in
let k2 = ((ret(Seq::subrange(kdfval286, 0 + ENCKEY_SIZE, 0 + ENCKEY_SIZE + ENCKEY_SIZE)))) in
let _unused805 = (call(key_confirm_initiator_send_spec(cfg, mut_state, ghost_unit()))) in
let _unused806 = (call(key_confirm_initiator_recv_spec(cfg, mut_state, ghost_unit()))) in
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
let kdfval307 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, C0, e_init, empty_seq_u8())))) in
let C1 = ((ret(Seq::subrange(kdfval307, 0, 0 + KDFKEY_SIZE)))) in
let H2 = ((ret(crh(concat(H1, e_init))))) in
let ss_S_resp_E_init = ((ret(dh_combine(dhpk_S_resp, cfg.owl_E_init.view())))) in
let kdfval312 = ((ret(kdf((0 + KDFKEY_SIZE + ENCKEY_SIZE) as usize, C1, ss_S_resp_E_init, empty_seq_u8())))) in
let C2 = ((ret(Seq::subrange(kdfval312, 0, 0 + KDFKEY_SIZE)))) in
let k0 = ((ret(Seq::subrange(kdfval312, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + ENCKEY_SIZE)))) in
let aead_counter_msg1_C2 = ((ret(counter_as_bytes(mut_state.owl_aead_counter_msg1_C2)))) in
let _unused811 = (((inc_counter(owl_aead_counter_msg1_C2)))) in
let msg1_static = ((ret(enc_st_aead(k0, dhpk_S_init, aead_counter_msg1_C2, H2)))) in
let H3 = ((ret(crh(concat(H2, msg1_static))))) in
let kdfval321 = ((ret(kdf((0 + KDFKEY_SIZE + ENCKEY_SIZE) as usize, C2, ss_S_resp_S_init, empty_seq_u8())))) in
let c3 = ((ret(Seq::subrange(kdfval321, 0, 0 + KDFKEY_SIZE)))) in
let k1 = ((ret(Seq::subrange(kdfval321, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + ENCKEY_SIZE)))) in
let timestamp = (call(timestamp_i_spec(cfg, mut_state))) in
let aead_counter_msg1_C3 = ((ret(counter_as_bytes(mut_state.owl_aead_counter_msg1_C3)))) in
let _unused812 = (((inc_counter(owl_aead_counter_msg1_C3)))) in
let msg1_timestamp = ((ret(enc_st_aead(k1, timestamp, aead_counter_msg1_C3, H3)))) in
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
pub open spec fn key_confirm_initiator_recv_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    k: Ghost<()>,
) -> (res: ITree<((), state_Initiator), Endpoint>) {
    owl_spec!(mut_state, state_Initiator,
        (ret(()))
    )
}

#[verifier::opaque]
pub open spec fn key_confirm_initiator_send_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    k: Ghost<()>,
) -> (res: ITree<((), state_Initiator), Endpoint>) {
    owl_spec!(mut_state, state_Initiator,
        (ret(()))
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
let _unused817 = (call(resp_sent_message_spec(cfg, mut_state, ghost_unit()))) in
let N_resp_send = ((ret(counter_as_bytes(mut_state.owl_N_resp_send)))) in
let _unused818 = (((inc_counter(owl_N_resp_send)))) in
let c = ((ret(enc_st_aead(resp_send, msg, N_resp_send, empty_seq_u8())))) in
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
        (input(i,_407)) in
let tki_ = ((ret(tki))) in
(parse (tki_) as (owlSpec_transp_keys_resp{owlSpec_tkr_msg2_receiver : init, owlSpec_tkr_msg2_sender : resp, owlSpec_tkr_has_psk : haspsk, owlSpec_tkr_eph : eph, owlSpec_tkr_c7 : c7, owlSpec_tkr_recvd : _unused820, owlSpec_tkr_k_init_send : init_send, owlSpec_tkr_k_resp_send : resp_send}) in {
(parse (parse_owlSpec_transp(i)) as (owlSpec_transp{owlSpec__transp_tag : tag, owlSpec__transp_receiver : from, owlSpec__transp_counter : ctr, owlSpec__transp_packet : pkt}) in {
(if (from == init) then
(let caseval = ((declassify(DeclassifyingOp::StAeadDec(init_send, pkt, ctr, empty_seq_u8()))) in
(ret(dec_st_aead(init_send, pkt, ctr, empty_seq_u8())))) in
(case (caseval) {
| Some(x) => {
let st_ = ((ret(transp_keys_resp(init, resp, haspsk, ghost_unit(), ghost_unit(), true, init_send, resp_send)))) in
let ret = ((ret(resp_transp_recv_result(st_, x)))) in
let _assert_82 = ((ret(ghost_unit()))) in
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
pub open spec fn resp_sent_message_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    x: Ghost<()>,
) -> (res: ITree<((), state_Responder), Endpoint>) {
    owl_spec!(mut_state, state_Responder,
        (ret(()))
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
let kdfval529 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, C3, e_resp_pk, empty_seq_u8())))) in
let c4 = ((ret(Seq::subrange(kdfval529, 0, 0 + KDFKEY_SIZE)))) in
let h5 = ((ret(crh(concat(H4, e_resp_pk))))) in
let ss = ((ret(dh_combine(msg1_ephemeral, cfg.owl_E_resp.view())))) in
let kdfval542 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, c4, ss, empty_seq_u8())))) in
let c5 = ((ret(Seq::subrange(kdfval542, 0, 0 + KDFKEY_SIZE)))) in
let kdfval549 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, c5, dh_combine(dhpk_S_init, cfg.owl_E_resp.view()), empty_seq_u8())))) in
let c6 = ((ret(Seq::subrange(kdfval549, 0, 0 + KDFKEY_SIZE)))) in
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
let kdfval558 = ((ret(kdf((0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE) as usize, c6, psk_val, empty_seq_u8())))) in
let c7 = ((ret(Seq::subrange(kdfval558, 0, 0 + KDFKEY_SIZE)))) in
let tau = ((ret(Seq::subrange(kdfval558, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + NONCE_SIZE)))) in
let k0 = ((ret(Seq::subrange(kdfval558, 0 + KDFKEY_SIZE + NONCE_SIZE, 0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE)))) in
let msg2_tag = ((ret(msg2_tag_value()))) in
let msg2_sender = (call(get_sender_r_spec(cfg, mut_state))) in
let msg2_mac1_k = ((ret(crh(concat(mac1(), dhpk_S_init))))) in
let h6 = ((ret(crh(concat(h5, tau))))) in
let kdfval568 = ((ret(kdf((0 + ENCKEY_SIZE + ENCKEY_SIZE) as usize, c7, empty_seq_u8(), empty_seq_u8())))) in
let tk1 = ((ret(Seq::subrange(kdfval568, 0, 0 + ENCKEY_SIZE)))) in
let tk2 = ((ret(Seq::subrange(kdfval568, 0 + ENCKEY_SIZE, 0 + ENCKEY_SIZE + ENCKEY_SIZE)))) in
let _unused823 = (call(key_confirm_responder_recv_spec(cfg, mut_state, ghost_unit()))) in
let _unused824 = (call(key_confirm_responder_send_spec(cfg, mut_state, ghost_unit()))) in
let aead_counter_msg2_C7 = ((ret(counter_as_bytes(mut_state.owl_aead_counter_msg2_C7)))) in
let _unused825 = (((inc_counter(owl_aead_counter_msg2_C7)))) in
let msg2_empty = ((ret(enc_st_aead(k0, empty_seq_u8(), aead_counter_msg2_C7, h6)))) in
let msg2_mac1 = ((ret(mac(msg2_mac1_k, concat(concat(concat(concat(msg2_tag, msg2_sender), msg2_receiver), e_resp_pk), msg2_empty))))) in
let _assert_273 = ((ret(ghost_unit()))) in
let msg2_mac2 = ((ret(zeros_16()))) in
let msg2_output = ((ret(msg2((), msg2_sender, msg2_receiver, e_resp_pk, msg2_empty, msg2_mac1, ())))) in
(output (serialize_owlSpec_msg2(msg2_output)) to (Endpoint::Loc_Initiator)) in
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
        (input(inp,_589)) in
(parse (parse_owlSpec_msg1(inp)) as (owlSpec_msg1{owlSpec__msg1_tag : msg1_tag, owlSpec__msg1_sender : msg1_sender, owlSpec__msg1_ephemeral : msg1_ephemeral, owlSpec__msg1_static : msg1_static, owlSpec__msg1_timestamp : msg1_timestamp, owlSpec__msg1_mac1 : msg1_mac1, owlSpec__msg1_mac2 : msg1_mac2}) in {
(if (length(msg1_sender) == 4) then
((if (is_group_elem(msg1_ephemeral)) then
(let C0 = ((ret(crh(construction())))) in
let H0 = ((ret(crh(concat(C0, identifier()))))) in
let H1 = ((ret(crh(concat(H0, dhpk_S_resp))))) in
let kdfval611 = ((ret(kdf((0 + KDFKEY_SIZE) as usize, C0, msg1_ephemeral, empty_seq_u8())))) in
let C1 = ((ret(Seq::subrange(kdfval611, 0, 0 + KDFKEY_SIZE)))) in
let H2 = ((ret(crh(concat(H1, msg1_ephemeral))))) in
let ss_msg1_ephemeral_S_resp = ((ret(dh_combine(msg1_ephemeral, cfg.owl_S_resp.view())))) in
let kdfval621 = ((ret(kdf((0 + KDFKEY_SIZE + ENCKEY_SIZE) as usize, C1, ss_msg1_ephemeral_S_resp, empty_seq_u8())))) in
let C2 = ((ret(Seq::subrange(kdfval621, 0, 0 + KDFKEY_SIZE)))) in
let k0 = ((ret(Seq::subrange(kdfval621, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + ENCKEY_SIZE)))) in
let caseval = ((declassify(DeclassifyingOp::StAeadDec(k0, msg1_static, empty_seq_u8(), H2))) in
(ret(dec_st_aead(k0, msg1_static, empty_seq_u8(), H2)))) in
(case (caseval) {
| None => {
(ret(Option::None))
},
| Some(msg1_static_dec) => {
let declassified_buf = ((declassify(DeclassifyingOp::ControlFlow(msg1_static_dec))) in
(ret((msg1_static_dec)))) in
let oinfo = (call(get_pk_info_spec(cfg, mut_state, declassified_buf))) in
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
let kdfval658 = ((ret(kdf((0 + KDFKEY_SIZE + ENCKEY_SIZE) as usize, C2, ss, empty_seq_u8())))) in
let C3 = ((ret(Seq::subrange(kdfval658, 0, 0 + KDFKEY_SIZE)))) in
let k1 = ((ret(Seq::subrange(kdfval658, 0 + KDFKEY_SIZE, 0 + KDFKEY_SIZE + ENCKEY_SIZE)))) in
let caseval = ((declassify(DeclassifyingOp::StAeadDec(k1, msg1_timestamp, empty_seq_u8(), H3))) in
(ret(dec_st_aead(k1, msg1_timestamp, empty_seq_u8(), H3)))) in
(case (caseval) {
| None => {
(ret(Option::None))
},
| Some(msg1_timestamp_dec) => {
let H4 = ((ret(crh(concat(H3, msg1_timestamp))))) in
let declassified_buf = ((declassify(DeclassifyingOp::ControlFlow(dhpk_S_init))) in
(ret((dhpk_S_init)))) in
let st = ((ret(resp_received_state(msg1_sender, psk, declassified_buf, msg1_ephemeral, ghost_unit(), H4, C3)))) in
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
pub open spec fn key_confirm_responder_recv_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    k: Ghost<()>,
) -> (res: ITree<((), state_Responder), Endpoint>) {
    owl_spec!(mut_state, state_Responder,
        (ret(()))
    )
}

#[verifier::opaque]
pub open spec fn key_confirm_responder_send_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    k: Ghost<()>,
) -> (res: ITree<((), state_Responder), Endpoint>) {
    owl_spec!(mut_state, state_Responder,
        (ret(()))
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
pub closed spec fn construction() -> (res: Seq<u8>) {
    seq![
        0x4eu8,
        0x6fu8,
        0x69u8,
        0x73u8,
        0x65u8,
        0x5fu8,
        0x49u8,
        0x4bu8,
        0x70u8,
        0x73u8,
        0x6bu8,
        0x32u8,
        0x5fu8,
        0x32u8,
        0x35u8,
        0x35u8,
        0x31u8,
        0x39u8,
        0x5fu8,
        0x43u8,
        0x68u8,
        0x61u8,
        0x43u8,
        0x68u8,
        0x61u8,
        0x50u8,
        0x6fu8,
        0x6cu8,
        0x79u8,
        0x5fu8,
        0x42u8,
        0x4cu8,
        0x41u8,
        0x4bu8,
        0x45u8,
        0x32u8,
        0x73u8,
    ]
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
    seq![
        0x57u8,
        0x69u8,
        0x72u8,
        0x65u8,
        0x47u8,
        0x75u8,
        0x61u8,
        0x72u8,
        0x64u8,
        0x20u8,
        0x76u8,
        0x31u8,
        0x20u8,
        0x7au8,
        0x78u8,
        0x32u8,
        0x63u8,
        0x34u8,
        0x20u8,
        0x4au8,
        0x61u8,
        0x73u8,
        0x6fu8,
        0x6eu8,
        0x40u8,
        0x7au8,
        0x78u8,
        0x32u8,
        0x63u8,
        0x34u8,
        0x2eu8,
        0x63u8,
        0x6fu8,
        0x6du8,
    ]
}

#[verifier::opaque]
pub closed spec fn mac1() -> (res: Seq<u8>) {
    seq![0x6du8, 0x61u8, 0x63u8, 0x31u8, 0x2du8, 0x2du8, 0x2du8, 0x2du8]
}

#[verifier::opaque]
pub closed spec fn msg1_tag_value() -> (res: Seq<u8>) {
    seq![0x01u8, 0x00u8, 0x00u8, 0x00u8]
}

#[verifier::opaque]
pub closed spec fn msg2_tag_value() -> (res: Seq<u8>) {
    seq![0x02u8, 0x00u8, 0x00u8, 0x00u8]
}

#[verifier::opaque]
pub closed spec fn transp_tag_value() -> (res: Seq<u8>) {
    seq![0x04u8, 0x00u8, 0x00u8, 0x00u8]
}

#[verifier::opaque]
pub closed spec fn zeros_16() -> (res: Seq<u8>) {
    seq![
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
    ]
}

#[verifier::opaque]
pub closed spec fn zeros_32() -> (res: Seq<u8>) {
    seq![
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
    ]
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
    owl_HasPSK(SecretBuf<'a>),
    owl_NoPSK(),
}

use owl_PSKMode::*;

impl<'a> owl_PSKMode<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_PSKMode<'a>)
        ensures
            result.view() == self.view(),
    {
        match self {
            owl_HasPSK(x) => owl_HasPSK(SecretBuf::another_ref(x)),
            owl_NoPSK() => owl_NoPSK(),
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

#[verifier(external_body)]
pub exec fn parse_owl_PSKMode<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_PSKMode<'a>>)
    ensures
        res is Some ==> parse_owlSpec_PSKMode(arg.view()) is Some,
        res is None ==> parse_owlSpec_PSKMode(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_PSKMode(arg.view())->Some_0,
{
    reveal(parse_owlSpec_PSKMode);
    let exec_comb = ord_choice!((Tag::new(U8, 1), Bytes(32)), (Tag::new(U8, 2), Bytes(0)));
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let v = match parsed {
            inj_ord_choice_pat!((_,x), *) => owl_PSKMode::owl_HasPSK(
                SecretBuf::from_buf(x.another_ref()),
            ),
            inj_ord_choice_pat!(*, _) => owl_PSKMode::owl_NoPSK(),
        };
        Some(v)
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn serialize_owl_PSKMode_inner(arg: &owl_PSKMode) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_PSKMode_inner(arg.view()) is Some,
        res is None ==> serialize_owlSpec_PSKMode_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_PSKMode_inner(arg.view())->Some_0,
{
    todo!()/* reveal(serialize_owlSpec_PSKMode_inner);
    let empty_vec: Vec<u8> = mk_vec_u8![];
    let exec_comb = ord_choice!((Tag::new(U8, 1), Bytes(32)), (Tag::new(U8, 2), Bytes(0)));
    match arg {
        owl_PSKMode::owl_HasPSK(x) => {
    if no_usize_overflows![ 1, x.len() ] {
        let mut obuf = vec_u8_of_len(1 + x.len());
        let ser_result = exec_comb.serialize(inj_ord_choice_result!(((), x.as_slice()), *), &mut obuf, 0);
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_PSKMode_inner(arg.view())->Some_0);
            Some(obuf)
        } else {
            None
        }
    } else {
        None
    }
},
owl_PSKMode::owl_NoPSK() => {
    if no_usize_overflows![ 1, 0 ] {
        let mut obuf = vec_u8_of_len(1 + 0);
        let ser_result = exec_comb.serialize(inj_ord_choice_result!(*, ((), &empty_vec.as_slice())), &mut obuf, 0);
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_PSKMode_inner(arg.view())->Some_0);
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
pub exec fn serialize_owl_PSKMode(arg: &owl_PSKMode) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_PSKMode(arg.view()),
{
    reveal(serialize_owlSpec_PSKMode);
    let res = serialize_owl_PSKMode_inner(arg);
    assume(res is Some);
    res.unwrap()
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
    ensures
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

impl<'a> owl_msg1<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg1<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg1 {
            owl__msg1_tag: self.owl__msg1_tag,
            owl__msg1_sender: OwlBuf::another_ref(&self.owl__msg1_sender),
            owl__msg1_ephemeral: OwlBuf::another_ref(&self.owl__msg1_ephemeral),
            owl__msg1_static: OwlBuf::another_ref(&self.owl__msg1_static),
            owl__msg1_timestamp: OwlBuf::another_ref(&self.owl__msg1_timestamp),
            owl__msg1_mac1: OwlBuf::another_ref(&self.owl__msg1_mac1),
            owl__msg1_mac2: self.owl__msg1_mac2,
        }
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
    ensures
        res is Some ==> parse_owlSpec_msg1(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg1(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg1(arg.view())->Some_0,
{
    reveal(parse_owlSpec_msg1);
    let exec_comb = exec_combinator_owl_msg1();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
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
                owl__msg1_tag: owl__msg1_tag,
                owl__msg1_sender: OwlBuf::another_ref(&owl__msg1_sender),
                owl__msg1_ephemeral: OwlBuf::another_ref(&owl__msg1_ephemeral),
                owl__msg1_static: OwlBuf::another_ref(&owl__msg1_static),
                owl__msg1_timestamp: OwlBuf::another_ref(&owl__msg1_timestamp),
                owl__msg1_mac1: OwlBuf::another_ref(&owl__msg1_mac1),
                owl__msg1_mac2: owl__msg1_mac2,
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_msg1_inner<'a>(arg: &owl_msg1<'a>) -> (res: Option<OwlBuf<'a>>)
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
                                (arg.owl__msg1_tag, OwlBuf::another_ref(&arg.owl__msg1_sender)),
                                OwlBuf::another_ref(&arg.owl__msg1_ephemeral),
                            ),
                            OwlBuf::another_ref(&arg.owl__msg1_static),
                        ),
                        OwlBuf::another_ref(&arg.owl__msg1_timestamp),
                    ),
                    OwlBuf::another_ref(&arg.owl__msg1_mac1),
                ),
                arg.owl__msg1_mac2,
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_msg1_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_msg1<'a>(arg: &owl_msg1<'a>) -> (res: OwlBuf<'a>)
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
    ensures
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

impl<'a> owl_msg2<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_msg2<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_msg2 {
            owl__msg2_tag: self.owl__msg2_tag,
            owl__msg2_sender: OwlBuf::another_ref(&self.owl__msg2_sender),
            owl__msg2_receiver: OwlBuf::another_ref(&self.owl__msg2_receiver),
            owl__msg2_ephemeral: OwlBuf::another_ref(&self.owl__msg2_ephemeral),
            owl__msg2_empty: OwlBuf::another_ref(&self.owl__msg2_empty),
            owl__msg2_mac1: OwlBuf::another_ref(&self.owl__msg2_mac1),
            owl__msg2_mac2: self.owl__msg2_mac2,
        }
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
    ensures
        res is Some ==> parse_owlSpec_msg2(arg.view()) is Some,
        res is None ==> parse_owlSpec_msg2(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_msg2(arg.view())->Some_0,
{
    reveal(parse_owlSpec_msg2);
    let exec_comb = exec_combinator_owl_msg2();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
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
                owl__msg2_tag: owl__msg2_tag,
                owl__msg2_sender: OwlBuf::another_ref(&owl__msg2_sender),
                owl__msg2_receiver: OwlBuf::another_ref(&owl__msg2_receiver),
                owl__msg2_ephemeral: OwlBuf::another_ref(&owl__msg2_ephemeral),
                owl__msg2_empty: OwlBuf::another_ref(&owl__msg2_empty),
                owl__msg2_mac1: OwlBuf::another_ref(&owl__msg2_mac1),
                owl__msg2_mac2: owl__msg2_mac2,
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_msg2_inner<'a>(arg: &owl_msg2<'a>) -> (res: Option<OwlBuf<'a>>)
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
                                (arg.owl__msg2_tag, OwlBuf::another_ref(&arg.owl__msg2_sender)),
                                OwlBuf::another_ref(&arg.owl__msg2_receiver),
                            ),
                            OwlBuf::another_ref(&arg.owl__msg2_ephemeral),
                        ),
                        OwlBuf::another_ref(&arg.owl__msg2_empty),
                    ),
                    OwlBuf::another_ref(&arg.owl__msg2_mac1),
                ),
                arg.owl__msg2_mac2,
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_msg2_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_msg2<'a>(arg: &owl_msg2<'a>) -> (res: OwlBuf<'a>)
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
    ensures
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

impl<'a> owl_transp<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_transp<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_transp {
            owl__transp_tag: self.owl__transp_tag,
            owl__transp_receiver: OwlBuf::another_ref(&self.owl__transp_receiver),
            owl__transp_counter: OwlBuf::another_ref(&self.owl__transp_counter),
            owl__transp_packet: OwlBuf::another_ref(&self.owl__transp_packet),
        }
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
    ensures
        res is Some ==> parse_owlSpec_transp(arg.view()) is Some,
        res is None ==> parse_owlSpec_transp(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_transp(arg.view())->Some_0,
{
    reveal(parse_owlSpec_transp);
    let exec_comb = exec_combinator_owl_transp();
    if let Ok((_, parsed)) = <_ as Combinator<OwlBuf<'_>, Vec<u8>>>::parse(&exec_comb, arg) {
        let (((owl__transp_tag, owl__transp_receiver), owl__transp_counter), owl__transp_packet) =
            parsed;
        Some(
            owl_transp {
                owl__transp_tag: owl__transp_tag,
                owl__transp_receiver: OwlBuf::another_ref(&owl__transp_receiver),
                owl__transp_counter: OwlBuf::another_ref(&owl__transp_counter),
                owl__transp_packet: OwlBuf::another_ref(&owl__transp_packet),
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_transp_inner<'a>(arg: &owl_transp<'a>) -> (res: Option<OwlBuf<'a>>)
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
                    (arg.owl__transp_tag, OwlBuf::another_ref(&arg.owl__transp_receiver)),
                    OwlBuf::another_ref(&arg.owl__transp_counter),
                ),
                OwlBuf::another_ref(&arg.owl__transp_packet),
            ),
            &mut obuf,
            0,
        );
        if let Ok((num_written)) = ser_result {
            assert(obuf.view() == serialize_owlSpec_transp_inner(arg.view())->Some_0);
            Some(OwlBuf::from_vec(obuf))
        } else {
            None
        }
    } else {
        None
    }
}

#[inline]
pub exec fn serialize_owl_transp<'a>(arg: &owl_transp<'a>) -> (res: OwlBuf<'a>)
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
    pub owl_tki_k_init_send: SecretBuf<'a>,
    pub owl_tki_k_resp_send: SecretBuf<'a>,
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
    arg_owl_tki_k_init_send: SecretBuf<'a>,
    arg_owl_tki_k_resp_send: SecretBuf<'a>,
) -> (res: owl_transp_keys_init<'a>)
    ensures
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

impl<'a> owl_transp_keys_init<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_transp_keys_init<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_transp_keys_init {
            owl_tki_msg2_receiver: OwlBuf::another_ref(&self.owl_tki_msg2_receiver),
            owl_tki_msg2_sender: OwlBuf::another_ref(&self.owl_tki_msg2_sender),
            owl_tki_has_psk: self.owl_tki_has_psk,
            owl_tki_eph: self.owl_tki_eph,
            owl_tki_c7: self.owl_tki_c7,
            owl_tki_k_init_send: SecretBuf::another_ref(&self.owl_tki_k_init_send),
            owl_tki_k_resp_send: SecretBuf::another_ref(&self.owl_tki_k_resp_send),
        }
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

#[verifier::external_body]
pub exec fn parse_owl_transp_keys_init<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_transp_keys_init<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_transp_keys_init(arg.view()) is Some,
        res is None ==> parse_owlSpec_transp_keys_init(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_transp_keys_init(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_transp_keys_init_inner(arg: &owl_transp_keys_init) -> (res: Option<
    Vec<u8>,
>)
    ensures
        res is Some ==> serialize_owlSpec_transp_keys_init_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_transp_keys_init_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_transp_keys_init_inner(
            arg.view(),
        )->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_transp_keys_init(arg: &owl_transp_keys_init) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_transp_keys_init(arg.view()),
{
    todo!()
}

pub struct owl_transp_keys_resp<'a> {
    pub owl_tkr_msg2_receiver: OwlBuf<'a>,
    pub owl_tkr_msg2_sender: OwlBuf<'a>,
    pub owl_tkr_has_psk: bool,
    pub owl_tkr_eph: Ghost<()>,
    pub owl_tkr_c7: Ghost<()>,
    pub owl_tkr_recvd: bool,
    pub owl_tkr_k_init_send: SecretBuf<'a>,
    pub owl_tkr_k_resp_send: SecretBuf<'a>,
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
    arg_owl_tkr_k_init_send: SecretBuf<'a>,
    arg_owl_tkr_k_resp_send: SecretBuf<'a>,
) -> (res: owl_transp_keys_resp<'a>)
    ensures
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

impl<'a> owl_transp_keys_resp<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_transp_keys_resp<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_transp_keys_resp {
            owl_tkr_msg2_receiver: OwlBuf::another_ref(&self.owl_tkr_msg2_receiver),
            owl_tkr_msg2_sender: OwlBuf::another_ref(&self.owl_tkr_msg2_sender),
            owl_tkr_has_psk: self.owl_tkr_has_psk,
            owl_tkr_eph: self.owl_tkr_eph,
            owl_tkr_c7: self.owl_tkr_c7,
            owl_tkr_recvd: self.owl_tkr_recvd,
            owl_tkr_k_init_send: SecretBuf::another_ref(&self.owl_tkr_k_init_send),
            owl_tkr_k_resp_send: SecretBuf::another_ref(&self.owl_tkr_k_resp_send),
        }
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

#[verifier::external_body]
pub exec fn parse_owl_transp_keys_resp<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_transp_keys_resp<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_transp_keys_resp(arg.view()) is Some,
        res is None ==> parse_owlSpec_transp_keys_resp(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_transp_keys_resp(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_transp_keys_resp_inner(arg: &owl_transp_keys_resp) -> (res: Option<
    Vec<u8>,
>)
    ensures
        res is Some ==> serialize_owlSpec_transp_keys_resp_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_transp_keys_resp_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_transp_keys_resp_inner(
            arg.view(),
        )->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_transp_keys_resp(arg: &owl_transp_keys_resp) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_transp_keys_resp(arg.view()),
{
    todo!()
}

pub struct owl_init_sent_state<'a> {
    pub owl_iss_c2: Ghost<()>,
    pub owl_iss_psk: owl_PSKMode<'a>,
    pub owl_iss_static_ss: Ghost<()>,
    pub owl_ss_h4: OwlBuf<'a>,
    pub owl_iss_c3: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_init_sent_state<'a>(
    arg_owl_iss_c2: Ghost<()>,
    arg_owl_iss_psk: owl_PSKMode<'a>,
    arg_owl_iss_static_ss: Ghost<()>,
    arg_owl_ss_h4: OwlBuf<'a>,
    arg_owl_iss_c3: SecretBuf<'a>,
) -> (res: owl_init_sent_state<'a>)
    ensures
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

impl<'a> owl_init_sent_state<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_init_sent_state<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_init_sent_state {
            owl_iss_c2: self.owl_iss_c2,
            owl_iss_psk: owl_PSKMode::another_ref(&self.owl_iss_psk),
            owl_iss_static_ss: self.owl_iss_static_ss,
            owl_ss_h4: OwlBuf::another_ref(&self.owl_ss_h4),
            owl_iss_c3: SecretBuf::another_ref(&self.owl_iss_c3),
        }
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

#[verifier::external_body]
pub exec fn parse_owl_init_sent_state<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_init_sent_state<'a>>)
    ensures
        res is Some ==> parse_owlSpec_init_sent_state(arg.view()) is Some,
        res is None ==> parse_owlSpec_init_sent_state(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_init_sent_state(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_init_sent_state_inner(arg: &owl_init_sent_state) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_init_sent_state_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_init_sent_state_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_init_sent_state_inner(
            arg.view(),
        )->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_init_sent_state(arg: &owl_init_sent_state) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_init_sent_state(arg.view()),
{
    todo!()
}

pub struct owl_init_info<'a> {
    pub owl_init_info_ss: SecretBuf<'a>,
    pub owl_init_info_psk: owl_PSKMode<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_init_info<'a>(
    arg_owl_init_info_ss: SecretBuf<'a>,
    arg_owl_init_info_psk: owl_PSKMode<'a>,
) -> (res: owl_init_info<'a>)
    ensures
        res.owl_init_info_ss.view() == arg_owl_init_info_ss.view(),
        res.owl_init_info_psk.view() == arg_owl_init_info_psk.view(),
{
    owl_init_info {
        owl_init_info_ss: arg_owl_init_info_ss,
        owl_init_info_psk: arg_owl_init_info_psk,
    }
}

impl<'a> owl_init_info<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_init_info<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_init_info {
            owl_init_info_ss: SecretBuf::another_ref(&self.owl_init_info_ss),
            owl_init_info_psk: owl_PSKMode::another_ref(&self.owl_init_info_psk),
        }
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

#[verifier::external_body]
pub exec fn parse_owl_init_info<'a>(arg: OwlBuf<'a>) -> (res: Option<owl_init_info<'a>>)
    ensures
        res is Some ==> parse_owlSpec_init_info(arg.view()) is Some,
        res is None ==> parse_owlSpec_init_info(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_init_info(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_init_info_inner(arg: &owl_init_info) -> (res: Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_init_info_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_init_info_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_init_info_inner(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_init_info(arg: &owl_init_info) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_init_info(arg.view()),
{
    todo!()
}

pub struct owl_resp_received_state<'a> {
    pub owl_rrs_msg1_sender: OwlBuf<'a>,
    pub owl_rrs_psk: owl_PSKMode<'a>,
    pub owl_rrs_dhpk_S_init: OwlBuf<'a>,
    pub owl_rrs_msg1_ephemeral: OwlBuf<'a>,
    pub owl_rrs_c2: Ghost<()>,
    pub owl_rrs_h4: OwlBuf<'a>,
    pub owl_rrs_c3: SecretBuf<'a>,
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
    arg_owl_rrs_c3: SecretBuf<'a>,
) -> (res: owl_resp_received_state<'a>)
    ensures
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

impl<'a> owl_resp_received_state<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_resp_received_state<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_resp_received_state {
            owl_rrs_msg1_sender: OwlBuf::another_ref(&self.owl_rrs_msg1_sender),
            owl_rrs_psk: owl_PSKMode::another_ref(&self.owl_rrs_psk),
            owl_rrs_dhpk_S_init: OwlBuf::another_ref(&self.owl_rrs_dhpk_S_init),
            owl_rrs_msg1_ephemeral: OwlBuf::another_ref(&self.owl_rrs_msg1_ephemeral),
            owl_rrs_c2: self.owl_rrs_c2,
            owl_rrs_h4: OwlBuf::another_ref(&self.owl_rrs_h4),
            owl_rrs_c3: SecretBuf::another_ref(&self.owl_rrs_c3),
        }
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

#[verifier::external_body]
pub exec fn parse_owl_resp_received_state<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_resp_received_state<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_resp_received_state(arg.view()) is Some,
        res is None ==> parse_owlSpec_resp_received_state(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_resp_received_state(arg.view())->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_resp_received_state_inner(arg: &owl_resp_received_state) -> (res: Option<
    Vec<u8>,
>)
    ensures
        res is Some ==> serialize_owlSpec_resp_received_state_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_resp_received_state_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_resp_received_state_inner(
            arg.view(),
        )->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_resp_received_state(arg: &owl_resp_received_state) -> (res: Vec<u8>)
    ensures
        res.view() == serialize_owlSpec_resp_received_state(arg.view()),
{
    todo!()
}

pub struct owl_resp_transp_recv_result<'a> {
    pub owl_rr_st: owl_transp_keys_resp<'a>,
    pub owl_rr_msg: SecretBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_resp_transp_recv_result<'a>(
    arg_owl_rr_st: owl_transp_keys_resp<'a>,
    arg_owl_rr_msg: SecretBuf<'a>,
) -> (res: owl_resp_transp_recv_result<'a>)
    ensures
        res.owl_rr_st.view() == arg_owl_rr_st.view(),
        res.owl_rr_msg.view() == arg_owl_rr_msg.view(),
{
    owl_resp_transp_recv_result { owl_rr_st: arg_owl_rr_st, owl_rr_msg: arg_owl_rr_msg }
}

impl<'a> owl_resp_transp_recv_result<'a> {
    pub fn another_ref<'other>(&'other self) -> (result: owl_resp_transp_recv_result<'a>)
        ensures
            result.view() == self.view(),
    {
        owl_resp_transp_recv_result {
            owl_rr_st: owl_transp_keys_resp::another_ref(&self.owl_rr_st),
            owl_rr_msg: SecretBuf::another_ref(&self.owl_rr_msg),
        }
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

#[verifier::external_body]
pub exec fn parse_owl_resp_transp_recv_result<'a>(arg: OwlBuf<'a>) -> (res: Option<
    owl_resp_transp_recv_result<'a>,
>)
    ensures
        res is Some ==> parse_owlSpec_resp_transp_recv_result(arg.view()) is Some,
        res is None ==> parse_owlSpec_resp_transp_recv_result(arg.view()) is None,
        res matches Some(x) ==> x.view() == parse_owlSpec_resp_transp_recv_result(
            arg.view(),
        )->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_resp_transp_recv_result_inner(arg: &owl_resp_transp_recv_result) -> (res:
    Option<Vec<u8>>)
    ensures
        res is Some ==> serialize_owlSpec_resp_transp_recv_result_inner(arg.view()) is Some,
        // res is None ==> serialize_owlSpec_resp_transp_recv_result_inner(arg.view()) is None,
        res matches Some(x) ==> x.view() == serialize_owlSpec_resp_transp_recv_result_inner(
            arg.view(),
        )->Some_0,
{
    todo!()
}

#[verifier::external_body]
pub exec fn serialize_owl_resp_transp_recv_result(arg: &owl_resp_transp_recv_result) -> (res: Vec<
    u8,
>)
    ensures
        res.view() == serialize_owlSpec_resp_transp_recv_result(arg.view()),
{
    todo!()
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

pub struct cfg_Initiator<'Initiator> {
    pub salt: Vec<u8>,
    pub owl_S_init: SecretBuf<'Initiator>,
    pub owl_E_init: SecretBuf<'Initiator>,
    pub pk_owl_S_resp: OwlBuf<'Initiator>,
    pub pk_owl_S_init: OwlBuf<'Initiator>,
    pub pk_owl_E_resp: OwlBuf<'Initiator>,
    pub pk_owl_E_init: OwlBuf<'Initiator>,
}

impl cfg_Initiator<'_> {

    pub fn mk_cfg_Initiator<'a>(
        salt: Vec<u8>,
        owl_S_init: &'a [u8],
        owl_E_init: &'a [u8],
        pk_owl_S_resp: &'a [u8],
        pk_owl_S_init: &'a [u8],
        pk_owl_E_resp: &'a [u8],
        pk_owl_E_init: &'a [u8],
    ) -> cfg_Initiator<'a> {
        cfg_Initiator {
            salt,
            owl_S_init: SecretBuf::from_buf(OwlBuf::from_slice(owl_S_init)),
            owl_E_init: SecretBuf::from_buf(OwlBuf::from_slice(owl_E_init)),
            pk_owl_S_resp: OwlBuf::from_slice(pk_owl_S_resp),
            pk_owl_S_init: OwlBuf::from_slice(pk_owl_S_init),
            pk_owl_E_resp: OwlBuf::from_slice(pk_owl_E_resp),
            pk_owl_E_init: OwlBuf::from_slice(pk_owl_E_init),
        }
    }

    
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
            owl_tki_k_init_send: SecretBuf::from_buf(OwlBuf::from_slice(owl_tki_k_init_send)),
            owl_tki_k_resp_send: SecretBuf::from_buf(OwlBuf::from_slice(owl_tki_k_resp_send)),
        };
        let (res, _) =
            self.owl_init_send(Tracked(call_token), mut_state, owl_transp_keys_val, SecretBuf::from_buf(OwlBuf::from_slice(owl_plaintext)), obuf).unwrap();
        res
    }


    #[verifier::spinoff_prover]
    pub fn owl_init_send<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_tki1103: owl_transp_keys_init<'a>,
        owl_msg1104: SecretBuf<'_>,
        obuf: &mut Vec<u8>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Initiator), Endpoint>>), OwlError>)
        requires
            itree.view() == init_send_spec(
                *self,
                *old(mut_state),
                owl_tki1103.view(),
                owl_msg1104.view(),
            ),
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
            let parseval = owl_transp_keys_init::another_ref(&owl_tki1103);
            let owl_init838 = OwlBuf::another_ref(&parseval.owl_tki_msg2_receiver);
            let owl_resp837 = OwlBuf::another_ref(&parseval.owl_tki_msg2_sender);
            let owl_haspsk836 = parseval.owl_tki_has_psk;
            let owl_eph835 = parseval.owl_tki_eph;
            let owl_c7834 = parseval.owl_tki_c7;
            let owl_init_send833 = SecretBuf::another_ref(&parseval.owl_tki_k_init_send);
            let owl_resp_send832 = SecretBuf::another_ref(&parseval.owl_tki_k_resp_send);
            let tmp_owl_transp_counter839 = { owl_counter_as_bytes(&mut_state.owl_N_init_send) };
            let owl_transp_counter839 = OwlBuf::from_slice(&tmp_owl_transp_counter839);
            let (owl__840, Tracked(itree)) = {
                let tmp_arg11105 = owl_ghost_unit();
                owl_call_ret_unit!(itree, *mut_state, init_sent_message_spec(*self, *mut_state, tmp_arg11105), self.owl_init_sent_message(mut_state, tmp_arg11105))
            };
            let tmp_owl_N_init_send841 = { owl_counter_as_bytes(&mut_state.owl_N_init_send) };
            let owl_N_init_send841 = OwlBuf::from_slice(&tmp_owl_N_init_send841).into_secret();
            let owl__842 = {
                if mut_state.owl_N_init_send > usize::MAX - 1 {
                    return Err(OwlError::IntegerOverflow);
                };
                mut_state.owl_N_init_send = mut_state.owl_N_init_send + 1;
            };
            let tmp_owl_transp_tag845 = { owl_public_transp_tag_value() };
            let owl_transp_tag845 = OwlBuf::another_ref(&tmp_owl_transp_tag845);
            let tmp_owl_hexconst844 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst844 = OwlBuf::another_ref(&tmp_owl_hexconst844);
            let owl_c843 = {
                owl_enc_st_aead_builder(
                    SecretBuf::another_ref(&owl_init_send833),
                    SecretBuf::another_ref(&owl_msg1104),
                    SecretBuf::another_ref(&owl_N_init_send841),
                    SecretBuf::from_buf(owl_hexconst844.another_ref()),
                )
            };
            let exec_comb = (
                ((OwlConstBytes::<4>(EXEC_BYTES_CONST_04000000_TRANSP), Bytes(4)), Bytes(8)),
                BuilderCombinator(owl_c843),
            );
            reveal(serialize_owlSpec_transp_inner);
            reveal(serialize_owlSpec_transp);
            owl_output_serialize_fused::<
                ((), state_Initiator),
                OwlBuf<'_>,
                (((OwlConstBytes<4>, Bytes), Bytes), BuilderCombinator<OwlStAEADBuilder>),
            >(
                Tracked(&mut itree),
                exec_comb,
                (
                    (
                        ((), OwlBuf::another_ref(&OwlBuf::another_ref(&owl_init838))),
                        OwlBuf::another_ref(&OwlBuf::another_ref(&owl_transp_counter839)),
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

    pub exec fn owl_transp_recv_init_wrapper<'a, 'b>(
        &'a self,         
        mut_state: &mut state_Initiator,
        ibuf: &'a [u8],
        owl_tki_msg2_receiver: &'a [u8],
        owl_tki_msg2_sender: &'a [u8],
        owl_tki_k_init_send: &'a [u8],
        owl_tki_k_resp_send: &'a [u8],
    ) -> (Option<SecretBuf<'b>>) {
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
            owl_tki_k_init_send: SecretBuf::from_buf(OwlBuf::from_slice(owl_tki_k_init_send)),
            owl_tki_k_resp_send: SecretBuf::from_buf(OwlBuf::from_slice(owl_tki_k_resp_send)),
        };
        let (res, _) =
            self.owl_init_recv(Tracked(call_token), mut_state, owl_tki, ibuf).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_init_recv<'a,'b>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_tki1106: owl_transp_keys_init<'a>,
        ibuf: &'a [u8],
    ) -> (res: Result<
        (Option<SecretBuf<'b>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == init_recv_spec(*self, *old(mut_state), owl_tki1106.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<SecretBuf<'b>>,
            Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(init_recv_spec);
            let (tmp_owl_i849, owl__848) = {
                owl_input::<(Option<Seq<u8>>, state_Initiator)>(Tracked(&mut itree), ibuf)
            };
            let owl_i849 = OwlBuf::from_slice(tmp_owl_i849);
            let parseval = owl_transp_keys_init::another_ref(&owl_tki1106);
            let owl_init856 = OwlBuf::another_ref(&parseval.owl_tki_msg2_receiver);
            let owl_resp855 = OwlBuf::another_ref(&parseval.owl_tki_msg2_sender);
            let owl_haspsk854 = parseval.owl_tki_has_psk;
            let owl_eph853 = parseval.owl_tki_eph;
            let owl_c7852 = parseval.owl_tki_c7;
            let owl_init_send851 = SecretBuf::another_ref(&parseval.owl_tki_k_init_send);
            let owl_resp_send850 = SecretBuf::another_ref(&parseval.owl_tki_k_resp_send);
            let parseval_tmp = OwlBuf::another_ref(&owl_i849);
            if let Some(parseval) = parse_owl_transp(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_tag860 = parseval.owl__transp_tag;
                let owl_from859 = OwlBuf::another_ref(&parseval.owl__transp_receiver);
                let owl_ctr858 = OwlBuf::another_ref(&parseval.owl__transp_counter);
                let owl_pkt857 = OwlBuf::another_ref(&parseval.owl__transp_packet);
                {
                    if { slice_eq(owl_from859.as_slice(), owl_resp855.as_slice()) } {
                        let tmp_owl_p861 = {
                            let tracked owl_declassify_tok862 = consume_itree_declassify::<
                                (Option<Seq<u8>>, state_Initiator),
                                Endpoint,
                            >(&mut itree);
                            let tmp_owl_hexconst863 = {
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }
                            };
                            let owl_hexconst863 = OwlBuf::another_ref(&tmp_owl_hexconst863);
                            owl_dec_st_aead(
                                SecretBuf::another_ref(&owl_resp_send850),
                                OwlBuf::another_ref(&owl_pkt857),
                                SecretBuf::from_buf(owl_ctr858.another_ref()),
                                SecretBuf::from_buf(owl_hexconst863.another_ref()),
                                Tracked(owl_declassify_tok862),
                            )
                        };
                        let owl_p861 = SecretBuf::another_ref_option(&tmp_owl_p861);
                        let owl__864 = {
                            {
                                let owl__865 = {
                                    let tmp_owl_caseval866 = {
                                        SecretBuf::another_ref_option(&owl_p861)
                                    };
                                    let owl_caseval866 = SecretBuf::another_ref_option(
                                        &tmp_owl_caseval866,
                                    );
                                    match SecretBuf::another_ref_option(&owl_caseval866) {
                                        Option::None => { owl_unit() },
                                        Option::Some(tmp_owl_m867) => {
                                            let owl_m867 = SecretBuf::another_ref(&tmp_owl_m867);
                                            let owl__assert_21868 = { owl_ghost_unit() };
                                            owl_unit()
                                        },
                                    }
                                };
                                owl_unit()
                            }
                        };
                        return Ok((owl_p861, Tracked(itree)))
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
    pub fn owl_init_sent_message(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_x1107: Ghost<()>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Initiator), Endpoint>>), OwlError>)
        requires
            itree.view() == init_sent_message_spec(*self, *old(mut_state), owl_x1107),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(init_sent_message_spec);
            (owl_unit(), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_init_dummy(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Initiator), Endpoint>>), OwlError>)
        requires
            itree.view() == init_dummy_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(init_dummy_spec);
            (owl_unit(), Tracked(itree))
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
            Some(psk) => owl_PSKMode::owl_HasPSK(SecretBuf::from_buf(OwlBuf::from_slice(psk))),
            None => owl_PSKMode::owl_NoPSK(),
        };
        let owl_st = owl_init_sent_state {
            owl_iss_c2: Ghost(()),
            owl_iss_psk: pskmode,
            owl_iss_static_ss: Ghost(()),
            owl_ss_h4: OwlBuf::from_slice(h4),
            owl_iss_c3: SecretBuf::from_buf(OwlBuf::from_slice(c3)),
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
        owl_st1108: owl_init_sent_state<'a>,
        ibuf: &'a [u8]
    ) -> (res: Result<
        (
            Option<owl_transp_keys_init<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_transp_keys_init>, state_Initiator), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == init_stage2_spec(*self, *old(mut_state), owl_st1108.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_transp_keys_init<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_transp_keys_init>, state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(init_stage2_spec);
            let parseval = owl_init_sent_state::another_ref(&owl_st1108);
            let owl_c2875 = parseval.owl_iss_c2;
            let owl_opsk874 = owl_PSKMode::another_ref(&parseval.owl_iss_psk);
            let owl_static_ss873 = parseval.owl_iss_static_ss;
            let owl_h4872 = OwlBuf::another_ref(&parseval.owl_ss_h4);
            let owl_c3871 = SecretBuf::another_ref(&parseval.owl_iss_c3);
            let (tmp_owl_i877, owl__876) = {
                owl_input::<(Option<owlSpec_transp_keys_init>, state_Initiator)>(
                    Tracked(&mut itree),
                    ibuf,
                )
            };
            let owl_i877 = OwlBuf::from_slice(tmp_owl_i877);
            let parseval_tmp = OwlBuf::another_ref(&owl_i877);
            if let Some(parseval) = parse_owl_msg2(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_msg2_tag884 = parseval.owl__msg2_tag;
                let owl_msg2_sender883 = OwlBuf::another_ref(&parseval.owl__msg2_sender);
                let owl_msg2_receiver882 = OwlBuf::another_ref(&parseval.owl__msg2_receiver);
                let owl_msg2_ephemeral881 = OwlBuf::another_ref(&parseval.owl__msg2_ephemeral);
                let owl_msg2_empty_enc880 = OwlBuf::another_ref(&parseval.owl__msg2_empty);
                let owl_msg2_mac1879 = OwlBuf::another_ref(&parseval.owl__msg2_mac1);
                let owl_msg2_mac2878 = parseval.owl__msg2_mac2;
                {
                    if owl_msg2_sender883.len() == 4 && owl_msg2_receiver882.len() == 4 {
                        if owl_is_group_elem(
                            SecretBuf::from_buf(owl_msg2_ephemeral881.another_ref()),
                        ) {
                            let tmp_owl_e_init885 = { SecretBuf::another_ref(&self.owl_E_init) };
                            let owl_e_init885 = SecretBuf::another_ref(&tmp_owl_e_init885);
                            let tmp_owl_hexconst887 = {
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }
                            };
                            let owl_hexconst887 = OwlBuf::another_ref(&tmp_owl_hexconst887);
                            let tmp_owl_kdfval220886 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE,
                                    SecretBuf::another_ref(&owl_c3871),
                                    SecretBuf::from_buf(owl_msg2_ephemeral881.another_ref()),
                                    OwlBuf::another_ref(&owl_hexconst887),
                                )
                            };
                            let owl_kdfval220886 = SecretBuf::another_ref(&tmp_owl_kdfval220886);
                            let tmp_owl_c4888 = {
                                {
                                    SecretBuf::another_ref(&owl_kdfval220886).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let owl_c4888 = SecretBuf::another_ref(&tmp_owl_c4888);
                            let tmp_owl_h5889 = {
                                owl_crh(
                                    owl_concat(
                                        owl_h4872.as_slice(),
                                        owl_msg2_ephemeral881.as_slice(),
                                    ).as_slice(),
                                )
                            };
                            let owl_h5889 = OwlBuf::from_vec(tmp_owl_h5889);
                            let tmp_owl_ss890 = {
                                owl_dh_combine(
                                    SecretBuf::from_buf(owl_msg2_ephemeral881.another_ref()),
                                    SecretBuf::another_ref(&owl_e_init885),
                                )
                            };
                            let owl_ss890 = SecretBuf::another_ref(&tmp_owl_ss890);
                            let tmp_owl_hexconst892 = {
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }
                            };
                            let owl_hexconst892 = OwlBuf::another_ref(&tmp_owl_hexconst892);
                            let tmp_owl_kdfval254891 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE,
                                    SecretBuf::another_ref(&owl_c4888),
                                    SecretBuf::another_ref(&owl_ss890),
                                    OwlBuf::another_ref(&owl_hexconst892),
                                )
                            };
                            let owl_kdfval254891 = SecretBuf::another_ref(&tmp_owl_kdfval254891);
                            let tmp_owl_c5893 = {
                                {
                                    SecretBuf::another_ref(&owl_kdfval254891).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let owl_c5893 = SecretBuf::another_ref(&tmp_owl_c5893);
                            let tmp_owl_hexconst895 = {
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }
                            };
                            let owl_hexconst895 = OwlBuf::another_ref(&tmp_owl_hexconst895);
                            let tmp_owl_kdfval267894 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE,
                                    SecretBuf::another_ref(&owl_c5893),
                                    SecretBuf::another_ref(
                                        &owl_dh_combine(
                                            SecretBuf::from_buf(
                                                owl_msg2_ephemeral881.another_ref(),
                                            ),
                                            SecretBuf::another_ref(
                                                &SecretBuf::another_ref(&self.owl_S_init),
                                            ),
                                        ),
                                    ),
                                    OwlBuf::another_ref(&owl_hexconst895),
                                )
                            };
                            let owl_kdfval267894 = SecretBuf::another_ref(&tmp_owl_kdfval267894);
                            let tmp_owl_c6896 = {
                                {
                                    SecretBuf::another_ref(&owl_kdfval267894).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let owl_c6896 = SecretBuf::another_ref(&tmp_owl_c6896);
                            let tmp_owl_psk897 = {
                                let tmp_owl_caseval898 = { owl_PSKMode::another_ref(&owl_opsk874) };
                                let owl_caseval898 = owl_PSKMode::another_ref(&tmp_owl_caseval898);
                                match owl_PSKMode::another_ref(&owl_caseval898) {
                                    owl_PSKMode::owl_HasPSK(tmp_owl_v899) => {
                                        let owl_v899 = SecretBuf::another_ref(&tmp_owl_v899);
                                        owl_v899
                                    },
                                    owl_PSKMode::owl_NoPSK() => SecretBuf::from_buf(
                                        { owl_public_zeros_32() }.another_ref(),
                                    ),
                                }
                            };
                            let owl_psk897 = SecretBuf::another_ref(&tmp_owl_psk897);
                            let tmp_owl_hexconst901 = {
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }
                            };
                            let owl_hexconst901 = OwlBuf::another_ref(&tmp_owl_hexconst901);
                            let tmp_owl_kdfval276900 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE,
                                    SecretBuf::another_ref(&owl_c6896),
                                    SecretBuf::another_ref(&owl_psk897),
                                    OwlBuf::another_ref(&owl_hexconst901),
                                )
                            };
                            let owl_kdfval276900 = SecretBuf::another_ref(&tmp_owl_kdfval276900);
                            let tmp_owl_c7902 = {
                                {
                                    SecretBuf::another_ref(&owl_kdfval276900).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let owl_c7902 = SecretBuf::another_ref(&tmp_owl_c7902);
                            let tmp_owl_tau903 = {
                                {
                                    SecretBuf::another_ref(&owl_kdfval276900).subrange(
                                        0 + KDFKEY_SIZE,
                                        0 + KDFKEY_SIZE + NONCE_SIZE,
                                    )
                                }
                            };
                            let owl_tau903 = SecretBuf::another_ref(&tmp_owl_tau903);
                            let tmp_owl_k0904 = {
                                {
                                    SecretBuf::another_ref(&owl_kdfval276900).subrange(
                                        0 + KDFKEY_SIZE + NONCE_SIZE,
                                        0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE,
                                    )
                                }
                            };
                            let owl_k0904 = SecretBuf::another_ref(&tmp_owl_k0904);
                            let tmp_owl_h6905 = {
                                owl_secret_crh(
                                    SecretBuf::another_ref(
                                        &owl_secret_concat(
                                            SecretBuf::from_buf(owl_h5889.another_ref()),
                                            SecretBuf::another_ref(&owl_tau903),
                                        ),
                                    ),
                                )
                            };
                            let owl_h6905 = SecretBuf::another_ref(&tmp_owl_h6905);
                            let tmp_owl_caseval906 = {
                                let tracked owl_declassify_tok907 = consume_itree_declassify::<
                                    (Option<owlSpec_transp_keys_init>, state_Initiator),
                                    Endpoint,
                                >(&mut itree);
                                let tmp_owl_hexconst908 = {
                                    {
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    }
                                };
                                let owl_hexconst908 = OwlBuf::another_ref(&tmp_owl_hexconst908);
                                owl_dec_st_aead(
                                    SecretBuf::another_ref(&owl_k0904),
                                    OwlBuf::another_ref(&owl_msg2_empty_enc880),
                                    SecretBuf::from_buf(owl_hexconst908.another_ref()),
                                    SecretBuf::another_ref(&owl_h6905),
                                    Tracked(owl_declassify_tok907),
                                )
                            };
                            let owl_caseval906 = SecretBuf::another_ref_option(&tmp_owl_caseval906);
                            match SecretBuf::another_ref_option(&owl_caseval906) {
                                Option::None => { (None, Tracked(itree)) },
                                Option::Some(tmp_owl_x909) => {
                                    let owl_x909 = SecretBuf::another_ref(&tmp_owl_x909);
                                    {
                                        let tmp_owl_hexconst911 = {
                                            {
                                                let x = mk_vec_u8![];
                                                OwlBuf::from_vec(x)
                                            }
                                        };
                                        let owl_hexconst911 = OwlBuf::another_ref(
                                            &tmp_owl_hexconst911,
                                        );
                                        let tmp_owl_hexconst912 = {
                                            {
                                                let x = mk_vec_u8![];
                                                OwlBuf::from_vec(x)
                                            }
                                        };
                                        let owl_hexconst912 = OwlBuf::another_ref(
                                            &tmp_owl_hexconst912,
                                        );
                                        let tmp_owl_kdfval286910 = {
                                            owl_extract_expand_to_len(
                                                0 + ENCKEY_SIZE + ENCKEY_SIZE,
                                                SecretBuf::another_ref(&owl_c7902),
                                                SecretBuf::from_buf(owl_hexconst911.another_ref()),
                                                OwlBuf::another_ref(&owl_hexconst912),
                                            )
                                        };
                                        let owl_kdfval286910 = SecretBuf::another_ref(
                                            &tmp_owl_kdfval286910,
                                        );
                                        let tmp_owl_k1913 = {
                                            {
                                                SecretBuf::another_ref(&owl_kdfval286910).subrange(
                                                    0,
                                                    0 + ENCKEY_SIZE,
                                                )
                                            }
                                        };
                                        let owl_k1913 = SecretBuf::another_ref(&tmp_owl_k1913);
                                        let tmp_owl_k2914 = {
                                            {
                                                SecretBuf::another_ref(&owl_kdfval286910).subrange(
                                                    0 + ENCKEY_SIZE,
                                                    0 + ENCKEY_SIZE + ENCKEY_SIZE,
                                                )
                                            }
                                        };
                                        let owl_k2914 = SecretBuf::another_ref(&tmp_owl_k2914);
                                        let (owl__915, Tracked(itree)) = {
                                            let tmp_arg11109 = owl_ghost_unit();
                                            owl_call_ret_unit!(itree, *mut_state, key_confirm_initiator_send_spec(*self, *mut_state, tmp_arg11109), self.owl_key_confirm_initiator_send(mut_state, tmp_arg11109))
                                        };
                                        let (owl__916, Tracked(itree)) = {
                                            let tmp_arg11110 = owl_ghost_unit();
                                            owl_call_ret_unit!(itree, *mut_state, key_confirm_initiator_recv_spec(*self, *mut_state, tmp_arg11110), self.owl_key_confirm_initiator_recv(mut_state, tmp_arg11110))
                                        };
                                        (
                                            Some(
                                                owl_transp_keys_init::another_ref(
                                                    &owl_transp_keys_init(
                                                        OwlBuf::another_ref(&owl_msg2_receiver882),
                                                        OwlBuf::another_ref(&owl_msg2_sender883),
                                                        owl_HasPSK_enumtest(&owl_opsk874),
                                                        owl_ghost_unit(),
                                                        owl_ghost_unit(),
                                                        SecretBuf::another_ref(&owl_k1913),
                                                        SecretBuf::another_ref(&owl_k2914),
                                                    ),
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
            Some(psk) => owl_PSKMode::owl_HasPSK(SecretBuf::from_buf(OwlBuf::from_slice(psk))),
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
                SecretBuf::from_buf(OwlBuf::from_slice(owl_ss_S_resp_S_init)),
                pskmode,
                obuf).unwrap();
        res
        
    }

    #[verifier::spinoff_prover]
    pub fn owl_init_stage1<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(owlSpec_init_sent_state, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_dhpk_S_resp1111: OwlBuf<'a>,
        owl_dhpk_S_init1112: OwlBuf<'a>,
        owl_ss_S_resp_S_init1113: SecretBuf<'_>,
        owl_psk1114: owl_PSKMode<'a>,
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
                owl_dhpk_S_resp1111.view(),
                owl_dhpk_S_init1112.view(),
                owl_ss_S_resp_S_init1113.view(),
                owl_psk1114.view(),
            ),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            owl_init_sent_state<'a>,
            Tracked<ITreeToken<(owlSpec_init_sent_state, state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(init_stage1_spec);
            let tmp_owl_C0921 = { owl_crh(owl_public_construction().as_slice()) };
            let owl_C0921 = OwlBuf::from_vec(tmp_owl_C0921);
            let tmp_owl_H0922 = {
                owl_crh(
                    owl_concat(owl_C0921.as_slice(), owl_public_identifier().as_slice()).as_slice(),
                )
            };
            let owl_H0922 = OwlBuf::from_vec(tmp_owl_H0922);
            let tmp_owl_H1923 = {
                owl_crh(owl_concat(owl_H0922.as_slice(), owl_dhpk_S_resp1111.as_slice()).as_slice())
            };
            let owl_H1923 = OwlBuf::from_vec(tmp_owl_H1923);
            let tmp_owl_e_init924 = {
                owl_dhpk(SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_E_init)))
            };
            let owl_e_init924 = OwlBuf::from_vec(tmp_owl_e_init924);
            let tmp_owl_hexconst926 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst926 = OwlBuf::another_ref(&tmp_owl_hexconst926);
            let tmp_owl_kdfval307925 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE,
                    SecretBuf::from_buf(owl_C0921.another_ref()),
                    SecretBuf::from_buf(owl_e_init924.another_ref()),
                    OwlBuf::another_ref(&owl_hexconst926),
                )
            };
            let owl_kdfval307925 = SecretBuf::another_ref(&tmp_owl_kdfval307925);
            let tmp_owl_C1927 = {
                { SecretBuf::another_ref(&owl_kdfval307925).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_C1927 = SecretBuf::another_ref(&tmp_owl_C1927);
            let tmp_owl_H2928 = {
                owl_crh(owl_concat(owl_H1923.as_slice(), owl_e_init924.as_slice()).as_slice())
            };
            let owl_H2928 = OwlBuf::from_vec(tmp_owl_H2928);
            let tmp_owl_ss_S_resp_E_init929 = {
                owl_dh_combine(
                    SecretBuf::from_buf(owl_dhpk_S_resp1111.another_ref()),
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_E_init)),
                )
            };
            let owl_ss_S_resp_E_init929 = SecretBuf::another_ref(&tmp_owl_ss_S_resp_E_init929);
            let tmp_owl_hexconst931 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst931 = OwlBuf::another_ref(&tmp_owl_hexconst931);
            let tmp_owl_kdfval312930 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE + ENCKEY_SIZE,
                    SecretBuf::another_ref(&owl_C1927),
                    SecretBuf::another_ref(&owl_ss_S_resp_E_init929),
                    OwlBuf::another_ref(&owl_hexconst931),
                )
            };
            let owl_kdfval312930 = SecretBuf::another_ref(&tmp_owl_kdfval312930);
            let tmp_owl_C2932 = {
                { SecretBuf::another_ref(&owl_kdfval312930).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_C2932 = SecretBuf::another_ref(&tmp_owl_C2932);
            let tmp_owl_k0933 = {
                {
                    SecretBuf::another_ref(&owl_kdfval312930).subrange(
                        0 + KDFKEY_SIZE,
                        0 + KDFKEY_SIZE + ENCKEY_SIZE,
                    )
                }
            };
            let owl_k0933 = SecretBuf::another_ref(&tmp_owl_k0933);
            let tmp_owl_aead_counter_msg1_C2934 = {
                owl_counter_as_bytes(&mut_state.owl_aead_counter_msg1_C2)
            };
            let owl_aead_counter_msg1_C2934 = OwlBuf::from_slice(
                &tmp_owl_aead_counter_msg1_C2934,
            ).into_secret();
            let owl__935 = {
                if mut_state.owl_aead_counter_msg1_C2 > usize::MAX - 1 {
                    return Err(OwlError::IntegerOverflow);
                };
                mut_state.owl_aead_counter_msg1_C2 = mut_state.owl_aead_counter_msg1_C2 + 1;
            };
            let tmp_owl_msg1_static936 = {
                owl_enc_st_aead(
                    SecretBuf::another_ref(&owl_k0933),
                    SecretBuf::from_buf(owl_dhpk_S_init1112.another_ref()),
                    SecretBuf::another_ref(&owl_aead_counter_msg1_C2934),
                    SecretBuf::from_buf(owl_H2928.another_ref()),
                )
            };
            let owl_msg1_static936 = OwlBuf::from_vec(tmp_owl_msg1_static936);
            let tmp_owl_H3937 = {
                owl_crh(owl_concat(owl_H2928.as_slice(), owl_msg1_static936.as_slice()).as_slice())
            };
            let owl_H3937 = OwlBuf::from_vec(tmp_owl_H3937);
            let tmp_owl_hexconst939 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst939 = OwlBuf::another_ref(&tmp_owl_hexconst939);
            let tmp_owl_kdfval321938 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE + ENCKEY_SIZE,
                    SecretBuf::another_ref(&owl_C2932),
                    SecretBuf::another_ref(&owl_ss_S_resp_S_init1113),
                    OwlBuf::another_ref(&owl_hexconst939),
                )
            };
            let owl_kdfval321938 = SecretBuf::another_ref(&tmp_owl_kdfval321938);
            let tmp_owl_c3940 = {
                { SecretBuf::another_ref(&owl_kdfval321938).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_c3940 = SecretBuf::another_ref(&tmp_owl_c3940);
            let tmp_owl_k1941 = {
                {
                    SecretBuf::another_ref(&owl_kdfval321938).subrange(
                        0 + KDFKEY_SIZE,
                        0 + KDFKEY_SIZE + ENCKEY_SIZE,
                    )
                }
            };
            let owl_k1941 = SecretBuf::another_ref(&tmp_owl_k1941);
            let (tmp_owl_timestamp942, Tracked(itree)) = {
                owl_call!(itree, *mut_state, timestamp_i_spec(*self, *mut_state), self.owl_timestamp_i(mut_state))
            };
            let owl_timestamp942 = OwlBuf::another_ref(&tmp_owl_timestamp942);
            let tmp_owl_aead_counter_msg1_C3943 = {
                owl_counter_as_bytes(&mut_state.owl_aead_counter_msg1_C3)
            };
            let owl_aead_counter_msg1_C3943 = OwlBuf::from_slice(
                &tmp_owl_aead_counter_msg1_C3943,
            ).into_secret();
            let owl__944 = {
                if mut_state.owl_aead_counter_msg1_C3 > usize::MAX - 1 {
                    return Err(OwlError::IntegerOverflow);
                };
                mut_state.owl_aead_counter_msg1_C3 = mut_state.owl_aead_counter_msg1_C3 + 1;
            };
            let tmp_owl_msg1_timestamp945 = {
                owl_enc_st_aead(
                    SecretBuf::another_ref(&owl_k1941),
                    SecretBuf::from_buf(owl_timestamp942.another_ref()),
                    SecretBuf::another_ref(&owl_aead_counter_msg1_C3943),
                    SecretBuf::from_buf(owl_H3937.another_ref()),
                )
            };
            let owl_msg1_timestamp945 = OwlBuf::from_vec(tmp_owl_msg1_timestamp945);
            let tmp_owl_h4946 = {
                owl_crh(
                    owl_concat(owl_H3937.as_slice(), owl_msg1_timestamp945.as_slice()).as_slice(),
                )
            };
            let owl_h4946 = OwlBuf::from_vec(tmp_owl_h4946);
            let (tmp_owl_msg1_sender947, Tracked(itree)) = {
                owl_call!(itree, *mut_state, get_sender_i_spec(*self, *mut_state), self.owl_get_sender_i(mut_state))
            };
            let owl_msg1_sender947 = OwlBuf::another_ref(&tmp_owl_msg1_sender947);
            let tmp_owl_msg1_tag948 = { owl_public_msg1_tag_value() };
            let owl_msg1_tag948 = OwlBuf::another_ref(&tmp_owl_msg1_tag948);
            let tmp_owl_msg1_mac1_k949 = {
                owl_crh(
                    owl_concat(
                        owl_public_mac1().as_slice(),
                        owl_dhpk_S_resp1111.as_slice(),
                    ).as_slice(),
                )
            };
            let owl_msg1_mac1_k949 = OwlBuf::from_vec(tmp_owl_msg1_mac1_k949);
            let tmp_owl_msg1_mac1950 = {
                owl_mac(
                    SecretBuf::from_buf(owl_msg1_mac1_k949.another_ref()),
                    OwlBuf::from_vec(
                        owl_concat(
                            owl_concat(
                                owl_concat(
                                    owl_concat(
                                        owl_msg1_tag948.as_slice(),
                                        owl_msg1_sender947.as_slice(),
                                    ).as_slice(),
                                    owl_e_init924.as_slice(),
                                ).as_slice(),
                                owl_msg1_static936.as_slice(),
                            ).as_slice(),
                            owl_msg1_timestamp945.as_slice(),
                        ),
                    ),
                )
            };
            let owl_msg1_mac1950 = OwlBuf::from_vec(tmp_owl_msg1_mac1950);
            let tmp_owl_msg1_mac2951 = { owl_public_zeros_16() };
            let owl_msg1_mac2951 = OwlBuf::another_ref(&tmp_owl_msg1_mac2951);
            let tmp_owl_msg1_output952 = {
                owl_msg1(
                    (),
                    OwlBuf::another_ref(&owl_msg1_sender947),
                    OwlBuf::another_ref(&owl_e_init924),
                    OwlBuf::another_ref(&owl_msg1_static936),
                    OwlBuf::another_ref(&owl_msg1_timestamp945),
                    OwlBuf::another_ref(&owl_msg1_mac1950),
                    (),
                )
            };
            let owl_msg1_output952 = owl_msg1::another_ref(&tmp_owl_msg1_output952);
            let owl__953 = {
                owl_output::<(owlSpec_init_sent_state, state_Initiator)>(
                    Tracked(&mut itree),
                    serialize_owl_msg1(&owl_msg1_output952).as_slice(),
                    &Responder_addr(),
                    &Initiator_addr(),
                    obuf,
                );
            };
            (
                owl_init_sent_state::another_ref(
                    &owl_init_sent_state(
                        owl_ghost_unit(),
                        owl_PSKMode::another_ref(&owl_psk1114),
                        owl_ghost_unit(),
                        OwlBuf::another_ref(&owl_h4946),
                        SecretBuf::another_ref(&owl_c3940),
                    ),
                ),
                Tracked(itree),
            )
        };
        Ok((owl_init_sent_state::another_ref(&res_inner), Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_key_confirm_initiator_recv(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_k1115: Ghost<()>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Initiator), Endpoint>>), OwlError>)
        requires
            itree.view() == key_confirm_initiator_recv_spec(*self, *old(mut_state), owl_k1115),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(key_confirm_initiator_recv_spec);
            (owl_unit(), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_key_confirm_initiator_send(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_k1116: Ghost<()>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Initiator), Endpoint>>), OwlError>)
        requires
            itree.view() == key_confirm_initiator_send_spec(*self, *old(mut_state), owl_k1116),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(key_confirm_initiator_send_spec);
            (owl_unit(), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::external_body]
    #[verifier::spinoff_prover]
    pub fn owl_timestamp_i<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
    ) -> (res: Result<
        (OwlBuf<'a>, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == timestamp_i_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            OwlBuf<'a>,
            Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(timestamp_i_spec);
            todo!()
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::external_body]
    #[verifier::spinoff_prover]
    pub fn owl_get_sender_i<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
    ) -> (res: Result<
        (OwlBuf<'a>, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == get_sender_i_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((r.0).view(), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            OwlBuf<'a>,
            Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(get_sender_i_spec);
            todo!()
        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub struct state_Responder {
    pub owl_aead_counter_msg2_C7: usize,
    pub owl_N_resp_recv: usize,
    pub owl_N_resp_send: usize,
}

impl state_Responder {
    #[verifier::external_body]
    pub fn init_state_Responder() -> Self {
        state_Responder { owl_aead_counter_msg2_C7: 0, owl_N_resp_recv: 0, owl_N_resp_send: 0 }
    }
}

pub struct cfg_Responder<'Responder> {
    pub salt: Vec<u8>,
    pub owl_S_resp: SecretBuf<'Responder>,
    pub owl_E_resp: SecretBuf<'Responder>,
    pub pk_owl_S_resp: OwlBuf<'Responder>,
    pub pk_owl_S_init: OwlBuf<'Responder>,
    pub pk_owl_E_resp: OwlBuf<'Responder>,
    pub pk_owl_E_init: OwlBuf<'Responder>,
}

impl cfg_Responder<'_> {

    pub fn mk_cfg_Responder<'a>(
        salt: Vec<u8>,
        owl_S_resp: &'a [u8],
        owl_E_resp: &'a [u8],
        pk_owl_S_resp: &'a [u8],
        pk_owl_S_init: &'a [u8],
        pk_owl_E_resp: &'a [u8],
        pk_owl_E_init: &'a [u8],
    ) -> cfg_Responder<'a> {
        cfg_Responder {
            salt,
            owl_S_resp: SecretBuf::from_buf(OwlBuf::from_slice(owl_S_resp)),
            owl_E_resp: SecretBuf::from_buf(OwlBuf::from_slice(owl_E_resp)),
            pk_owl_S_resp: OwlBuf::from_slice(pk_owl_S_resp),
            pk_owl_S_init: OwlBuf::from_slice(pk_owl_S_init),
            pk_owl_E_resp: OwlBuf::from_slice(pk_owl_E_resp),
            pk_owl_E_init: OwlBuf::from_slice(pk_owl_E_init),
        }
    }

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
            owl_tkr_k_init_send: SecretBuf::from_buf(OwlBuf::from_slice(owl_tkr_k_init_send)),
            owl_tkr_k_resp_send: SecretBuf::from_buf(OwlBuf::from_slice(owl_tkr_k_resp_send)),
        };
        let (res, _) =
            self.owl_resp_send(Tracked(call_token), mut_state, owl_transp_keys_val, SecretBuf::from_buf(OwlBuf::from_slice(owl_plaintext)), obuf).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_resp_send<'a>(
        &'a self,
        Tracked(itree): Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_tki1117: owl_transp_keys_resp<'a>,
        owl_msg1118: SecretBuf<'_>,
        obuf: &mut Vec<u8>
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == resp_send_spec(
                *self,
                *old(mut_state),
                owl_tki1117.view(),
                owl_msg1118.view(),
            ),
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
            let tmp_owl_tki_958 = { owl_transp_keys_resp::another_ref(&owl_tki1117) };
            let owl_tki_958 = owl_transp_keys_resp::another_ref(&tmp_owl_tki_958);
            let parseval = owl_transp_keys_resp::another_ref(&owl_tki_958);
            let owl_init966 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_receiver);
            let owl_resp965 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_sender);
            let owl_haspsk964 = parseval.owl_tkr_has_psk;
            let owl_eph963 = parseval.owl_tkr_eph;
            let owl_c7962 = parseval.owl_tkr_c7;
            let owl_b961 = parseval.owl_tkr_recvd;
            let owl_init_send960 = SecretBuf::another_ref(&parseval.owl_tkr_k_init_send);
            let owl_resp_send959 = SecretBuf::another_ref(&parseval.owl_tkr_k_resp_send);

            if owl_b961 {
                {
                    let tmp_owl_transp_counter967 = {
                        owl_counter_as_bytes(&mut_state.owl_N_resp_send)
                    };
                    let owl_transp_counter967 = OwlBuf::from_slice(&tmp_owl_transp_counter967);
                    let (owl__968, Tracked(itree)) = {
                        let tmp_arg11119 = owl_ghost_unit();
                        owl_call_ret_unit!(itree, *mut_state, resp_sent_message_spec(*self, *mut_state, tmp_arg11119), self.owl_resp_sent_message(mut_state, tmp_arg11119))
                    };
                    let tmp_owl_N_resp_send969 = { owl_counter_as_bytes(&mut_state.owl_N_resp_send)
                    };
                    let owl_N_resp_send969 = OwlBuf::from_slice(
                        &tmp_owl_N_resp_send969,
                    ).into_secret();
                    let owl__970 = {
                        if mut_state.owl_N_resp_send > usize::MAX - 1 {
                            return Err(OwlError::IntegerOverflow);
                        };
                        mut_state.owl_N_resp_send = mut_state.owl_N_resp_send + 1;
                    };
                    let tmp_owl_transp_tag973 = { owl_public_transp_tag_value() };
                    let owl_transp_tag973 = OwlBuf::another_ref(&tmp_owl_transp_tag973);
                    let tmp_owl_hexconst972 = {
                        {
                            let x = mk_vec_u8![];
                            OwlBuf::from_vec(x)
                        }
                    };
                    let owl_hexconst972 = OwlBuf::another_ref(&tmp_owl_hexconst972);
                    let owl_c971 = {
                        owl_enc_st_aead_builder(
                            SecretBuf::another_ref(&owl_resp_send959),
                            SecretBuf::another_ref(&owl_msg1118),
                            SecretBuf::another_ref(&owl_N_resp_send969),
                            SecretBuf::from_buf(owl_hexconst972.another_ref()),
                        )
                    };
                    let owl__975 = {
                        let exec_comb = (
                            (
                                (OwlConstBytes::<4>(EXEC_BYTES_CONST_04000000_TRANSP), Bytes(4)),
                                Bytes(8),
                            ),
                            BuilderCombinator(owl_c971),
                        );
                        reveal(serialize_owlSpec_transp_inner);
                        reveal(serialize_owlSpec_transp);
                        owl_output_serialize_fused::<
                            (Option<()>, state_Responder),
                            OwlBuf<'_>,
                            (
                                ((OwlConstBytes<4>, Bytes), Bytes),
                                BuilderCombinator<OwlStAEADBuilder>,
                            ),
                        >(
                            Tracked(&mut itree),
                            exec_comb,
                            (
                                (
                                    ((), OwlBuf::another_ref(&OwlBuf::another_ref(&owl_resp965))),
                                    OwlBuf::another_ref(
                                        &OwlBuf::another_ref(&owl_transp_counter967),
                                    ),
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
    ) -> Option<SecretBuf<'a>> {
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
            owl_tkr_k_init_send: SecretBuf::from_buf(OwlBuf::from_slice(owl_tkr_k_init_send)),
            owl_tkr_k_resp_send: SecretBuf::from_buf(OwlBuf::from_slice(owl_tkr_k_resp_send)),
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
        owl_tki1120: owl_transp_keys_resp<'a>,
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
            itree.view() == resp_recv_spec(*self, *old(mut_state), owl_tki1120.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
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
            let (tmp_owl_i978, owl__977) = {
                owl_input::<(Option<owlSpec_resp_transp_recv_result>, state_Responder)>(
                    Tracked(&mut itree),
                    ibuf,
                )
            };
            let owl_i978 = OwlBuf::from_slice(tmp_owl_i978);
            let tmp_owl_tki_979 = { owl_transp_keys_resp::another_ref(&owl_tki1120) };
            let owl_tki_979 = owl_transp_keys_resp::another_ref(&tmp_owl_tki_979);
            let parseval = owl_transp_keys_resp::another_ref(&owl_tki_979);
            let owl_init987 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_receiver);
            let owl_resp986 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_sender);
            let owl_haspsk985 = parseval.owl_tkr_has_psk;
            let owl_eph984 = parseval.owl_tkr_eph;
            let owl_c7983 = parseval.owl_tkr_c7;
            let owl__982 = parseval.owl_tkr_recvd;
            let owl_init_send981 = SecretBuf::another_ref(&parseval.owl_tkr_k_init_send);
            let owl_resp_send980 = SecretBuf::another_ref(&parseval.owl_tkr_k_resp_send);
            let parseval_tmp = OwlBuf::another_ref(&owl_i978);
            if let Some(parseval) = parse_owl_transp(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_tag991 = parseval.owl__transp_tag;
                let owl_from990 = OwlBuf::another_ref(&parseval.owl__transp_receiver);
                let owl_ctr989 = OwlBuf::another_ref(&parseval.owl__transp_counter);
                let owl_pkt988 = OwlBuf::another_ref(&parseval.owl__transp_packet);
                {
                    if { slice_eq(owl_from990.as_slice(), owl_init987.as_slice()) } {
                        let tmp_owl_caseval992 = {
                            let tracked owl_declassify_tok993 = consume_itree_declassify::<
                                (Option<owlSpec_resp_transp_recv_result>, state_Responder),
                                Endpoint,
                            >(&mut itree);
                            let tmp_owl_hexconst994 = {
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }
                            };
                            let owl_hexconst994 = OwlBuf::another_ref(&tmp_owl_hexconst994);
                            owl_dec_st_aead(
                                SecretBuf::another_ref(&owl_init_send981),
                                OwlBuf::another_ref(&owl_pkt988),
                                SecretBuf::from_buf(owl_ctr989.another_ref()),
                                SecretBuf::from_buf(owl_hexconst994.another_ref()),
                                Tracked(owl_declassify_tok993),
                            )
                        };
                        let owl_caseval992 = SecretBuf::another_ref_option(&tmp_owl_caseval992);
                        match SecretBuf::another_ref_option(&owl_caseval992) {
                            Option::Some(tmp_owl_x995) => {
                                let owl_x995 = SecretBuf::another_ref(&tmp_owl_x995);
                                let tmp_owl_st_996 = {
                                    owl_transp_keys_resp(
                                        OwlBuf::another_ref(&owl_init987),
                                        OwlBuf::another_ref(&owl_resp986),
                                        owl_haspsk985,
                                        owl_ghost_unit(),
                                        owl_ghost_unit(),
                                        true,
                                        SecretBuf::another_ref(&owl_init_send981),
                                        SecretBuf::another_ref(&owl_resp_send980),
                                    )
                                };
                                let owl_st_996 = owl_transp_keys_resp::another_ref(&tmp_owl_st_996);
                                let tmp_owl_ret997 = {
                                    owl_resp_transp_recv_result(
                                        owl_transp_keys_resp::another_ref(&owl_st_996),
                                        SecretBuf::another_ref(&owl_x995),
                                    )
                                };
                                let owl_ret997 = owl_resp_transp_recv_result::another_ref(
                                    &tmp_owl_ret997,
                                );
                                let owl__assert_82998 = { owl_ghost_unit() };
                                (
                                    Some(owl_resp_transp_recv_result::another_ref(&owl_ret997)),
                                    Tracked(itree),
                                )
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

    #[verifier::spinoff_prover]
    pub fn owl_resp_sent_message(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_x1121: Ghost<()>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Responder), Endpoint>>), OwlError>)
        requires
            itree.view() == resp_sent_message_spec(*self, *old(mut_state), owl_x1121),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(resp_sent_message_spec);
            (owl_unit(), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_resp_dummy(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Responder), Endpoint>>), OwlError>)
        requires
            itree.view() == resp_dummy_spec(*self, *old(mut_state)),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(resp_dummy_spec);
            (owl_unit(), Tracked(itree))
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
        owl_st1122: owl_resp_received_state<'a>,
        obuf: &mut [u8],
    ) -> (res: Result<
        (
            Option<owl_transp_keys_resp<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_transp_keys_resp>, state_Responder), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == resp_stage2_spec(*self, *old(mut_state), owl_st1122.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_transp_keys_resp<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_transp_keys_resp>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(resp_stage2_spec);
            let tmp_owl_st_1001 = { owl_resp_received_state::another_ref(&owl_st1122) };
            let owl_st_1001 = owl_resp_received_state::another_ref(&tmp_owl_st_1001);
            let tmp_owl_st__1002 = { owl_resp_received_state::another_ref(&owl_st_1001) };
            let owl_st__1002 = owl_resp_received_state::another_ref(&tmp_owl_st__1002);
            let parseval = owl_resp_received_state::another_ref(&owl_st__1002);
            let owl_msg2_receiver1009 = OwlBuf::another_ref(&parseval.owl_rrs_msg1_sender);
            let owl_psk1008 = owl_PSKMode::another_ref(&parseval.owl_rrs_psk);
            let owl_dhpk_S_init1007 = OwlBuf::another_ref(&parseval.owl_rrs_dhpk_S_init);
            let owl_msg1_ephemeral1006 = OwlBuf::another_ref(&parseval.owl_rrs_msg1_ephemeral);
            let owl_C21005 = parseval.owl_rrs_c2;
            let owl_H41004 = OwlBuf::another_ref(&parseval.owl_rrs_h4);
            let owl_C31003 = SecretBuf::another_ref(&parseval.owl_rrs_c3);
            let tmp_owl_e_resp_pk1010 = {
                owl_dhpk(SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_E_resp)))
            };
            let owl_e_resp_pk1010 = OwlBuf::from_vec(tmp_owl_e_resp_pk1010);
            let tmp_owl_hexconst1012 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst1012 = OwlBuf::another_ref(&tmp_owl_hexconst1012);
            let tmp_owl_kdfval5291011 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE,
                    SecretBuf::another_ref(&owl_C31003),
                    SecretBuf::from_buf(owl_e_resp_pk1010.another_ref()),
                    OwlBuf::another_ref(&owl_hexconst1012),
                )
            };
            let owl_kdfval5291011 = SecretBuf::another_ref(&tmp_owl_kdfval5291011);
            let tmp_owl_c41013 = {
                { SecretBuf::another_ref(&owl_kdfval5291011).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_c41013 = SecretBuf::another_ref(&tmp_owl_c41013);
            let tmp_owl_h51014 = {
                owl_crh(owl_concat(owl_H41004.as_slice(), owl_e_resp_pk1010.as_slice()).as_slice())
            };
            let owl_h51014 = OwlBuf::from_vec(tmp_owl_h51014);
            let tmp_owl_ss1015 = {
                owl_dh_combine(
                    SecretBuf::from_buf(owl_msg1_ephemeral1006.another_ref()),
                    SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_E_resp)),
                )
            };
            let owl_ss1015 = SecretBuf::another_ref(&tmp_owl_ss1015);
            let tmp_owl_hexconst1017 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst1017 = OwlBuf::another_ref(&tmp_owl_hexconst1017);
            let tmp_owl_kdfval5421016 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE,
                    SecretBuf::another_ref(&owl_c41013),
                    SecretBuf::another_ref(&owl_ss1015),
                    OwlBuf::another_ref(&owl_hexconst1017),
                )
            };
            let owl_kdfval5421016 = SecretBuf::another_ref(&tmp_owl_kdfval5421016);
            let tmp_owl_c51018 = {
                { SecretBuf::another_ref(&owl_kdfval5421016).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_c51018 = SecretBuf::another_ref(&tmp_owl_c51018);
            let tmp_owl_hexconst1020 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst1020 = OwlBuf::another_ref(&tmp_owl_hexconst1020);
            let tmp_owl_kdfval5491019 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE,
                    SecretBuf::another_ref(&owl_c51018),
                    SecretBuf::another_ref(
                        &owl_dh_combine(
                            SecretBuf::from_buf(owl_dhpk_S_init1007.another_ref()),
                            SecretBuf::another_ref(&SecretBuf::another_ref(&self.owl_E_resp)),
                        ),
                    ),
                    OwlBuf::another_ref(&owl_hexconst1020),
                )
            };
            let owl_kdfval5491019 = SecretBuf::another_ref(&tmp_owl_kdfval5491019);
            let tmp_owl_c61021 = {
                { SecretBuf::another_ref(&owl_kdfval5491019).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_c61021 = SecretBuf::another_ref(&tmp_owl_c61021);
            let tmp_owl_psk_val1022 = {
                let tmp_owl_caseval1023 = { owl_PSKMode::another_ref(&owl_psk1008) };
                let owl_caseval1023 = owl_PSKMode::another_ref(&tmp_owl_caseval1023);
                match owl_PSKMode::another_ref(&owl_caseval1023) {
                    owl_PSKMode::owl_HasPSK(tmp_owl_v1024) => {
                        let owl_v1024 = SecretBuf::another_ref(&tmp_owl_v1024);
                        owl_v1024
                    },
                    owl_PSKMode::owl_NoPSK() => SecretBuf::from_buf(
                        { owl_public_zeros_32() }.another_ref(),
                    ),
                }
            };
            let owl_psk_val1022 = SecretBuf::another_ref(&tmp_owl_psk_val1022);
            let tmp_owl_hexconst1026 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst1026 = OwlBuf::another_ref(&tmp_owl_hexconst1026);
            let tmp_owl_kdfval5581025 = {
                owl_extract_expand_to_len(
                    0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE,
                    SecretBuf::another_ref(&owl_c61021),
                    SecretBuf::another_ref(&owl_psk_val1022),
                    OwlBuf::another_ref(&owl_hexconst1026),
                )
            };
            let owl_kdfval5581025 = SecretBuf::another_ref(&tmp_owl_kdfval5581025);
            let tmp_owl_c71027 = {
                { SecretBuf::another_ref(&owl_kdfval5581025).subrange(0, 0 + KDFKEY_SIZE) }
            };
            let owl_c71027 = SecretBuf::another_ref(&tmp_owl_c71027);
            let tmp_owl_tau1028 = {
                {
                    SecretBuf::another_ref(&owl_kdfval5581025).subrange(
                        0 + KDFKEY_SIZE,
                        0 + KDFKEY_SIZE + NONCE_SIZE,
                    )
                }
            };
            let owl_tau1028 = SecretBuf::another_ref(&tmp_owl_tau1028);
            let tmp_owl_k01029 = {
                {
                    SecretBuf::another_ref(&owl_kdfval5581025).subrange(
                        0 + KDFKEY_SIZE + NONCE_SIZE,
                        0 + KDFKEY_SIZE + NONCE_SIZE + ENCKEY_SIZE,
                    )
                }
            };
            let owl_k01029 = SecretBuf::another_ref(&tmp_owl_k01029);
            let tmp_owl_msg2_tag1030 = { owl_public_msg2_tag_value() };
            let owl_msg2_tag1030 = OwlBuf::another_ref(&tmp_owl_msg2_tag1030);
            let (tmp_owl_msg2_sender1031, Tracked(itree)) = {
                owl_call!(itree, *mut_state, get_sender_r_spec(*self, *mut_state), self.owl_get_sender_r(mut_state))
            };
            let owl_msg2_sender1031 = OwlBuf::another_ref(&tmp_owl_msg2_sender1031);
            let tmp_owl_msg2_mac1_k1032 = {
                owl_crh(
                    owl_concat(
                        owl_public_mac1().as_slice(),
                        owl_dhpk_S_init1007.as_slice(),
                    ).as_slice(),
                )
            };
            let owl_msg2_mac1_k1032 = OwlBuf::from_vec(tmp_owl_msg2_mac1_k1032);
            let tmp_owl_h61033 = {
                owl_secret_crh(
                    SecretBuf::another_ref(
                        &owl_secret_concat(
                            SecretBuf::from_buf(owl_h51014.another_ref()),
                            SecretBuf::another_ref(&owl_tau1028),
                        ),
                    ),
                )
            };
            let owl_h61033 = SecretBuf::another_ref(&tmp_owl_h61033);
            let tmp_owl_hexconst1035 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst1035 = OwlBuf::another_ref(&tmp_owl_hexconst1035);
            let tmp_owl_hexconst1036 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst1036 = OwlBuf::another_ref(&tmp_owl_hexconst1036);
            let tmp_owl_kdfval5681034 = {
                owl_extract_expand_to_len(
                    0 + ENCKEY_SIZE + ENCKEY_SIZE,
                    SecretBuf::another_ref(&owl_c71027),
                    SecretBuf::from_buf(owl_hexconst1035.another_ref()),
                    OwlBuf::another_ref(&owl_hexconst1036),
                )
            };
            let owl_kdfval5681034 = SecretBuf::another_ref(&tmp_owl_kdfval5681034);
            let tmp_owl_tk11037 = {
                { SecretBuf::another_ref(&owl_kdfval5681034).subrange(0, 0 + ENCKEY_SIZE) }
            };
            let owl_tk11037 = SecretBuf::another_ref(&tmp_owl_tk11037);
            let tmp_owl_tk21038 = {
                {
                    SecretBuf::another_ref(&owl_kdfval5681034).subrange(
                        0 + ENCKEY_SIZE,
                        0 + ENCKEY_SIZE + ENCKEY_SIZE,
                    )
                }
            };
            let owl_tk21038 = SecretBuf::another_ref(&tmp_owl_tk21038);
            let (owl__1039, Tracked(itree)) = {
                let tmp_arg11123 = owl_ghost_unit();
                owl_call_ret_unit!(itree, *mut_state, key_confirm_responder_recv_spec(*self, *mut_state, tmp_arg11123), self.owl_key_confirm_responder_recv(mut_state, tmp_arg11123))
            };
            let (owl__1040, Tracked(itree)) = {
                let tmp_arg11124 = owl_ghost_unit();
                owl_call_ret_unit!(itree, *mut_state, key_confirm_responder_send_spec(*self, *mut_state, tmp_arg11124), self.owl_key_confirm_responder_send(mut_state, tmp_arg11124))
            };
            let tmp_owl_aead_counter_msg2_C71041 = {
                owl_counter_as_bytes(&mut_state.owl_aead_counter_msg2_C7)
            };
            let owl_aead_counter_msg2_C71041 = OwlBuf::from_slice(
                &tmp_owl_aead_counter_msg2_C71041,
            ).into_secret();
            let owl__1042 = {
                if mut_state.owl_aead_counter_msg2_C7 > usize::MAX - 1 {
                    return Err(OwlError::IntegerOverflow);
                };
                mut_state.owl_aead_counter_msg2_C7 = mut_state.owl_aead_counter_msg2_C7 + 1;
            };
            let tmp_owl_hexconst1044 = {
                {
                    let x = mk_vec_u8![];
                    OwlBuf::from_vec(x)
                }
            };
            let owl_hexconst1044 = OwlBuf::another_ref(&tmp_owl_hexconst1044);
            let tmp_owl_msg2_empty1043 = {
                owl_enc_st_aead(
                    SecretBuf::another_ref(&owl_k01029),
                    SecretBuf::from_buf(owl_hexconst1044.another_ref()),
                    SecretBuf::another_ref(&owl_aead_counter_msg2_C71041),
                    SecretBuf::another_ref(&owl_h61033),
                )
            };
            let owl_msg2_empty1043 = OwlBuf::from_vec(tmp_owl_msg2_empty1043);
            let tmp_owl_msg2_mac11045 = {
                owl_mac(
                    SecretBuf::from_buf(owl_msg2_mac1_k1032.another_ref()),
                    OwlBuf::from_vec(
                        owl_concat(
                            owl_concat(
                                owl_concat(
                                    owl_concat(
                                        owl_msg2_tag1030.as_slice(),
                                        owl_msg2_sender1031.as_slice(),
                                    ).as_slice(),
                                    owl_msg2_receiver1009.as_slice(),
                                ).as_slice(),
                                owl_e_resp_pk1010.as_slice(),
                            ).as_slice(),
                            owl_msg2_empty1043.as_slice(),
                        ),
                    ),
                )
            };
            let owl_msg2_mac11045 = OwlBuf::from_vec(tmp_owl_msg2_mac11045);
            let owl__assert_2731046 = { owl_ghost_unit() };
            let tmp_owl_msg2_mac21047 = { owl_public_zeros_16() };
            let owl_msg2_mac21047 = OwlBuf::another_ref(&tmp_owl_msg2_mac21047);
            let tmp_owl_msg2_output1048 = {
                owl_msg2(
                    (),
                    OwlBuf::another_ref(&owl_msg2_sender1031),
                    OwlBuf::another_ref(&owl_msg2_receiver1009),
                    OwlBuf::another_ref(&owl_e_resp_pk1010),
                    OwlBuf::another_ref(&owl_msg2_empty1043),
                    OwlBuf::another_ref(&owl_msg2_mac11045),
                    (),
                )
            };
            let owl_msg2_output1048 = owl_msg2::another_ref(&tmp_owl_msg2_output1048);
            let owl__1049 = {
                owl_output::<(Option<owlSpec_transp_keys_resp>, state_Responder)>(
                    Tracked(&mut itree),
                    serialize_owl_msg2(&owl_msg2_output1048).as_slice(),
                    &Initiator_addr(),
                    &Responder_addr(),
                    obuf,
                );
            };
            let tmp_owl_ret1050 = {
                owl_transp_keys_resp(
                    OwlBuf::another_ref(&owl_msg2_receiver1009),
                    OwlBuf::another_ref(&owl_msg2_sender1031),
                    owl_HasPSK_enumtest(&owl_psk1008),
                    owl_ghost_unit(),
                    owl_ghost_unit(),
                    false,
                    SecretBuf::another_ref(&owl_tk11037),
                    SecretBuf::another_ref(&owl_tk21038),
                )
            };
            let owl_ret1050 = owl_transp_keys_resp::another_ref(&tmp_owl_ret1050);
            (Some(owl_transp_keys_resp::another_ref(&owl_ret1050)), Tracked(itree))
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
        owl_dhpk_S_resp1125: OwlBuf<'a>,
        ibuf: &'a [u8],
    ) -> (res: Result<
        (
            Option<owl_resp_received_state<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_resp_received_state>, state_Responder), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == resp_stage1_spec(*self, *old(mut_state), owl_dhpk_S_resp1125.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_resp_received_state<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_resp_received_state>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(resp_stage1_spec);
            let (tmp_owl_inp1053, owl__1052) = {
                owl_input::<(Option<owlSpec_resp_received_state>, state_Responder)>(
                    Tracked(&mut itree),
                    ibuf,
                )
            };
            let owl_inp1053 = OwlBuf::from_slice(tmp_owl_inp1053);
            let parseval_tmp = OwlBuf::another_ref(&owl_inp1053);
            if let Some(parseval) = parse_owl_msg1(OwlBuf::another_ref(&parseval_tmp)) {
                let owl_msg1_tag1060 = parseval.owl__msg1_tag;
                let owl_msg1_sender1059 = OwlBuf::another_ref(&parseval.owl__msg1_sender);
                let owl_msg1_ephemeral1058 = OwlBuf::another_ref(&parseval.owl__msg1_ephemeral);
                let owl_msg1_static1057 = OwlBuf::another_ref(&parseval.owl__msg1_static);
                let owl_msg1_timestamp1056 = OwlBuf::another_ref(&parseval.owl__msg1_timestamp);
                let owl_msg1_mac11055 = OwlBuf::another_ref(&parseval.owl__msg1_mac1);
                let owl_msg1_mac21054 = parseval.owl__msg1_mac2;
                {
                    if owl_msg1_sender1059.len() == 4 {
                        if owl_is_group_elem(
                            SecretBuf::from_buf(owl_msg1_ephemeral1058.another_ref()),
                        ) {
                            let tmp_owl_C01061 = { owl_crh(owl_public_construction().as_slice()) };
                            let owl_C01061 = OwlBuf::from_vec(tmp_owl_C01061);
                            let tmp_owl_H01062 = {
                                owl_crh(
                                    owl_concat(
                                        owl_C01061.as_slice(),
                                        owl_public_identifier().as_slice(),
                                    ).as_slice(),
                                )
                            };
                            let owl_H01062 = OwlBuf::from_vec(tmp_owl_H01062);
                            let tmp_owl_H11063 = {
                                owl_crh(
                                    owl_concat(
                                        owl_H01062.as_slice(),
                                        owl_dhpk_S_resp1125.as_slice(),
                                    ).as_slice(),
                                )
                            };
                            let owl_H11063 = OwlBuf::from_vec(tmp_owl_H11063);
                            let tmp_owl_hexconst1065 = {
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }
                            };
                            let owl_hexconst1065 = OwlBuf::another_ref(&tmp_owl_hexconst1065);
                            let tmp_owl_kdfval6111064 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE,
                                    SecretBuf::from_buf(owl_C01061.another_ref()),
                                    SecretBuf::from_buf(owl_msg1_ephemeral1058.another_ref()),
                                    OwlBuf::another_ref(&owl_hexconst1065),
                                )
                            };
                            let owl_kdfval6111064 = SecretBuf::another_ref(&tmp_owl_kdfval6111064);
                            let tmp_owl_C11066 = {
                                {
                                    SecretBuf::another_ref(&owl_kdfval6111064).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let owl_C11066 = SecretBuf::another_ref(&tmp_owl_C11066);
                            let tmp_owl_H21067 = {
                                owl_crh(
                                    owl_concat(
                                        owl_H11063.as_slice(),
                                        owl_msg1_ephemeral1058.as_slice(),
                                    ).as_slice(),
                                )
                            };
                            let owl_H21067 = OwlBuf::from_vec(tmp_owl_H21067);
                            let tmp_owl_ss_msg1_ephemeral_S_resp1068 = {
                                owl_dh_combine(
                                    SecretBuf::from_buf(owl_msg1_ephemeral1058.another_ref()),
                                    SecretBuf::another_ref(
                                        &SecretBuf::another_ref(&self.owl_S_resp),
                                    ),
                                )
                            };
                            let owl_ss_msg1_ephemeral_S_resp1068 = SecretBuf::another_ref(
                                &tmp_owl_ss_msg1_ephemeral_S_resp1068,
                            );
                            let tmp_owl_hexconst1070 = {
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }
                            };
                            let owl_hexconst1070 = OwlBuf::another_ref(&tmp_owl_hexconst1070);
                            let tmp_owl_kdfval6211069 = {
                                owl_extract_expand_to_len(
                                    0 + KDFKEY_SIZE + ENCKEY_SIZE,
                                    SecretBuf::another_ref(&owl_C11066),
                                    SecretBuf::another_ref(&owl_ss_msg1_ephemeral_S_resp1068),
                                    OwlBuf::another_ref(&owl_hexconst1070),
                                )
                            };
                            let owl_kdfval6211069 = SecretBuf::another_ref(&tmp_owl_kdfval6211069);
                            let tmp_owl_C21071 = {
                                {
                                    SecretBuf::another_ref(&owl_kdfval6211069).subrange(
                                        0,
                                        0 + KDFKEY_SIZE,
                                    )
                                }
                            };
                            let owl_C21071 = SecretBuf::another_ref(&tmp_owl_C21071);
                            let tmp_owl_k01072 = {
                                {
                                    SecretBuf::another_ref(&owl_kdfval6211069).subrange(
                                        0 + KDFKEY_SIZE,
                                        0 + KDFKEY_SIZE + ENCKEY_SIZE,
                                    )
                                }
                            };
                            let owl_k01072 = SecretBuf::another_ref(&tmp_owl_k01072);
                            let tmp_owl_caseval1073 = {
                                let tracked owl_declassify_tok1074 = consume_itree_declassify::<
                                    (Option<owlSpec_resp_received_state>, state_Responder),
                                    Endpoint,
                                >(&mut itree);
                                let tmp_owl_hexconst1075 = {
                                    {
                                        let x = mk_vec_u8![];
                                        OwlBuf::from_vec(x)
                                    }
                                };
                                let owl_hexconst1075 = OwlBuf::another_ref(&tmp_owl_hexconst1075);
                                owl_dec_st_aead(
                                    SecretBuf::another_ref(&owl_k01072),
                                    OwlBuf::another_ref(&owl_msg1_static1057),
                                    SecretBuf::from_buf(owl_hexconst1075.another_ref()),
                                    SecretBuf::from_buf(owl_H21067.another_ref()),
                                    Tracked(owl_declassify_tok1074),
                                )
                            };
                            let owl_caseval1073 = SecretBuf::another_ref_option(
                                &tmp_owl_caseval1073,
                            );
                            match SecretBuf::another_ref_option(&owl_caseval1073) {
                                Option::None => { (None, Tracked(itree)) },
                                Option::Some(tmp_owl_msg1_static_dec1076) => {
                                    let owl_msg1_static_dec1076 = SecretBuf::another_ref(
                                        &tmp_owl_msg1_static_dec1076,
                                    );
                                    let tmp_owl_declassified_buf1077 = {
                                        let tracked owl_declassify_tok1078 =
                                            consume_itree_declassify::<
                                            (Option<owlSpec_resp_received_state>, state_Responder),
                                            Endpoint,
                                        >(&mut itree);
                                        {
                                            SecretBuf::another_ref(
                                                &owl_msg1_static_dec1076,
                                            ).declassify(Tracked(owl_declassify_tok1078))
                                        }
                                    };
                                    let owl_declassified_buf1077 = OwlBuf::another_ref(
                                        &tmp_owl_declassified_buf1077,
                                    );
                                    let (owl_oinfo1079, Tracked(itree)) = {
                                        let tmp_arg11126 = OwlBuf::another_ref(
                                            &owl_declassified_buf1077,
                                        );
                                        owl_call_ret_option!(itree, *mut_state, get_pk_info_spec(*self, *mut_state, tmp_arg11126.view()), self.owl_get_pk_info(mut_state, tmp_arg11126))
                                    };
                                    let owl_caseval1080 = { owl_oinfo1079 };
                                    match owl_caseval1080 {
                                        Option::None => { (None, Tracked(itree)) },
                                        Option::Some(tmp_owl_info1081) => {
                                            let owl_info1081 = owl_init_info::another_ref(
                                                &tmp_owl_info1081,
                                            );
                                            let tmp_owl_info1082 = {
                                                owl_init_info::another_ref(&owl_info1081)
                                            };
                                            let owl_info1082 = owl_init_info::another_ref(
                                                &tmp_owl_info1082,
                                            );
                                            let parseval = owl_init_info::another_ref(
                                                &owl_info1082,
                                            );
                                            let owl_ss1084 = SecretBuf::another_ref(
                                                &parseval.owl_init_info_ss,
                                            );
                                            let owl_psk1083 = owl_PSKMode::another_ref(
                                                &parseval.owl_init_info_psk,
                                            );
                                            let tmp_owl_H31085 = {
                                                owl_crh(
                                                    owl_concat(
                                                        owl_H21067.as_slice(),
                                                        owl_msg1_static1057.as_slice(),
                                                    ).as_slice(),
                                                )
                                            };
                                            let owl_H31085 = OwlBuf::from_vec(tmp_owl_H31085);
                                            let tmp_owl_dhpk_S_init1086 = {
                                                SecretBuf::another_ref(&owl_msg1_static_dec1076)
                                            };
                                            let owl_dhpk_S_init1086 = SecretBuf::another_ref(
                                                &tmp_owl_dhpk_S_init1086,
                                            );
                                            let tmp_owl_hexconst1088 = {
                                                {
                                                    let x = mk_vec_u8![];
                                                    OwlBuf::from_vec(x)
                                                }
                                            };
                                            let owl_hexconst1088 = OwlBuf::another_ref(
                                                &tmp_owl_hexconst1088,
                                            );
                                            let tmp_owl_kdfval6581087 = {
                                                owl_extract_expand_to_len(
                                                    0 + KDFKEY_SIZE + ENCKEY_SIZE,
                                                    SecretBuf::another_ref(&owl_C21071),
                                                    SecretBuf::another_ref(&owl_ss1084),
                                                    OwlBuf::another_ref(&owl_hexconst1088),
                                                )
                                            };
                                            let owl_kdfval6581087 = SecretBuf::another_ref(
                                                &tmp_owl_kdfval6581087,
                                            );
                                            let tmp_owl_C31089 = {
                                                {
                                                    SecretBuf::another_ref(
                                                        &owl_kdfval6581087,
                                                    ).subrange(0, 0 + KDFKEY_SIZE)
                                                }
                                            };
                                            let owl_C31089 = SecretBuf::another_ref(
                                                &tmp_owl_C31089,
                                            );
                                            let tmp_owl_k11090 = {
                                                {
                                                    SecretBuf::another_ref(
                                                        &owl_kdfval6581087,
                                                    ).subrange(
                                                        0 + KDFKEY_SIZE,
                                                        0 + KDFKEY_SIZE + ENCKEY_SIZE,
                                                    )
                                                }
                                            };
                                            let owl_k11090 = SecretBuf::another_ref(
                                                &tmp_owl_k11090,
                                            );
                                            let tmp_owl_caseval1091 = {
                                                let tracked owl_declassify_tok1092 =
                                                    consume_itree_declassify::<
                                                    (
                                                        Option<owlSpec_resp_received_state>,
                                                        state_Responder,
                                                    ),
                                                    Endpoint,
                                                >(&mut itree);
                                                let tmp_owl_hexconst1093 = {
                                                    {
                                                        let x = mk_vec_u8![];
                                                        OwlBuf::from_vec(x)
                                                    }
                                                };
                                                let owl_hexconst1093 = OwlBuf::another_ref(
                                                    &tmp_owl_hexconst1093,
                                                );
                                                owl_dec_st_aead(
                                                    SecretBuf::another_ref(&owl_k11090),
                                                    OwlBuf::another_ref(&owl_msg1_timestamp1056),
                                                    SecretBuf::from_buf(
                                                        owl_hexconst1093.another_ref(),
                                                    ),
                                                    SecretBuf::from_buf(owl_H31085.another_ref()),
                                                    Tracked(owl_declassify_tok1092),
                                                )
                                            };
                                            let owl_caseval1091 = SecretBuf::another_ref_option(
                                                &tmp_owl_caseval1091,
                                            );
                                            match SecretBuf::another_ref_option(&owl_caseval1091) {
                                                Option::None => { (None, Tracked(itree)) },
                                                Option::Some(tmp_owl_msg1_timestamp_dec1094) => {
                                                    let owl_msg1_timestamp_dec1094 =
                                                        SecretBuf::another_ref(
                                                        &tmp_owl_msg1_timestamp_dec1094,
                                                    );
                                                    let tmp_owl_H41095 = {
                                                        owl_crh(
                                                            owl_concat(
                                                                owl_H31085.as_slice(),
                                                                owl_msg1_timestamp1056.as_slice(),
                                                            ).as_slice(),
                                                        )
                                                    };
                                                    let owl_H41095 = OwlBuf::from_vec(
                                                        tmp_owl_H41095,
                                                    );
                                                    let tmp_owl_declassified_buf1096 = {
                                                        let tracked owl_declassify_tok1097 =
                                                            consume_itree_declassify::<
                                                            (
                                                                Option<owlSpec_resp_received_state>,
                                                                state_Responder,
                                                            ),
                                                            Endpoint,
                                                        >(&mut itree);
                                                        {
                                                            SecretBuf::another_ref(
                                                                &owl_dhpk_S_init1086,
                                                            ).declassify(
                                                                Tracked(owl_declassify_tok1097),
                                                            )
                                                        }
                                                    };
                                                    let owl_declassified_buf1096 =
                                                        OwlBuf::another_ref(
                                                        &tmp_owl_declassified_buf1096,
                                                    );
                                                    let tmp_owl_st1098 = {
                                                        owl_resp_received_state(
                                                            OwlBuf::another_ref(
                                                                &owl_msg1_sender1059,
                                                            ),
                                                            owl_PSKMode::another_ref(&owl_psk1083),
                                                            OwlBuf::another_ref(
                                                                &owl_declassified_buf1096,
                                                            ),
                                                            OwlBuf::another_ref(
                                                                &owl_msg1_ephemeral1058,
                                                            ),
                                                            owl_ghost_unit(),
                                                            OwlBuf::another_ref(&owl_H41095),
                                                            SecretBuf::another_ref(&owl_C31089),
                                                        )
                                                    };
                                                    let owl_st1098 =
                                                        owl_resp_received_state::another_ref(
                                                        &tmp_owl_st1098,
                                                    );
                                                    let tmp_owl_y1099 = {
                                                        owl_resp_received_state::another_ref(
                                                            &owl_st1098,
                                                        )
                                                    };
                                                    let owl_y1099 =
                                                        owl_resp_received_state::another_ref(
                                                        &tmp_owl_y1099,
                                                    );
                                                    (
                                                        Some(
                                                            owl_resp_received_state::another_ref(
                                                                &owl_y1099,
                                                            ),
                                                        ),
                                                        Tracked(itree),
                                                    )
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
        owl_pk1127: OwlBuf<'a>,
    ) -> (res: Result<
        (
            Option<owl_init_info<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_init_info>, state_Responder), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == get_pk_info_spec(*self, *old(mut_state), owl_pk1127.view()),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((view_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            Option<owl_init_info<'a>>,
            Tracked<ITreeToken<(Option<owlSpec_init_info>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(get_pk_info_spec);
            todo!()

        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_key_confirm_responder_recv(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_k1128: Ghost<()>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Responder), Endpoint>>), OwlError>)
        requires
            itree.view() == key_confirm_responder_recv_spec(*self, *old(mut_state), owl_k1128),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(key_confirm_responder_recv_spec);
            (owl_unit(), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }

    #[verifier::spinoff_prover]
    pub fn owl_key_confirm_responder_send(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_k1129: Ghost<()>,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Responder), Endpoint>>), OwlError>)
        requires
            itree.view() == key_confirm_responder_send_spec(*self, *old(mut_state), owl_k1129),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            (),
            Tracked<ITreeToken<((), state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(key_confirm_responder_send_spec);
            (owl_unit(), Tracked(itree))
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
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            OwlBuf<'a>,
            Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(timestamp_r_spec);
            todo!()
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
    {
        let tracked mut itree = itree;
        let (res_inner, Tracked(itree)): (
            OwlBuf<'a>,
            Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        ) = {
            broadcast use itree_axioms;

            reveal(get_sender_r_spec);
            todo!()
        };
        Ok((res_inner, Tracked(itree)))
    }
}

pub fn owl_secret_construction<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == construction(),
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

pub fn owl_public_construction<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == construction(),
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

pub fn owl_secret_honest_c1() -> (res: Ghost<()>)
    ensures
        res.view() == honest_c1(),
{
    reveal(honest_c1);
    owl_ghost_unit()
}

pub fn owl_public_honest_c1() -> (res: Ghost<()>)
    ensures
        res.view() == honest_c1(),
{
    reveal(honest_c1);
    owl_ghost_unit()
}

pub fn owl_secret_honest_c3() -> (res: Ghost<()>)
    ensures
        res.view() == honest_c3(),
{
    reveal(honest_c3);
    owl_ghost_unit()
}

pub fn owl_public_honest_c3() -> (res: Ghost<()>)
    ensures
        res.view() == honest_c3(),
{
    reveal(honest_c3);
    owl_ghost_unit()
}

pub fn owl_secret_honest_c4() -> (res: Ghost<()>)
    ensures
        res.view() == honest_c4(),
{
    reveal(honest_c4);
    owl_ghost_unit()
}

pub fn owl_public_honest_c4() -> (res: Ghost<()>)
    ensures
        res.view() == honest_c4(),
{
    reveal(honest_c4);
    owl_ghost_unit()
}

pub fn owl_secret_identifier<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == identifier(),
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

pub fn owl_public_identifier<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == identifier(),
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

pub fn owl_secret_mac1<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == mac1(),
{
    reveal(mac1);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x6du8, 0x61u8, 0x63u8, 0x31u8, 0x2du8, 0x2du8, 0x2du8, 0x2du8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_mac1<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == mac1(),
{
    reveal(mac1);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x6du8, 0x61u8, 0x63u8, 0x31u8, 0x2du8, 0x2du8, 0x2du8, 0x2du8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_msg1_tag_value<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == msg1_tag_value(),
{
    reveal(msg1_tag_value);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x01u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_msg1_tag_value<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == msg1_tag_value(),
{
    reveal(msg1_tag_value);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x01u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_msg2_tag_value<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == msg2_tag_value(),
{
    reveal(msg2_tag_value);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x02u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_msg2_tag_value<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == msg2_tag_value(),
{
    reveal(msg2_tag_value);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x02u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_transp_tag_value<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == transp_tag_value(),
{
    reveal(transp_tag_value);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x04u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_public_transp_tag_value<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == transp_tag_value(),
{
    reveal(transp_tag_value);
    OwlBuf::another_ref(
        &{
            let x = mk_vec_u8![0x04u8, 0x00u8, 0x00u8, 0x00u8, ];
            OwlBuf::from_vec(x)
        },
    )
}

pub fn owl_secret_zeros_16<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == zeros_16(),
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

pub fn owl_public_zeros_16<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == zeros_16(),
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

pub fn owl_secret_zeros_32<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == zeros_32(),
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

pub fn owl_public_zeros_32<'a>() -> (res: OwlBuf<'a>)
    ensures
        res.view() == zeros_32(),
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
/* no entry point */
} // verus!
