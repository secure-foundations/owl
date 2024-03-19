// Extracted verus code from file tests/wip/wg/transp.owl:
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]

pub use vstd::{modes::*, prelude::*, seq::*, string::*};
pub use crate::wireguard::owl_wg::speclib::{*, itree::*};
pub use crate::wireguard::owl_wg::execlib::{*};
pub use crate::wireguard::owl_wg::deep_view::{*};
pub use crate::wireguard::owl_wg::*;
use crate::wireguard::owl_wg::parse_serialize;
use crate::wireguard::handshake::device::Device;

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
// pub use crate::parse_serialize::View as _;

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
        old(t).view().is_output(x.dview(), endpoint_of_addr(dest_addr.view())),
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
        t.view() == old(t).view().take_input(ie.0.dview(), endpoint_of_addr(ie.1.view())),
{
    (ibuf, String::from_rust_string("".to_string())) // Specific to Wireguard---we never use the endpoints
}

#[verifier(external_body)]
pub fn owl_sample<A>(Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>, n: usize) -> (res: Vec<u8>)
    requires
        old(t).view().is_sample(n),
    ensures
        t.view() == old(t).view().get_sample(res.dview()),
{
    owl_util::gen_rand_bytes(n)
}

// for debugging purposes, not used by the compiler
#[verifier(external_body)]
pub fn debug_print_bytes(x: &[u8]) {
    println!("debug_print_bytes: {:?}", x);
}

pub fn ghost_unit() -> (res: Ghost<()>)
    ensures
        res == Ghost(()),
{
    Ghost(())
}

} // verus!
verus! {

// ------------------------------------
// ---------- SPECIFICATIONS ----------
// ------------------------------------
pub struct owlSpec_msg1 {
    pub owlSpec__msg1_tag: Seq<u8>,
    pub owlSpec__msg1_sender: Seq<u8>,
    pub owlSpec__msg1_ephemeral: Seq<u8>,
    pub owlSpec__msg1_static: Seq<u8>,
    pub owlSpec__msg1_timestamp: Seq<u8>,
    pub owlSpec__msg1_mac1: Seq<u8>,
    pub owlSpec__msg1_mac2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_msg1(x: Seq<u8>) -> Option<owlSpec_msg1> {
    let stream = parse_serialize::SpecStream { data: x, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::spec_parse_owl_msg1(stream) {
        let (
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
        ) = parsed;
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
    if no_usize_overflows_spec![ x.owlSpec__msg1_tag.len(), x.owlSpec__msg1_sender.len(), x.owlSpec__msg1_ephemeral.len(), x.owlSpec__msg1_static.len(), x.owlSpec__msg1_timestamp.len(), x.owlSpec__msg1_mac1.len(), x.owlSpec__msg1_mac2.len() ] {
        let stream = parse_serialize::SpecStream {
            data: seq_u8_of_len(
                x.owlSpec__msg1_tag.len() + x.owlSpec__msg1_sender.len()
                    + x.owlSpec__msg1_ephemeral.len() + x.owlSpec__msg1_static.len()
                    + x.owlSpec__msg1_timestamp.len() + x.owlSpec__msg1_mac1.len()
                    + x.owlSpec__msg1_mac2.len(),
            ),
            start: 0,
        };
        if let Ok((serialized, n)) = parse_serialize::spec_serialize_owl_msg1(
            stream,
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
            Some(seq_truncate(serialized.data, n))
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
    arg__msg1_tag: Seq<u8>,
    arg__msg1_sender: Seq<u8>,
    arg__msg1_ephemeral: Seq<u8>,
    arg__msg1_static: Seq<u8>,
    arg__msg1_timestamp: Seq<u8>,
    arg__msg1_mac1: Seq<u8>,
    arg__msg1_mac2: Seq<u8>,
) -> Seq<u8> {
    serialize_owlSpec_msg1(
        owlSpec_msg1 {
            owlSpec__msg1_tag: arg__msg1_tag,
            owlSpec__msg1_sender: arg__msg1_sender,
            owlSpec__msg1_ephemeral: arg__msg1_ephemeral,
            owlSpec__msg1_static: arg__msg1_static,
            owlSpec__msg1_timestamp: arg__msg1_timestamp,
            owlSpec__msg1_mac1: arg__msg1_mac1,
            owlSpec__msg1_mac2: arg__msg1_mac2,
        },
    )
}

pub struct owlSpec_msg2 {
    pub owlSpec__msg2_tag: Seq<u8>,
    pub owlSpec__msg2_sender: Seq<u8>,
    pub owlSpec__msg2_receiver: Seq<u8>,
    pub owlSpec__msg2_ephemeral: Seq<u8>,
    pub owlSpec__msg2_empty: Seq<u8>,
    pub owlSpec__msg2_mac1: Seq<u8>,
    pub owlSpec__msg2_mac2: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_msg2(x: Seq<u8>) -> Option<owlSpec_msg2> {
    let stream = parse_serialize::SpecStream { data: x, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::spec_parse_owl_msg2(stream) {
        let (
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
        ) = parsed;
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
    if no_usize_overflows_spec![ x.owlSpec__msg2_tag.len(), x.owlSpec__msg2_sender.len(), x.owlSpec__msg2_receiver.len(), x.owlSpec__msg2_ephemeral.len(), x.owlSpec__msg2_empty.len(), x.owlSpec__msg2_mac1.len(), x.owlSpec__msg2_mac2.len() ] {
        let stream = parse_serialize::SpecStream {
            data: seq_u8_of_len(
                x.owlSpec__msg2_tag.len() + x.owlSpec__msg2_sender.len()
                    + x.owlSpec__msg2_receiver.len() + x.owlSpec__msg2_ephemeral.len()
                    + x.owlSpec__msg2_empty.len() + x.owlSpec__msg2_mac1.len()
                    + x.owlSpec__msg2_mac2.len(),
            ),
            start: 0,
        };
        if let Ok((serialized, n)) = parse_serialize::spec_serialize_owl_msg2(
            stream,
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
            Some(seq_truncate(serialized.data, n))
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
    arg__msg2_tag: Seq<u8>,
    arg__msg2_sender: Seq<u8>,
    arg__msg2_receiver: Seq<u8>,
    arg__msg2_ephemeral: Seq<u8>,
    arg__msg2_empty: Seq<u8>,
    arg__msg2_mac1: Seq<u8>,
    arg__msg2_mac2: Seq<u8>,
) -> Seq<u8> {
    serialize_owlSpec_msg2(
        owlSpec_msg2 {
            owlSpec__msg2_tag: arg__msg2_tag,
            owlSpec__msg2_sender: arg__msg2_sender,
            owlSpec__msg2_receiver: arg__msg2_receiver,
            owlSpec__msg2_ephemeral: arg__msg2_ephemeral,
            owlSpec__msg2_empty: arg__msg2_empty,
            owlSpec__msg2_mac1: arg__msg2_mac1,
            owlSpec__msg2_mac2: arg__msg2_mac2,
        },
    )
}

pub struct owlSpec_transp {
    pub owlSpec__transp_tag: Seq<u8>,
    pub owlSpec__transp_receiver: Seq<u8>,
    pub owlSpec__transp_counter: Seq<u8>,
    pub owlSpec__transp_packet: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_transp(x: Seq<u8>) -> Option<owlSpec_transp> {
    let stream = parse_serialize::SpecStream { data: x, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::spec_parse_owl_transp(stream) {
        let (
            ((owlSpec__transp_tag, owlSpec__transp_receiver), owlSpec__transp_counter),
            owlSpec__transp_packet,
        ) = parsed;
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
    if no_usize_overflows_spec![ x.owlSpec__transp_tag.len(), x.owlSpec__transp_receiver.len(), x.owlSpec__transp_counter.len(), x.owlSpec__transp_packet.len() ] {
        let stream = parse_serialize::SpecStream {
            data: seq_u8_of_len(
                x.owlSpec__transp_tag.len() + x.owlSpec__transp_receiver.len()
                    + x.owlSpec__transp_counter.len() + x.owlSpec__transp_packet.len(),
            ),
            start: 0,
        };
        if let Ok((serialized, n)) = parse_serialize::spec_serialize_owl_transp(
            stream,
            ((
                ((x.owlSpec__transp_tag, x.owlSpec__transp_receiver), x.owlSpec__transp_counter),
                x.owlSpec__transp_packet,
            )),
        ) {
            Some(seq_truncate(serialized.data, n))
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
    arg__transp_tag: Seq<u8>,
    arg__transp_receiver: Seq<u8>,
    arg__transp_counter: Seq<u8>,
    arg__transp_packet: Seq<u8>,
) -> Seq<u8> {
    serialize_owlSpec_transp(
        owlSpec_transp {
            owlSpec__transp_tag: arg__transp_tag,
            owlSpec__transp_receiver: arg__transp_receiver,
            owlSpec__transp_counter: arg__transp_counter,
            owlSpec__transp_packet: arg__transp_packet,
        },
    )
}

pub struct owlSpec_transp_keys_init {
    pub owlSpec_tki_msg2_receiver: Seq<u8>,
    pub owlSpec_tki_msg2_sender: Seq<u8>,
    pub owlSpec_tki_k_init_send: Seq<u8>,
    pub owlSpec_tki_k_resp_send: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_transp_keys_init(x: Seq<u8>) -> Option<owlSpec_transp_keys_init> {
    let stream = parse_serialize::SpecStream { data: x, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::spec_parse_owl_transp_keys_init(stream) {
        let (
            ((owlSpec_tki_msg2_receiver, owlSpec_tki_msg2_sender), owlSpec_tki_k_init_send),
            owlSpec_tki_k_resp_send,
        ) = parsed;
        Some(
            owlSpec_transp_keys_init {
                owlSpec_tki_msg2_receiver,
                owlSpec_tki_msg2_sender,
                owlSpec_tki_k_init_send,
                owlSpec_tki_k_resp_send,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_transp_keys_init_inner(x: owlSpec_transp_keys_init) -> Option<
    Seq<u8>,
> {
    if no_usize_overflows_spec![ x.owlSpec_tki_msg2_receiver.len(), x.owlSpec_tki_msg2_sender.len(), x.owlSpec_tki_k_init_send.len(), x.owlSpec_tki_k_resp_send.len() ] {
        let stream = parse_serialize::SpecStream {
            data: seq_u8_of_len(
                x.owlSpec_tki_msg2_receiver.len() + x.owlSpec_tki_msg2_sender.len()
                    + x.owlSpec_tki_k_init_send.len() + x.owlSpec_tki_k_resp_send.len(),
            ),
            start: 0,
        };
        if let Ok((serialized, n)) = parse_serialize::spec_serialize_owl_transp_keys_init(
            stream,
            ((
                (
                    (x.owlSpec_tki_msg2_receiver, x.owlSpec_tki_msg2_sender),
                    x.owlSpec_tki_k_init_send,
                ),
                x.owlSpec_tki_k_resp_send,
            )),
        ) {
            Some(seq_truncate(serialized.data, n))
        } else {
            None
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_transp_keys_init(x: owlSpec_transp_keys_init) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_transp_keys_init_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_transp_keys_init {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_transp_keys_init(self)
    }
}

pub open spec fn transp_keys_init(
    arg_tki_msg2_receiver: Seq<u8>,
    arg_tki_msg2_sender: Seq<u8>,
    arg_tki_k_init_send: Seq<u8>,
    arg_tki_k_resp_send: Seq<u8>,
) -> Seq<u8> {
    serialize_owlSpec_transp_keys_init(
        owlSpec_transp_keys_init {
            owlSpec_tki_msg2_receiver: arg_tki_msg2_receiver,
            owlSpec_tki_msg2_sender: arg_tki_msg2_sender,
            owlSpec_tki_k_init_send: arg_tki_k_init_send,
            owlSpec_tki_k_resp_send: arg_tki_k_resp_send,
        },
    )
}

pub struct owlSpec_transp_keys_resp {
    pub owlSpec_tkr_msg2_receiver: Seq<u8>,
    pub owlSpec_tkr_msg2_sender: Seq<u8>,
    pub owlSpec_tkr_recvd: bool,
    pub owlSpec_tkr_k_init_send: Seq<u8>,
    pub owlSpec_tkr_k_resp_send: Seq<u8>,
}

#[verifier(external_body)]
pub closed spec fn parse_owlSpec_transp_keys_resp(x: Seq<u8>) -> Option<owlSpec_transp_keys_resp> {
    // can't autogenerate vest parser
    todo!()
}

#[verifier(external_body)]
pub closed spec fn serialize_owlSpec_transp_keys_resp(x: owlSpec_transp_keys_resp) -> Seq<u8> {
    // can't autogenerate vest serializer
    todo!()
}

impl OwlSpecSerialize for owlSpec_transp_keys_resp {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_transp_keys_resp(self)
    }
}

pub open spec fn transp_keys_resp(
    arg_tkr_msg2_receiver: Seq<u8>,
    arg_tkr_msg2_sender: Seq<u8>,
    arg_tkr_recvd: bool,
    arg_tkr_k_init_send: Seq<u8>,
    arg_tkr_k_resp_send: Seq<u8>,
) -> Seq<u8> {
    serialize_owlSpec_transp_keys_resp(
        owlSpec_transp_keys_resp {
            owlSpec_tkr_msg2_receiver: arg_tkr_msg2_receiver,
            owlSpec_tkr_msg2_sender: arg_tkr_msg2_sender,
            owlSpec_tkr_recvd: arg_tkr_recvd,
            owlSpec_tkr_k_init_send: arg_tkr_k_init_send,
            owlSpec_tkr_k_resp_send: arg_tkr_k_resp_send,
        },
    )
}

pub struct owlSpec_resp_transp_recv_result {
    pub owlSpec_rr_st: Seq<u8>,
    pub owlSpec_rr_msg: Seq<u8>,
}

#[verifier(external_body)]
pub closed spec fn parse_owlSpec_resp_transp_recv_result(x: Seq<u8>) -> Option<
    owlSpec_resp_transp_recv_result,
> {
    // can't autogenerate vest parser
    todo!()
}

#[verifier(external_body)]
pub closed spec fn serialize_owlSpec_resp_transp_recv_result(
    x: owlSpec_resp_transp_recv_result,
) -> Seq<u8> {
    // can't autogenerate vest serializer
    todo!()
}

impl OwlSpecSerialize for owlSpec_resp_transp_recv_result {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_resp_transp_recv_result(self)
    }
}

pub open spec fn resp_transp_recv_result(arg_rr_st: Seq<u8>, arg_rr_msg: Seq<u8>) -> Seq<u8> {
    serialize_owlSpec_resp_transp_recv_result(
        owlSpec_resp_transp_recv_result { owlSpec_rr_st: arg_rr_st, owlSpec_rr_msg: arg_rr_msg },
    )
}

#[derive(Copy, Clone)]
pub enum Endpoint {
    Loc_Initiator,
    Loc_Responder,
    Loc_nobody,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */

}

#[verifier::opaque]
pub open spec fn init_send_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    tki: owlSpec_transp_keys_init,
    msg: Seq<u8>,
) -> (res: ITree<((), state_Initiator), Endpoint>) {
    owl_spec!(mut_state,state_Initiator,
(parse (tki) as (owlSpec_transp_keys_init{owlSpec_tki_msg2_receiver : init , owlSpec_tki_msg2_sender : resp , owlSpec_tki_k_init_send : init_send , owlSpec_tki_k_resp_send : resp_send }) in {
let transp_counter = ((ret(counter_as_bytes(mut_state.owl_N_init_send)))) in
let c = ((ret(enc_st_aead(init_send, msg, owl_N_init_send, empty_seq_u8())))) in
let transp_tag = ((ret (transp_tag_value()))) in
let o = ((ret (transp(transp_tag, init, transp_counter, c)))) in
(output (o) to (Endpoint::Loc_Responder))
} )
)
}

#[verifier::opaque]
pub open spec fn init_recv_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    tki: owlSpec_transp_keys_init,
) -> (res: ITree<(Option<Seq<u8>>, state_Initiator), Endpoint>) {
    owl_spec!(mut_state,state_Initiator,
(input (i, _unused74)) in
(parse (tki) as (owlSpec_transp_keys_init{owlSpec_tki_msg2_receiver : init , owlSpec_tki_msg2_sender : resp , owlSpec_tki_k_init_send : init_send , owlSpec_tki_k_resp_send : resp_send }) in {
(parse (parse_owlSpec_transp(i)) as (owlSpec_transp{owlSpec__transp_tag : tag , owlSpec__transp_receiver : from , owlSpec__transp_counter : ctr , owlSpec__transp_packet : pkt }) in {
(if (from == resp) then (let p = ((ret(dec_st_aead( resp_send
, pkt
, ctr
, empty_seq_u8() )))) in
(ret (p))) else ((ret (Option::None))))
} otherwise ((ret (Option::None))))
} )
)
}

#[verifier::opaque]
pub open spec fn timestamp_i_spec(cfg: cfg_Initiator, mut_state: state_Initiator) -> (res: ITree<
    (Seq<u8>, state_Initiator),
    Endpoint,
>) {
    owl_spec!(mut_state,state_Initiator,
(ret(owlSpec_timestamp_i_pure()))
)
}

#[verifier(external_body)]
pub closed spec fn owlSpec_timestamp_i_pure() -> Seq<u8> {
    unimplemented!()
}

#[verifier::opaque]
pub open spec fn get_sender_i_spec(cfg: cfg_Initiator, mut_state: state_Initiator) -> (res: ITree<
    (Seq<u8>, state_Initiator),
    Endpoint,
>) {
    owl_spec!(mut_state,state_Initiator,
(ret(owlSpec_get_sender_i_pure()))
)
}

#[verifier(external_body)]
pub closed spec fn owlSpec_get_sender_i_pure() -> Seq<u8> {
    unimplemented!()
}

#[verifier::opaque]
pub open spec fn resp_send_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    tki: owlSpec_transp_keys_resp,
    msg: Seq<u8>,
) -> (res: ITree<(Option<()>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(parse (tki) as (owlSpec_transp_keys_resp{owlSpec_tkr_msg2_receiver : init , owlSpec_tkr_msg2_sender : resp , owlSpec_tkr_recvd : b , owlSpec_tkr_k_init_send : init_send , owlSpec_tkr_k_resp_send : resp_send }) in {
(if (b) then (let transp_counter = ((ret(counter_as_bytes(mut_state.owl_N_resp_send)))) in
let c = ((ret(enc_st_aead(resp_send, msg, owl_N_resp_send, empty_seq_u8())))) in
let transp_tag = ((ret (transp_tag_value()))) in
let o = ((ret (transp(transp_tag, resp, transp_counter, c)))) in
(output (o) to (Endpoint::Loc_Initiator)) in
(ret (Option::Some(())))) else ((ret (Option::None))))
} )
)
}

#[verifier::opaque]
pub open spec fn resp_recv_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    tki: owlSpec_transp_keys_resp,
) -> (res: ITree<(Option<Seq<u8>>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(input (i, _unused242)) in
(parse (tki) as (owlSpec_transp_keys_resp{owlSpec_tkr_msg2_receiver : init , owlSpec_tkr_msg2_sender : resp , owlSpec_tkr_recvd : _unused241 , owlSpec_tkr_k_init_send : init_send , owlSpec_tkr_k_resp_send : resp_send }) in {
(parse (parse_owlSpec_transp(i)) as (owlSpec_transp{owlSpec__transp_tag : tag , owlSpec__transp_receiver : from , owlSpec__transp_counter : ctr , owlSpec__transp_packet : pkt }) in {
(if (from == init) then (let caseval = ((ret(dec_st_aead( init_send
, pkt
, ctr
, empty_seq_u8() )))) in
(case (caseval){
| Some (x) => {let st_ = ((ret (transp_keys_resp( init
, resp
, true
, init_send
, resp_send )))) in
(ret (Option::Some(resp_transp_recv_result(st_, x))))},
| None => {(ret (Option::None))},

})) else ((ret (Option::None))))
} otherwise ((ret (Option::None))))
} )
)
}

#[verifier::opaque]
pub open spec fn timestamp_r_spec(cfg: cfg_Responder, mut_state: state_Responder) -> (res: ITree<
    (Seq<u8>, state_Responder),
    Endpoint,
>) {
    owl_spec!(mut_state,state_Responder,
(ret(owlSpec_timestamp_r_pure()))
)
}

#[verifier(external_body)]
pub closed spec fn owlSpec_timestamp_r_pure() -> Seq<u8> {
    unimplemented!()
}

#[verifier::opaque]
pub open spec fn get_sender_r_spec(cfg: cfg_Responder, mut_state: state_Responder) -> (res: ITree<
    (Seq<u8>, state_Responder),
    Endpoint,
>) {
    owl_spec!(mut_state,state_Responder,
(ret(owlSpec_get_sender_r_pure()))
)
}

#[verifier(external_body)]
pub closed spec fn owlSpec_get_sender_r_pure() -> Seq<u8> {
    unimplemented!()
}

// ------------------------------------
// ---------- IMPLEMENTATIONS ---------
// ------------------------------------
/* TODO this will be generated by parsley */

pub struct owl_msg1<'a> {
    pub owl__msg1_tag: OwlBuf<'a>,
    pub owl__msg1_sender: OwlBuf<'a>,
    pub owl__msg1_ephemeral: OwlBuf<'a>,
    pub owl__msg1_static: OwlBuf<'a>,
    pub owl__msg1_timestamp: OwlBuf<'a>,
    pub owl__msg1_mac1: OwlBuf<'a>,
    pub owl__msg1_mac2: OwlBuf<'a>,
}

impl DView for owl_msg1<'_> {
    type V = owlSpec_msg1;

    open spec fn dview(&self) -> owlSpec_msg1 {
        owlSpec_msg1 {
            owlSpec__msg1_tag: self.owl__msg1_tag.dview().as_seq(),
            owlSpec__msg1_sender: self.owl__msg1_sender.dview().as_seq(),
            owlSpec__msg1_ephemeral: self.owl__msg1_ephemeral.dview().as_seq(),
            owlSpec__msg1_static: self.owl__msg1_static.dview().as_seq(),
            owlSpec__msg1_timestamp: self.owl__msg1_timestamp.dview().as_seq(),
            owlSpec__msg1_mac1: self.owl__msg1_mac1.dview().as_seq(),
            owlSpec__msg1_mac2: self.owl__msg1_mac2.dview().as_seq(),
        }
    }
}

impl owl_msg1<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl__msg1_tag.len_valid() && self.owl__msg1_sender.len_valid()
            && self.owl__msg1_ephemeral.len_valid() && self.owl__msg1_static.len_valid()
            && self.owl__msg1_timestamp.len_valid() && self.owl__msg1_mac1.len_valid()
            && self.owl__msg1_mac2.len_valid()
    }
}

pub exec fn parse_owl_msg1<'a>(arg: &'a OwlBuf<'a>) -> (res: Option<owl_msg1<'a>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_msg1(arg.dview()) is Some,
        res is None ==> parse_owlSpec_msg1(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == parse_owlSpec_msg1(arg.dview())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_msg1);
    let stream = parse_serialize::Stream { data: arg.as_slice(), start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::parse_owl_msg1(stream) {
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
                owl__msg1_tag: OwlBuf::from_slice(owl__msg1_tag),
                owl__msg1_sender: OwlBuf::from_slice(owl__msg1_sender),
                owl__msg1_ephemeral: OwlBuf::from_slice(owl__msg1_ephemeral),
                owl__msg1_static: OwlBuf::from_slice(owl__msg1_static),
                owl__msg1_timestamp: OwlBuf::from_slice(owl__msg1_timestamp),
                owl__msg1_mac1: OwlBuf::from_slice(owl__msg1_mac1),
                owl__msg1_mac2: OwlBuf::from_slice(owl__msg1_mac2),
            },
        )
    } else {
        None
    }
}

/* TODO work around `as_mut_slice` call */

#[verifier(external_body)]
pub exec fn serialize_owl_msg1_inner(arg: &owl_msg1) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> serialize_owlSpec_msg1_inner(arg.dview()) is Some,
        res is None ==> serialize_owlSpec_msg1_inner(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == serialize_owlSpec_msg1_inner(arg.dview())->Some_0,
{
    reveal(serialize_owlSpec_msg1_inner);
    if no_usize_overflows![ arg.owl__msg1_tag.len(), arg.owl__msg1_sender.len(), arg.owl__msg1_ephemeral.len(), arg.owl__msg1_static.len(), arg.owl__msg1_timestamp.len(), arg.owl__msg1_mac1.len(), arg.owl__msg1_mac2.len() ] {
        let mut obuf = vec_u8_of_len(
            arg.owl__msg1_tag.len() + arg.owl__msg1_sender.len() + arg.owl__msg1_ephemeral.len()
                + arg.owl__msg1_static.len() + arg.owl__msg1_timestamp.len()
                + arg.owl__msg1_mac1.len() + arg.owl__msg1_mac2.len(),
        );
        let ser_result = parse_serialize::serialize_owl_msg1(
            obuf.as_mut_slice(),
            0,
            ((
                (
                    (
                        (
                            (
                                (&arg.owl__msg1_tag.as_slice(), &arg.owl__msg1_sender.as_slice()),
                                &arg.owl__msg1_ephemeral.as_slice(),
                            ),
                            &arg.owl__msg1_static.as_slice(),
                        ),
                        &arg.owl__msg1_timestamp.as_slice(),
                    ),
                    &arg.owl__msg1_mac1.as_slice(),
                ),
                &arg.owl__msg1_mac2.as_slice(),
            )),
        );
        if let Ok((_new_start, num_written)) = ser_result {
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
        res.dview() == serialize_owlSpec_msg1(arg.dview()),
{
    reveal(serialize_owlSpec_msg1);
    let res = serialize_owl_msg1_inner(arg);
    assume(res is Some);
    res.unwrap()
}

/* TODO this will be generated by parsley */

pub struct owl_msg2<'a> {
    pub owl__msg2_tag: OwlBuf<'a>,
    pub owl__msg2_sender: OwlBuf<'a>,
    pub owl__msg2_receiver: OwlBuf<'a>,
    pub owl__msg2_ephemeral: OwlBuf<'a>,
    pub owl__msg2_empty: OwlBuf<'a>,
    pub owl__msg2_mac1: OwlBuf<'a>,
    pub owl__msg2_mac2: OwlBuf<'a>,
}

impl DView for owl_msg2<'_> {
    type V = owlSpec_msg2;

    open spec fn dview(&self) -> owlSpec_msg2 {
        owlSpec_msg2 {
            owlSpec__msg2_tag: self.owl__msg2_tag.dview().as_seq(),
            owlSpec__msg2_sender: self.owl__msg2_sender.dview().as_seq(),
            owlSpec__msg2_receiver: self.owl__msg2_receiver.dview().as_seq(),
            owlSpec__msg2_ephemeral: self.owl__msg2_ephemeral.dview().as_seq(),
            owlSpec__msg2_empty: self.owl__msg2_empty.dview().as_seq(),
            owlSpec__msg2_mac1: self.owl__msg2_mac1.dview().as_seq(),
            owlSpec__msg2_mac2: self.owl__msg2_mac2.dview().as_seq(),
        }
    }
}

impl owl_msg2<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl__msg2_tag.len_valid() && self.owl__msg2_sender.len_valid()
            && self.owl__msg2_receiver.len_valid() && self.owl__msg2_ephemeral.len_valid()
            && self.owl__msg2_empty.len_valid() && self.owl__msg2_mac1.len_valid()
            && self.owl__msg2_mac2.len_valid()
    }
}

pub exec fn parse_owl_msg2<'a>(arg: &'a OwlBuf<'a>) -> (res: Option<owl_msg2<'a>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_msg2(arg.dview()) is Some,
        res is None ==> parse_owlSpec_msg2(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == parse_owlSpec_msg2(arg.dview())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_msg2);
    let stream = parse_serialize::Stream { data: arg.as_slice(), start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::parse_owl_msg2(stream) {
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
                owl__msg2_tag: OwlBuf::from_slice(owl__msg2_tag),
                owl__msg2_sender: OwlBuf::from_slice(owl__msg2_sender),
                owl__msg2_receiver: OwlBuf::from_slice(owl__msg2_receiver),
                owl__msg2_ephemeral: OwlBuf::from_slice(owl__msg2_ephemeral),
                owl__msg2_empty: OwlBuf::from_slice(owl__msg2_empty),
                owl__msg2_mac1: OwlBuf::from_slice(owl__msg2_mac1),
                owl__msg2_mac2: OwlBuf::from_slice(owl__msg2_mac2),
            },
        )
    } else {
        None
    }
}

/* TODO work around `as_mut_slice` call */

#[verifier(external_body)]
pub exec fn serialize_owl_msg2_inner(arg: &owl_msg2) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> serialize_owlSpec_msg2_inner(arg.dview()) is Some,
        res is None ==> serialize_owlSpec_msg2_inner(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == serialize_owlSpec_msg2_inner(arg.dview())->Some_0,
{
    reveal(serialize_owlSpec_msg2_inner);
    if no_usize_overflows![ arg.owl__msg2_tag.len(), arg.owl__msg2_sender.len(), arg.owl__msg2_receiver.len(), arg.owl__msg2_ephemeral.len(), arg.owl__msg2_empty.len(), arg.owl__msg2_mac1.len(), arg.owl__msg2_mac2.len() ] {
        let mut obuf = vec_u8_of_len(
            arg.owl__msg2_tag.len() + arg.owl__msg2_sender.len() + arg.owl__msg2_receiver.len()
                + arg.owl__msg2_ephemeral.len() + arg.owl__msg2_empty.len()
                + arg.owl__msg2_mac1.len() + arg.owl__msg2_mac2.len(),
        );
        let ser_result = parse_serialize::serialize_owl_msg2(
            obuf.as_mut_slice(),
            0,
            ((
                (
                    (
                        (
                            (
                                (&arg.owl__msg2_tag.as_slice(), &arg.owl__msg2_sender.as_slice()),
                                &arg.owl__msg2_receiver.as_slice(),
                            ),
                            &arg.owl__msg2_ephemeral.as_slice(),
                        ),
                        &arg.owl__msg2_empty.as_slice(),
                    ),
                    &arg.owl__msg2_mac1.as_slice(),
                ),
                &arg.owl__msg2_mac2.as_slice(),
            )),
        );
        if let Ok((_new_start, num_written)) = ser_result {
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
        res.dview() == serialize_owlSpec_msg2(arg.dview()),
{
    reveal(serialize_owlSpec_msg2);
    let res = serialize_owl_msg2_inner(arg);
    assume(res is Some);
    res.unwrap()
}

/* TODO this will be generated by parsley */

pub struct owl_transp<'a> {
    pub owl__transp_tag: OwlBuf<'a>,
    pub owl__transp_receiver: OwlBuf<'a>,
    pub owl__transp_counter: OwlBuf<'a>,
    pub owl__transp_packet: OwlBuf<'a>,
}

impl DView for owl_transp<'_> {
    type V = owlSpec_transp;

    open spec fn dview(&self) -> owlSpec_transp {
        owlSpec_transp {
            owlSpec__transp_tag: self.owl__transp_tag.dview().as_seq(),
            owlSpec__transp_receiver: self.owl__transp_receiver.dview().as_seq(),
            owlSpec__transp_counter: self.owl__transp_counter.dview().as_seq(),
            owlSpec__transp_packet: self.owl__transp_packet.dview().as_seq(),
        }
    }
}

impl owl_transp<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl__transp_tag.len_valid() && self.owl__transp_receiver.len_valid()
            && self.owl__transp_counter.len_valid() && self.owl__transp_packet.len_valid()
    }
}

pub exec fn parse_owl_transp<'a>(arg: &'a OwlBuf<'a>) -> (res: Option<owl_transp<'a>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_transp(arg.dview()) is Some,
        res is None ==> parse_owlSpec_transp(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == parse_owlSpec_transp(arg.dview())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_transp);
    let stream = parse_serialize::Stream { data: arg.as_slice(), start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::parse_owl_transp(stream) {
        let (((owl__transp_tag, owl__transp_receiver), owl__transp_counter), owl__transp_packet) =
            parsed;
        Some(
            owl_transp {
                owl__transp_tag: OwlBuf::from_slice(owl__transp_tag),
                owl__transp_receiver: OwlBuf::from_slice(owl__transp_receiver),
                owl__transp_counter: OwlBuf::from_slice(owl__transp_counter),
                owl__transp_packet: OwlBuf::from_slice(owl__transp_packet),
            },
        )
    } else {
        None
    }
}

/* TODO work around `as_mut_slice` call */

#[verifier(external_body)]
pub exec fn serialize_owl_transp_inner(arg: &owl_transp) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> serialize_owlSpec_transp_inner(arg.dview()) is Some,
        res is None ==> serialize_owlSpec_transp_inner(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == serialize_owlSpec_transp_inner(arg.dview())->Some_0,
{
    reveal(serialize_owlSpec_transp_inner);
    if no_usize_overflows![ arg.owl__transp_tag.len(), arg.owl__transp_receiver.len(), arg.owl__transp_counter.len(), arg.owl__transp_packet.len() ] {
        let mut obuf = vec_u8_of_len(
            arg.owl__transp_tag.len() + arg.owl__transp_receiver.len()
                + arg.owl__transp_counter.len() + arg.owl__transp_packet.len(),
        );
        // dbg!(hex::encode(arg.owl__transp_tag.as_slice()));
        // dbg!(hex::encode(arg.owl__transp_receiver.as_slice()));
        // dbg!(hex::encode(arg.owl__transp_counter.as_slice()));
        // dbg!(hex::encode(arg.owl__transp_packet.as_slice()));
        // dbg!(arg.owl__transp_tag.len());
        // dbg!(arg.owl__transp_receiver.len());
        // dbg!(arg.owl__transp_counter.len());
        // dbg!(arg.owl__transp_packet.len());
        // dbg!(obuf.len());
        let ser_result = parse_serialize::serialize_owl_transp(
            obuf.as_mut_slice(),
            0,
            ((
                (
                    (&arg.owl__transp_tag.as_slice(), &arg.owl__transp_receiver.as_slice()),
                    &arg.owl__transp_counter.as_slice(),
                ),
                &arg.owl__transp_packet.as_slice(),
            )),
        );
        if let Ok((_new_start, num_written)) = ser_result {
            vec_truncate(&mut obuf, num_written);
            Some(obuf)
        } else {
            dbg!(ser_result);
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
        res.dview() == serialize_owlSpec_transp(arg.dview()),
{
    reveal(serialize_owlSpec_transp);
    let res = serialize_owl_transp_inner(arg);
    assume(res is Some);
    res.unwrap()
}

/* TODO this will be generated by parsley */

pub struct owl_transp_keys_init<'a> {
    pub owl_tki_msg2_receiver: OwlBuf<'a>,
    pub owl_tki_msg2_sender: OwlBuf<'a>,
    pub owl_tki_k_init_send: OwlBuf<'a>,
    pub owl_tki_k_resp_send: OwlBuf<'a>,
}

impl DView for owl_transp_keys_init<'_> {
    type V = owlSpec_transp_keys_init;

    open spec fn dview(&self) -> owlSpec_transp_keys_init {
        owlSpec_transp_keys_init {
            owlSpec_tki_msg2_receiver: self.owl_tki_msg2_receiver.dview().as_seq(),
            owlSpec_tki_msg2_sender: self.owl_tki_msg2_sender.dview().as_seq(),
            owlSpec_tki_k_init_send: self.owl_tki_k_init_send.dview().as_seq(),
            owlSpec_tki_k_resp_send: self.owl_tki_k_resp_send.dview().as_seq(),
        }
    }
}

impl owl_transp_keys_init<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_tki_msg2_receiver.len_valid() && self.owl_tki_msg2_sender.len_valid()
            && self.owl_tki_k_init_send.len_valid() && self.owl_tki_k_resp_send.len_valid()
    }
}

pub exec fn parse_owl_transp_keys_init<'a>(arg: &'a OwlBuf<'a>) -> (res: Option<
    owl_transp_keys_init<'a>,
>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_transp_keys_init(arg.dview()) is Some,
        res is None ==> parse_owlSpec_transp_keys_init(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == parse_owlSpec_transp_keys_init(arg.dview())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_transp_keys_init);
    let stream = parse_serialize::Stream { data: arg.as_slice(), start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::parse_owl_transp_keys_init(stream) {
        let (
            ((owl_tki_msg2_receiver, owl_tki_msg2_sender), owl_tki_k_init_send),
            owl_tki_k_resp_send,
        ) = parsed;
        Some(
            owl_transp_keys_init {
                owl_tki_msg2_receiver: OwlBuf::from_slice(owl_tki_msg2_receiver),
                owl_tki_msg2_sender: OwlBuf::from_slice(owl_tki_msg2_sender),
                owl_tki_k_init_send: OwlBuf::from_slice(owl_tki_k_init_send),
                owl_tki_k_resp_send: OwlBuf::from_slice(owl_tki_k_resp_send),
            },
        )
    } else {
        None
    }
}

/* TODO work around `as_mut_slice` call */

#[verifier(external_body)]
pub exec fn serialize_owl_transp_keys_init_inner(arg: &owl_transp_keys_init) -> (res: Option<
    Vec<u8>,
>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> serialize_owlSpec_transp_keys_init_inner(arg.dview()) is Some,
        res is None ==> serialize_owlSpec_transp_keys_init_inner(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == serialize_owlSpec_transp_keys_init_inner(
            arg.dview(),
        )->Some_0,
{
    reveal(serialize_owlSpec_transp_keys_init_inner);
    if no_usize_overflows![ arg.owl_tki_msg2_receiver.len(), arg.owl_tki_msg2_sender.len(), arg.owl_tki_k_init_send.len(), arg.owl_tki_k_resp_send.len() ] {
        let mut obuf = vec_u8_of_len(
            arg.owl_tki_msg2_receiver.len() + arg.owl_tki_msg2_sender.len()
                + arg.owl_tki_k_init_send.len() + arg.owl_tki_k_resp_send.len(),
        );
        let ser_result = parse_serialize::serialize_owl_transp_keys_init(
            obuf.as_mut_slice(),
            0,
            ((
                (
                    (&arg.owl_tki_msg2_receiver.as_slice(), &arg.owl_tki_msg2_sender.as_slice()),
                    &arg.owl_tki_k_init_send.as_slice(),
                ),
                &arg.owl_tki_k_resp_send.as_slice(),
            )),
        );
        if let Ok((_new_start, num_written)) = ser_result {
            vec_truncate(&mut obuf, num_written);
            Some(obuf)
        } else {
            None
        }
    } else {
        None
    }
}

pub exec fn serialize_owl_transp_keys_init(arg: &owl_transp_keys_init) -> (res: Vec<u8>)
    requires
        arg.len_valid(),
    ensures
        res.dview() == serialize_owlSpec_transp_keys_init(arg.dview()),
{
    reveal(serialize_owlSpec_transp_keys_init);
    let res = serialize_owl_transp_keys_init_inner(arg);
    assume(res is Some);
    res.unwrap()
}

/* TODO this will be generated by parsley */

pub struct owl_transp_keys_resp<'a> {
    pub owl_tkr_msg2_receiver: OwlBuf<'a>,
    pub owl_tkr_msg2_sender: OwlBuf<'a>,
    pub owl_tkr_recvd: bool,
    pub owl_tkr_k_init_send: OwlBuf<'a>,
    pub owl_tkr_k_resp_send: OwlBuf<'a>,
}

impl DView for owl_transp_keys_resp<'_> {
    type V = owlSpec_transp_keys_resp;

    open spec fn dview(&self) -> owlSpec_transp_keys_resp {
        owlSpec_transp_keys_resp {
            owlSpec_tkr_msg2_receiver: self.owl_tkr_msg2_receiver.dview().as_seq(),
            owlSpec_tkr_msg2_sender: self.owl_tkr_msg2_sender.dview().as_seq(),
            owlSpec_tkr_recvd: self.owl_tkr_recvd.dview(),
            owlSpec_tkr_k_init_send: self.owl_tkr_k_init_send.dview().as_seq(),
            owlSpec_tkr_k_resp_send: self.owl_tkr_k_resp_send.dview().as_seq(),
        }
    }
}

impl owl_transp_keys_resp<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_tkr_msg2_receiver.len_valid() && self.owl_tkr_msg2_sender.len_valid()
            && self.owl_tkr_k_init_send.len_valid() && self.owl_tkr_k_resp_send.len_valid()
    }
}

#[verifier(external_body)]
pub exec fn parse_owl_transp_keys_resp<'a>(arg: &'a OwlBuf<'a>) -> (res: Option<
    owl_transp_keys_resp<'a>,
>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_transp_keys_resp(arg.dview()) is Some,
        res is None ==> parse_owlSpec_transp_keys_resp(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == parse_owlSpec_transp_keys_resp(arg.dview())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    // can't autogenerate vest parser
    todo!()
}

/* TODO work around `as_mut_slice` call */

#[verifier(external_body)]
#[verifier(external_body)]
pub exec fn serialize_owl_transp_keys_resp(arg: &owl_transp_keys_resp) -> (res: Vec<u8>)
    requires
        arg.len_valid(),
    ensures
        res.dview() == serialize_owlSpec_transp_keys_resp(arg.dview()),
{
    // can't autogenerate vest serializer
    todo!()
}

/* TODO this will be generated by parsley */

pub struct owl_resp_transp_recv_result<'a> {
    pub owl_rr_st: owl_transp_keys_resp<'a>,
    pub owl_rr_msg: OwlBuf<'a>,
}

impl DView for owl_resp_transp_recv_result<'_> {
    type V = owlSpec_resp_transp_recv_result;

    open spec fn dview(&self) -> owlSpec_resp_transp_recv_result {
        owlSpec_resp_transp_recv_result {
            owlSpec_rr_st: self.owl_rr_st.dview().as_seq(),
            owlSpec_rr_msg: self.owl_rr_msg.dview().as_seq(),
        }
    }
}

impl owl_resp_transp_recv_result<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_rr_st.len_valid() && self.owl_rr_msg.len_valid()
    }
}

#[verifier(external_body)]
pub exec fn parse_owl_resp_transp_recv_result<'a>(arg: &'a OwlBuf<'a>) -> (res: Option<
    owl_resp_transp_recv_result<'a>,
>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> parse_owlSpec_resp_transp_recv_result(arg.dview()) is Some,
        res is None ==> parse_owlSpec_resp_transp_recv_result(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == parse_owlSpec_resp_transp_recv_result(
            arg.dview(),
        )->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    // can't autogenerate vest parser
    todo!()
}

/* TODO work around `as_mut_slice` call */

#[verifier(external_body)]
#[verifier(external_body)]
pub exec fn serialize_owl_resp_transp_recv_result(arg: &owl_resp_transp_recv_result) -> (res: Vec<
    u8,
>)
    requires
        arg.len_valid(),
    ensures
        res.dview() == serialize_owlSpec_resp_transp_recv_result(arg.dview()),
{
    // can't autogenerate vest serializer
    todo!()
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

pub struct state_Initiator {
    pub owl_aead_counter_msg1_C2: usize,
    pub owl_aead_counter_msg1_C3: usize,
    pub owl_N_init_recv: usize,
    pub owl_N_init_send: usize,
}

impl state_Initiator {
    #[verifier(external_body)]
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
    pub owl_S_init: Vec<u8>,
    pub owl_E_init: Vec<u8>,
    pub pk_owl_S_resp: Vec<u8>,
    pub pk_owl_S_init: Vec<u8>,
    pub pk_owl_E_resp: Vec<u8>,
    pub pk_owl_E_init: Vec<u8>,
    pub salt: Vec<u8>,
    pub device: Option<crate::wireguard::handshake::device::DeviceInner<O>>,
}

impl<O> cfg_Initiator<O> {    
    pub exec fn owl_transp_send_init_wrapper(
        &self,         
        mut_state: &mut state_Initiator,
        owl_transp_keys_val: owl_transp_keys_init,
        owl_plaintext: &[u8],
        obuf: &mut [u8]
    ) -> () {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_init_send(Tracked(call_token), mut_state, owl_transp_keys_val, owl_plaintext, obuf).unwrap();
        res
    }


    #[verifier::spinoff_prover]
    pub fn owl_init_send(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_tki92527: owl_transp_keys_init,
        owl_msg92528: &[u8],
        obuf: &mut [u8]
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Initiator), Endpoint>>), OwlError>)
        requires
            itree.view() == init_send_spec(
                *self,
                *old(mut_state),
                owl_tki92527.dview(),
                owl_msg92528.dview(),
            ),
            owl_tki92527.len_valid(),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(init_send_spec);
            let temp_owl__x36 = { owl_tki92527 };
            let owl__x36 = temp_owl__x36;
            let owl_eph3 = ghost_unit();
            let owl_c72 = ghost_unit();
            let parseval = owl__x36;
            let owl_init5 = parseval.owl_tki_msg2_receiver;
            let owl_resp4 = parseval.owl_tki_msg2_sender;
            let owl_init_send1 = parseval.owl_tki_k_init_send;
            let owl_resp_send = parseval.owl_tki_k_resp_send;
            let temp_owl__x7 = { owl_counter_as_bytes(&(mut_state.owl_N_init_send)) };
            let owl__x7 = OwlBuf::from_vec(temp_owl__x7);
            let temp_owl__x13 = { OwlBuf::another_ref(&owl_init_send1) };
            let owl__x13 = temp_owl__x13;
            let temp_owl__x15 = { owl_msg92528 };
            let owl__x15 = OwlBuf::from_slice(&temp_owl__x15);
            let temp_owl__x17 = {
                {
                    let x: Vec<u8> = mk_vec_u8![];
                    x
                }
            };
            let owl__x17 = OwlBuf::from_vec(temp_owl__x17);
            let temp_owl__x18 = {
                match owl_enc_st_aead(
                    (OwlBuf::another_ref(&owl__x13)).as_slice(),
                    (OwlBuf::another_ref(&owl__x15)).as_slice(),
                    &mut mut_state.owl_N_init_send,
                    (OwlBuf::another_ref(&owl__x17)).as_slice(),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x18 = OwlBuf::from_vec(temp_owl__x18);
            let temp_owl__x20 = { owl_transp_tag_value() };
            let owl__x20 = OwlBuf::from_vec(temp_owl__x20);
            let temp_owl__x27 = { OwlBuf::another_ref(&owl__x20) };
            let owl__x27 = temp_owl__x27;
            let temp_owl__x29 = { OwlBuf::another_ref(&owl_init5) };
            let owl__x29 = temp_owl__x29;
            let temp_owl__x31 = { OwlBuf::another_ref(&owl__x7) };
            let owl__x31 = temp_owl__x31;
            let temp_owl__x33 = { OwlBuf::another_ref(&owl__x18) };
            let owl__x33 = temp_owl__x33;
            let temp_owl__x34 = {
                owl_transp {
                    owl__transp_tag: OwlBuf::another_ref(&owl__x27),
                    owl__transp_receiver: OwlBuf::another_ref(&owl__x29),
                    owl__transp_counter: OwlBuf::another_ref(&owl__x31),
                    owl__transp_packet: OwlBuf::another_ref(&owl__x33),
                }
            };
            let owl__x34 = temp_owl__x34;
            let temp_owl__x35 = { owl__x34 };
            let owl__x35 = temp_owl__x35;
            (
                owl_output::<((), state_Initiator)>(
                    Tracked(&mut itree),
                    vec_as_slice(&(serialize_owl_transp(&owl__x35))),
                    &Responder_addr(),
                    &Initiator_addr(),
                    obuf
                ),
                Tracked(itree),
            )
        };
        Ok(res_inner)
    }

    pub exec fn owl_transp_recv_init_wrapper<'a>(
        &self,         
        mut_state: &mut state_Initiator,
        owl_tki: owl_transp_keys_init,
        ibuf: &'a [u8],
    ) -> (Option<OwlBuf<'a>>) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_init_recv(Tracked(call_token), mut_state, owl_tki, ibuf).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_init_recv<'a> (
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_tki82859: owl_transp_keys_init,
        ibuf: &'a [u8],
    ) -> (res: Result<
        (Option<OwlBuf<'a>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == init_recv_spec(*self, *old(mut_state), owl_tki82859.dview()),
            owl_tki82859.len_valid(),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(init_recv_spec);
            let (temp_owl_i38, owl__37) = owl_input::<(Option<Seq<u8>>, state_Initiator)>(
                Tracked(&mut itree),
                ibuf,
            );
            let owl_i38 = OwlBuf::from_slice(temp_owl_i38);
            let temp_owl__x73 = { owl_tki82859 };
            let owl__x73 = temp_owl__x73;
            let owl_eph42 = ghost_unit();
            let owl_c741 = ghost_unit();
            let parseval = owl__x73;
            let owl_init44 = parseval.owl_tki_msg2_receiver;
            let owl_resp43 = parseval.owl_tki_msg2_sender;
            let owl_init_send40 = parseval.owl_tki_k_init_send;
            let owl_resp_send39 = parseval.owl_tki_k_resp_send;
            let temp_owl__x72 = { OwlBuf::another_ref(&owl_i38) };
            let owl__x72 = temp_owl__x72;
            if let Some(parseval) = parse_owl_transp(&OwlBuf::another_ref(&owl__x72)) {
                let owl_tag49 = parseval.owl__transp_tag;
                let owl_from48 = parseval.owl__transp_receiver;
                let owl_ctr47 = parseval.owl__transp_counter;
                let owl_pkt46 = parseval.owl__transp_packet;
                {
                    let temp_owl__x68 = { OwlBuf::another_ref(&owl_from48) };
                    let owl__x68 = temp_owl__x68;
                    let temp_owl__x70 = { OwlBuf::another_ref(&owl_resp43) };
                    let owl__x70 = temp_owl__x70;
                    let temp_owl__x71 = {
                        slice_eq(
                            &OwlBuf::another_ref(&owl__x68).as_slice(),
                            &OwlBuf::another_ref(&owl__x70).as_slice(),
                        )
                    };
                    let owl__x71 = temp_owl__x71;
                    if owl__x71 {
                        let temp_owl__x56 = { OwlBuf::another_ref(&owl_resp_send39) };
                        let owl__x56 = temp_owl__x56;
                        let temp_owl__x58 = { OwlBuf::another_ref(&owl_pkt46) };
                        let owl__x58 = temp_owl__x58;
                        let temp_owl__x60 = {
                            {
                                let x: Vec<u8> = mk_vec_u8![];
                                x
                            }
                        };
                        let owl__x60 = OwlBuf::from_vec(temp_owl__x60);
                        let temp_owl__x62 = { OwlBuf::another_ref(&owl_ctr47) };
                        let owl__x62 = temp_owl__x62;
                        let temp_owl__x63 = {
                            owl_dec_st_aead(
                                (OwlBuf::another_ref(&owl__x56)).as_slice(),
                                (OwlBuf::another_ref(&owl__x58)).as_slice(),
                                (OwlBuf::another_ref(&owl__x62)).as_slice(),
                                (OwlBuf::another_ref(&owl__x60)).as_slice(),
                            )
                        };
                        let owl__x63 = OwlBuf::from_vec_option(temp_owl__x63);
                        let temp_owl__x64 = { owl__x63 };
                        let owl__x64 = temp_owl__x64;
                        (owl__x64, Tracked(itree))
                    } else {
                        (None, Tracked(itree))
                    }
                }
            } else {
                let temp_owl__x45 = { None };
                let owl__x45 = temp_owl__x45;
                (owl__x45, Tracked(itree))
            }
        };
        Ok(res_inner)
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
    pub owl_S_resp: Vec<u8>,
    pub owl_E_resp: Vec<u8>,
    pub pk_owl_S_resp: Vec<u8>,
    pub pk_owl_S_init: Vec<u8>,
    pub pk_owl_E_resp: Vec<u8>,
    pub pk_owl_E_init: Vec<u8>,
    pub salt: Vec<u8>,
    pub device: Option<crate::wireguard::handshake::device::DeviceInner<O>>,
}

impl<O> cfg_Responder<O> {
    pub exec fn owl_transp_send_resp_wrapper(
        &self,         
        mut_state: &mut state_Responder,
        owl_transp_keys_val: owl_transp_keys_resp,
        owl_plaintext: &[u8],
        obuf: &mut [u8]
    ) -> Option<()> {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_resp_send(Tracked(call_token), mut_state, owl_transp_keys_val, owl_plaintext, obuf).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_resp_send(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_tki162686: owl_transp_keys_resp,
        owl_msg162687: &[u8],
        obuf: &mut [u8]
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == resp_send_spec(
                *self,
                *old(mut_state),
                owl_tki162686.dview(),
                owl_msg162687.dview(),
            ),
            owl_tki162686.len_valid(),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(resp_send_spec);
            let temp_owl__x138 = { owl_tki162686 };
            let owl__x138 = temp_owl__x138;
            let temp_owl__x137 = { owl__x138 };
            let owl__x137 = temp_owl__x137;
            let owl_eph83 = ghost_unit();
            let owl_c782 = ghost_unit();
            let parseval = owl__x137;
            let owl_init85 = parseval.owl_tkr_msg2_receiver;
            let owl_resp84 = parseval.owl_tkr_msg2_sender;
            let owl_b81 = parseval.owl_tkr_recvd;
            let owl_init_send80 = parseval.owl_tkr_k_init_send;
            let owl_resp_send79 = parseval.owl_tkr_k_resp_send;
            let temp_owl__x136 = { owl_b81 };
            let owl__x136 = temp_owl__x136;
            if owl__x136 {
                {
                    let temp_owl__x99 = { owl_counter_as_bytes(&(mut_state.owl_N_resp_send)) };
                    let owl__x99 = OwlBuf::from_vec(temp_owl__x99);
                    let temp_owl__x105 = { OwlBuf::another_ref(&owl_resp_send79) };
                    let owl__x105 = temp_owl__x105;
                    let temp_owl__x107 = { owl_msg162687 };
                    let owl__x107 = OwlBuf::from_slice(&temp_owl__x107);
                    let temp_owl__x109 = {
                        {
                            let x: Vec<u8> = mk_vec_u8![];
                            x
                        }
                    };
                    let owl__x109 = OwlBuf::from_vec(temp_owl__x109);
                    let temp_owl__x110 = {
                        match owl_enc_st_aead(
                            (OwlBuf::another_ref(&owl__x105)).as_slice(),
                            (OwlBuf::another_ref(&owl__x107)).as_slice(),
                            &mut mut_state.owl_N_resp_send,
                            (OwlBuf::another_ref(&owl__x109)).as_slice(),
                        ) {
                            Ok(ctxt) => ctxt,
                            Err(e) => { return Err(e) },
                        }
                    };
                    let owl__x110 = OwlBuf::from_vec(temp_owl__x110);
                    let temp_owl__x112 = { owl_transp_tag_value() };
                    let owl__x112 = OwlBuf::from_vec(temp_owl__x112);
                    let temp_owl__x119 = { OwlBuf::another_ref(&owl__x112) };
                    let owl__x119 = temp_owl__x119;
                    let temp_owl__x121 = { OwlBuf::another_ref(&owl_resp84) };
                    let owl__x121 = temp_owl__x121;
                    let temp_owl__x123 = { OwlBuf::another_ref(&owl__x99) };
                    let owl__x123 = temp_owl__x123;
                    let temp_owl__x125 = { OwlBuf::another_ref(&owl__x110) };
                    let owl__x125 = temp_owl__x125;
                    let temp_owl__x126 = {
                        owl_transp {
                            owl__transp_tag: OwlBuf::another_ref(&owl__x119),
                            owl__transp_receiver: OwlBuf::another_ref(&owl__x121),
                            owl__transp_counter: OwlBuf::another_ref(&owl__x123),
                            owl__transp_packet: OwlBuf::another_ref(&owl__x125),
                        }
                    };
                    let owl__x126 = temp_owl__x126;
                    let temp_owl__x130 = { owl__x126 };
                    let owl__x130 = temp_owl__x130;
                    let temp_owl__x131 = {
                        owl_output::<(Option<()>, state_Responder)>(
                            Tracked(&mut itree),
                            vec_as_slice(&(serialize_owl_transp(&owl__x130))),
                            &Initiator_addr(),
                            &Responder_addr(),
                            obuf
                        )
                    };
                    let owl__x131 = temp_owl__x131;
                    let temp_owl__x134 = { () };
                    let owl__x134 = temp_owl__x134;
                    let temp_owl__x135 = { Some(owl__x134) };
                    let owl__x135 = temp_owl__x135;
                    (owl__x135, Tracked(itree))
                }
            } else {
                (None, Tracked(itree))
            }
        };
        Ok(res_inner)
    }

    pub exec fn owl_transp_recv_resp_wrapper<'a>(
        &self,         
        mut_state: &mut state_Responder,
        owl_transp_keys_val: owl_transp_keys_resp<'a>,
        ibuf: &'a [u8],
    ) -> Option<OwlBuf<'a>> {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_recv_resp_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_resp_recv(Tracked(call_token), mut_state, owl_transp_keys_val, ibuf).unwrap();
        res.map(move |resp_result| resp_result.owl_rr_msg)
    }    

    #[verifier::spinoff_prover]
    pub fn owl_resp_recv<'a>(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_tki116116: owl_transp_keys_resp<'a>,
        ibuf: &'a [u8]
    ) -> (res: Result<
        (
            Option<owl_resp_transp_recv_result<'a>>,
            Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == resp_recv_spec(*self, *old(mut_state), owl_tki116116.dview()),
            owl_tki116116.len_valid(),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (option_as_seq(dview_option(res.get_Ok_0().0)), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(resp_recv_spec);
            let (temp_owl_i145, owl__144) = owl_input::<(Option<Seq<u8>>, state_Responder)>(
                Tracked(&mut itree),
                ibuf,
            );
            let owl_i145 = OwlBuf::from_slice(temp_owl_i145);
            let temp_owl__x237 = { owl_tki116116 };
            let owl__x237 = temp_owl__x237;
            let temp_owl__x236 = { owl__x237 };
            let owl__x236 = temp_owl__x236;
            let owl_eph152 = ghost_unit();
            let owl_c7151 = ghost_unit();
            let parseval = owl__x236;
            let owl_init154 = parseval.owl_tkr_msg2_receiver;
            let owl_resp153 = parseval.owl_tkr_msg2_sender;
            let owl__150 = parseval.owl_tkr_recvd;
            let owl_init_send149 = parseval.owl_tkr_k_init_send;
            let owl_resp_send148 = parseval.owl_tkr_k_resp_send;
            let temp_owl__x235 = { OwlBuf::another_ref(&owl_i145) };
            let owl__x235 = temp_owl__x235;
            if let Some(parseval) = parse_owl_transp(&OwlBuf::another_ref(&owl__x235)) {
                let owl_tag159 = parseval.owl__transp_tag;
                let owl_from158 = parseval.owl__transp_receiver;
                let owl_ctr157 = parseval.owl__transp_counter;
                let owl_pkt156 = parseval.owl__transp_packet;
                {
                    let temp_owl__x231 = { OwlBuf::another_ref(&owl_from158) };
                    let owl__x231 = temp_owl__x231;
                    let temp_owl__x233 = { OwlBuf::another_ref(&owl_init154) };
                    let owl__x233 = temp_owl__x233;
                    let temp_owl__x234 = {
                        slice_eq(
                            &OwlBuf::another_ref(&owl__x231).as_slice(),
                            &OwlBuf::another_ref(&owl__x233).as_slice(),
                        )
                    };
                    let owl__x234 = temp_owl__x234;
                    if owl__x234 {
                        let temp_owl__x220 = { OwlBuf::another_ref(&owl_init_send149) };
                        let owl__x220 = temp_owl__x220;
                        let temp_owl__x222 = { OwlBuf::another_ref(&owl_pkt156) };
                        let owl__x222 = temp_owl__x222;
                        let temp_owl__x224 = {
                            {
                                let x: Vec<u8> = mk_vec_u8![];
                                x
                            }
                        };
                        let owl__x224 = OwlBuf::from_vec(temp_owl__x224);
                        let temp_owl__x226 = { OwlBuf::another_ref(&owl_ctr157) };
                        let owl__x226 = temp_owl__x226;
                        let temp_owl__x227 = {
                            owl_dec_st_aead(
                                (OwlBuf::another_ref(&owl__x220)).as_slice(),
                                (OwlBuf::another_ref(&owl__x222)).as_slice(),
                                (OwlBuf::another_ref(&owl__x226)).as_slice(),
                                (OwlBuf::another_ref(&owl__x224)).as_slice(),
                            )
                        };
                        let owl__x227 = OwlBuf::from_vec_option(temp_owl__x227);
                        let temp_owl_caseval240 = { owl__x227 };
                        let owl_caseval240 = temp_owl_caseval240;
                        match owl_caseval240 {
                            Some(temp_owl_x164) => {
                                let owl_x164 = temp_owl_x164;
                                let temp_owl__x189 = { OwlBuf::another_ref(&owl_init154) };
                                let owl__x189 = temp_owl__x189;
                                let temp_owl__x191 = { OwlBuf::another_ref(&owl_resp153) };
                                let owl__x191 = temp_owl__x191;
                                let temp_owl__x193 = { owl_eph152 };
                                let owl__x193 = temp_owl__x193;
                                let temp_owl__x195 = { owl_c7151 };
                                let owl__x195 = temp_owl__x195;
                                let temp_owl__x197 = { true };
                                let owl__x197 = temp_owl__x197;
                                let temp_owl__x199 = { OwlBuf::another_ref(&owl_init_send149) };
                                let owl__x199 = temp_owl__x199;
                                let temp_owl__x201 = { OwlBuf::another_ref(&owl_resp_send148) };
                                let owl__x201 = temp_owl__x201;
                                let temp_owl__x203 = {
                                    owl_transp_keys_resp {
                                        owl_tkr_msg2_receiver: OwlBuf::another_ref(&owl__x189),
                                        owl_tkr_msg2_sender: OwlBuf::another_ref(&owl__x191),
                                        owl_tkr_recvd: owl__x197,
                                        owl_tkr_k_init_send: OwlBuf::another_ref(&owl__x199),
                                        owl_tkr_k_resp_send: OwlBuf::another_ref(&owl__x201),
                                    }
                                };
                                let owl__x203 = temp_owl__x203;
                                let temp_owl__x204 = { owl__x203 };
                                let owl__x204 = temp_owl__x204;
                                let temp_owl__x212 = { owl__x204 };
                                let owl__x212 = temp_owl__x212;
                                let temp_owl__x214 = { OwlBuf::another_ref(&owl_x164) };
                                let owl__x214 = temp_owl__x214;
                                let temp_owl__x215 = {
                                    owl_resp_transp_recv_result {
                                        owl_rr_st: owl__x212,
                                        owl_rr_msg: OwlBuf::another_ref(&owl__x214),
                                    }
                                };
                                let owl__x215 = temp_owl__x215;
                                let temp_owl__x216 = { owl__x215 };
                                let owl__x216 = temp_owl__x216;
                                let temp_owl__x217 = { Some(owl__x216) };
                                let owl__x217 = temp_owl__x217;
                                (owl__x217, Tracked(itree))
                            },
                            None => {
                                let temp_owl__x218 = { None };
                                let owl__x218 = temp_owl__x218;
                                (owl__x218, Tracked(itree))
                            },
                        }
                    } else {
                        (None, Tracked(itree))
                    }
                }
            } else {
                let temp_owl__x155 = { None };
                let owl__x155 = temp_owl__x155;
                (owl__x155, Tracked(itree))
            }
        };
        Ok(res_inner)
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

pub exec fn owl_transp_tag_value() -> (res: Vec<u8>)
    ensures
        res.dview() == transp_tag_value(),
{
    reveal(transp_tag_value);
    {
        let x: Vec<u8> = mk_vec_u8![0x04u8, 0x00u8, 0x00u8, 0x00u8, ];
        x
    }
}

// ------------------------------------
// ------------ ENTRY POINT -----------
// ------------------------------------
// no entry point

} // verus!
