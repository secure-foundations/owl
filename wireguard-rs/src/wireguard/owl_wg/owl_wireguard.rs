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

pub struct owl_msg1<'a> {
    pub owl__msg1_tag: OwlBuf<'a>,
    pub owl__msg1_sender: OwlBuf<'a>,
    pub owl__msg1_ephemeral: OwlBuf<'a>,
    pub owl__msg1_static: OwlBuf<'a>,
    pub owl__msg1_timestamp: OwlBuf<'a>,
    pub owl__msg1_mac1: OwlBuf<'a>,
    pub owl__msg1_mac2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg1<'a>(
    arg_owl__msg1_tag: OwlBuf<'a>,
    arg_owl__msg1_sender: OwlBuf<'a>,
    arg_owl__msg1_ephemeral: OwlBuf<'a>,
    arg_owl__msg1_static: OwlBuf<'a>,
    arg_owl__msg1_timestamp: OwlBuf<'a>,
    arg_owl__msg1_mac1: OwlBuf<'a>,
    arg_owl__msg1_mac2: OwlBuf<'a>,
) -> (res: owl_msg1<'a>)
    requires
        arg_owl__msg1_tag.len_valid(),
        arg_owl__msg1_sender.len_valid(),
        arg_owl__msg1_ephemeral.len_valid(),
        arg_owl__msg1_static.len_valid(),
        arg_owl__msg1_timestamp.len_valid(),
        arg_owl__msg1_mac1.len_valid(),
        arg_owl__msg1_mac2.len_valid(),
    ensures
        res.len_valid(),
        res.owl__msg1_tag.dview() == arg_owl__msg1_tag.dview(),
        res.owl__msg1_sender.dview() == arg_owl__msg1_sender.dview(),
        res.owl__msg1_ephemeral.dview() == arg_owl__msg1_ephemeral.dview(),
        res.owl__msg1_static.dview() == arg_owl__msg1_static.dview(),
        res.owl__msg1_timestamp.dview() == arg_owl__msg1_timestamp.dview(),
        res.owl__msg1_mac1.dview() == arg_owl__msg1_mac1.dview(),
        res.owl__msg1_mac2.dview() == arg_owl__msg1_mac2.dview(),
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
        self.owl__msg1_tag.len_valid() && self.owl__msg1_sender.len_valid()
            && self.owl__msg1_ephemeral.len_valid() && self.owl__msg1_static.len_valid()
            && self.owl__msg1_timestamp.len_valid() && self.owl__msg1_mac1.len_valid()
            && self.owl__msg1_mac2.len_valid()
    }
}

impl DView for owl_msg1<'_> {
    type V = owlSpec_msg1;

    open spec fn dview(&self) -> owlSpec_msg1 {
        owlSpec_msg1 {
            owlSpec__msg1_tag: self.owl__msg1_tag.dview(),
            owlSpec__msg1_sender: self.owl__msg1_sender.dview(),
            owlSpec__msg1_ephemeral: self.owl__msg1_ephemeral.dview(),
            owlSpec__msg1_static: self.owl__msg1_static.dview(),
            owlSpec__msg1_timestamp: self.owl__msg1_timestamp.dview(),
            owlSpec__msg1_mac1: self.owl__msg1_mac1.dview(),
            owlSpec__msg1_mac2: self.owl__msg1_mac2.dview(),
        }
    }
}

pub exec fn parse_owl_msg1<'a>(arg: &'a [u8]) -> (res: Option<
    owl_msg1<'a>,
>)
// requires arg.len_valid()

    ensures
        res is Some ==> parse_owlSpec_msg1(arg.dview()) is Some,
        res is None ==> parse_owlSpec_msg1(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == parse_owlSpec_msg1(arg.dview())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_msg1);
    let stream = parse_serialize::Stream { data: arg, start: 0 };
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
                owl__msg1_tag: OwlBuf::from_slice(&owl__msg1_tag),
                owl__msg1_sender: OwlBuf::from_slice(&owl__msg1_sender),
                owl__msg1_ephemeral: OwlBuf::from_slice(&owl__msg1_ephemeral),
                owl__msg1_static: OwlBuf::from_slice(&owl__msg1_static),
                owl__msg1_timestamp: OwlBuf::from_slice(&owl__msg1_timestamp),
                owl__msg1_mac1: OwlBuf::from_slice(&owl__msg1_mac1),
                owl__msg1_mac2: OwlBuf::from_slice(&owl__msg1_mac2),
            },
        )
    } else {
        None
    }
}

#[verifier(external_body)]  // to allow `as_mut_slice` call, TODO fix
pub exec fn serialize_owl_msg1_inner(arg: &owl_msg1) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> serialize_owlSpec_msg1_inner(arg.dview()) is Some,
        res is None ==> serialize_owlSpec_msg1_inner(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == serialize_owlSpec_msg1_inner(arg.dview())->Some_0,
{
    reveal(serialize_owlSpec_msg1_inner);
    if no_usize_overflows![ arg.owl__msg1_tag.len(), arg.owl__msg1_sender.len(), arg.owl__msg1_ephemeral.len(), arg.owl__msg1_static.len(), arg.owl__msg1_timestamp.len(), arg.owl__msg1_mac1.len(), arg.owl__msg1_mac2.len(), 0 ] {
        let mut obuf = vec_u8_of_len(
            arg.owl__msg1_tag.len() + arg.owl__msg1_sender.len() + arg.owl__msg1_ephemeral.len()
                + arg.owl__msg1_static.len() + arg.owl__msg1_timestamp.len()
                + arg.owl__msg1_mac1.len() + arg.owl__msg1_mac2.len() + 0,
        );
        let ser_result = parse_serialize::serialize_owl_msg1(
            obuf.as_mut_slice(),
            0,
            ((
                (
                    (
                        (
                            (
                                (arg.owl__msg1_tag.as_slice(), arg.owl__msg1_sender.as_slice()),
                                arg.owl__msg1_ephemeral.as_slice(),
                            ),
                            arg.owl__msg1_static.as_slice(),
                        ),
                        arg.owl__msg1_timestamp.as_slice(),
                    ),
                    arg.owl__msg1_mac1.as_slice(),
                ),
                arg.owl__msg1_mac2.as_slice(),
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

pub struct owl_msg2<'a> {
    pub owl__msg2_tag: OwlBuf<'a>,
    pub owl__msg2_sender: OwlBuf<'a>,
    pub owl__msg2_receiver: OwlBuf<'a>,
    pub owl__msg2_ephemeral: OwlBuf<'a>,
    pub owl__msg2_empty: OwlBuf<'a>,
    pub owl__msg2_mac1: OwlBuf<'a>,
    pub owl__msg2_mac2: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_msg2<'a>(
    arg_owl__msg2_tag: OwlBuf<'a>,
    arg_owl__msg2_sender: OwlBuf<'a>,
    arg_owl__msg2_receiver: OwlBuf<'a>,
    arg_owl__msg2_ephemeral: OwlBuf<'a>,
    arg_owl__msg2_empty: OwlBuf<'a>,
    arg_owl__msg2_mac1: OwlBuf<'a>,
    arg_owl__msg2_mac2: OwlBuf<'a>,
) -> (res: owl_msg2<'a>)
    requires
        arg_owl__msg2_tag.len_valid(),
        arg_owl__msg2_sender.len_valid(),
        arg_owl__msg2_receiver.len_valid(),
        arg_owl__msg2_ephemeral.len_valid(),
        arg_owl__msg2_empty.len_valid(),
        arg_owl__msg2_mac1.len_valid(),
        arg_owl__msg2_mac2.len_valid(),
    ensures
        res.len_valid(),
        res.owl__msg2_tag.dview() == arg_owl__msg2_tag.dview(),
        res.owl__msg2_sender.dview() == arg_owl__msg2_sender.dview(),
        res.owl__msg2_receiver.dview() == arg_owl__msg2_receiver.dview(),
        res.owl__msg2_ephemeral.dview() == arg_owl__msg2_ephemeral.dview(),
        res.owl__msg2_empty.dview() == arg_owl__msg2_empty.dview(),
        res.owl__msg2_mac1.dview() == arg_owl__msg2_mac1.dview(),
        res.owl__msg2_mac2.dview() == arg_owl__msg2_mac2.dview(),
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
        self.owl__msg2_tag.len_valid() && self.owl__msg2_sender.len_valid()
            && self.owl__msg2_receiver.len_valid() && self.owl__msg2_ephemeral.len_valid()
            && self.owl__msg2_empty.len_valid() && self.owl__msg2_mac1.len_valid()
            && self.owl__msg2_mac2.len_valid()
    }
}

impl DView for owl_msg2<'_> {
    type V = owlSpec_msg2;

    open spec fn dview(&self) -> owlSpec_msg2 {
        owlSpec_msg2 {
            owlSpec__msg2_tag: self.owl__msg2_tag.dview(),
            owlSpec__msg2_sender: self.owl__msg2_sender.dview(),
            owlSpec__msg2_receiver: self.owl__msg2_receiver.dview(),
            owlSpec__msg2_ephemeral: self.owl__msg2_ephemeral.dview(),
            owlSpec__msg2_empty: self.owl__msg2_empty.dview(),
            owlSpec__msg2_mac1: self.owl__msg2_mac1.dview(),
            owlSpec__msg2_mac2: self.owl__msg2_mac2.dview(),
        }
    }
}

pub exec fn parse_owl_msg2<'a>(arg: &'a [u8]) -> (res: Option<
    owl_msg2<'a>,
>)
// requires arg.len_valid()

    ensures
        res is Some ==> parse_owlSpec_msg2(arg.dview()) is Some,
        res is None ==> parse_owlSpec_msg2(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == parse_owlSpec_msg2(arg.dview())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_msg2);
    let stream = parse_serialize::Stream { data: arg, start: 0 };
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
                owl__msg2_tag: OwlBuf::from_slice(&owl__msg2_tag),
                owl__msg2_sender: OwlBuf::from_slice(&owl__msg2_sender),
                owl__msg2_receiver: OwlBuf::from_slice(&owl__msg2_receiver),
                owl__msg2_ephemeral: OwlBuf::from_slice(&owl__msg2_ephemeral),
                owl__msg2_empty: OwlBuf::from_slice(&owl__msg2_empty),
                owl__msg2_mac1: OwlBuf::from_slice(&owl__msg2_mac1),
                owl__msg2_mac2: OwlBuf::from_slice(&owl__msg2_mac2),
            },
        )
    } else {
        None
    }
}

#[verifier(external_body)]  // to allow `as_mut_slice` call, TODO fix
pub exec fn serialize_owl_msg2_inner(arg: &owl_msg2) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> serialize_owlSpec_msg2_inner(arg.dview()) is Some,
        res is None ==> serialize_owlSpec_msg2_inner(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == serialize_owlSpec_msg2_inner(arg.dview())->Some_0,
{
    reveal(serialize_owlSpec_msg2_inner);
    if no_usize_overflows![ arg.owl__msg2_tag.len(), arg.owl__msg2_sender.len(), arg.owl__msg2_receiver.len(), arg.owl__msg2_ephemeral.len(), arg.owl__msg2_empty.len(), arg.owl__msg2_mac1.len(), arg.owl__msg2_mac2.len(), 0 ] {
        let mut obuf = vec_u8_of_len(
            arg.owl__msg2_tag.len() + arg.owl__msg2_sender.len() + arg.owl__msg2_receiver.len()
                + arg.owl__msg2_ephemeral.len() + arg.owl__msg2_empty.len()
                + arg.owl__msg2_mac1.len() + arg.owl__msg2_mac2.len() + 0,
        );
        let ser_result = parse_serialize::serialize_owl_msg2(
            obuf.as_mut_slice(),
            0,
            ((
                (
                    (
                        (
                            (
                                (arg.owl__msg2_tag.as_slice(), arg.owl__msg2_sender.as_slice()),
                                arg.owl__msg2_receiver.as_slice(),
                            ),
                            arg.owl__msg2_ephemeral.as_slice(),
                        ),
                        arg.owl__msg2_empty.as_slice(),
                    ),
                    arg.owl__msg2_mac1.as_slice(),
                ),
                arg.owl__msg2_mac2.as_slice(),
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

pub struct owl_transp<'a> {
    pub owl__transp_tag: OwlBuf<'a>,
    pub owl__transp_receiver: OwlBuf<'a>,
    pub owl__transp_counter: OwlBuf<'a>,
    pub owl__transp_packet: OwlBuf<'a>,
}

// Allows us to use function call syntax to construct members of struct types, a la Owl,
// so we don't have to special-case struct constructors in the compiler
#[inline]
pub fn owl_transp<'a>(
    arg_owl__transp_tag: OwlBuf<'a>,
    arg_owl__transp_receiver: OwlBuf<'a>,
    arg_owl__transp_counter: OwlBuf<'a>,
    arg_owl__transp_packet: OwlBuf<'a>,
) -> (res: owl_transp<'a>)
    requires
        arg_owl__transp_tag.len_valid(),
        arg_owl__transp_receiver.len_valid(),
        arg_owl__transp_counter.len_valid(),
        arg_owl__transp_packet.len_valid(),
    ensures
        res.len_valid(),
        res.owl__transp_tag.dview() == arg_owl__transp_tag.dview(),
        res.owl__transp_receiver.dview() == arg_owl__transp_receiver.dview(),
        res.owl__transp_counter.dview() == arg_owl__transp_counter.dview(),
        res.owl__transp_packet.dview() == arg_owl__transp_packet.dview(),
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
        self.owl__transp_tag.len_valid() && self.owl__transp_receiver.len_valid()
            && self.owl__transp_counter.len_valid() && self.owl__transp_packet.len_valid()
    }
}

impl DView for owl_transp<'_> {
    type V = owlSpec_transp;

    open spec fn dview(&self) -> owlSpec_transp {
        owlSpec_transp {
            owlSpec__transp_tag: self.owl__transp_tag.dview(),
            owlSpec__transp_receiver: self.owl__transp_receiver.dview(),
            owlSpec__transp_counter: self.owl__transp_counter.dview(),
            owlSpec__transp_packet: self.owl__transp_packet.dview(),
        }
    }
}

pub exec fn parse_owl_transp<'a>(arg: &'a [u8]) -> (res: Option<
    owl_transp<'a>,
>)
// requires arg.len_valid()

    ensures
        res is Some ==> parse_owlSpec_transp(arg.dview()) is Some,
        res is None ==> parse_owlSpec_transp(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == parse_owlSpec_transp(arg.dview())->Some_0,
        res matches Some(x) ==> x.len_valid(),
{
    reveal(parse_owlSpec_transp);
    let stream = parse_serialize::Stream { data: arg, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::parse_owl_transp(stream) {
        let (((owl__transp_tag, owl__transp_receiver), owl__transp_counter), owl__transp_packet) =
            parsed;
        Some(
            owl_transp {
                owl__transp_tag: OwlBuf::from_slice(&owl__transp_tag),
                owl__transp_receiver: OwlBuf::from_slice(&owl__transp_receiver),
                owl__transp_counter: OwlBuf::from_slice(&owl__transp_counter),
                owl__transp_packet: OwlBuf::from_slice(&owl__transp_packet),
            },
        )
    } else {
        None
    }
}

#[verifier(external_body)]  // to allow `as_mut_slice` call, TODO fix
pub exec fn serialize_owl_transp_inner(arg: &owl_transp) -> (res: Option<Vec<u8>>)
    requires
        arg.len_valid(),
    ensures
        res is Some ==> serialize_owlSpec_transp_inner(arg.dview()) is Some,
        res is None ==> serialize_owlSpec_transp_inner(arg.dview()) is None,
        res matches Some(x) ==> x.dview() == serialize_owlSpec_transp_inner(arg.dview())->Some_0,
{
    reveal(serialize_owlSpec_transp_inner);
    if no_usize_overflows![ arg.owl__transp_tag.len(), arg.owl__transp_receiver.len(), arg.owl__transp_counter.len(), arg.owl__transp_packet.len(), 0 ] {
        let mut obuf = vec_u8_of_len(
            arg.owl__transp_tag.len() + arg.owl__transp_receiver.len()
                + arg.owl__transp_counter.len() + arg.owl__transp_packet.len() + 0,
        );
        let ser_result = parse_serialize::serialize_owl_transp(
            obuf.as_mut_slice(),
            0,
            ((
                (
                    (arg.owl__transp_tag.as_slice(), arg.owl__transp_receiver.as_slice()),
                    arg.owl__transp_counter.as_slice(),
                ),
                arg.owl__transp_packet.as_slice(),
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

pub struct owl_transp_keys_init<'a> {
    pub owl_tki_msg2_receiver: OwlBuf<'a>,
    pub owl_tki_msg2_sender: OwlBuf<'a>,
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
        res.owl_tki_msg2_receiver.dview() == arg_owl_tki_msg2_receiver.dview(),
        res.owl_tki_msg2_sender.dview() == arg_owl_tki_msg2_sender.dview(),
        res.owl_tki_eph.dview() == arg_owl_tki_eph.dview(),
        res.owl_tki_c7.dview() == arg_owl_tki_c7.dview(),
        res.owl_tki_k_init_send.dview() == arg_owl_tki_k_init_send.dview(),
        res.owl_tki_k_resp_send.dview() == arg_owl_tki_k_resp_send.dview(),
{
    owl_transp_keys_init {
        owl_tki_msg2_receiver: arg_owl_tki_msg2_receiver,
        owl_tki_msg2_sender: arg_owl_tki_msg2_sender,
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

impl DView for owl_transp_keys_init<'_> {
    type V = owlSpec_transp_keys_init;

    open spec fn dview(&self) -> owlSpec_transp_keys_init {
        owlSpec_transp_keys_init {
            owlSpec_tki_msg2_receiver: self.owl_tki_msg2_receiver.dview(),
            owlSpec_tki_msg2_sender: self.owl_tki_msg2_sender.dview(),
            owlSpec_tki_eph: self.owl_tki_eph.dview(),
            owlSpec_tki_c7: self.owl_tki_c7.dview(),
            owlSpec_tki_k_init_send: self.owl_tki_k_init_send.dview(),
            owlSpec_tki_k_resp_send: self.owl_tki_k_resp_send.dview(),
        }
    }
}

pub struct owl_transp_keys_resp<'a> {
    pub owl_tkr_msg2_receiver: OwlBuf<'a>,
    pub owl_tkr_msg2_sender: OwlBuf<'a>,
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
        res.owl_tkr_msg2_receiver.dview() == arg_owl_tkr_msg2_receiver.dview(),
        res.owl_tkr_msg2_sender.dview() == arg_owl_tkr_msg2_sender.dview(),
        res.owl_tkr_eph.dview() == arg_owl_tkr_eph.dview(),
        res.owl_tkr_c7.dview() == arg_owl_tkr_c7.dview(),
        res.owl_tkr_recvd.dview() == arg_owl_tkr_recvd.dview(),
        res.owl_tkr_k_init_send.dview() == arg_owl_tkr_k_init_send.dview(),
        res.owl_tkr_k_resp_send.dview() == arg_owl_tkr_k_resp_send.dview(),
{
    owl_transp_keys_resp {
        owl_tkr_msg2_receiver: arg_owl_tkr_msg2_receiver,
        owl_tkr_msg2_sender: arg_owl_tkr_msg2_sender,
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

impl DView for owl_transp_keys_resp<'_> {
    type V = owlSpec_transp_keys_resp;

    open spec fn dview(&self) -> owlSpec_transp_keys_resp {
        owlSpec_transp_keys_resp {
            owlSpec_tkr_msg2_receiver: self.owl_tkr_msg2_receiver.dview(),
            owlSpec_tkr_msg2_sender: self.owl_tkr_msg2_sender.dview(),
            owlSpec_tkr_eph: self.owl_tkr_eph.dview(),
            owlSpec_tkr_c7: self.owl_tkr_c7.dview(),
            owlSpec_tkr_recvd: self.owl_tkr_recvd.dview(),
            owlSpec_tkr_k_init_send: self.owl_tkr_k_init_send.dview(),
            owlSpec_tkr_k_resp_send: self.owl_tkr_k_resp_send.dview(),
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
        arg_owl_rr_msg.len_valid(),
    ensures
        res.len_valid(),
        res.owl_rr_st.dview() == arg_owl_rr_st.dview(),
        res.owl_rr_msg.dview() == arg_owl_rr_msg.dview(),
{
    owl_resp_transp_recv_result { owl_rr_st: arg_owl_rr_st, owl_rr_msg: arg_owl_rr_msg }
}

impl owl_resp_transp_recv_result<'_> {
    pub open spec fn len_valid(&self) -> bool {
        self.owl_rr_msg.len_valid()
    }
}

impl DView for owl_resp_transp_recv_result<'_> {
    type V = owlSpec_resp_transp_recv_result;

    open spec fn dview(&self) -> owlSpec_resp_transp_recv_result {
        owlSpec_resp_transp_recv_result {
            owlSpec_rr_st: self.owl_rr_st.dview(),
            owlSpec_rr_msg: self.owl_rr_msg.dview(),
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
        obuf: &'a mut [u8],
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
        owl_tki373: owl_transp_keys_init<'a>,
        owl_msg374: OwlBuf<'a>,
        obuf: &mut [u8],
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Initiator), Endpoint>>), OwlError>)
        requires
            itree.view() == init_send_spec(
                *self,
                *old(mut_state),
                owl_tki373.dview(),
                owl_msg374.dview(),
            ),
            owl_tki373.len_valid(),
            owl_msg374.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let tracked mut itree = itree;
        let res_inner = {
            // broadcast use itree_axioms;

            reveal(init_send_spec);
            let parseval = owl_tki373;
            let owl_init317 = OwlBuf::another_ref(&parseval.owl_tki_msg2_receiver);
            let owl_resp316 = OwlBuf::another_ref(&parseval.owl_tki_msg2_sender);
            let owl_eph315 = parseval.owl_tki_eph;
            let owl_c7314 = parseval.owl_tki_c7;
            let owl_init_send313 = OwlBuf::another_ref(&parseval.owl_tki_k_init_send);
            let owl_resp_send312 = OwlBuf::another_ref(&parseval.owl_tki_k_resp_send);
            let tmp_owl_transp_counter318 = { owl_counter_as_bytes(&mut_state.owl_N_init_send) };
            let owl_transp_counter318 = OwlBuf::from_slice(&tmp_owl_transp_counter318);
            let owl_c319 = {
                {
                    match owl_enc_st_aead(
                        owl_init_send313.as_slice(),
                        owl_msg374.as_slice(),
                        &mut mut_state.owl_N_init_send,
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
            let owl_transp_tag320 = { owl_transp_tag_value() };
            let owl_o321 = {
                owl_transp(owl_transp_tag320, owl_init317, owl_transp_counter318, owl_c319)
            };
            owl_output::<((), state_Initiator)>(
                Tracked(&mut itree),
                &serialize_owl_transp(&owl_o321).as_slice(),
                &Responder_addr(),
                &Initiator_addr(),
                obuf
            );
            ((), Tracked(itree))
        };
        Ok(res_inner)
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
        owl_tki375: owl_transp_keys_init<'a>,
        ibuf: &'a [u8],
    ) -> (res: Result<
        (Option<OwlBuf<'a>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == init_recv_spec(*self, *old(mut_state), owl_tki375.dview()),
            owl_tki375.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((dview_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let res_inner = {
            // broadcast use itree_axioms;

            reveal(init_recv_spec);
            let (tmp_owl_i324, owl__323) = {
                owl_input::<(Option<Seq<u8>>, state_Initiator)>(Tracked(&mut itree), ibuf)
            };
            let owl_i324 = OwlBuf::from_slice(tmp_owl_i324);
            let parseval = owl_tki375;
            let owl_init330 = OwlBuf::another_ref(&parseval.owl_tki_msg2_receiver);
            let owl_resp329 = OwlBuf::another_ref(&parseval.owl_tki_msg2_sender);
            let owl_eph328 = parseval.owl_tki_eph;
            let owl_c7327 = parseval.owl_tki_c7;
            let owl_init_send326 = OwlBuf::another_ref(&parseval.owl_tki_k_init_send);
            let owl_resp_send325 = OwlBuf::another_ref(&parseval.owl_tki_k_resp_send);
            let parseval_tmp = OwlBuf::another_ref(&owl_i324);
            if let Some(parseval) = parse_owl_transp(parseval_tmp.as_slice()) {
                let owl_tag334 = OwlBuf::another_ref(&parseval.owl__transp_tag);
                let owl_from333 = OwlBuf::another_ref(&parseval.owl__transp_receiver);
                let owl_ctr332 = OwlBuf::another_ref(&parseval.owl__transp_counter);
                let owl_pkt331 = OwlBuf::another_ref(&parseval.owl__transp_packet);
                {
                    if { slice_eq(owl_from333.as_slice(), owl_resp329.as_slice()) } {
                        let tmp_owl_p335 = {
                            owl_dec_st_aead(
                                owl_resp_send325.as_slice(),
                                owl_pkt331.as_slice(),
                                owl_ctr332.as_slice(),
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }.as_slice(),
                            )
                        };
                        let owl_p335 = OwlBuf::from_vec_option(tmp_owl_p335);
                        (owl_p335, Tracked(itree))
                    } else {
                        (None, Tracked(itree))
                    }
                }
            } else {
                (None, Tracked(itree))
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
        owl_tki376: owl_transp_keys_resp<'a>,
        owl_msg377: OwlBuf<'a>,
        obuf: &mut [u8],
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == resp_send_spec(
                *self,
                *old(mut_state),
                owl_tki376.dview(),
                owl_msg377.dview(),
            ),
            owl_tki376.len_valid(),
            owl_msg377.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((dview_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let res_inner = {
            // broadcast use itree_axioms;

            reveal(resp_send_spec);
            let owl_tki_338 = { owl_tki376 };
            let parseval = owl_tki_338;
            let owl_init345 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_receiver);
            let owl_resp344 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_sender);
            let owl_eph343 = parseval.owl_tkr_eph;
            let owl_c7342 = parseval.owl_tkr_c7;
            let owl_b341 = parseval.owl_tkr_recvd;
            let owl_init_send340 = OwlBuf::another_ref(&parseval.owl_tkr_k_init_send);
            let owl_resp_send339 = OwlBuf::another_ref(&parseval.owl_tkr_k_resp_send);
            if owl_b341 {
                {
                    let owl__346 = {
                        let owl__347 = {
                            let owl__assert_91348 = { owl_unit() };
                            owl_unit()
                        };
                        owl_unit()
                    };
                    let tmp_owl_transp_counter349 = {
                        owl_counter_as_bytes(&mut_state.owl_N_resp_send)
                    };
                    let owl_transp_counter349 = OwlBuf::from_slice(&tmp_owl_transp_counter349);
                    let owl_c350 = {
                        {
                            match owl_enc_st_aead(
                                owl_resp_send339.as_slice(),
                                owl_msg377.as_slice(),
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
                    let owl_transp_tag351 = { owl_transp_tag_value() };
                    let owl_o352 = {
                        owl_transp(owl_transp_tag351, owl_resp344, owl_transp_counter349, owl_c350)
                    };
                    let owl__353 = {
                        owl_output::<(Option<()>, state_Responder)>(
                            Tracked(&mut itree),
                            &serialize_owl_transp(&owl_o352).as_slice(),
                            &Initiator_addr(),
                            &Responder_addr(),
                            obuf,
                        );
                    };
                    (Some(owl_unit()), Tracked(itree))
                }
            } else {
                (None, Tracked(itree))
            }
        };
        Ok(res_inner)
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
        owl_tki378: owl_transp_keys_resp<'a>,
        ibuf: &'a [u8],
    ) -> (res: Result<
        (
            Option<owl_resp_transp_recv_result>,
            Tracked<
                ITreeToken<(Option<owlSpec_resp_transp_recv_result>, state_Responder), Endpoint>,
            >,
        ),
        OwlError,
    >)
        requires
            itree.view() == resp_recv_spec(*self, *old(mut_state), owl_tki378.dview()),
            owl_tki378.len_valid(),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in((dview_option((r.0)), *mut_state)),
    {
        let tracked mut itree = itree;
        let res_inner = {
            // broadcast use itree_axioms;

            reveal(resp_recv_spec);
            let (tmp_owl_i356, owl__355) = {
                owl_input::<(Option<owlSpec_resp_transp_recv_result>, state_Responder)>(
                    Tracked(&mut itree),
                    ibuf,
                )
            };
            let owl_i356 = OwlBuf::from_slice(tmp_owl_i356);
            let owl_tki_357 = { owl_tki378 };
            let parseval = owl_tki_357;
            let owl_init364 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_receiver);
            let owl_resp363 = OwlBuf::another_ref(&parseval.owl_tkr_msg2_sender);
            let owl_eph362 = parseval.owl_tkr_eph;
            let owl_c7361 = parseval.owl_tkr_c7;
            let owl__360 = parseval.owl_tkr_recvd;
            let owl_init_send359 = OwlBuf::another_ref(&parseval.owl_tkr_k_init_send);
            let owl_resp_send358 = OwlBuf::another_ref(&parseval.owl_tkr_k_resp_send);
            let parseval_tmp = OwlBuf::another_ref(&owl_i356);
            if let Some(parseval) = parse_owl_transp(parseval_tmp.as_slice()) {
                let owl_tag368 = OwlBuf::another_ref(&parseval.owl__transp_tag);
                let owl_from367 = OwlBuf::another_ref(&parseval.owl__transp_receiver);
                let owl_ctr366 = OwlBuf::another_ref(&parseval.owl__transp_counter);
                let owl_pkt365 = OwlBuf::another_ref(&parseval.owl__transp_packet);
                {
                    if { slice_eq(owl_from367.as_slice(), owl_init364.as_slice()) } {
                        let tmp_owl_caseval369 = {
                            owl_dec_st_aead(
                                owl_init_send359.as_slice(),
                                owl_pkt365.as_slice(),
                                owl_ctr366.as_slice(),
                                {
                                    let x = mk_vec_u8![];
                                    OwlBuf::from_vec(x)
                                }.as_slice(),
                            )
                        };
                        let owl_caseval369 = OwlBuf::from_vec_option(tmp_owl_caseval369);
                        match owl_caseval369 {
                            Option::Some(tmp_owl_x370) => {
                                let owl_x370 = OwlBuf::another_ref(&tmp_owl_x370);
                                let owl_st_371 = {
                                    owl_transp_keys_resp(
                                        owl_init364,
                                        owl_resp363,
                                        owl_eph362,
                                        owl_c7361,
                                        true,
                                        owl_init_send359,
                                        owl_resp_send358,
                                    )
                                };
                                let owl_ret372 = { owl_resp_transp_recv_result(owl_st_371, owl_x370)
                                };
                                (Some(owl_ret372), Tracked(itree))
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
