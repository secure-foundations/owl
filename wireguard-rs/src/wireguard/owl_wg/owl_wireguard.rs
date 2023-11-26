// Extracted verus code from file tests/wip/wireguard-full.owl:
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
pub use std::sync::Arc;
pub use std::str;
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
        old(t).view().is_output(x.dview(), endpoint_of_addr(dest_addr.view())),
    ensures
        t.view() == old(t).view().give_output(),
{
    // todo!()
    println!("owl_output: {:?}", hex::encode(x));
    // let len = std::cmp::min(x.len(), obuf.len());
    // dbg!(len);
    obuf[..x.len()].copy_from_slice(x);
}

#[verifier(external_body)]
pub fn owl_input<A>(
    Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
    ibuf: &[u8]
) -> (ie: (Vec<u8>, String))
    requires
        old(t).view().is_input(),
    ensures
        t.view() == old(t).view().take_input(ie.0.dview(), endpoint_of_addr(ie.1.view())),
{
    (ibuf.to_vec(), String::from_rust_string("".to_string())) // Specific to Wireguard---we never use the endpoints
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

pub struct owlSpec_initiator_msg1_val {
    pub owlSpec__initiator_msg1_C3: Seq<u8>,
    pub owlSpec__initiator_msg1_H4: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_initiator_msg1_val(x: Seq<u8>) -> Option<
    owlSpec_initiator_msg1_val,
> {
    let stream = parse_serialize::SpecStream { data: x, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::spec_parse_owl_initiator_msg1_val(stream) {
        let (owlSpec__initiator_msg1_C3, owlSpec__initiator_msg1_H4) = parsed;
        Some(owlSpec_initiator_msg1_val { owlSpec__initiator_msg1_C3, owlSpec__initiator_msg1_H4 })
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_initiator_msg1_val_inner(
    x: owlSpec_initiator_msg1_val,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__initiator_msg1_C3.len(), x.owlSpec__initiator_msg1_H4.len() ] {
        let stream = parse_serialize::SpecStream {
            data: seq_u8_of_len(
                x.owlSpec__initiator_msg1_C3.len() + x.owlSpec__initiator_msg1_H4.len(),
            ),
            start: 0,
        };
        if let Ok((serialized, n)) = parse_serialize::spec_serialize_owl_initiator_msg1_val(
            stream,
            ((x.owlSpec__initiator_msg1_C3, x.owlSpec__initiator_msg1_H4)),
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
pub closed spec fn serialize_owlSpec_initiator_msg1_val(x: owlSpec_initiator_msg1_val) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_initiator_msg1_val_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_initiator_msg1_val {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_initiator_msg1_val(self)
    }
}

pub open spec fn initiator_msg1_val(
    arg__initiator_msg1_C3: Seq<u8>,
    arg__initiator_msg1_H4: Seq<u8>,
) -> Seq<u8> {
    serialize_owlSpec_initiator_msg1_val(
        owlSpec_initiator_msg1_val {
            owlSpec__initiator_msg1_C3: arg__initiator_msg1_C3,
            owlSpec__initiator_msg1_H4: arg__initiator_msg1_H4,
        },
    )
}

pub struct owlSpec_transp_keys {
    pub owlSpec__transp_keys_initiator: Seq<u8>,
    pub owlSpec__transp_keys_responder: Seq<u8>,
    pub owlSpec__transp_keys_init_ephemeral: Seq<u8>,
    pub owlSpec__transp_keys_resp_ephemeral: Seq<u8>,
    pub owlSpec__transp_keys_T_init_send: Seq<u8>,
    pub owlSpec__transp_keys_T_resp_send: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_transp_keys(x: Seq<u8>) -> Option<owlSpec_transp_keys> {
    let stream = parse_serialize::SpecStream { data: x, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::spec_parse_owl_transp_keys(stream) {
        let (
            (
                (
                    (
                        (owlSpec__transp_keys_initiator, owlSpec__transp_keys_responder),
                        owlSpec__transp_keys_init_ephemeral,
                    ),
                    owlSpec__transp_keys_resp_ephemeral,
                ),
                owlSpec__transp_keys_T_init_send,
            ),
            owlSpec__transp_keys_T_resp_send,
        ) = parsed;
        Some(
            owlSpec_transp_keys {
                owlSpec__transp_keys_initiator,
                owlSpec__transp_keys_responder,
                owlSpec__transp_keys_init_ephemeral,
                owlSpec__transp_keys_resp_ephemeral,
                owlSpec__transp_keys_T_init_send,
                owlSpec__transp_keys_T_resp_send,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_transp_keys_inner(x: owlSpec_transp_keys) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__transp_keys_initiator.len(), x.owlSpec__transp_keys_responder.len(), x.owlSpec__transp_keys_init_ephemeral.len(), x.owlSpec__transp_keys_resp_ephemeral.len(), x.owlSpec__transp_keys_T_init_send.len(), x.owlSpec__transp_keys_T_resp_send.len() ] {
        let stream = parse_serialize::SpecStream {
            data: seq_u8_of_len(
                x.owlSpec__transp_keys_initiator.len() + x.owlSpec__transp_keys_responder.len()
                    + x.owlSpec__transp_keys_init_ephemeral.len()
                    + x.owlSpec__transp_keys_resp_ephemeral.len()
                    + x.owlSpec__transp_keys_T_init_send.len()
                    + x.owlSpec__transp_keys_T_resp_send.len(),
            ),
            start: 0,
        };
        if let Ok((serialized, n)) = parse_serialize::spec_serialize_owl_transp_keys(
            stream,
            ((
                (
                    (
                        (
                            (x.owlSpec__transp_keys_initiator, x.owlSpec__transp_keys_responder),
                            x.owlSpec__transp_keys_init_ephemeral,
                        ),
                        x.owlSpec__transp_keys_resp_ephemeral,
                    ),
                    x.owlSpec__transp_keys_T_init_send,
                ),
                x.owlSpec__transp_keys_T_resp_send,
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
pub closed spec fn serialize_owlSpec_transp_keys(x: owlSpec_transp_keys) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_transp_keys_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_transp_keys {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_transp_keys(self)
    }
}

pub open spec fn transp_keys(
    arg__transp_keys_initiator: Seq<u8>,
    arg__transp_keys_responder: Seq<u8>,
    arg__transp_keys_init_ephemeral: Seq<u8>,
    arg__transp_keys_resp_ephemeral: Seq<u8>,
    arg__transp_keys_T_init_send: Seq<u8>,
    arg__transp_keys_T_resp_send: Seq<u8>,
) -> Seq<u8> {
    serialize_owlSpec_transp_keys(
        owlSpec_transp_keys {
            owlSpec__transp_keys_initiator: arg__transp_keys_initiator,
            owlSpec__transp_keys_responder: arg__transp_keys_responder,
            owlSpec__transp_keys_init_ephemeral: arg__transp_keys_init_ephemeral,
            owlSpec__transp_keys_resp_ephemeral: arg__transp_keys_resp_ephemeral,
            owlSpec__transp_keys_T_init_send: arg__transp_keys_T_init_send,
            owlSpec__transp_keys_T_resp_send: arg__transp_keys_T_resp_send,
        },
    )
}

pub struct owlSpec_responder_msg1_val {
    pub owlSpec__responder_msg1_C3: Seq<u8>,
    pub owlSpec__responder_msg1_H4: Seq<u8>,
    pub owlSpec__responder_msg1_ephemeral: Seq<u8>,
    pub owlSpec__responder_msg1_sender_pk: Seq<u8>,
    pub owlSpec__responder_msg1_sender: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_responder_msg1_val(x: Seq<u8>) -> Option<
    owlSpec_responder_msg1_val,
> {
    let stream = parse_serialize::SpecStream { data: x, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::spec_parse_owl_responder_msg1_val(stream) {
        let (
            (
                (
                    (owlSpec__responder_msg1_C3, owlSpec__responder_msg1_H4),
                    owlSpec__responder_msg1_ephemeral,
                ),
                owlSpec__responder_msg1_sender_pk,
            ),
            owlSpec__responder_msg1_sender,
        ) = parsed;
        Some(
            owlSpec_responder_msg1_val {
                owlSpec__responder_msg1_C3,
                owlSpec__responder_msg1_H4,
                owlSpec__responder_msg1_ephemeral,
                owlSpec__responder_msg1_sender_pk,
                owlSpec__responder_msg1_sender,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_responder_msg1_val_inner(
    x: owlSpec_responder_msg1_val,
) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__responder_msg1_C3.len(), x.owlSpec__responder_msg1_H4.len(), x.owlSpec__responder_msg1_ephemeral.len(), x.owlSpec__responder_msg1_sender_pk.len(), x.owlSpec__responder_msg1_sender.len() ] {
        let stream = parse_serialize::SpecStream {
            data: seq_u8_of_len(
                x.owlSpec__responder_msg1_C3.len() + x.owlSpec__responder_msg1_H4.len()
                    + x.owlSpec__responder_msg1_ephemeral.len()
                    + x.owlSpec__responder_msg1_sender_pk.len()
                    + x.owlSpec__responder_msg1_sender.len(),
            ),
            start: 0,
        };
        if let Ok((serialized, n)) = parse_serialize::spec_serialize_owl_responder_msg1_val(
            stream,
            ((
                (
                    (
                        (x.owlSpec__responder_msg1_C3, x.owlSpec__responder_msg1_H4),
                        x.owlSpec__responder_msg1_ephemeral,
                    ),
                    x.owlSpec__responder_msg1_sender_pk,
                ),
                x.owlSpec__responder_msg1_sender,
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
pub closed spec fn serialize_owlSpec_responder_msg1_val(x: owlSpec_responder_msg1_val) -> Seq<u8> {
    if let Some(val) = serialize_owlSpec_responder_msg1_val_inner(x) {
        val
    } else {
        seq![]
    }
}

impl OwlSpecSerialize for owlSpec_responder_msg1_val {
    open spec fn as_seq(self) -> Seq<u8> {
        serialize_owlSpec_responder_msg1_val(self)
    }
}

pub open spec fn responder_msg1_val(
    arg__responder_msg1_C3: Seq<u8>,
    arg__responder_msg1_H4: Seq<u8>,
    arg__responder_msg1_ephemeral: Seq<u8>,
    arg__responder_msg1_sender_pk: Seq<u8>,
    arg__responder_msg1_sender: Seq<u8>,
) -> Seq<u8> {
    serialize_owlSpec_responder_msg1_val(
        owlSpec_responder_msg1_val {
            owlSpec__responder_msg1_C3: arg__responder_msg1_C3,
            owlSpec__responder_msg1_H4: arg__responder_msg1_H4,
            owlSpec__responder_msg1_ephemeral: arg__responder_msg1_ephemeral,
            owlSpec__responder_msg1_sender_pk: arg__responder_msg1_sender_pk,
            owlSpec__responder_msg1_sender: arg__responder_msg1_sender,
        },
    )
}

#[is_variant]
#[derive(Copy, Clone)]
pub enum Endpoint {
    Loc_Initiator,
    Loc_Responder,
    Loc_dummy,
}

#[verifier(external_body)]
pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint {
    unimplemented!()  /* axiomatized */
}

pub open spec fn transp_recv_init_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    transp_keys_val: owlSpec_transp_keys,
    c: Seq<u8>,
) -> (res: ITree<(Option<Seq<u8>>, state_Initiator), Endpoint>) {
    owl_spec!(mut_state,state_Initiator,
(parse (parse_owlSpec_transp(c)) as (owlSpec_transp{owlSpec__transp_tag : _unused35 , owlSpec__transp_receiver : from , owlSpec__transp_counter : ctr , owlSpec__transp_packet : pkt }) in {
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : _unused36 , owlSpec__transp_keys_responder : responder_name , owlSpec__transp_keys_init_ephemeral : _unused37 , owlSpec__transp_keys_resp_ephemeral : eph_resp , owlSpec__transp_keys_T_init_send : _unused38 , owlSpec__transp_keys_T_resp_send : r2i_ }) in {
(if (c == responder_name) then (let r2i = ((ret (r2i_))) in
(ret(dec_st_aead(r2i, pkt, empty_seq_u8(), ctr)))) else ((ret (Option::None))))
} )
} otherwise ((ret (Option::None))))
)
}

#[verifier::opaque]
pub open spec fn transp_send_init_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    transp_keys_val: owlSpec_transp_keys,
    plaintext: Seq<u8>,
) -> (res: ITree<(Option<()>, state_Initiator), Endpoint>) {
    owl_spec!(mut_state,state_Initiator,
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : _unused116 , owlSpec__transp_keys_responder : transp_receiver , owlSpec__transp_keys_init_ephemeral : _unused117 , owlSpec__transp_keys_resp_ephemeral : eph_resp , owlSpec__transp_keys_T_init_send : i2r_ , owlSpec__transp_keys_T_resp_send : _unused118 }) in {
let i2r = ((ret (i2r_))) in
let transp_counter = ((ret(counter_as_bytes(mut_state.owl_N_init_send)))) in
let transp_tag = ((ret (transp_tag_value()))) in
(if (length( transp_receiver ) == 4) then (let transp_packet = ((ret(enc_st_aead( i2r
, plaintext
, owl_N_init_send
, empty_seq_u8() )))) in
let transp_output = ((ret (transp( transp_tag
, transp_receiver
, transp_counter
, transp_packet )))) in
(output (transp_output) to (Endpoint::Loc_Responder)) in
(ret (Option::Some(())))) else ((ret (Option::None))))
} )
)
}

#[verifier::opaque]
pub open spec fn receive_msg2_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    msg1_val: owlSpec_initiator_msg1_val,
    dhpk_S_resp: Seq<u8>,
) -> (res: ITree<(Option<Seq<u8>>, state_Initiator), Endpoint>) {
    owl_spec!(mut_state,state_Initiator,
(input (inp, _unused415)) in
(parse (parse_owlSpec_msg2(inp)) as (owlSpec_msg2{owlSpec__msg2_tag : msg2_tag , owlSpec__msg2_sender : msg2_sender , owlSpec__msg2_receiver : msg2_receiver , owlSpec__msg2_ephemeral : msg2_ephemeral_ , owlSpec__msg2_empty : msg2_empty , owlSpec__msg2_mac1 : msg2_mac1 , owlSpec__msg2_mac2 : msg2_mac2 }) in {
(parse (msg1_val) as (owlSpec_initiator_msg1_val{owlSpec__initiator_msg1_C3 : C3 , owlSpec__initiator_msg1_H4 : H4 }) in {
(if (andb( length(msg2_sender) == 4
, length( msg2_receiver ) == 4 )) then ((if (is_group_elem( msg2_ephemeral_ )) then (let psk = ((ret (zeros_32(  )))) in
let msg2_ephemeral = ((ret (msg2_ephemeral_))) in
let e_init = ((ret ((*cfg.owl_E_init).dview()))) in
let e_init_pk = ((ret (dhpk(e_init)))) in
let C4 = ((ret(kdf((0+NONCE_SIZE()) as usize, C3, msg2_ephemeral).subrange( 0
, 0+NONCE_SIZE() )))) in
let H5 = ((ret (crh(concat(H4, msg2_ephemeral))))) in
let ss = ((ret (dh_combine(msg2_ephemeral, e_init)))) in
let C5 = ((ret(kdf((0+NONCE_SIZE()) as usize, C4, ss).subrange( 0
, 0+NONCE_SIZE() )))) in
let C6 = ((ret(kdf( (0+NONCE_SIZE()) as usize
, C5
, dh_combine(msg2_ephemeral, (*cfg.owl_S_init).dview()) ).subrange( 0
, 0+NONCE_SIZE() )))) in
let C7 = ((ret(kdf( (0+NONCE_SIZE()+NONCE_SIZE()+KEY_SIZE()) as usize
, C6
, psk ).subrange(0, 0+NONCE_SIZE())))) in
let tau = ((ret(kdf( (0+NONCE_SIZE()+NONCE_SIZE()+KEY_SIZE()) as usize
, C6
, psk ).subrange(0+NONCE_SIZE(), 0+NONCE_SIZE()+NONCE_SIZE())))) in
let k0 = ((ret(kdf( (0+NONCE_SIZE()+NONCE_SIZE()+KEY_SIZE()) as usize
, C6
, psk ).subrange( 0+NONCE_SIZE()+NONCE_SIZE()
, 0+NONCE_SIZE()+NONCE_SIZE()+KEY_SIZE() )))) in
let H6 = ((ret (crh(concat(H5, tau))))) in
let emptystring = ((ret (empty_seq_u8()))) in
let caseval = ((ret(dec_st_aead(k0, msg2_empty, empty_seq_u8(), H6)))) in
(case (caseval){
| None => {(ret (Option::None))},
| Some (msg2_empty_dec) => {(if (msg2_empty_dec == emptystring) then (let H7 = ((ret (crh( concat( H6
, msg2_empty ) )))) in
let T_init_send = ((ret(kdf( (0+KEY_SIZE()+KEY_SIZE()) as usize
, C7
, empty_seq_u8() ).subrange(0, 0+KEY_SIZE())))) in
let T_init_recv = ((ret(kdf( (0+KEY_SIZE()+KEY_SIZE()) as usize
, C7
, empty_seq_u8() ).subrange(0+KEY_SIZE(), 0+KEY_SIZE()+KEY_SIZE())))) in
let retval = ((ret (transp_keys( msg2_receiver
, msg2_sender
, dhpk(e_init)
, msg2_ephemeral
, T_init_send
, T_init_recv )))) in
(ret (Option::Some(retval)))) else ((ret (Option::None))))},

})) else ((ret (Option::None))))) else ((ret (Option::None))))
} )
} otherwise ((ret (Option::None))))
)
}

#[verifier::opaque]
pub open spec fn generate_msg1_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    dhpk_S_resp: Seq<u8>,
) -> (res: ITree<(Seq<u8>, state_Initiator), Endpoint>) {
    owl_spec!(mut_state,state_Initiator,
let C0 = ((ret (crh(construction())))) in
let H0 = ((ret (crh(concat(C0, identifier()))))) in
let H1 = ((ret (crh(concat(H0, dhpk_S_resp))))) in
let e_init = ((ret (dhpk((*cfg.owl_E_init).dview())))) in
let C1 = ((ret(kdf((0+NONCE_SIZE()) as usize, C0, e_init).subrange( 0
, 0+NONCE_SIZE() )))) in
let H2 = ((ret (crh(concat(H1, e_init))))) in
let ss_S_resp_E_init = ((ret (dh_combine( dhpk_S_resp
, (*cfg.owl_E_init).dview() )))) in
let C2 = ((ret(kdf( (0+NONCE_SIZE()+KEY_SIZE()) as usize
, C1
, ss_S_resp_E_init ).subrange(0, 0+NONCE_SIZE())))) in
let k0 = ((ret(kdf( (0+NONCE_SIZE()+KEY_SIZE()) as usize
, C1
, ss_S_resp_E_init ).subrange(0+NONCE_SIZE(), 0+NONCE_SIZE()+KEY_SIZE())))) in
let msg1_static = ((ret(enc_st_aead( k0
, dhpk((*cfg.owl_S_init).dview())
, owl_aead_counter_msg1_C2
, H2 )))) in
let H3 = ((ret (crh(concat(H2, msg1_static))))) in
let ss_S_resp_S_init = ((ret (dh_combine( dhpk_S_resp
, (*cfg.owl_S_init).dview() )))) in
let C3 = ((ret(kdf( (0+NONCE_SIZE()+KEY_SIZE()) as usize
, C2
, ss_S_resp_S_init ).subrange(0, 0+NONCE_SIZE())))) in
let k1 = ((ret(kdf( (0+NONCE_SIZE()+KEY_SIZE()) as usize
, C2
, ss_S_resp_S_init ).subrange(0+NONCE_SIZE(), 0+NONCE_SIZE()+KEY_SIZE())))) in
let timestamp = (call(timestamp_i_spec(cfg, mut_state))) in
let msg1_timestamp = ((ret(enc_st_aead( k1
, timestamp
, owl_aead_counter_msg1_C3
, H3 )))) in
let H4 = ((ret (crh(concat(H3, msg1_timestamp))))) in
let msg1_sender = (call(get_sender_i_spec(cfg, mut_state))) in
let msg1_tag = ((ret (msg1_tag_value()))) in
let msg1_mac1_k = ((ret (crh(concat(mac1(), dhpk_S_resp))))) in
let msg1_mac1 = ((ret(mac( msg1_mac1_k
, concat( concat(concat(concat(msg1_tag, msg1_sender), e_init), msg1_static)
, msg1_timestamp ) )))) in
let msg1_mac2 = ((ret (zeros_16()))) in
let msg1_output = ((ret (msg1( msg1_tag
, msg1_sender
, e_init
, msg1_static
, msg1_timestamp
, msg1_mac1
, msg1_mac2 )))) in
(output (msg1_output) to (Endpoint::Loc_Responder)) in
let retval = ((ret (initiator_msg1_val(C3, H4)))) in
(ret (retval))
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
pub open spec fn Responder_main_spec(cfg: cfg_Responder, mut_state: state_Responder) -> (res: ITree<
    ((), state_Responder),
    Endpoint,
>) {
    owl_spec!(mut_state,state_Responder,
(ret (()))
)
}

#[verifier::opaque]
pub open spec fn transp_recv_resp_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    transp_keys_val: owlSpec_transp_keys,
    c: Seq<u8>,
) -> (res: ITree<(Option<Seq<u8>>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(parse (parse_owlSpec_transp(c)) as (owlSpec_transp{owlSpec__transp_tag : _unused799 , owlSpec__transp_receiver : from , owlSpec__transp_counter : ctr , owlSpec__transp_packet : pkt }) in {
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : initiator_name , owlSpec__transp_keys_responder : _unused800 , owlSpec__transp_keys_init_ephemeral : eph_init , owlSpec__transp_keys_resp_ephemeral : _unused801 , owlSpec__transp_keys_T_init_send : i2r_ , owlSpec__transp_keys_T_resp_send : _unused802 }) in {
(if (c == initiator_name) then (let i2r = ((ret (i2r_))) in
(ret(dec_st_aead(i2r, pkt, empty_seq_u8(), ctr)))) else ((ret (Option::None))))
} )
} otherwise ((ret (Option::None))))
)
}

#[verifier::opaque]
pub open spec fn transp_send_resp_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    transp_keys_val: owlSpec_transp_keys,
    plaintext: Seq<u8>,
) -> (res: ITree<(Option<()>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : transp_receiver , owlSpec__transp_keys_responder : _unused880 , owlSpec__transp_keys_init_ephemeral : eph_init , owlSpec__transp_keys_resp_ephemeral : _unused881 , owlSpec__transp_keys_T_init_send : _unused882 , owlSpec__transp_keys_T_resp_send : r2i_ }) in {
let r2i = ((ret (r2i_))) in
let transp_counter = ((ret(counter_as_bytes(mut_state.owl_N_resp_send)))) in
let transp_tag = ((ret (transp_tag_value()))) in
(if (length( transp_receiver ) == 4) then (let transp_packet = ((ret(enc_st_aead( r2i
, plaintext
, owl_N_resp_send
, empty_seq_u8() )))) in
let transp_output = ((ret (transp( transp_tag
, transp_receiver
, transp_counter
, transp_packet )))) in
(output (transp_output) to (Endpoint::Loc_Initiator)) in
(ret (Option::Some(())))) else ((ret (Option::None))))
} )
)
}

#[verifier::opaque]
pub open spec fn generate_msg2_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    msg1_val_: owlSpec_responder_msg1_val,
) -> (res: ITree<(Seq<u8>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(parse (msg1_val_) as (owlSpec_responder_msg1_val{owlSpec__responder_msg1_C3 : C3 , owlSpec__responder_msg1_H4 : H4 , owlSpec__responder_msg1_ephemeral : ephemeral_ , owlSpec__responder_msg1_sender_pk : dhpk_S_init , owlSpec__responder_msg1_sender : msg2_receiver }) in {
let ephemeral = ((ret (ephemeral_))) in
let e_resp_pk = ((ret (dhpk((*cfg.owl_E_resp).dview())))) in
let psk = ((ret (zeros_32()))) in
let C4 = ((ret(kdf((0+NONCE_SIZE()) as usize, C3, e_resp_pk).subrange( 0
, 0+NONCE_SIZE() )))) in
let H5 = ((ret (crh(concat(H4, e_resp_pk))))) in
let ss = ((ret (dh_combine(ephemeral, (*cfg.owl_E_resp).dview())))) in
let C5 = ((ret(kdf((0+NONCE_SIZE()) as usize, C4, ss).subrange( 0
, 0+NONCE_SIZE() )))) in
let C6 = ((ret(kdf( (0+NONCE_SIZE()) as usize
, C5
, dh_combine(dhpk_S_init, (*cfg.owl_E_resp).dview()) ).subrange( 0
, 0+NONCE_SIZE() )))) in
let C7 = ((ret(kdf( (0+NONCE_SIZE()+NONCE_SIZE()+KEY_SIZE()) as usize
, C6
, psk ).subrange(0, 0+NONCE_SIZE())))) in
let tau = ((ret(kdf( (0+NONCE_SIZE()+NONCE_SIZE()+KEY_SIZE()) as usize
, C6
, psk ).subrange(0+NONCE_SIZE(), 0+NONCE_SIZE()+NONCE_SIZE())))) in
let k0 = ((ret(kdf( (0+NONCE_SIZE()+NONCE_SIZE()+KEY_SIZE()) as usize
, C6
, psk ).subrange( 0+NONCE_SIZE()+NONCE_SIZE()
, 0+NONCE_SIZE()+NONCE_SIZE()+KEY_SIZE() )))) in
let H6 = ((ret (crh(concat(H5, tau))))) in
let emptystring = ((ret (empty_seq_u8()))) in
let msg2_empty = ((ret(enc_st_aead( k0
, emptystring
, owl_aead_counter_msg2_C7
, H6 )))) in
let H7 = ((ret (crh(concat(H6, msg2_empty))))) in
let msg2_sender = (call(get_sender_r_spec(cfg, mut_state))) in
let msg2_tag = ((ret (msg2_tag_value()))) in
let msg2_mac1_k = ((ret (crh(concat(mac1(), dhpk_S_init))))) in
let msg2_mac1 = ((ret(mac( msg2_mac1_k
, concat( concat( concat(concat(msg2_tag, msg2_sender), msg2_receiver)
, e_resp_pk )
, msg2_empty ) )))) in
let msg2_mac2 = ((ret (zeros_16()))) in
let msg2_output = ((ret (msg2( msg2_tag
, msg2_sender
, msg2_receiver
, e_resp_pk
, msg2_empty
, msg2_mac1
, msg2_mac2 )))) in
(output (msg2_output) to (Endpoint::Loc_Initiator)) in
let T_resp_recv = ((ret(kdf( (0+KEY_SIZE()+KEY_SIZE()) as usize
, C7
, empty_seq_u8() ).subrange(0, 0+KEY_SIZE())))) in
let T_resp_send = ((ret(kdf( (0+KEY_SIZE()+KEY_SIZE()) as usize
, C7
, empty_seq_u8() ).subrange(0+KEY_SIZE(), 0+KEY_SIZE()+KEY_SIZE())))) in
let retval = ((ret (transp_keys( msg2_receiver
, msg2_sender
, ephemeral
, e_resp_pk
, T_resp_recv
, T_resp_send )))) in
(ret (retval))
} )
)
}

#[verifier::opaque]
pub open spec fn receive_msg1_spec(cfg: cfg_Responder, mut_state: state_Responder) -> (res: ITree<
    (Option<Seq<u8>>, state_Responder),
    Endpoint,
>) {
    owl_spec!(mut_state,state_Responder,
(input (inp, _unused1562)) in
(parse (parse_owlSpec_msg1(inp)) as (owlSpec_msg1{owlSpec__msg1_tag : msg1_tag , owlSpec__msg1_sender : msg1_sender , owlSpec__msg1_ephemeral : msg1_ephemeral_ , owlSpec__msg1_static : msg1_static , owlSpec__msg1_timestamp : msg1_timestamp , owlSpec__msg1_mac1 : msg1_mac1 , owlSpec__msg1_mac2 : msg1_mac2 }) in {
(if (length( msg1_sender ) == 4) then ((if (is_group_elem( msg1_ephemeral_ )) then (let C0 = ((ret (crh( construction(  ) )))) in
let H0 = ((ret (crh(concat(C0, identifier()))))) in
let H1 = ((ret (crh(concat(H0, dhpk((*cfg.owl_S_resp).dview())))))) in
let msg1_ephemeral = ((ret (msg1_ephemeral_))) in
let C1 = ((ret(kdf((0+NONCE_SIZE()) as usize, C0, msg1_ephemeral).subrange( 0
, 0+NONCE_SIZE() )))) in
let H2 = ((ret (crh(concat(H1, msg1_ephemeral))))) in
let ss_msg1_ephemeral_S_resp = ((ret (dh_combine( msg1_ephemeral
, (*cfg.owl_S_resp).dview() )))) in
let C2 = ((ret(kdf( (0+NONCE_SIZE()+KEY_SIZE()) as usize
, C1
, ss_msg1_ephemeral_S_resp ).subrange(0, 0+NONCE_SIZE())))) in
let k0 = ((ret(kdf( (0+NONCE_SIZE()+KEY_SIZE()) as usize
, C1
, ss_msg1_ephemeral_S_resp ).subrange( 0+NONCE_SIZE()
, 0+NONCE_SIZE()+KEY_SIZE() )))) in
let caseval = ((ret(dec_st_aead(k0, msg1_static, H2, empty_seq_u8())))) in
(case (caseval){
| None => {(ret (Option::None))},
| Some (msg1_static_dec) => {let opk = (call(checkpk_resp_spec( cfg
, mut_state
, msg1_static_dec ))) in
let caseval = ((ret (opk))) in
(case (caseval){
| None => {(ret (Option::None))},
| Some (dhpk_S_init_) => {(if (msg1_static_dec == dhpk_S_init_) then (let H3 = ((ret (crh( concat( H2
, msg1_static ) )))) in
let ss_S_init_S_resp = ((ret (dh_combine( dhpk_S_init_
, (*cfg.owl_S_resp).dview() )))) in
let C3 = ((ret(kdf( (0+NONCE_SIZE()+KEY_SIZE()) as usize
, C2
, ss_S_init_S_resp ).subrange(0, 0+NONCE_SIZE())))) in
let k1 = ((ret(kdf( (0+NONCE_SIZE()+KEY_SIZE()) as usize
, C2
, ss_S_init_S_resp ).subrange(0+NONCE_SIZE(), 0+NONCE_SIZE()+KEY_SIZE())))) in
let caseval = ((ret(dec_st_aead(k1, msg1_timestamp, H3, empty_seq_u8())))) in
(case (caseval){
| None => {(ret (Option::None))},
| Some (msg1_timestamp_dec) => {let H4 = ((ret (crh( concat( H3
, msg1_timestamp_dec ) )))) in
let retval = ((ret (responder_msg1_val( C3
, H4
, msg1_ephemeral
, dhpk_S_init_
, msg1_sender )))) in
let v = ((ret (retval))) in
(ret (Option::Some(v)))},

})) else ((ret (Option::None))))},

})},

})) else ((ret (Option::None))))) else ((ret (Option::None))))
} otherwise ((ret (Option::None))))
)
}

#[verifier::opaque]
pub open spec fn checkpk_resp_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    pk: Seq<u8>,
) -> (res: ITree<(Option<Seq<u8>>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(ret(owlSpec_checkpk_resp_pure(pk)))
)
}

#[verifier(external_body)]
pub closed spec fn owlSpec_checkpk_resp_pure(pk: Seq<u8>) -> Option<Seq<u8>> {
    unimplemented!()
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
pub struct owl_msg1 {
    pub owl__msg1_tag: Vec<u8>,
    pub owl__msg1_sender: Vec<u8>,
    pub owl__msg1_ephemeral: Vec<u8>,
    pub owl__msg1_static: Vec<u8>,
    pub owl__msg1_timestamp: Vec<u8>,
    pub owl__msg1_mac1: Vec<u8>,
    pub owl__msg1_mac2: Vec<u8>,
}

impl DView for owl_msg1 {
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

pub exec fn parse_owl_msg1(arg: &[u8]) -> (res: Option<owl_msg1>)
    ensures
        res.is_Some() ==> parse_owlSpec_msg1(arg.dview()).is_Some(),
        res.is_None() ==> parse_owlSpec_msg1(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == parse_owlSpec_msg1(arg.dview()).get_Some_0(),
{
    reveal(parse_owlSpec_msg1);
    let vec_arg = slice_to_vec(arg);
    let stream = parse_serialize::Stream { data: vec_arg, start: 0 };
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
                owl__msg1_tag,
                owl__msg1_sender,
                owl__msg1_ephemeral,
                owl__msg1_static,
                owl__msg1_timestamp,
                owl__msg1_mac1,
                owl__msg1_mac2,
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_msg1_inner(arg: &owl_msg1) -> (res: Option<Vec<u8>>)
    ensures
        res.is_Some() ==> serialize_owlSpec_msg1_inner(arg.dview()).is_Some(),
        res.is_None() ==> serialize_owlSpec_msg1_inner(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == serialize_owlSpec_msg1_inner(
            arg.dview(),
        ).get_Some_0(),
{
    reveal(serialize_owlSpec_msg1_inner);
    if no_usize_overflows![ vec_length(&arg.owl__msg1_tag), vec_length(&arg.owl__msg1_sender), vec_length(&arg.owl__msg1_ephemeral), vec_length(&arg.owl__msg1_static), vec_length(&arg.owl__msg1_timestamp), vec_length(&arg.owl__msg1_mac1), vec_length(&arg.owl__msg1_mac2) ] {
        let stream = parse_serialize::Stream {
            data: vec_u8_of_len(
                vec_length(&arg.owl__msg1_tag) + vec_length(&arg.owl__msg1_sender) + vec_length(
                    &arg.owl__msg1_ephemeral,
                ) + vec_length(&arg.owl__msg1_static) + vec_length(&arg.owl__msg1_timestamp)
                    + vec_length(&arg.owl__msg1_mac1) + vec_length(&arg.owl__msg1_mac2),
            ),
            start: 0,
        };
        let ser_result = parse_serialize::serialize_owl_msg1(
            stream,
            ((
                (
                    (
                        (
                            (
                                (
                                    clone_vec_u8(&arg.owl__msg1_tag),
                                    clone_vec_u8(&arg.owl__msg1_sender),
                                ),
                                clone_vec_u8(&arg.owl__msg1_ephemeral),
                            ),
                            clone_vec_u8(&arg.owl__msg1_static),
                        ),
                        clone_vec_u8(&arg.owl__msg1_timestamp),
                    ),
                    clone_vec_u8(&arg.owl__msg1_mac1),
                ),
                clone_vec_u8(&arg.owl__msg1_mac2),
            )),
        );
        if let Ok((mut serialized, n)) = ser_result {
            vec_truncate(&mut serialized.data, n);
            Some(serialized.data)
        } else {
            None
        }
    } else {
        None
    }
}

pub exec fn serialize_owl_msg1(arg: &owl_msg1) -> (res: Vec<u8>)
    ensures
        res.dview() == serialize_owlSpec_msg1(arg.dview()),
{
    reveal(serialize_owlSpec_msg1);
    let res = serialize_owl_msg1_inner(arg);
    assume(res.is_Some());
    res.unwrap()
}

/* TODO this will be generated by parsley */
pub struct owl_msg2 {
    pub owl__msg2_tag: Vec<u8>,
    pub owl__msg2_sender: Vec<u8>,
    pub owl__msg2_receiver: Vec<u8>,
    pub owl__msg2_ephemeral: Vec<u8>,
    pub owl__msg2_empty: Vec<u8>,
    pub owl__msg2_mac1: Vec<u8>,
    pub owl__msg2_mac2: Vec<u8>,
}

impl DView for owl_msg2 {
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

pub exec fn parse_owl_msg2(arg: &[u8]) -> (res: Option<owl_msg2>)
    ensures
        res.is_Some() ==> parse_owlSpec_msg2(arg.dview()).is_Some(),
        res.is_None() ==> parse_owlSpec_msg2(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == parse_owlSpec_msg2(arg.dview()).get_Some_0(),
{
    reveal(parse_owlSpec_msg2);
    let vec_arg = slice_to_vec(arg);
    let stream = parse_serialize::Stream { data: vec_arg, start: 0 };
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
                owl__msg2_tag,
                owl__msg2_sender,
                owl__msg2_receiver,
                owl__msg2_ephemeral,
                owl__msg2_empty,
                owl__msg2_mac1,
                owl__msg2_mac2,
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_msg2_inner(arg: &owl_msg2) -> (res: Option<Vec<u8>>)
    ensures
        res.is_Some() ==> serialize_owlSpec_msg2_inner(arg.dview()).is_Some(),
        res.is_None() ==> serialize_owlSpec_msg2_inner(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == serialize_owlSpec_msg2_inner(
            arg.dview(),
        ).get_Some_0(),
{
    reveal(serialize_owlSpec_msg2_inner);
    if no_usize_overflows![ vec_length(&arg.owl__msg2_tag), vec_length(&arg.owl__msg2_sender), vec_length(&arg.owl__msg2_receiver), vec_length(&arg.owl__msg2_ephemeral), vec_length(&arg.owl__msg2_empty), vec_length(&arg.owl__msg2_mac1), vec_length(&arg.owl__msg2_mac2) ] {
        let stream = parse_serialize::Stream {
            data: vec_u8_of_len(
                vec_length(&arg.owl__msg2_tag) + vec_length(&arg.owl__msg2_sender) + vec_length(
                    &arg.owl__msg2_receiver,
                ) + vec_length(&arg.owl__msg2_ephemeral) + vec_length(&arg.owl__msg2_empty)
                    + vec_length(&arg.owl__msg2_mac1) + vec_length(&arg.owl__msg2_mac2),
            ),
            start: 0,
        };
        let ser_result = parse_serialize::serialize_owl_msg2(
            stream,
            ((
                (
                    (
                        (
                            (
                                (
                                    clone_vec_u8(&arg.owl__msg2_tag),
                                    clone_vec_u8(&arg.owl__msg2_sender),
                                ),
                                clone_vec_u8(&arg.owl__msg2_receiver),
                            ),
                            clone_vec_u8(&arg.owl__msg2_ephemeral),
                        ),
                        clone_vec_u8(&arg.owl__msg2_empty),
                    ),
                    clone_vec_u8(&arg.owl__msg2_mac1),
                ),
                clone_vec_u8(&arg.owl__msg2_mac2),
            )),
        );
        if let Ok((mut serialized, n)) = ser_result {
            vec_truncate(&mut serialized.data, n);
            Some(serialized.data)
        } else {
            None
        }
    } else {
        None
    }
}

pub exec fn serialize_owl_msg2(arg: &owl_msg2) -> (res: Vec<u8>)
    ensures
        res.dview() == serialize_owlSpec_msg2(arg.dview()),
{
    reveal(serialize_owlSpec_msg2);
    let res = serialize_owl_msg2_inner(arg);
    assume(res.is_Some());
    res.unwrap()
}

/* TODO this will be generated by parsley */
pub struct owl_transp {
    pub owl__transp_tag: Vec<u8>,
    pub owl__transp_receiver: Vec<u8>,
    pub owl__transp_counter: Vec<u8>,
    pub owl__transp_packet: Vec<u8>,
}

impl DView for owl_transp {
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

pub exec fn parse_owl_transp(arg: &[u8]) -> (res: Option<owl_transp>)
    ensures
        res.is_Some() ==> parse_owlSpec_transp(arg.dview()).is_Some(),
        res.is_None() ==> parse_owlSpec_transp(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == parse_owlSpec_transp(
            arg.dview(),
        ).get_Some_0(),
{
    reveal(parse_owlSpec_transp);
    let vec_arg = slice_to_vec(arg);
    let stream = parse_serialize::Stream { data: vec_arg, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::parse_owl_transp(stream) {
        let (((owl__transp_tag, owl__transp_receiver), owl__transp_counter), owl__transp_packet) =
            parsed;
        Some(
            owl_transp {
                owl__transp_tag,
                owl__transp_receiver,
                owl__transp_counter,
                owl__transp_packet,
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_transp_inner(arg: &owl_transp) -> (res: Option<Vec<u8>>)
    ensures
        res.is_Some() ==> serialize_owlSpec_transp_inner(arg.dview()).is_Some(),
        res.is_None() ==> serialize_owlSpec_transp_inner(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == serialize_owlSpec_transp_inner(
            arg.dview(),
        ).get_Some_0(),
{
    reveal(serialize_owlSpec_transp_inner);
    if no_usize_overflows![ vec_length(&arg.owl__transp_tag), vec_length(&arg.owl__transp_receiver), vec_length(&arg.owl__transp_counter), vec_length(&arg.owl__transp_packet) ] {
        let stream = parse_serialize::Stream {
            data: vec_u8_of_len(
                vec_length(&arg.owl__transp_tag) + vec_length(&arg.owl__transp_receiver)
                    + vec_length(&arg.owl__transp_counter) + vec_length(&arg.owl__transp_packet),
            ),
            start: 0,
        };
        let ser_result = parse_serialize::serialize_owl_transp(
            stream,
            ((
                (
                    (clone_vec_u8(&arg.owl__transp_tag), clone_vec_u8(&arg.owl__transp_receiver)),
                    clone_vec_u8(&arg.owl__transp_counter),
                ),
                clone_vec_u8(&arg.owl__transp_packet),
            )),
        );
        if let Ok((mut serialized, n)) = ser_result {
            vec_truncate(&mut serialized.data, n);
            Some(serialized.data)
        } else {
            None
        }
    } else {
        None
    }
}

pub exec fn serialize_owl_transp(arg: &owl_transp) -> (res: Vec<u8>)
    ensures
        res.dview() == serialize_owlSpec_transp(arg.dview()),
{
    reveal(serialize_owlSpec_transp);
    let res = serialize_owl_transp_inner(arg);
    assume(res.is_Some());
    res.unwrap()
}

/* TODO this will be generated by parsley */
pub struct owl_initiator_msg1_val {
    pub owl__initiator_msg1_C3: Vec<u8>,
    pub owl__initiator_msg1_H4: Vec<u8>,
}

impl DView for owl_initiator_msg1_val {
    type V = owlSpec_initiator_msg1_val;
    
    open spec fn dview(&self) -> owlSpec_initiator_msg1_val {
        owlSpec_initiator_msg1_val {
            owlSpec__initiator_msg1_C3: self.owl__initiator_msg1_C3.dview().as_seq(),
            owlSpec__initiator_msg1_H4: self.owl__initiator_msg1_H4.dview().as_seq(),
        }
    }
}

pub exec fn parse_owl_initiator_msg1_val(arg: &[u8]) -> (res: Option<owl_initiator_msg1_val>)
    ensures
        res.is_Some() ==> parse_owlSpec_initiator_msg1_val(arg.dview()).is_Some(),
        res.is_None() ==> parse_owlSpec_initiator_msg1_val(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == parse_owlSpec_initiator_msg1_val(
            arg.dview(),
        ).get_Some_0(),
{
    reveal(parse_owlSpec_initiator_msg1_val);
    let vec_arg = slice_to_vec(arg);
    let stream = parse_serialize::Stream { data: vec_arg, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::parse_owl_initiator_msg1_val(stream) {
        let (owl__initiator_msg1_C3, owl__initiator_msg1_H4) = parsed;
        Some(owl_initiator_msg1_val { owl__initiator_msg1_C3, owl__initiator_msg1_H4 })
    } else {
        None
    }
}

pub exec fn serialize_owl_initiator_msg1_val_inner(arg: &owl_initiator_msg1_val) -> (res: Option<
    Vec<u8>,
>)
    ensures
        res.is_Some() ==> serialize_owlSpec_initiator_msg1_val_inner(arg.dview()).is_Some(),
        res.is_None() ==> serialize_owlSpec_initiator_msg1_val_inner(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == serialize_owlSpec_initiator_msg1_val_inner(
            arg.dview(),
        ).get_Some_0(),
{
    reveal(serialize_owlSpec_initiator_msg1_val_inner);
    if no_usize_overflows![ vec_length(&arg.owl__initiator_msg1_C3), vec_length(&arg.owl__initiator_msg1_H4) ] {
        let stream = parse_serialize::Stream {
            data: vec_u8_of_len(
                vec_length(&arg.owl__initiator_msg1_C3) + vec_length(&arg.owl__initiator_msg1_H4),
            ),
            start: 0,
        };
        let ser_result = parse_serialize::serialize_owl_initiator_msg1_val(
            stream,
            ((
                clone_vec_u8(&arg.owl__initiator_msg1_C3),
                clone_vec_u8(&arg.owl__initiator_msg1_H4),
            )),
        );
        if let Ok((mut serialized, n)) = ser_result {
            vec_truncate(&mut serialized.data, n);
            Some(serialized.data)
        } else {
            None
        }
    } else {
        None
    }
}

pub exec fn serialize_owl_initiator_msg1_val(arg: &owl_initiator_msg1_val) -> (res: Vec<u8>)
    ensures
        res.dview() == serialize_owlSpec_initiator_msg1_val(arg.dview()),
{
    reveal(serialize_owlSpec_initiator_msg1_val);
    let res = serialize_owl_initiator_msg1_val_inner(arg);
    assume(res.is_Some());
    res.unwrap()
}

/* TODO this will be generated by parsley */
pub struct owl_transp_keys {
    pub owl__transp_keys_initiator: Vec<u8>,
    pub owl__transp_keys_responder: Vec<u8>,
    pub owl__transp_keys_init_ephemeral: Vec<u8>,
    pub owl__transp_keys_resp_ephemeral: Vec<u8>,
    pub owl__transp_keys_T_init_send: Vec<u8>,
    pub owl__transp_keys_T_resp_send: Vec<u8>,
}

impl DView for owl_transp_keys {
    type V = owlSpec_transp_keys;
    
    open spec fn dview(&self) -> owlSpec_transp_keys {
        owlSpec_transp_keys {
            owlSpec__transp_keys_initiator: self.owl__transp_keys_initiator.dview().as_seq(),
            owlSpec__transp_keys_responder: self.owl__transp_keys_responder.dview().as_seq(),
            owlSpec__transp_keys_init_ephemeral:
                self.owl__transp_keys_init_ephemeral.dview().as_seq(),
            owlSpec__transp_keys_resp_ephemeral:
                self.owl__transp_keys_resp_ephemeral.dview().as_seq(),
            owlSpec__transp_keys_T_init_send: self.owl__transp_keys_T_init_send.dview().as_seq(),
            owlSpec__transp_keys_T_resp_send: self.owl__transp_keys_T_resp_send.dview().as_seq(),
        }
    }
}

pub exec fn parse_owl_transp_keys(arg: &[u8]) -> (res: Option<owl_transp_keys>)
    ensures
        res.is_Some() ==> parse_owlSpec_transp_keys(arg.dview()).is_Some(),
        res.is_None() ==> parse_owlSpec_transp_keys(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == parse_owlSpec_transp_keys(
            arg.dview(),
        ).get_Some_0(),
{
    reveal(parse_owlSpec_transp_keys);
    let vec_arg = slice_to_vec(arg);
    let stream = parse_serialize::Stream { data: vec_arg, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::parse_owl_transp_keys(stream) {
        let (
            (
                (
                    (
                        (owl__transp_keys_initiator, owl__transp_keys_responder),
                        owl__transp_keys_init_ephemeral,
                    ),
                    owl__transp_keys_resp_ephemeral,
                ),
                owl__transp_keys_T_init_send,
            ),
            owl__transp_keys_T_resp_send,
        ) = parsed;
        Some(
            owl_transp_keys {
                owl__transp_keys_initiator,
                owl__transp_keys_responder,
                owl__transp_keys_init_ephemeral,
                owl__transp_keys_resp_ephemeral,
                owl__transp_keys_T_init_send,
                owl__transp_keys_T_resp_send,
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_transp_keys_inner(arg: &owl_transp_keys) -> (res: Option<Vec<u8>>)
    ensures
        res.is_Some() ==> serialize_owlSpec_transp_keys_inner(arg.dview()).is_Some(),
        res.is_None() ==> serialize_owlSpec_transp_keys_inner(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == serialize_owlSpec_transp_keys_inner(
            arg.dview(),
        ).get_Some_0(),
{
    reveal(serialize_owlSpec_transp_keys_inner);
    if no_usize_overflows![ vec_length(&arg.owl__transp_keys_initiator), vec_length(&arg.owl__transp_keys_responder), vec_length(&arg.owl__transp_keys_init_ephemeral), vec_length(&arg.owl__transp_keys_resp_ephemeral), vec_length(&arg.owl__transp_keys_T_init_send), vec_length(&arg.owl__transp_keys_T_resp_send) ] {
        let stream = parse_serialize::Stream {
            data: vec_u8_of_len(
                vec_length(&arg.owl__transp_keys_initiator) + vec_length(
                    &arg.owl__transp_keys_responder,
                ) + vec_length(&arg.owl__transp_keys_init_ephemeral) + vec_length(
                    &arg.owl__transp_keys_resp_ephemeral,
                ) + vec_length(&arg.owl__transp_keys_T_init_send) + vec_length(
                    &arg.owl__transp_keys_T_resp_send,
                ),
            ),
            start: 0,
        };
        let ser_result = parse_serialize::serialize_owl_transp_keys(
            stream,
            ((
                (
                    (
                        (
                            (
                                clone_vec_u8(&arg.owl__transp_keys_initiator),
                                clone_vec_u8(&arg.owl__transp_keys_responder),
                            ),
                            clone_vec_u8(&arg.owl__transp_keys_init_ephemeral),
                        ),
                        clone_vec_u8(&arg.owl__transp_keys_resp_ephemeral),
                    ),
                    clone_vec_u8(&arg.owl__transp_keys_T_init_send),
                ),
                clone_vec_u8(&arg.owl__transp_keys_T_resp_send),
            )),
        );
        if let Ok((mut serialized, n)) = ser_result {
            vec_truncate(&mut serialized.data, n);
            Some(serialized.data)
        } else {
            None
        }
    } else {
        None
    }
}

pub exec fn serialize_owl_transp_keys(arg: &owl_transp_keys) -> (res: Vec<u8>)
    ensures
        res.dview() == serialize_owlSpec_transp_keys(arg.dview()),
{
    reveal(serialize_owlSpec_transp_keys);
    let res = serialize_owl_transp_keys_inner(arg);
    assume(res.is_Some());
    res.unwrap()
}

/* TODO this will be generated by parsley */
pub struct owl_responder_msg1_val {
    pub owl__responder_msg1_C3: Vec<u8>,
    pub owl__responder_msg1_H4: Vec<u8>,
    pub owl__responder_msg1_ephemeral: Vec<u8>,
    pub owl__responder_msg1_sender_pk: Vec<u8>,
    pub owl__responder_msg1_sender: Vec<u8>,
}

impl DView for owl_responder_msg1_val {
    type V = owlSpec_responder_msg1_val;
    
    open spec fn dview(&self) -> owlSpec_responder_msg1_val {
        owlSpec_responder_msg1_val {
            owlSpec__responder_msg1_C3: self.owl__responder_msg1_C3.dview().as_seq(),
            owlSpec__responder_msg1_H4: self.owl__responder_msg1_H4.dview().as_seq(),
            owlSpec__responder_msg1_ephemeral: self.owl__responder_msg1_ephemeral.dview().as_seq(),
            owlSpec__responder_msg1_sender_pk: self.owl__responder_msg1_sender_pk.dview().as_seq(),
            owlSpec__responder_msg1_sender: self.owl__responder_msg1_sender.dview().as_seq(),
        }
    }
}

pub exec fn parse_owl_responder_msg1_val(arg: &[u8]) -> (res: Option<owl_responder_msg1_val>)
    ensures
        res.is_Some() ==> parse_owlSpec_responder_msg1_val(arg.dview()).is_Some(),
        res.is_None() ==> parse_owlSpec_responder_msg1_val(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == parse_owlSpec_responder_msg1_val(
            arg.dview(),
        ).get_Some_0(),
{
    reveal(parse_owlSpec_responder_msg1_val);
    let vec_arg = slice_to_vec(arg);
    let stream = parse_serialize::Stream { data: vec_arg, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::parse_owl_responder_msg1_val(stream) {
        let (
            (
                ((owl__responder_msg1_C3, owl__responder_msg1_H4), owl__responder_msg1_ephemeral),
                owl__responder_msg1_sender_pk,
            ),
            owl__responder_msg1_sender,
        ) = parsed;
        Some(
            owl_responder_msg1_val {
                owl__responder_msg1_C3,
                owl__responder_msg1_H4,
                owl__responder_msg1_ephemeral,
                owl__responder_msg1_sender_pk,
                owl__responder_msg1_sender,
            },
        )
    } else {
        None
    }
}

pub exec fn serialize_owl_responder_msg1_val_inner(arg: &owl_responder_msg1_val) -> (res: Option<
    Vec<u8>,
>)
    ensures
        res.is_Some() ==> serialize_owlSpec_responder_msg1_val_inner(arg.dview()).is_Some(),
        res.is_None() ==> serialize_owlSpec_responder_msg1_val_inner(arg.dview()).is_None(),
        res.is_Some() ==> res.get_Some_0().dview() == serialize_owlSpec_responder_msg1_val_inner(
            arg.dview(),
        ).get_Some_0(),
{
    reveal(serialize_owlSpec_responder_msg1_val_inner);
    if no_usize_overflows![ vec_length(&arg.owl__responder_msg1_C3), vec_length(&arg.owl__responder_msg1_H4), vec_length(&arg.owl__responder_msg1_ephemeral), vec_length(&arg.owl__responder_msg1_sender_pk), vec_length(&arg.owl__responder_msg1_sender) ] {
        let stream = parse_serialize::Stream {
            data: vec_u8_of_len(
                vec_length(&arg.owl__responder_msg1_C3) + vec_length(&arg.owl__responder_msg1_H4)
                    + vec_length(&arg.owl__responder_msg1_ephemeral) + vec_length(
                    &arg.owl__responder_msg1_sender_pk,
                ) + vec_length(&arg.owl__responder_msg1_sender),
            ),
            start: 0,
        };
        let ser_result = parse_serialize::serialize_owl_responder_msg1_val(
            stream,
            ((
                (
                    (
                        (
                            clone_vec_u8(&arg.owl__responder_msg1_C3),
                            clone_vec_u8(&arg.owl__responder_msg1_H4),
                        ),
                        clone_vec_u8(&arg.owl__responder_msg1_ephemeral),
                    ),
                    clone_vec_u8(&arg.owl__responder_msg1_sender_pk),
                ),
                clone_vec_u8(&arg.owl__responder_msg1_sender),
            )),
        );
        if let Ok((mut serialized, n)) = ser_result {
            vec_truncate(&mut serialized.data, n);
            Some(serialized.data)
        } else {
            None
        }
    } else {
        None
    }
}

pub exec fn serialize_owl_responder_msg1_val(arg: &owl_responder_msg1_val) -> (res: Vec<u8>)
    ensures
        res.dview() == serialize_owlSpec_responder_msg1_val(arg.dview()),
{
    reveal(serialize_owlSpec_responder_msg1_val);
    let res = serialize_owl_responder_msg1_val_inner(arg);
    assume(res.is_Some());
    res.unwrap()
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
pub const fn dummy_addr() -> (a: StrSlice<'static>)
    ensures
        endpoint_of_addr(a.view()) == Endpoint::Loc_dummy,
{
    new_strlit("127.0.0.1:9003")
}

pub struct state_Initiator {
    pub owl_N_init_recv: usize,
    pub owl_N_init_send: usize,
    pub owl_aead_counter_msg1_C3: usize,
    pub owl_aead_counter_msg1_C2: usize,
}

impl state_Initiator {
    #[verifier(external_body)]
    pub fn init_state_Initiator() -> Self {
        state_Initiator {
            owl_N_init_recv: 0,
            owl_N_init_send: 0,
            owl_aead_counter_msg1_C3: 0,
            owl_aead_counter_msg1_C2: 0,
        }
    }
}

pub struct cfg_Initiator<O> {
    pub owl_S_init: Arc<Vec<u8>>,
    pub owl_E_init: Arc<Vec<u8>>,
    pub pk_owl_S_resp: Arc<Vec<u8>>,
    pub pk_owl_S_init: Arc<Vec<u8>>,
    pub pk_owl_E_resp: Arc<Vec<u8>>,
    pub pk_owl_E_init: Arc<Vec<u8>>,
    pub salt: Arc<Vec<u8>>,
    pub device: crate::wireguard::handshake::device::DeviceInner<O>,
}

impl<O> cfg_Initiator<O> {
    #[verifier::spinoff_prover]
    pub fn owl_transp_recv_init(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_transp_keys_val11330: owl_transp_keys,
        owl_c11329: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<Arc<Vec<u8>>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_recv_init_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val11330.dview(),
                owl_c11329.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(transp_recv_init_spec);
            let temp_owl__x33 = { arc_clone(&owl_c11329) };
            let owl__x33 = arc_clone(&temp_owl__x33);
            if let Some(parseval) = parse_owl_transp(vec_as_slice(&(*arc_clone(&owl__x33)))) {
                let owl__6 = arc_new(parseval.owl__transp_tag);
                let owl_from5 = arc_new(parseval.owl__transp_receiver);
                let owl_ctr4 = arc_new(parseval.owl__transp_counter);
                let owl_pkt3 = arc_new(parseval.owl__transp_packet);
                {
                    let temp_owl__x32 = { owl_transp_keys_val11330 };
                    let owl__x32 = temp_owl__x32;
                    let parseval = owl__x32;
                    let owl__12 = arc_new(parseval.owl__transp_keys_initiator);
                    let owl_responder_name11 = arc_new(parseval.owl__transp_keys_responder);
                    let owl__10 = arc_new(parseval.owl__transp_keys_init_ephemeral);
                    let owl_eph_resp9 = arc_new(parseval.owl__transp_keys_resp_ephemeral);
                    let owl__8 = arc_new(parseval.owl__transp_keys_T_init_send);
                    let owl_r2i_7 = arc_new(parseval.owl__transp_keys_T_resp_send);
                    {
                        let temp_owl__x28 = { arc_clone(&owl_c11329) };
                        let owl__x28 = arc_clone(&temp_owl__x28);
                        let temp_owl__x30 = { arc_clone(&owl_responder_name11) };
                        let owl__x30 = arc_clone(&temp_owl__x30);
                        let temp_owl__x31 = {
                        rc_vec_eq(&arc_clone(&owl__x28), &arc_clone(&owl__x30))
                        };
                        let owl__x31 = temp_owl__x31;
                        if owl__x31 {
                            let temp_owl__x17 = { arc_clone(&owl_r2i_7) };
                            let owl__x17 = arc_clone(&temp_owl__x17);
                            let temp_owl__x18 = { arc_clone(&owl__x17) };
                            let owl__x18 = arc_clone(&temp_owl__x18);
                            let temp_owl__x21 = { arc_clone(&owl__x18) };
                            let owl__x21 = arc_clone(&temp_owl__x21);
                            let temp_owl__x22 = { arc_clone(&owl_pkt3) };
                            let owl__x22 = arc_clone(&temp_owl__x22);
                            let temp_owl__x23 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x23 = arc_new(temp_owl__x23);
                            let temp_owl__x24 = { arc_clone(&owl_ctr4) };
                            let owl__x24 = arc_clone(&temp_owl__x24);
                            (
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x21))),
                                    vec_as_slice(&(*arc_clone(&owl__x22))),
                                    vec_as_slice(&(*arc_clone(&owl__x23))),
                                    vec_as_slice(&(*arc_clone(&owl__x24))),
                                ),
                                Tracked(itree),
                            )
                        } else {
                            (None, Tracked(itree))
                        }
                    }
                }
            } else {
                let temp_owl__x2 = { None };
                let owl__x2 = temp_owl__x2;
                (owl__x2, Tracked(itree))
            }
        };
        Ok(res_inner)
    }
    
    #[verifier::spinoff_prover]
    pub fn owl_transp_send_init(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<()>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_transp_keys_val9517: owl_transp_keys,
        owl_plaintext9516: Arc<Vec<u8>>,
        obuf: &mut [u8]
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_send_init_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val9517.dview(),
                owl_plaintext9516.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(transp_send_init_spec);
            let temp_owl__x114 = { owl_transp_keys_val9517 };
            let owl__x114 = temp_owl__x114;
            let parseval = owl__x114;
            let owl__45 = arc_new(parseval.owl__transp_keys_initiator);
            let owl_transp_receiver44 = arc_new(parseval.owl__transp_keys_responder);
            let owl__43 = arc_new(parseval.owl__transp_keys_init_ephemeral);
            let owl_eph_resp42 = arc_new(parseval.owl__transp_keys_resp_ephemeral);
            let owl_i2r_41 = arc_new(parseval.owl__transp_keys_T_init_send);
            let owl__40 = arc_new(parseval.owl__transp_keys_T_resp_send);
            {
                let temp_owl__x50 = { arc_clone(&owl_i2r_41) };
                let owl__x50 = arc_clone(&temp_owl__x50);
                let temp_owl__x51 = { arc_clone(&owl__x50) };
                let owl__x51 = arc_clone(&temp_owl__x51);
                let temp_owl__x53 = { owl_counter_as_bytes(&(mut_state.owl_N_init_send)) };
                let owl__x53 = arc_new(temp_owl__x53);
                let temp_owl__x57 = { owl_transp_tag_value() };
                let owl__x57 = arc_new(temp_owl__x57);
                let temp_owl__x58 = { arc_clone(&owl__x57) };
                let owl__x58 = arc_clone(&temp_owl__x58);
                let temp_owl__x109 = { arc_clone(&owl_transp_receiver44) };
                let owl__x109 = arc_clone(&temp_owl__x109);
                let temp_owl__x110 = { vec_length(&(*arc_clone(&owl__x109))) };
                let owl__x110 = temp_owl__x110;
                let temp_owl__x112 = { 4 };
                let owl__x112 = temp_owl__x112;
                let temp_owl__x113 = { owl__x110 == owl__x112 };
                let owl__x113 = temp_owl__x113;
                if owl__x113 {
                    let temp_owl__x64 = { arc_clone(&owl__x51) };
                    let owl__x64 = arc_clone(&temp_owl__x64);
                    let temp_owl__x66 = { arc_clone(&owl_plaintext9516) };
                    let owl__x66 = arc_clone(&temp_owl__x66);
                    let temp_owl__x68 = {
                        {
                            let x: Vec<u8> = mk_vec_u8![];
                            x
                        }
                    };
                    let owl__x68 = arc_new(temp_owl__x68);
                    let temp_owl__x69 = {
                        match owl_enc_st_aead(
                            vec_as_slice(&(*arc_clone(&owl__x64))),
                            vec_as_slice(&(*arc_clone(&owl__x66))),
                            &mut mut_state.owl_N_init_send,
                            vec_as_slice(&(*arc_clone(&owl__x68))),
                        ) {
                            Ok(ctxt) => ctxt,
                            Err(e) => { return Err(e) },
                        }
                    };
                    let owl__x69 = arc_clone(&temp_owl__x69);
                    let temp_owl__x85 = { arc_clone(&owl__x58) };
                    let owl__x85 = arc_clone(&temp_owl__x85);
                    let temp_owl__x87 = { arc_clone(&owl_transp_receiver44) };
                    let owl__x87 = arc_clone(&temp_owl__x87);
                    let temp_owl__x89 = { arc_clone(&owl__x53) };
                    let owl__x89 = arc_clone(&temp_owl__x89);
                    let temp_owl__x91 = { arc_clone(&owl__x69) };
                    let owl__x91 = arc_clone(&temp_owl__x91);
                    let temp_owl__x93 = {
                    owl_transp {
                        owl__transp_tag: clone_vec_u8(&*arc_clone(&owl__x85)),
                        owl__transp_receiver: clone_vec_u8(&*arc_clone(&owl__x87)),
                        owl__transp_counter: clone_vec_u8(&*arc_clone(&owl__x89)),
                        owl__transp_packet: clone_vec_u8(&*arc_clone(&owl__x91)),
                    }
                    };
                    let owl__x93 = temp_owl__x93;
                    let temp_owl__x94 = { owl__x93 };
                    let owl__x94 = temp_owl__x94;
                    let temp_owl__x98 = { owl__x94 };
                    let owl__x98 = temp_owl__x98;
                    let temp_owl__x99 = {
                    owl_output::<(Option<()>, state_Initiator)>(
                        Tracked(&mut itree),
                        vec_as_slice(&(serialize_owl_transp(&owl__x98))),
                        &Responder_addr(),
                        &Initiator_addr(),
                        obuf
                    )
                    };
                    let owl__x99 = temp_owl__x99;
                    let temp_owl__x102 = { () };
                    let owl__x102 = temp_owl__x102;
                    let temp_owl__x103 = { Some(owl__x102) };
                    let owl__x103 = temp_owl__x103;
                    (owl__x103, Tracked(itree))
                } else {
                    (None, Tracked(itree))
                }
            }
        };
        Ok(res_inner)
    }
    
    pub exec fn owl_receive_msg2_wrapper(&self, s: &mut state_Initiator, dhpk_S_resp: Arc<Vec<u8>>, msg1_val: owl_initiator_msg1_val, ibuf: &[u8]) -> (_: Option<owl_transp_keys>) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            receive_msg2_spec_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_receive_msg2(Tracked(call_token), s, msg1_val, dhpk_S_resp, ibuf).unwrap();
        res
    }

    
    #[verifier::spinoff_prover]
    pub fn owl_receive_msg2(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_msg1_val5826: owl_initiator_msg1_val,
        owl_dhpk_S_resp5825: Arc<Vec<u8>>,
        ibuf: &[u8]
    ) -> (res: Result<
        (
            Option<owl_transp_keys>,
            Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == receive_msg2_spec(
                *self,
                *old(mut_state),
                owl_msg1_val5826.dview(),
                owl_dhpk_S_resp5825.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (option_as_seq(dview_option(res.get_Ok_0().0)), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(receive_msg2_spec);
            let (temp_owl_inp122, owl__121) = owl_input::<(Option<Seq<u8>>, state_Initiator)>(
                Tracked(&mut itree),
                ibuf
            );
            let owl_inp122 = arc_new(temp_owl_inp122);
            let temp_owl__x407 = { arc_clone(&owl_inp122) };
            let owl__x407 = arc_clone(&temp_owl__x407);
            if let Some(parseval) = parse_owl_msg2(vec_as_slice(&(*arc_clone(&owl__x407)))) {
                let owl_msg2_tag130 = arc_new(parseval.owl__msg2_tag);
                let owl_msg2_sender129 = arc_new(parseval.owl__msg2_sender);
                let owl_msg2_receiver128 = arc_new(parseval.owl__msg2_receiver);
                let owl_msg2_ephemeral_127 = arc_new(parseval.owl__msg2_ephemeral);
                let owl_msg2_empty126 = arc_new(parseval.owl__msg2_empty);
                let owl_msg2_mac1125 = arc_new(parseval.owl__msg2_mac1);
                let owl_msg2_mac2124 = arc_new(parseval.owl__msg2_mac2);
                {
                    let temp_owl__x406 = { owl_msg1_val5826 };
                    let owl__x406 = temp_owl__x406;
                    let parseval = owl__x406;
                    let owl_C3132 = arc_new(parseval.owl__initiator_msg1_C3);
                    let owl_H4131 = arc_new(parseval.owl__initiator_msg1_H4);
                    {
                        let temp_owl__x392 = { arc_clone(&owl_msg2_sender129) };
                        let owl__x392 = arc_clone(&temp_owl__x392);
                        let temp_owl__x393 = { vec_length(&(*arc_clone(&owl__x392))) };
                        let owl__x393 = temp_owl__x393;
                        let temp_owl__x395 = { 4 };
                        let owl__x395 = temp_owl__x395;
                        let temp_owl__x396 = { owl__x393 == owl__x395 };
                        let owl__x396 = temp_owl__x396;
                        let temp_owl__x400 = { arc_clone(&owl_msg2_receiver128) };
                        let owl__x400 = arc_clone(&temp_owl__x400);
                        let temp_owl__x401 = { vec_length(&(*arc_clone(&owl__x400))) };
                        let owl__x401 = temp_owl__x401;
                        let temp_owl__x403 = { 4 };
                        let owl__x403 = temp_owl__x403;
                        let temp_owl__x404 = { owl__x401 == owl__x403 };
                        let owl__x404 = temp_owl__x404;
                        let temp_owl__x405 = { owl__x396 && owl__x404 };
                        let owl__x405 = temp_owl__x405;
                        if owl__x405 {
                            let temp_owl__x379 = { arc_clone(&owl_msg2_ephemeral_127) };
                            let owl__x379 = arc_clone(&temp_owl__x379);
                            let temp_owl__x380 = {
                            owl_is_group_elem(vec_as_slice(&(*arc_clone(&owl__x379))))
                            };
                            let owl__x380 = temp_owl__x380;
                            if owl__x380 {
                                let temp_owl__x136 = { owl_zeros_32() };
                                let owl__x136 = arc_new(temp_owl__x136);
                                let temp_owl__x137 = { arc_clone(&owl__x136) };
                                let owl__x137 = arc_clone(&temp_owl__x137);
                                let temp_owl__x142 = { arc_clone(&owl_msg2_ephemeral_127) };
                                let owl__x142 = arc_clone(&temp_owl__x142);
                                let temp_owl__x143 = { arc_clone(&owl__x142) };
                                let owl__x143 = arc_clone(&temp_owl__x143);
                                let temp_owl__x147 = { arc_clone(&self.owl_E_init) };
                                let owl__x147 = arc_clone(&temp_owl__x147);
                                let temp_owl__x148 = { arc_clone(&owl__x147) };
                                let owl__x148 = arc_clone(&temp_owl__x148);
                                let temp_owl__x155 = { arc_clone(&owl__x148) };
                                let owl__x155 = arc_clone(&temp_owl__x155);
                                let temp_owl__x157 = {
                                owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x155))))
                                };
                                let owl__x157 = arc_clone(&temp_owl__x157);
                                let temp_owl__x158 = { arc_clone(&owl__x157) };
                                let owl__x158 = arc_clone(&temp_owl__x158);
                                let temp_owl__x163 = { arc_clone(&owl_C3132) };
                                let owl__x163 = arc_clone(&temp_owl__x163);
                                let temp_owl__x165 = { arc_clone(&owl__x143) };
                                let owl__x165 = arc_clone(&temp_owl__x165);
                                let owl_msg2_C4410 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x163))),
                                    vec_as_slice(&(*arc_clone(&owl__x165))),
                                );
                                let temp_owl__x166 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C4410),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x166 = arc_clone(&temp_owl__x166);
                                let temp_owl__x179 = { arc_clone(&owl_H4131) };
                                let owl__x179 = arc_clone(&temp_owl__x179);
                                let temp_owl__x181 = { arc_clone(&owl__x143) };
                                let owl__x181 = arc_clone(&temp_owl__x181);
                                let temp_owl__x183 = {
                                owl_concat(
                                    vec_as_slice(&(*arc_clone(&owl__x179))),
                                    vec_as_slice(&(*arc_clone(&owl__x181))),
                                )
                                };
                                let owl__x183 = arc_new(temp_owl__x183);
                                let temp_owl__x185 = {
                                owl_crh(vec_as_slice(&(*arc_clone(&owl__x183))))
                                };
                                let owl__x185 = arc_clone(&temp_owl__x185);
                                let temp_owl__x186 = { arc_clone(&owl__x185) };
                                let owl__x186 = arc_clone(&temp_owl__x186);
                                let temp_owl__x196 = { arc_clone(&owl__x143) };
                                let owl__x196 = arc_clone(&temp_owl__x196);
                                let temp_owl__x198 = { arc_clone(&owl__x148) };
                                let owl__x198 = arc_clone(&temp_owl__x198);
                                let temp_owl__x200 = {
                                owl_dh_combine(
                                    vec_as_slice(&(*arc_clone(&owl__x196))),
                                    vec_as_slice(&(*arc_clone(&owl__x198))),
                                )
                                };
                                let owl__x200 = arc_clone(&temp_owl__x200);
                                let temp_owl__x201 = { arc_clone(&owl__x200) };
                                let owl__x201 = arc_clone(&temp_owl__x201);
                                let temp_owl__x206 = { arc_clone(&owl__x166) };
                                let owl__x206 = arc_clone(&temp_owl__x206);
                                let temp_owl__x208 = { arc_clone(&owl__x201) };
                                let owl__x208 = arc_clone(&temp_owl__x208);
                                let owl_msg2_C5411 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x206))),
                                    vec_as_slice(&(*arc_clone(&owl__x208))),
                                );
                                let temp_owl__x209 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C5411),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x209 = arc_clone(&temp_owl__x209);
                                let temp_owl__x216 = { arc_clone(&owl__x209) };
                                let owl__x216 = arc_clone(&temp_owl__x216);
                                let temp_owl__x219 = { arc_clone(&owl__x143) };
                                let owl__x219 = arc_clone(&temp_owl__x219);
                                let temp_owl__x221 = { arc_clone(&self.owl_S_init) };
                                let owl__x221 = arc_clone(&temp_owl__x221);
                                let temp_owl__x222 = {
                                owl_dh_combine(
                                    vec_as_slice(&(*arc_clone(&owl__x219))),
                                    vec_as_slice(&(*arc_clone(&owl__x221))),
                                )
                                };
                                let owl__x222 = arc_clone(&temp_owl__x222);
                                let owl_msg2_C6412 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x216))),
                                    vec_as_slice(&(*arc_clone(&owl__x222))),
                                );
                                let temp_owl__x223 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C6412),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x223 = arc_clone(&temp_owl__x223);
                                let temp_owl__x228 = { arc_clone(&owl__x223) };
                                let owl__x228 = arc_clone(&temp_owl__x228);
                                let temp_owl__x230 = { arc_clone(&owl__x137) };
                                let owl__x230 = arc_clone(&temp_owl__x230);
                                let owl_msg2_C7413 = owl_extract_expand_to_len(
                                    0 + nonce_size() + nonce_size() + key_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x228))),
                                    vec_as_slice(&(*arc_clone(&owl__x230))),
                                );
                                let temp_owl__x231 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7413),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x231 = arc_clone(&temp_owl__x231);
                                let temp_owl__x236 = { arc_clone(&owl__x223) };
                                let owl__x236 = arc_clone(&temp_owl__x236);
                                let temp_owl__x238 = { arc_clone(&owl__x137) };
                                let owl__x238 = arc_clone(&temp_owl__x238);
                                let temp_owl__x239 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7413),
                                            0 + nonce_size(),
                                            0 + nonce_size() + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x239 = arc_clone(&temp_owl__x239);
                                let temp_owl__x244 = { arc_clone(&owl__x223) };
                                let owl__x244 = arc_clone(&temp_owl__x244);
                                let temp_owl__x246 = { arc_clone(&owl__x137) };
                                let owl__x246 = arc_clone(&temp_owl__x246);
                                let temp_owl__x247 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7413),
                                            0 + nonce_size() + nonce_size(),
                                            0 + nonce_size() + nonce_size() + key_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x247 = arc_clone(&temp_owl__x247);
                                let temp_owl__x260 = { arc_clone(&owl__x186) };
                                let owl__x260 = arc_clone(&temp_owl__x260);
                                let temp_owl__x262 = { arc_clone(&owl__x239) };
                                let owl__x262 = arc_clone(&temp_owl__x262);
                                let temp_owl__x264 = {
                                owl_concat(
                                    vec_as_slice(&(*arc_clone(&owl__x260))),
                                    vec_as_slice(&(*arc_clone(&owl__x262))),
                                )
                                };
                                let owl__x264 = arc_new(temp_owl__x264);
                                let temp_owl__x266 = {
                                owl_crh(vec_as_slice(&(*arc_clone(&owl__x264))))
                                };
                                let owl__x266 = arc_clone(&temp_owl__x266);
                                let temp_owl__x267 = { arc_clone(&owl__x266) };
                                let owl__x267 = arc_clone(&temp_owl__x267);
                                let temp_owl__x271 = {
                                    {
                                        let x: Vec<u8> = mk_vec_u8![];
                                        x
                                    }
                                };
                                let owl__x271 = arc_new(temp_owl__x271);
                                let temp_owl__x272 = { arc_clone(&owl__x271) };
                                let owl__x272 = arc_clone(&temp_owl__x272);
                                let temp_owl__x369 = { arc_clone(&owl__x247) };
                                let owl__x369 = arc_clone(&temp_owl__x369);
                                let temp_owl__x371 = { arc_clone(&owl_msg2_empty126) };
                                let owl__x371 = arc_clone(&temp_owl__x371);
                                let temp_owl__x373 = {
                                    {
                                        let x: Vec<u8> = mk_vec_u8![];
                                        x
                                    }
                                };
                                let owl__x373 = arc_new(temp_owl__x373);
                                let temp_owl__x375 = { arc_clone(&owl__x267) };
                                let owl__x375 = arc_clone(&temp_owl__x375);
                                let temp_owl__x376 = {
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x369))),
                                    vec_as_slice(&(*arc_clone(&owl__x371))),
                                    vec_as_slice(&(*arc_clone(&owl__x373))),
                                    vec_as_slice(&(*arc_clone(&owl__x375))),
                                )
                                };
                                let owl__x376 = temp_owl__x376;
                                let temp_owl_caseval409 = { owl__x376 };
                                let owl_caseval409 = temp_owl_caseval409;
                                match owl_caseval409 {
                                    None => {
                                        let temp_owl__x277 = { None };
                                        let owl__x277 = temp_owl__x277;
                                        (owl__x277, Tracked(itree))
                                    },
                                    Some(temp_owl_msg2_empty_dec278) => {
                                        let owl_msg2_empty_dec278 = arc_clone(
                                            &temp_owl_msg2_empty_dec278,
                                        );
                                        let temp_owl__x364 = { arc_clone(&owl_msg2_empty_dec278) };
                                        let owl__x364 = arc_clone(&temp_owl__x364);
                                        let temp_owl__x366 = { arc_clone(&owl__x272) };
                                        let owl__x366 = arc_clone(&temp_owl__x366);
                                        let temp_owl__x367 = {
                                        rc_vec_eq(&arc_clone(&owl__x364), &arc_clone(&owl__x366))
                                        };
                                        let owl__x367 = temp_owl__x367;
                                        if owl__x367 {
                                            let temp_owl__x291 = { arc_clone(&owl__x267) };
                                            let owl__x291 = arc_clone(&temp_owl__x291);
                                            let temp_owl__x293 = { arc_clone(&owl_msg2_empty126) };
                                            let owl__x293 = arc_clone(&temp_owl__x293);
                                            let temp_owl__x295 = {
                                            owl_concat(
                                                vec_as_slice(&(*arc_clone(&owl__x291))),
                                                vec_as_slice(&(*arc_clone(&owl__x293))),
                                            )
                                            };
                                            let owl__x295 = arc_new(temp_owl__x295);
                                            let temp_owl__x297 = {
                                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x295))))
                                            };
                                            let owl__x297 = arc_clone(&temp_owl__x297);
                                            let temp_owl__x298 = { arc_clone(&owl__x297) };
                                            let owl__x298 = arc_clone(&temp_owl__x298);
                                            let temp_owl__x303 = { arc_clone(&owl__x231) };
                                            let owl__x303 = arc_clone(&temp_owl__x303);
                                            let temp_owl__x305 = {
                                                {
                                                    let x: Vec<u8> = mk_vec_u8![];
                                                    x
                                                }
                                            };
                                            let owl__x305 = arc_new(temp_owl__x305);
                                            let owl_transp_T414 = owl_extract_expand_to_len(
                                                0 + key_size() + key_size(),
                                                vec_as_slice(&(*arc_clone(&owl__x303))),
                                                vec_as_slice(&(*arc_clone(&owl__x305))),
                                            );
                                            let temp_owl__x306 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_transp_T414),
                                                        0,
                                                        0 + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x306 = arc_clone(&temp_owl__x306);
                                            let temp_owl__x311 = { arc_clone(&owl__x231) };
                                            let owl__x311 = arc_clone(&temp_owl__x311);
                                            let temp_owl__x313 = {
                                                {
                                                    let x: Vec<u8> = mk_vec_u8![];
                                                    x
                                                }
                                            };
                                            let owl__x313 = arc_new(temp_owl__x313);
                                            let temp_owl__x314 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_transp_T414),
                                                        0 + key_size(),
                                                        0 + key_size() + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x314 = arc_clone(&temp_owl__x314);
                                            let temp_owl__x339 = { arc_clone(&owl_msg2_receiver128)
                                            };
                                            let owl__x339 = arc_clone(&temp_owl__x339);
                                            let temp_owl__x341 = { arc_clone(&owl_msg2_sender129) };
                                            let owl__x341 = arc_clone(&temp_owl__x341);
                                            let temp_owl__x343 = { arc_clone(&owl__x148) };
                                            let owl__x343 = arc_clone(&temp_owl__x343);
                                            let temp_owl__x345 = {
                                            owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x343))))
                                            };
                                            let owl__x345 = arc_clone(&temp_owl__x345);
                                            let temp_owl__x347 = { arc_clone(&owl__x143) };
                                            let owl__x347 = arc_clone(&temp_owl__x347);
                                            let temp_owl__x349 = { arc_clone(&owl__x306) };
                                            let owl__x349 = arc_clone(&temp_owl__x349);
                                            let temp_owl__x351 = { arc_clone(&owl__x314) };
                                            let owl__x351 = arc_clone(&temp_owl__x351);
                                            let temp_owl__x353 = {
                                            owl_transp_keys {
                                                owl__transp_keys_initiator: clone_vec_u8(
                                                    &*arc_clone(&owl__x339),
                                                ),
                                                owl__transp_keys_responder: clone_vec_u8(
                                                    &*arc_clone(&owl__x341),
                                                ),
                                                owl__transp_keys_init_ephemeral: clone_vec_u8(
                                                    &*arc_clone(&owl__x345),
                                                ),
                                                owl__transp_keys_resp_ephemeral: clone_vec_u8(
                                                    &*arc_clone(&owl__x347),
                                                ),
                                                owl__transp_keys_T_init_send: clone_vec_u8(
                                                    &*arc_clone(&owl__x349),
                                                ),
                                                owl__transp_keys_T_resp_send: clone_vec_u8(
                                                    &*arc_clone(&owl__x351),
                                                ),
                                            }
                                            };
                                            let owl__x353 = temp_owl__x353;
                                            let temp_owl__x354 = { owl__x353 };
                                            let owl__x354 = temp_owl__x354;
                                            let temp_owl__x359 = { owl__x354 };
                                            let owl__x359 = temp_owl__x359;
                                            let temp_owl__x360 = { Some(owl__x359) };
                                            let owl__x360 = temp_owl__x360;
                                            (owl__x360, Tracked(itree))
                                        } else {
                                            (None, Tracked(itree))
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
                }
            } else {
                let temp_owl__x123 = { None };
                let owl__x123 = temp_owl__x123;
                (owl__x123, Tracked(itree))
            }
        };
        Ok(res_inner)
    }
    
    pub exec fn owl_generate_msg1_wrapper(&self, s: &mut state_Initiator, dhpk_S_resp: Arc<Vec<u8>>, obuf: &mut [u8]) -> (_: owl_initiator_msg1_val) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            generate_msg1_spec_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _): (owl_initiator_msg1_val, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>) =
            self.owl_generate_msg1(Tracked(call_token), s, dhpk_S_resp, obuf).unwrap();
        res
    }
    

    #[verifier::spinoff_prover]
    pub fn owl_generate_msg1(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_dhpk_S_resp5816: Arc<Vec<u8>>,
        obuf: &mut [u8]
    ) -> (res: Result<
        (owl_initiator_msg1_val, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == generate_msg1_spec(*self, *old(mut_state), owl_dhpk_S_resp5816.dview()),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview().as_seq(), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(generate_msg1_spec);
            let temp_owl__x422 = { owl_construction() };
            let owl__x422 = arc_new(temp_owl__x422);
            let temp_owl__x424 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x422)))) };
            let owl__x424 = arc_clone(&temp_owl__x424);
            let temp_owl__x425 = { arc_clone(&owl__x424) };
            let owl__x425 = arc_clone(&temp_owl__x425);
            let temp_owl__x438 = { arc_clone(&owl__x425) };
            let owl__x438 = arc_clone(&temp_owl__x438);
            let temp_owl__x440 = { owl_identifier() };
            let owl__x440 = arc_new(temp_owl__x440);
            let temp_owl__x442 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x438))),
                vec_as_slice(&(*arc_clone(&owl__x440))),
            )
            };
            let owl__x442 = arc_new(temp_owl__x442);
            let temp_owl__x444 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x442)))) };
            let owl__x444 = arc_clone(&temp_owl__x444);
            let temp_owl__x445 = { arc_clone(&owl__x444) };
            let owl__x445 = arc_clone(&temp_owl__x445);
            let temp_owl__x458 = { arc_clone(&owl__x445) };
            let owl__x458 = arc_clone(&temp_owl__x458);
            let temp_owl__x460 = { arc_clone(&owl_dhpk_S_resp5816) };
            let owl__x460 = arc_clone(&temp_owl__x460);
            let temp_owl__x462 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x458))),
                vec_as_slice(&(*arc_clone(&owl__x460))),
            )
            };
            let owl__x462 = arc_new(temp_owl__x462);
            let temp_owl__x464 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x462)))) };
            let owl__x464 = arc_clone(&temp_owl__x464);
            let temp_owl__x465 = { arc_clone(&owl__x464) };
            let owl__x465 = arc_clone(&temp_owl__x465);
            let temp_owl__x472 = { arc_clone(&self.owl_E_init) };
            let owl__x472 = arc_clone(&temp_owl__x472);
            let temp_owl__x474 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x472)))) };
            let owl__x474 = arc_clone(&temp_owl__x474);
            let temp_owl__x475 = { arc_clone(&owl__x474) };
            let owl__x475 = arc_clone(&temp_owl__x475);
            let temp_owl__x480 = { arc_clone(&owl__x425) };
            let owl__x480 = arc_clone(&temp_owl__x480);
            let temp_owl__x482 = { arc_clone(&owl__x475) };
            let owl__x482 = arc_clone(&temp_owl__x482);
            let owl_msg1_C1761 = owl_extract_expand_to_len(
                0 + nonce_size(),
                vec_as_slice(&(*arc_clone(&owl__x480))),
                vec_as_slice(&(*arc_clone(&owl__x482))),
            );
            let temp_owl__x483 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C1761), 0, 0 + nonce_size())),
            )
            };
            let owl__x483 = arc_clone(&temp_owl__x483);
            let temp_owl__x496 = { arc_clone(&owl__x465) };
            let owl__x496 = arc_clone(&temp_owl__x496);
            let temp_owl__x498 = { arc_clone(&owl__x475) };
            let owl__x498 = arc_clone(&temp_owl__x498);
            let temp_owl__x500 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x496))),
                vec_as_slice(&(*arc_clone(&owl__x498))),
            )
            };
            let owl__x500 = arc_new(temp_owl__x500);
            let temp_owl__x502 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x500)))) };
            let owl__x502 = arc_clone(&temp_owl__x502);
            let temp_owl__x503 = { arc_clone(&owl__x502) };
            let owl__x503 = arc_clone(&temp_owl__x503);
            let temp_owl__x513 = { arc_clone(&owl_dhpk_S_resp5816) };
            let owl__x513 = arc_clone(&temp_owl__x513);
            let temp_owl__x515 = { arc_clone(&self.owl_E_init) };
            let owl__x515 = arc_clone(&temp_owl__x515);
            let temp_owl__x517 = {
            owl_dh_combine(
                vec_as_slice(&(*arc_clone(&owl__x513))),
                vec_as_slice(&(*arc_clone(&owl__x515))),
            )
            };
            let owl__x517 = arc_clone(&temp_owl__x517);
            let temp_owl__x518 = { arc_clone(&owl__x517) };
            let owl__x518 = arc_clone(&temp_owl__x518);
            let temp_owl__x523 = { arc_clone(&owl__x483) };
            let owl__x523 = arc_clone(&temp_owl__x523);
            let temp_owl__x525 = { arc_clone(&owl__x518) };
            let owl__x525 = arc_clone(&temp_owl__x525);
            let owl_msg1_C2762 = owl_extract_expand_to_len(
                0 + nonce_size() + key_size(),
                vec_as_slice(&(*arc_clone(&owl__x523))),
                vec_as_slice(&(*arc_clone(&owl__x525))),
            );
            let temp_owl__x526 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C2762), 0, 0 + nonce_size())),
            )
            };
            let owl__x526 = arc_clone(&temp_owl__x526);
            let temp_owl__x531 = { arc_clone(&owl__x483) };
            let owl__x531 = arc_clone(&temp_owl__x531);
            let temp_owl__x533 = { arc_clone(&owl__x518) };
            let owl__x533 = arc_clone(&temp_owl__x533);
            let temp_owl__x534 = {
            arc_new(
                slice_to_vec(
                    slice_subrange(
                        vec_as_slice(&*owl_msg1_C2762),
                        0 + nonce_size(),
                        0 + nonce_size() + key_size(),
                    ),
                ),
            )
            };
            let owl__x534 = arc_clone(&temp_owl__x534);
            let temp_owl__x542 = { arc_clone(&owl__x534) };
            let owl__x542 = arc_clone(&temp_owl__x542);
            let temp_owl__x546 = { arc_clone(&self.owl_S_init) };
            let owl__x546 = arc_clone(&temp_owl__x546);
            let temp_owl__x547 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x546)))) };
            let owl__x547 = arc_clone(&temp_owl__x547);
            let temp_owl__x548 = { arc_clone(&owl__x547) };
            let owl__x548 = arc_clone(&temp_owl__x548);
            let temp_owl__x550 = { arc_clone(&owl__x503) };
            let owl__x550 = arc_clone(&temp_owl__x550);
            let temp_owl__x551 = {
                match owl_enc_st_aead(
                    vec_as_slice(&(*arc_clone(&owl__x542))),
                    vec_as_slice(&(*arc_clone(&owl__x548))),
                    &mut mut_state.owl_aead_counter_msg1_C2,
                    vec_as_slice(&(*arc_clone(&owl__x550))),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x551 = arc_clone(&temp_owl__x551);
            let temp_owl__x564 = { arc_clone(&owl__x503) };
            let owl__x564 = arc_clone(&temp_owl__x564);
            let temp_owl__x566 = { arc_clone(&owl__x551) };
            let owl__x566 = arc_clone(&temp_owl__x566);
            let temp_owl__x568 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x564))),
                vec_as_slice(&(*arc_clone(&owl__x566))),
            )
            };
            let owl__x568 = arc_new(temp_owl__x568);
            let temp_owl__x570 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x568)))) };
            let owl__x570 = arc_clone(&temp_owl__x570);
            let temp_owl__x571 = { arc_clone(&owl__x570) };
            let owl__x571 = arc_clone(&temp_owl__x571);
            let temp_owl__x581 = { arc_clone(&owl_dhpk_S_resp5816) };
            let owl__x581 = arc_clone(&temp_owl__x581);
            let temp_owl__x583 = { arc_clone(&self.owl_S_init) };
            let owl__x583 = arc_clone(&temp_owl__x583);
            let temp_owl__x585 = {
            owl_dh_combine(
                vec_as_slice(&(*arc_clone(&owl__x581))),
                vec_as_slice(&(*arc_clone(&owl__x583))),
            )
            };
            let owl__x585 = arc_clone(&temp_owl__x585);
            let temp_owl__x586 = { arc_clone(&owl__x585) };
            let owl__x586 = arc_clone(&temp_owl__x586);
            let temp_owl__x591 = { arc_clone(&owl__x526) };
            let owl__x591 = arc_clone(&temp_owl__x591);
            let temp_owl__x593 = { arc_clone(&owl__x586) };
            let owl__x593 = arc_clone(&temp_owl__x593);
            let owl_msg1_C3763 = owl_extract_expand_to_len(
                0 + nonce_size() + key_size(),
                vec_as_slice(&(*arc_clone(&owl__x591))),
                vec_as_slice(&(*arc_clone(&owl__x593))),
            );
            let temp_owl__x594 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C3763), 0, 0 + nonce_size())),
            )
            };
            let owl__x594 = arc_clone(&temp_owl__x594);
            let temp_owl__x599 = { arc_clone(&owl__x526) };
            let owl__x599 = arc_clone(&temp_owl__x599);
            let temp_owl__x601 = { arc_clone(&owl__x586) };
            let owl__x601 = arc_clone(&temp_owl__x601);
            let temp_owl__x602 = {
            arc_new(
                slice_to_vec(
                    slice_subrange(
                        vec_as_slice(&*owl_msg1_C3763),
                        0 + nonce_size(),
                        0 + nonce_size() + key_size(),
                    ),
                ),
            )
            };
            let owl__x602 = arc_clone(&temp_owl__x602);
            let (temp_owl__x604, Tracked(itree)): (
                _,
                Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
            ) = {
                owl_call!( itree
, *mut_state
, timestamp_i_spec(*self, *mut_state)
, self.owl_timestamp_i(mut_state) )
            };
            let owl__x604 = arc_clone(&temp_owl__x604);
            let temp_owl__x610 = { arc_clone(&owl__x602) };
            let owl__x610 = arc_clone(&temp_owl__x610);
            let temp_owl__x612 = { arc_clone(&owl__x604) };
            let owl__x612 = arc_clone(&temp_owl__x612);
            let temp_owl__x614 = { arc_clone(&owl__x571) };
            let owl__x614 = arc_clone(&temp_owl__x614);
            let temp_owl__x615 = {
                match owl_enc_st_aead(
                    vec_as_slice(&(*arc_clone(&owl__x610))),
                    vec_as_slice(&(*arc_clone(&owl__x612))),
                    &mut mut_state.owl_aead_counter_msg1_C3,
                    vec_as_slice(&(*arc_clone(&owl__x614))),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x615 = arc_clone(&temp_owl__x615);
            let temp_owl__x628 = { arc_clone(&owl__x571) };
            let owl__x628 = arc_clone(&temp_owl__x628);
            let temp_owl__x630 = { arc_clone(&owl__x615) };
            let owl__x630 = arc_clone(&temp_owl__x630);
            let temp_owl__x632 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x628))),
                vec_as_slice(&(*arc_clone(&owl__x630))),
            )
            };
            let owl__x632 = arc_new(temp_owl__x632);
            let temp_owl__x634 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x632)))) };
            let owl__x634 = arc_clone(&temp_owl__x634);
            let temp_owl__x635 = { arc_clone(&owl__x634) };
            let owl__x635 = arc_clone(&temp_owl__x635);
            let (temp_owl__x637, Tracked(itree)): (
                _,
                Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
            ) = {
                owl_call!( itree
, *mut_state
, get_sender_i_spec(*self, *mut_state)
, self.owl_get_sender_i(mut_state) )
            };
            let owl__x637 = arc_clone(&temp_owl__x637);
            let temp_owl__x641 = { owl_msg1_tag_value() };
            let owl__x641 = arc_new(temp_owl__x641);
            let temp_owl__x642 = { arc_clone(&owl__x641) };
            let owl__x642 = arc_clone(&temp_owl__x642);
            let temp_owl__x655 = { owl_mac1() };
            let owl__x655 = arc_new(temp_owl__x655);
            let temp_owl__x657 = { arc_clone(&owl_dhpk_S_resp5816) };
            let owl__x657 = arc_clone(&temp_owl__x657);
            let temp_owl__x659 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x655))),
                vec_as_slice(&(*arc_clone(&owl__x657))),
            )
            };
            let owl__x659 = arc_new(temp_owl__x659);
            let temp_owl__x661 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x659)))) };
            let owl__x661 = arc_clone(&temp_owl__x661);
            let temp_owl__x662 = { arc_clone(&owl__x661) };
            let owl__x662 = arc_clone(&temp_owl__x662);
            let temp_owl__x675 = { arc_clone(&owl__x662) };
            let owl__x675 = arc_clone(&temp_owl__x675);
            let temp_owl__x681 = { arc_clone(&owl__x642) };
            let owl__x681 = arc_clone(&temp_owl__x681);
            let temp_owl__x683 = { arc_clone(&owl__x637) };
            let owl__x683 = arc_clone(&temp_owl__x683);
            let temp_owl__x684 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x681))),
                vec_as_slice(&(*arc_clone(&owl__x683))),
            )
            };
            let owl__x684 = arc_new(temp_owl__x684);
            let temp_owl__x686 = { arc_clone(&owl__x475) };
            let owl__x686 = arc_clone(&temp_owl__x686);
            let temp_owl__x687 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x684))),
                vec_as_slice(&(*arc_clone(&owl__x686))),
            )
            };
            let owl__x687 = arc_new(temp_owl__x687);
            let temp_owl__x689 = { arc_clone(&owl__x551) };
            let owl__x689 = arc_clone(&temp_owl__x689);
            let temp_owl__x690 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x687))),
                vec_as_slice(&(*arc_clone(&owl__x689))),
            )
            };
            let owl__x690 = arc_new(temp_owl__x690);
            let temp_owl__x692 = { arc_clone(&owl__x615) };
            let owl__x692 = arc_clone(&temp_owl__x692);
            let temp_owl__x693 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x690))),
                vec_as_slice(&(*arc_clone(&owl__x692))),
            )
            };
            let owl__x693 = arc_new(temp_owl__x693);
            let temp_owl__x694 = {
            owl_mac(
                vec_as_slice(&(*arc_clone(&owl__x675))),
                vec_as_slice(&(*arc_clone(&owl__x693))),
            )
            };
            let owl__x694 = arc_clone(&temp_owl__x694);
            let temp_owl__x698 = { owl_zeros_16() };
            let owl__x698 = arc_new(temp_owl__x698);
            let temp_owl__x699 = { arc_clone(&owl__x698) };
            let owl__x699 = arc_clone(&temp_owl__x699);
            let temp_owl__x724 = { arc_clone(&owl__x642) };
            let owl__x724 = arc_clone(&temp_owl__x724);
            let temp_owl__x726 = { arc_clone(&owl__x637) };
            let owl__x726 = arc_clone(&temp_owl__x726);
            let temp_owl__x728 = { arc_clone(&owl__x475) };
            let owl__x728 = arc_clone(&temp_owl__x728);
            let temp_owl__x730 = { arc_clone(&owl__x551) };
            let owl__x730 = arc_clone(&temp_owl__x730);
            let temp_owl__x732 = { arc_clone(&owl__x615) };
            let owl__x732 = arc_clone(&temp_owl__x732);
            let temp_owl__x734 = { arc_clone(&owl__x694) };
            let owl__x734 = arc_clone(&temp_owl__x734);
            let temp_owl__x736 = { arc_clone(&owl__x699) };
            let owl__x736 = arc_clone(&temp_owl__x736);
            let temp_owl__x738 = {
            owl_msg1 {
                owl__msg1_tag: clone_vec_u8(&*arc_clone(&owl__x724)),
                owl__msg1_sender: clone_vec_u8(&*arc_clone(&owl__x726)),
                owl__msg1_ephemeral: clone_vec_u8(&*arc_clone(&owl__x728)),
                owl__msg1_static: clone_vec_u8(&*arc_clone(&owl__x730)),
                owl__msg1_timestamp: clone_vec_u8(&*arc_clone(&owl__x732)),
                owl__msg1_mac1: clone_vec_u8(&*arc_clone(&owl__x734)),
                owl__msg1_mac2: clone_vec_u8(&*arc_clone(&owl__x736)),
            }
            };
            let owl__x738 = temp_owl__x738;
            let temp_owl__x739 = { owl__x738 };
            let owl__x739 = temp_owl__x739;
            let temp_owl__x743 = { owl__x739 };
            let owl__x743 = temp_owl__x743;
            let temp_owl__x744 = {
            owl_output::<(Seq<u8>, state_Initiator)>(
                Tracked(&mut itree),
                vec_as_slice(&(serialize_owl_msg1(&owl__x743))),
                &Responder_addr(),
                &Initiator_addr(),
                obuf
            )
            };
            let owl__x744 = temp_owl__x744;
            let temp_owl__x754 = { arc_clone(&owl__x594) };
            let owl__x754 = arc_clone(&temp_owl__x754);
            let temp_owl__x756 = { arc_clone(&owl__x635) };
            let owl__x756 = arc_clone(&temp_owl__x756);
            let temp_owl__x758 = {
            owl_initiator_msg1_val {
                owl__initiator_msg1_C3: clone_vec_u8(&*arc_clone(&owl__x754)),
                owl__initiator_msg1_H4: clone_vec_u8(&*arc_clone(&owl__x756)),
            }
            };
            let owl__x758 = temp_owl__x758;
            let temp_owl__x759 = { owl__x758 };
            let owl__x759 = temp_owl__x759;
            let temp_owl__x760 = { owl__x759 };
            let owl__x760 = temp_owl__x760;
            (owl__x760, Tracked(itree))
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
        (Arc<Vec<u8>>, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == timestamp_i_spec(*self, *old(mut_state)),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview(), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let t = crate::wireguard::handshake::timestamp::now().to_vec();
            (arc_new(t), Tracked(itree))
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
        (Arc<Vec<u8>>, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == get_sender_i_spec(*self, *old(mut_state)),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview(), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let v = self.device.get_singleton_id();
            (Arc::new(v.to_le_bytes().to_vec()), Tracked(itree))
        };
        Ok(res_inner)
    }
}

pub struct state_Responder {
    pub owl_N_resp_recv: usize,
    pub owl_N_resp_send: usize,
    pub owl_aead_counter_msg2_C7: usize,
}

impl state_Responder {
    #[verifier(external_body)]
    pub fn init_state_Responder() -> Self {
        state_Responder { owl_N_resp_recv: 0, owl_N_resp_send: 0, owl_aead_counter_msg2_C7: 0 }
    }
}

pub struct cfg_Responder<O> {
    pub owl_S_resp: Arc<Vec<u8>>,
    pub owl_E_resp: Arc<Vec<u8>>,
    pub pk_owl_S_resp: Arc<Vec<u8>>,
    pub pk_owl_S_init: Arc<Vec<u8>>,
    pub pk_owl_E_resp: Arc<Vec<u8>>,
    pub pk_owl_E_init: Arc<Vec<u8>>,
    pub salt: Arc<Vec<u8>>,
    pub device: crate::wireguard::handshake::device::DeviceInner<O>,
}

impl<O> cfg_Responder<O> { 

    #[verifier::spinoff_prover]
    pub fn owl_transp_recv_resp(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_transp_keys_val14549: owl_transp_keys,
        owl_c14548: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<Arc<Vec<u8>>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_recv_resp_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val14549.dview(),
                owl_c14548.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(transp_recv_resp_spec);
            let temp_owl__x797 = { arc_clone(&owl_c14548) };
            let owl__x797 = arc_clone(&temp_owl__x797);
            if let Some(parseval) = parse_owl_transp(vec_as_slice(&(*arc_clone(&owl__x797)))) {
                let owl__770 = arc_new(parseval.owl__transp_tag);
                let owl_from769 = arc_new(parseval.owl__transp_receiver);
                let owl_ctr768 = arc_new(parseval.owl__transp_counter);
                let owl_pkt767 = arc_new(parseval.owl__transp_packet);
                {
                    let temp_owl__x796 = { owl_transp_keys_val14549 };
                    let owl__x796 = temp_owl__x796;
                    let parseval = owl__x796;
                    let owl_initiator_name776 = arc_new(parseval.owl__transp_keys_initiator);
                    let owl__775 = arc_new(parseval.owl__transp_keys_responder);
                    let owl_eph_init774 = arc_new(parseval.owl__transp_keys_init_ephemeral);
                    let owl__773 = arc_new(parseval.owl__transp_keys_resp_ephemeral);
                    let owl_i2r_772 = arc_new(parseval.owl__transp_keys_T_init_send);
                    let owl__771 = arc_new(parseval.owl__transp_keys_T_resp_send);
                    {
                        let temp_owl__x792 = { arc_clone(&owl_c14548) };
                        let owl__x792 = arc_clone(&temp_owl__x792);
                        let temp_owl__x794 = { arc_clone(&owl_initiator_name776) };
                        let owl__x794 = arc_clone(&temp_owl__x794);
                        let temp_owl__x795 = {
                        rc_vec_eq(&arc_clone(&owl__x792), &arc_clone(&owl__x794))
                        };
                        let owl__x795 = temp_owl__x795;
                        if owl__x795 {
                            let temp_owl__x781 = { arc_clone(&owl_i2r_772) };
                            let owl__x781 = arc_clone(&temp_owl__x781);
                            let temp_owl__x782 = { arc_clone(&owl__x781) };
                            let owl__x782 = arc_clone(&temp_owl__x782);
                            let temp_owl__x785 = { arc_clone(&owl__x782) };
                            let owl__x785 = arc_clone(&temp_owl__x785);
                            let temp_owl__x786 = { arc_clone(&owl_pkt767) };
                            let owl__x786 = arc_clone(&temp_owl__x786);
                            let temp_owl__x787 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x787 = arc_new(temp_owl__x787);
                            let temp_owl__x788 = { arc_clone(&owl_ctr768) };
                            let owl__x788 = arc_clone(&temp_owl__x788);
                            (
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x785))),
                                    vec_as_slice(&(*arc_clone(&owl__x786))),
                                    vec_as_slice(&(*arc_clone(&owl__x787))),
                                    vec_as_slice(&(*arc_clone(&owl__x788))),
                                ),
                                Tracked(itree),
                            )
                        } else {
                            (None, Tracked(itree))
                        }
                    }
                }
            } else {
                let temp_owl__x766 = { None };
                let owl__x766 = temp_owl__x766;
                (owl__x766, Tracked(itree))
            }
        };
        Ok(res_inner)
    }
    
    #[verifier::spinoff_prover]
    pub fn owl_transp_send_resp(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_transp_keys_val12784: owl_transp_keys,
        owl_plaintext12783: Arc<Vec<u8>>,
        obuf: &mut [u8]
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_send_resp_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val12784.dview(),
                owl_plaintext12783.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(transp_send_resp_spec);
            let temp_owl__x878 = { owl_transp_keys_val12784 };
            let owl__x878 = temp_owl__x878;
            let parseval = owl__x878;
            let owl_transp_receiver809 = arc_new(parseval.owl__transp_keys_initiator);
            let owl__808 = arc_new(parseval.owl__transp_keys_responder);
            let owl_eph_init807 = arc_new(parseval.owl__transp_keys_init_ephemeral);
            let owl__806 = arc_new(parseval.owl__transp_keys_resp_ephemeral);
            let owl__805 = arc_new(parseval.owl__transp_keys_T_init_send);
            let owl_r2i_804 = arc_new(parseval.owl__transp_keys_T_resp_send);
            {
                let temp_owl__x814 = { arc_clone(&owl_r2i_804) };
                let owl__x814 = arc_clone(&temp_owl__x814);
                let temp_owl__x815 = { arc_clone(&owl__x814) };
                let owl__x815 = arc_clone(&temp_owl__x815);
                let temp_owl__x817 = { owl_counter_as_bytes(&(mut_state.owl_N_resp_send)) };
                let owl__x817 = arc_new(temp_owl__x817);
                let temp_owl__x821 = { owl_transp_tag_value() };
                let owl__x821 = arc_new(temp_owl__x821);
                let temp_owl__x822 = { arc_clone(&owl__x821) };
                let owl__x822 = arc_clone(&temp_owl__x822);
                let temp_owl__x873 = { arc_clone(&owl_transp_receiver809) };
                let owl__x873 = arc_clone(&temp_owl__x873);
                let temp_owl__x874 = { vec_length(&(*arc_clone(&owl__x873))) };
                let owl__x874 = temp_owl__x874;
                let temp_owl__x876 = { 4 };
                let owl__x876 = temp_owl__x876;
                let temp_owl__x877 = { owl__x874 == owl__x876 };
                let owl__x877 = temp_owl__x877;
                if owl__x877 {
                    let temp_owl__x828 = { arc_clone(&owl__x815) };
                    let owl__x828 = arc_clone(&temp_owl__x828);
                    let temp_owl__x830 = { arc_clone(&owl_plaintext12783) };
                    let owl__x830 = arc_clone(&temp_owl__x830);
                    let temp_owl__x832 = {
                        {
                            let x: Vec<u8> = mk_vec_u8![];
                            x
                        }
                    };
                    let owl__x832 = arc_new(temp_owl__x832);
                    let temp_owl__x833 = {
                        match owl_enc_st_aead(
                            vec_as_slice(&(*arc_clone(&owl__x828))),
                            vec_as_slice(&(*arc_clone(&owl__x830))),
                            &mut mut_state.owl_N_resp_send,
                            vec_as_slice(&(*arc_clone(&owl__x832))),
                        ) {
                            Ok(ctxt) => ctxt,
                            Err(e) => { return Err(e) },
                        }
                    };
                    let owl__x833 = arc_clone(&temp_owl__x833);
                    let temp_owl__x849 = { arc_clone(&owl__x822) };
                    let owl__x849 = arc_clone(&temp_owl__x849);
                    let temp_owl__x851 = { arc_clone(&owl_transp_receiver809) };
                    let owl__x851 = arc_clone(&temp_owl__x851);
                    let temp_owl__x853 = { arc_clone(&owl__x817) };
                    let owl__x853 = arc_clone(&temp_owl__x853);
                    let temp_owl__x855 = { arc_clone(&owl__x833) };
                    let owl__x855 = arc_clone(&temp_owl__x855);
                    let temp_owl__x857 = {
                    owl_transp {
                        owl__transp_tag: clone_vec_u8(&*arc_clone(&owl__x849)),
                        owl__transp_receiver: clone_vec_u8(&*arc_clone(&owl__x851)),
                        owl__transp_counter: clone_vec_u8(&*arc_clone(&owl__x853)),
                        owl__transp_packet: clone_vec_u8(&*arc_clone(&owl__x855)),
                    }
                    };
                    let owl__x857 = temp_owl__x857;
                    let temp_owl__x858 = { owl__x857 };
                    let owl__x858 = temp_owl__x858;
                    let temp_owl__x862 = { owl__x858 };
                    let owl__x862 = temp_owl__x862;
                    let temp_owl__x863 = {
                    owl_output::<(Option<()>, state_Responder)>(
                        Tracked(&mut itree),
                        vec_as_slice(&(serialize_owl_transp(&owl__x862))),
                        &Initiator_addr(),
                        &Responder_addr(),
                        obuf
                    )
                    };
                    let owl__x863 = temp_owl__x863;
                    let temp_owl__x866 = { () };
                    let owl__x866 = temp_owl__x866;
                    let temp_owl__x867 = { Some(owl__x866) };
                    let owl__x867 = temp_owl__x867;
                    (owl__x867, Tracked(itree))
                } else {
                    (None, Tracked(itree))
                }
            }
        };
        Ok(res_inner)
    }
    
    #[verifier::spinoff_prover]
    pub fn owl_generate_msg2(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_msg1_val_8311: owl_responder_msg1_val,
        obuf: &mut [u8]
    ) -> (res: Result<
        (owl_transp_keys, Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == generate_msg2_spec(*self, *old(mut_state), owl_msg1_val_8311.dview()),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview().as_seq(), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(generate_msg2_spec);
            let temp_owl__x1224 = { owl_msg1_val_8311 };
            let owl__x1224 = temp_owl__x1224;
            let temp_owl__x1223 = { owl__x1224 };
            let owl__x1223 = temp_owl__x1223;
            let parseval = owl__x1223;
            let owl_C3892 = arc_new(parseval.owl__responder_msg1_C3);
            let owl_H4891 = arc_new(parseval.owl__responder_msg1_H4);
            let owl_ephemeral_890 = arc_new(parseval.owl__responder_msg1_ephemeral);
            let owl_dhpk_S_init889 = arc_new(parseval.owl__responder_msg1_sender_pk);
            let owl_msg2_receiver888 = arc_new(parseval.owl__responder_msg1_sender);
            {
                let temp_owl__x897 = { arc_clone(&owl_ephemeral_890) };
                let owl__x897 = arc_clone(&temp_owl__x897);
                let temp_owl__x898 = { arc_clone(&owl__x897) };
                let owl__x898 = arc_clone(&temp_owl__x898);
                let temp_owl__x905 = { arc_clone(&self.owl_E_resp) };
                let owl__x905 = arc_clone(&temp_owl__x905);
                let temp_owl__x907 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x905)))) };
                let owl__x907 = arc_clone(&temp_owl__x907);
                let temp_owl__x908 = { arc_clone(&owl__x907) };
                let owl__x908 = arc_clone(&temp_owl__x908);
                let temp_owl__x912 = { owl_zeros_32() };
                let owl__x912 = arc_new(temp_owl__x912);
                let temp_owl__x913 = { arc_clone(&owl__x912) };
                let owl__x913 = arc_clone(&temp_owl__x913);
                let temp_owl__x918 = { arc_clone(&owl_C3892) };
                let owl__x918 = arc_clone(&temp_owl__x918);
                let temp_owl__x920 = { arc_clone(&owl__x908) };
                let owl__x920 = arc_clone(&temp_owl__x920);
                let owl_msg2_C41228 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x918))),
                    vec_as_slice(&(*arc_clone(&owl__x920))),
                );
                let temp_owl__x921 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C41228), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x921 = arc_clone(&temp_owl__x921);
                let temp_owl__x934 = { arc_clone(&owl_H4891) };
                let owl__x934 = arc_clone(&temp_owl__x934);
                let temp_owl__x936 = { arc_clone(&owl__x908) };
                let owl__x936 = arc_clone(&temp_owl__x936);
                let temp_owl__x938 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x934))),
                    vec_as_slice(&(*arc_clone(&owl__x936))),
                )
                };
                let owl__x938 = arc_new(temp_owl__x938);
                let temp_owl__x940 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x938)))) };
                let owl__x940 = arc_clone(&temp_owl__x940);
                let temp_owl__x941 = { arc_clone(&owl__x940) };
                let owl__x941 = arc_clone(&temp_owl__x941);
                let temp_owl__x951 = { arc_clone(&owl__x898) };
                let owl__x951 = arc_clone(&temp_owl__x951);
                let temp_owl__x953 = { arc_clone(&self.owl_E_resp) };
                let owl__x953 = arc_clone(&temp_owl__x953);
                let temp_owl__x955 = {
                owl_dh_combine(
                    vec_as_slice(&(*arc_clone(&owl__x951))),
                    vec_as_slice(&(*arc_clone(&owl__x953))),
                )
                };
                let owl__x955 = arc_clone(&temp_owl__x955);
                let temp_owl__x956 = { arc_clone(&owl__x955) };
                let owl__x956 = arc_clone(&temp_owl__x956);
                let temp_owl__x961 = { arc_clone(&owl__x921) };
                let owl__x961 = arc_clone(&temp_owl__x961);
                let temp_owl__x963 = { arc_clone(&owl__x956) };
                let owl__x963 = arc_clone(&temp_owl__x963);
                let owl_msg2_C51229 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x961))),
                    vec_as_slice(&(*arc_clone(&owl__x963))),
                );
                let temp_owl__x964 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C51229), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x964 = arc_clone(&temp_owl__x964);
                let temp_owl__x971 = { arc_clone(&owl__x964) };
                let owl__x971 = arc_clone(&temp_owl__x971);
                let temp_owl__x974 = { arc_clone(&owl_dhpk_S_init889) };
                let owl__x974 = arc_clone(&temp_owl__x974);
                let temp_owl__x976 = { arc_clone(&self.owl_E_resp) };
                let owl__x976 = arc_clone(&temp_owl__x976);
                let temp_owl__x977 = {
                owl_dh_combine(
                    vec_as_slice(&(*arc_clone(&owl__x974))),
                    vec_as_slice(&(*arc_clone(&owl__x976))),
                )
                };
                let owl__x977 = arc_clone(&temp_owl__x977);
                let owl_msg2_C61230 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x971))),
                    vec_as_slice(&(*arc_clone(&owl__x977))),
                );
                let temp_owl__x978 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C61230), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x978 = arc_clone(&temp_owl__x978);
                let temp_owl__x983 = { arc_clone(&owl__x978) };
                let owl__x983 = arc_clone(&temp_owl__x983);
                let temp_owl__x985 = { arc_clone(&owl__x913) };
                let owl__x985 = arc_clone(&temp_owl__x985);
                let owl_msg2_C71231 = owl_extract_expand_to_len(
                    0 + nonce_size() + nonce_size() + key_size(),
                    vec_as_slice(&(*arc_clone(&owl__x983))),
                    vec_as_slice(&(*arc_clone(&owl__x985))),
                );
                let temp_owl__x986 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C71231), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x986 = arc_clone(&temp_owl__x986);
                let temp_owl__x991 = { arc_clone(&owl__x978) };
                let owl__x991 = arc_clone(&temp_owl__x991);
                let temp_owl__x993 = { arc_clone(&owl__x913) };
                let owl__x993 = arc_clone(&temp_owl__x993);
                let temp_owl__x994 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_msg2_C71231),
                            0 + nonce_size(),
                            0 + nonce_size() + nonce_size(),
                        ),
                    ),
                )
                };
                let owl__x994 = arc_clone(&temp_owl__x994);
                let temp_owl__x999 = { arc_clone(&owl__x978) };
                let owl__x999 = arc_clone(&temp_owl__x999);
                let temp_owl__x1001 = { arc_clone(&owl__x913) };
                let owl__x1001 = arc_clone(&temp_owl__x1001);
                let temp_owl__x1002 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_msg2_C71231),
                            0 + nonce_size() + nonce_size(),
                            0 + nonce_size() + nonce_size() + key_size(),
                        ),
                    ),
                )
                };
                let owl__x1002 = arc_clone(&temp_owl__x1002);
                let temp_owl__x1015 = { arc_clone(&owl__x941) };
                let owl__x1015 = arc_clone(&temp_owl__x1015);
                let temp_owl__x1017 = { arc_clone(&owl__x994) };
                let owl__x1017 = arc_clone(&temp_owl__x1017);
                let temp_owl__x1019 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1015))),
                    vec_as_slice(&(*arc_clone(&owl__x1017))),
                )
                };
                let owl__x1019 = arc_new(temp_owl__x1019);
                let temp_owl__x1021 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x1019)))) };
                let owl__x1021 = arc_clone(&temp_owl__x1021);
                let temp_owl__x1022 = { arc_clone(&owl__x1021) };
                let owl__x1022 = arc_clone(&temp_owl__x1022);
                let temp_owl__x1026 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1026 = arc_new(temp_owl__x1026);
                let temp_owl__x1027 = { arc_clone(&owl__x1026) };
                let owl__x1027 = arc_clone(&temp_owl__x1027);
                let temp_owl__x1033 = { arc_clone(&owl__x1002) };
                let owl__x1033 = arc_clone(&temp_owl__x1033);
                let temp_owl__x1035 = { arc_clone(&owl__x1027) };
                let owl__x1035 = arc_clone(&temp_owl__x1035);
                let temp_owl__x1037 = { arc_clone(&owl__x1022) };
                let owl__x1037 = arc_clone(&temp_owl__x1037);
                let temp_owl__x1038 = {
                    match owl_enc_st_aead(
                        vec_as_slice(&(*arc_clone(&owl__x1033))),
                        vec_as_slice(&(*arc_clone(&owl__x1035))),
                        &mut mut_state.owl_aead_counter_msg2_C7,
                        vec_as_slice(&(*arc_clone(&owl__x1037))),
                    ) {
                        Ok(ctxt) => ctxt,
                        Err(e) => { return Err(e) },
                    }
                };
                let owl__x1038 = arc_clone(&temp_owl__x1038);
                let temp_owl__x1051 = { arc_clone(&owl__x1022) };
                let owl__x1051 = arc_clone(&temp_owl__x1051);
                let temp_owl__x1053 = { arc_clone(&owl__x1038) };
                let owl__x1053 = arc_clone(&temp_owl__x1053);
                let temp_owl__x1055 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1051))),
                    vec_as_slice(&(*arc_clone(&owl__x1053))),
                )
                };
                let owl__x1055 = arc_new(temp_owl__x1055);
                let temp_owl__x1057 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x1055)))) };
                let owl__x1057 = arc_clone(&temp_owl__x1057);
                let temp_owl__x1058 = { arc_clone(&owl__x1057) };
                let owl__x1058 = arc_clone(&temp_owl__x1058);
                let (temp_owl__x1060, Tracked(itree)): (
                    _,
                    Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
                ) = {
                    owl_call!( itree
, *mut_state
, get_sender_r_spec(*self, *mut_state)
, self.owl_get_sender_r(mut_state) )
                };
                let owl__x1060 = arc_clone(&temp_owl__x1060);
                let temp_owl__x1064 = { owl_msg2_tag_value() };
                let owl__x1064 = arc_new(temp_owl__x1064);
                let temp_owl__x1065 = { arc_clone(&owl__x1064) };
                let owl__x1065 = arc_clone(&temp_owl__x1065);
                let temp_owl__x1078 = { owl_mac1() };
                let owl__x1078 = arc_new(temp_owl__x1078);
                let temp_owl__x1080 = { arc_clone(&owl_dhpk_S_init889) };
                let owl__x1080 = arc_clone(&temp_owl__x1080);
                let temp_owl__x1082 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1078))),
                    vec_as_slice(&(*arc_clone(&owl__x1080))),
                )
                };
                let owl__x1082 = arc_new(temp_owl__x1082);
                let temp_owl__x1084 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x1082)))) };
                let owl__x1084 = arc_clone(&temp_owl__x1084);
                let temp_owl__x1085 = { arc_clone(&owl__x1084) };
                let owl__x1085 = arc_clone(&temp_owl__x1085);
                let temp_owl__x1098 = { arc_clone(&owl__x1085) };
                let owl__x1098 = arc_clone(&temp_owl__x1098);
                let temp_owl__x1104 = { arc_clone(&owl__x1065) };
                let owl__x1104 = arc_clone(&temp_owl__x1104);
                let temp_owl__x1106 = { arc_clone(&owl__x1060) };
                let owl__x1106 = arc_clone(&temp_owl__x1106);
                let temp_owl__x1107 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1104))),
                    vec_as_slice(&(*arc_clone(&owl__x1106))),
                )
                };
                let owl__x1107 = arc_new(temp_owl__x1107);
                let temp_owl__x1109 = { arc_clone(&owl_msg2_receiver888) };
                let owl__x1109 = arc_clone(&temp_owl__x1109);
                let temp_owl__x1110 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1107))),
                    vec_as_slice(&(*arc_clone(&owl__x1109))),
                )
                };
                let owl__x1110 = arc_new(temp_owl__x1110);
                let temp_owl__x1112 = { arc_clone(&owl__x908) };
                let owl__x1112 = arc_clone(&temp_owl__x1112);
                let temp_owl__x1113 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1110))),
                    vec_as_slice(&(*arc_clone(&owl__x1112))),
                )
                };
                let owl__x1113 = arc_new(temp_owl__x1113);
                let temp_owl__x1115 = { arc_clone(&owl__x1038) };
                let owl__x1115 = arc_clone(&temp_owl__x1115);
                let temp_owl__x1116 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1113))),
                    vec_as_slice(&(*arc_clone(&owl__x1115))),
                )
                };
                let owl__x1116 = arc_new(temp_owl__x1116);
                let temp_owl__x1117 = {
                owl_mac(
                    vec_as_slice(&(*arc_clone(&owl__x1098))),
                    vec_as_slice(&(*arc_clone(&owl__x1116))),
                )
                };
                let owl__x1117 = arc_clone(&temp_owl__x1117);
                let temp_owl__x1121 = { owl_zeros_16() };
                let owl__x1121 = arc_new(temp_owl__x1121);
                let temp_owl__x1122 = { arc_clone(&owl__x1121) };
                let owl__x1122 = arc_clone(&temp_owl__x1122);
                let temp_owl__x1147 = { arc_clone(&owl__x1065) };
                let owl__x1147 = arc_clone(&temp_owl__x1147);
                let temp_owl__x1149 = { arc_clone(&owl__x1060) };
                let owl__x1149 = arc_clone(&temp_owl__x1149);
                let temp_owl__x1151 = { arc_clone(&owl_msg2_receiver888) };
                let owl__x1151 = arc_clone(&temp_owl__x1151);
                let temp_owl__x1153 = { arc_clone(&owl__x908) };
                let owl__x1153 = arc_clone(&temp_owl__x1153);
                let temp_owl__x1155 = { arc_clone(&owl__x1038) };
                let owl__x1155 = arc_clone(&temp_owl__x1155);
                let temp_owl__x1157 = { arc_clone(&owl__x1117) };
                let owl__x1157 = arc_clone(&temp_owl__x1157);
                let temp_owl__x1159 = { arc_clone(&owl__x1122) };
                let owl__x1159 = arc_clone(&temp_owl__x1159);
                let temp_owl__x1161 = {
                owl_msg2 {
                    owl__msg2_tag: clone_vec_u8(&*arc_clone(&owl__x1147)),
                    owl__msg2_sender: clone_vec_u8(&*arc_clone(&owl__x1149)),
                    owl__msg2_receiver: clone_vec_u8(&*arc_clone(&owl__x1151)),
                    owl__msg2_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1153)),
                    owl__msg2_empty: clone_vec_u8(&*arc_clone(&owl__x1155)),
                    owl__msg2_mac1: clone_vec_u8(&*arc_clone(&owl__x1157)),
                    owl__msg2_mac2: clone_vec_u8(&*arc_clone(&owl__x1159)),
                }
                };
                let owl__x1161 = temp_owl__x1161;
                let temp_owl__x1162 = { owl__x1161 };
                let owl__x1162 = temp_owl__x1162;
                let temp_owl__x1166 = { owl__x1162 };
                let owl__x1166 = temp_owl__x1166;
                let temp_owl__x1167 = {
                owl_output::<(Seq<u8>, state_Responder)>(
                    Tracked(&mut itree),
                    vec_as_slice(&(serialize_owl_msg2(&owl__x1166))),
                    &Initiator_addr(),
                    &Responder_addr(),
                    obuf
                )
                };
                let owl__x1167 = temp_owl__x1167;
                let temp_owl__x1172 = { arc_clone(&owl__x986) };
                let owl__x1172 = arc_clone(&temp_owl__x1172);
                let temp_owl__x1174 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1174 = arc_new(temp_owl__x1174);
                let owl_transp_T1232 = owl_extract_expand_to_len(
                    0 + key_size() + key_size(),
                    vec_as_slice(&(*arc_clone(&owl__x1172))),
                    vec_as_slice(&(*arc_clone(&owl__x1174))),
                );
                let temp_owl__x1175 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_transp_T1232), 0, 0 + key_size()),
                    ),
                )
                };
                let owl__x1175 = arc_clone(&temp_owl__x1175);
                let temp_owl__x1180 = { arc_clone(&owl__x986) };
                let owl__x1180 = arc_clone(&temp_owl__x1180);
                let temp_owl__x1182 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1182 = arc_new(temp_owl__x1182);
                let temp_owl__x1183 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_transp_T1232),
                            0 + key_size(),
                            0 + key_size() + key_size(),
                        ),
                    ),
                )
                };
                let owl__x1183 = arc_clone(&temp_owl__x1183);
                let temp_owl__x1205 = { arc_clone(&owl_msg2_receiver888) };
                let owl__x1205 = arc_clone(&temp_owl__x1205);
                let temp_owl__x1207 = { arc_clone(&owl__x1060) };
                let owl__x1207 = arc_clone(&temp_owl__x1207);
                let temp_owl__x1209 = { arc_clone(&owl__x898) };
                let owl__x1209 = arc_clone(&temp_owl__x1209);
                let temp_owl__x1211 = { arc_clone(&owl__x908) };
                let owl__x1211 = arc_clone(&temp_owl__x1211);
                let temp_owl__x1213 = { arc_clone(&owl__x1175) };
                let owl__x1213 = arc_clone(&temp_owl__x1213);
                let temp_owl__x1215 = { arc_clone(&owl__x1183) };
                let owl__x1215 = arc_clone(&temp_owl__x1215);
                let temp_owl__x1217 = {
                owl_transp_keys {
                    owl__transp_keys_initiator: clone_vec_u8(&*arc_clone(&owl__x1205)),
                    owl__transp_keys_responder: clone_vec_u8(&*arc_clone(&owl__x1207)),
                    owl__transp_keys_init_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1209)),
                    owl__transp_keys_resp_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1211)),
                    owl__transp_keys_T_init_send: clone_vec_u8(&*arc_clone(&owl__x1213)),
                    owl__transp_keys_T_resp_send: clone_vec_u8(&*arc_clone(&owl__x1215)),
                }
                };
                let owl__x1217 = temp_owl__x1217;
                let temp_owl__x1218 = { owl__x1217 };
                let owl__x1218 = temp_owl__x1218;
                let temp_owl__x1221 = { owl__x1218 };
                let owl__x1221 = temp_owl__x1221;
                let temp_owl__x1222 = { owl__x1221 };
                let owl__x1222 = temp_owl__x1222;
                (owl__x1222, Tracked(itree))
            }
        };
        Ok(res_inner)
    }
    
    #[verifier::spinoff_prover]
    pub fn owl_receive_msg1(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        ibuf: &[u8]
    ) -> (res: Result<
        (
            Option<owl_responder_msg1_val>,
            Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == receive_msg1_spec(*self, *old(mut_state)),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (option_as_seq(dview_option(res.get_Ok_0().0)), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(receive_msg1_spec);
            let (temp_owl_inp1241, owl__1240) = owl_input::<(Option<Seq<u8>>, state_Responder)>(
                Tracked(&mut itree),
                ibuf
            );
            let owl_inp1241 = arc_new(temp_owl_inp1241);
            let temp_owl__x1551 = { arc_clone(&owl_inp1241) };
            let owl__x1551 = arc_clone(&temp_owl__x1551);
            if let Some(parseval) = parse_owl_msg1(vec_as_slice(&(*arc_clone(&owl__x1551)))) {
                let owl_msg1_tag1249 = arc_new(parseval.owl__msg1_tag);
                let owl_msg1_sender1248 = arc_new(parseval.owl__msg1_sender);
                let owl_msg1_ephemeral_1247 = arc_new(parseval.owl__msg1_ephemeral);
                let owl_msg1_static1246 = arc_new(parseval.owl__msg1_static);
                let owl_msg1_timestamp1245 = arc_new(parseval.owl__msg1_timestamp);
                let owl_msg1_mac11244 = arc_new(parseval.owl__msg1_mac1);
                let owl_msg1_mac21243 = arc_new(parseval.owl__msg1_mac2);
                {
                    let temp_owl__x1546 = { arc_clone(&owl_msg1_sender1248) };
                    let owl__x1546 = arc_clone(&temp_owl__x1546);
                    let temp_owl__x1547 = { vec_length(&(*arc_clone(&owl__x1546))) };
                    let owl__x1547 = temp_owl__x1547;
                    let temp_owl__x1549 = { 4 };
                    let owl__x1549 = temp_owl__x1549;
                    let temp_owl__x1550 = { owl__x1547 == owl__x1549 };
                    let owl__x1550 = temp_owl__x1550;
                    if owl__x1550 {
                        let temp_owl__x1539 = { arc_clone(&owl_msg1_ephemeral_1247) };
                        let owl__x1539 = arc_clone(&temp_owl__x1539);
                        let temp_owl__x1540 = {
                        owl_is_group_elem(vec_as_slice(&(*arc_clone(&owl__x1539))))
                        };
                        let owl__x1540 = temp_owl__x1540;
                        if owl__x1540 {
                            let temp_owl__x1256 = { owl_construction() };
                            let owl__x1256 = arc_new(temp_owl__x1256);
                            let temp_owl__x1258 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1256))))
                            };
                            let owl__x1258 = arc_clone(&temp_owl__x1258);
                            let temp_owl__x1259 = { arc_clone(&owl__x1258) };
                            let owl__x1259 = arc_clone(&temp_owl__x1259);
                            let temp_owl__x1272 = { arc_clone(&owl__x1259) };
                            let owl__x1272 = arc_clone(&temp_owl__x1272);
                            let temp_owl__x1274 = { owl_identifier() };
                            let owl__x1274 = arc_new(temp_owl__x1274);
                            let temp_owl__x1276 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1272))),
                                vec_as_slice(&(*arc_clone(&owl__x1274))),
                            )
                            };
                            let owl__x1276 = arc_new(temp_owl__x1276);
                            let temp_owl__x1278 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1276))))
                            };
                            let owl__x1278 = arc_clone(&temp_owl__x1278);
                            let temp_owl__x1279 = { arc_clone(&owl__x1278) };
                            let owl__x1279 = arc_clone(&temp_owl__x1279);
                            let temp_owl__x1295 = { arc_clone(&owl__x1279) };
                            let owl__x1295 = arc_clone(&temp_owl__x1295);
                            let temp_owl__x1297 = { arc_clone(&self.owl_S_resp) };
                            let owl__x1297 = arc_clone(&temp_owl__x1297);
                            let temp_owl__x1299 = {
                            owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x1297))))
                            };
                            let owl__x1299 = arc_clone(&temp_owl__x1299);
                            let temp_owl__x1301 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1295))),
                                vec_as_slice(&(*arc_clone(&owl__x1299))),
                            )
                            };
                            let owl__x1301 = arc_new(temp_owl__x1301);
                            let temp_owl__x1303 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1301))))
                            };
                            let owl__x1303 = arc_clone(&temp_owl__x1303);
                            let temp_owl__x1304 = { arc_clone(&owl__x1303) };
                            let owl__x1304 = arc_clone(&temp_owl__x1304);
                            let temp_owl__x1310 = { arc_clone(&owl_msg1_ephemeral_1247) };
                            let owl__x1310 = arc_clone(&temp_owl__x1310);
                            let temp_owl__x1311 = { arc_clone(&owl__x1310) };
                            let owl__x1311 = arc_clone(&temp_owl__x1311);
                            let temp_owl__x1316 = { arc_clone(&owl__x1259) };
                            let owl__x1316 = arc_clone(&temp_owl__x1316);
                            let temp_owl__x1318 = { arc_clone(&owl__x1311) };
                            let owl__x1318 = arc_clone(&temp_owl__x1318);
                            let owl_msg1_C11559 = owl_extract_expand_to_len(
                                0 + nonce_size(),
                                vec_as_slice(&(*arc_clone(&owl__x1316))),
                                vec_as_slice(&(*arc_clone(&owl__x1318))),
                            );
                            let temp_owl__x1319 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C11559),
                                        0,
                                        0 + nonce_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1319 = arc_clone(&temp_owl__x1319);
                            let temp_owl__x1332 = { arc_clone(&owl__x1304) };
                            let owl__x1332 = arc_clone(&temp_owl__x1332);
                            let temp_owl__x1334 = { arc_clone(&owl__x1311) };
                            let owl__x1334 = arc_clone(&temp_owl__x1334);
                            let temp_owl__x1336 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1332))),
                                vec_as_slice(&(*arc_clone(&owl__x1334))),
                            )
                            };
                            let owl__x1336 = arc_new(temp_owl__x1336);
                            let temp_owl__x1338 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1336))))
                            };
                            let owl__x1338 = arc_clone(&temp_owl__x1338);
                            let temp_owl__x1339 = { arc_clone(&owl__x1338) };
                            let owl__x1339 = arc_clone(&temp_owl__x1339);
                            let temp_owl__x1349 = { arc_clone(&owl__x1311) };
                            let owl__x1349 = arc_clone(&temp_owl__x1349);
                            let temp_owl__x1351 = { arc_clone(&self.owl_S_resp) };
                            let owl__x1351 = arc_clone(&temp_owl__x1351);
                            let temp_owl__x1353 = {
                            owl_dh_combine(
                                vec_as_slice(&(*arc_clone(&owl__x1349))),
                                vec_as_slice(&(*arc_clone(&owl__x1351))),
                            )
                            };
                            let owl__x1353 = arc_clone(&temp_owl__x1353);
                            let temp_owl__x1354 = { arc_clone(&owl__x1353) };
                            let owl__x1354 = arc_clone(&temp_owl__x1354);
                            let temp_owl__x1359 = { arc_clone(&owl__x1319) };
                            let owl__x1359 = arc_clone(&temp_owl__x1359);
                            let temp_owl__x1361 = { arc_clone(&owl__x1354) };
                            let owl__x1361 = arc_clone(&temp_owl__x1361);
                            let owl_msg1_C21560 = owl_extract_expand_to_len(
                                0 + nonce_size() + key_size(),
                                vec_as_slice(&(*arc_clone(&owl__x1359))),
                                vec_as_slice(&(*arc_clone(&owl__x1361))),
                            );
                            let temp_owl__x1362 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C21560),
                                        0,
                                        0 + nonce_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1362 = arc_clone(&temp_owl__x1362);
                            let temp_owl__x1367 = { arc_clone(&owl__x1319) };
                            let owl__x1367 = arc_clone(&temp_owl__x1367);
                            let temp_owl__x1369 = { arc_clone(&owl__x1354) };
                            let owl__x1369 = arc_clone(&temp_owl__x1369);
                            let temp_owl__x1370 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C21560),
                                        0 + nonce_size(),
                                        0 + nonce_size() + key_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1370 = arc_clone(&temp_owl__x1370);
                            let temp_owl__x1529 = { arc_clone(&owl__x1370) };
                            let owl__x1529 = arc_clone(&temp_owl__x1529);
                            let temp_owl__x1531 = { arc_clone(&owl_msg1_static1246) };
                            let owl__x1531 = arc_clone(&temp_owl__x1531);
                            let temp_owl__x1533 = { arc_clone(&owl__x1339) };
                            let owl__x1533 = arc_clone(&temp_owl__x1533);
                            let temp_owl__x1535 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x1535 = arc_new(temp_owl__x1535);
                            let temp_owl__x1536 = {
                            owl_dec_st_aead(
                                vec_as_slice(&(*arc_clone(&owl__x1529))),
                                vec_as_slice(&(*arc_clone(&owl__x1531))),
                                vec_as_slice(&(*arc_clone(&owl__x1533))),
                                vec_as_slice(&(*arc_clone(&owl__x1535))),
                            )
                            };
                            let owl__x1536 = temp_owl__x1536;
                            let temp_owl_caseval1558 = { owl__x1536 };
                            let owl_caseval1558 = temp_owl_caseval1558;
                            match owl_caseval1558 {
                                None => {
                                    let temp_owl__x1375 = { None };
                                    let owl__x1375 = temp_owl__x1375;
                                    (owl__x1375, Tracked(itree))
                                },
                                Some(temp_owl_msg1_static_dec1376) => {
                                    let owl_msg1_static_dec1376 = arc_clone(
                                        &temp_owl_msg1_static_dec1376,
                                    );
                                    let temp_owl__x1380 = { arc_clone(&owl_msg1_static_dec1376) };
                                    let owl__x1380 = arc_clone(&temp_owl__x1380);
                                    let (temp_owl__x1381, Tracked(itree)): (
                                        _,
                                        Tracked<
                                            ITreeToken<
                                                (Option<Seq<u8>>, state_Responder),
                                                Endpoint,
                                            >,
                                        >,
                                    ) = {
                                        owl_call_ret_option!( itree
, *mut_state
, checkpk_resp_spec(*self, *mut_state, (&owl__x1380).dview())
, self.owl_checkpk_resp(mut_state, arc_clone(&owl__x1380)) )
                                    };
                                    let owl__x1381 = temp_owl__x1381;
                                    let temp_owl__x1526 = { owl__x1381 };
                                    let owl__x1526 = temp_owl__x1526;
                                    let temp_owl__x1527 = { owl__x1526 };
                                    let owl__x1527 = temp_owl__x1527;
                                    let temp_owl_caseval1557 = { owl__x1527 };
                                    let owl_caseval1557 = temp_owl_caseval1557;
                                    match owl_caseval1557 {
                                        None => {
                                            let temp_owl__x1383 = { None };
                                            let owl__x1383 = temp_owl__x1383;
                                            (owl__x1383, Tracked(itree))
                                        },
                                        Some(temp_owl_dhpk_S_init_1384) => {
                                            let owl_dhpk_S_init_1384 = arc_clone(
                                                &temp_owl_dhpk_S_init_1384,
                                            );
                                            let temp_owl__x1524 = { arc_clone(&owl_dhpk_S_init_1384)
                                            };
                                            let owl__x1524 = arc_clone(&temp_owl__x1524);
                                            let temp_owl__x1520 = {
                                            arc_clone(&owl_msg1_static_dec1376)
                                            };
                                            let owl__x1520 = arc_clone(&temp_owl__x1520);
                                            let temp_owl__x1522 = { arc_clone(&owl__x1524) };
                                            let owl__x1522 = arc_clone(&temp_owl__x1522);
                                            let temp_owl__x1523 = {
                                            rc_vec_eq(
                                                &arc_clone(&owl__x1520),
                                                &arc_clone(&owl__x1522),
                                            )
                                            };
                                            let owl__x1523 = temp_owl__x1523;
                                            if owl__x1523 {
                                                let temp_owl__x1399 = { arc_clone(&owl__x1339) };
                                                let owl__x1399 = arc_clone(&temp_owl__x1399);
                                                let temp_owl__x1401 = {
                                                arc_clone(&owl_msg1_static1246)
                                                };
                                                let owl__x1401 = arc_clone(&temp_owl__x1401);
                                                let temp_owl__x1403 = {
                                                owl_concat(
                                                    vec_as_slice(&(*arc_clone(&owl__x1399))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1401))),
                                                )
                                                };
                                                let owl__x1403 = arc_new(temp_owl__x1403);
                                                let temp_owl__x1405 = {
                                                owl_crh(vec_as_slice(&(*arc_clone(&owl__x1403))))
                                                };
                                                let owl__x1405 = arc_clone(&temp_owl__x1405);
                                                let temp_owl__x1406 = { arc_clone(&owl__x1405) };
                                                let owl__x1406 = arc_clone(&temp_owl__x1406);
                                                let temp_owl__x1416 = { arc_clone(&owl__x1524) };
                                                let owl__x1416 = arc_clone(&temp_owl__x1416);
                                                let temp_owl__x1418 = { arc_clone(&self.owl_S_resp)
                                                };
                                                let owl__x1418 = arc_clone(&temp_owl__x1418);
                                                let temp_owl__x1420 = {
                                                owl_dh_combine(
                                                    vec_as_slice(&(*arc_clone(&owl__x1416))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1418))),
                                                )
                                                };
                                                let owl__x1420 = arc_clone(&temp_owl__x1420);
                                                let temp_owl__x1421 = { arc_clone(&owl__x1420) };
                                                let owl__x1421 = arc_clone(&temp_owl__x1421);
                                                let temp_owl__x1426 = { arc_clone(&owl__x1362) };
                                                let owl__x1426 = arc_clone(&temp_owl__x1426);
                                                let temp_owl__x1428 = { arc_clone(&owl__x1421) };
                                                let owl__x1428 = arc_clone(&temp_owl__x1428);
                                                let owl_msg1_C31561 = owl_extract_expand_to_len(
                                                    0 + nonce_size() + key_size(),
                                                    vec_as_slice(&(*arc_clone(&owl__x1426))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1428))),
                                                );
                                                let temp_owl__x1429 = {
                                                arc_new(
                                                    slice_to_vec(
                                                        slice_subrange(
                                                            vec_as_slice(&*owl_msg1_C31561),
                                                            0,
                                                            0 + nonce_size(),
                                                        ),
                                                    ),
                                                )
                                                };
                                                let owl__x1429 = arc_clone(&temp_owl__x1429);
                                                let temp_owl__x1434 = { arc_clone(&owl__x1362) };
                                                let owl__x1434 = arc_clone(&temp_owl__x1434);
                                                let temp_owl__x1436 = { arc_clone(&owl__x1421) };
                                                let owl__x1436 = arc_clone(&temp_owl__x1436);
                                                let temp_owl__x1437 = {
                                                arc_new(
                                                    slice_to_vec(
                                                        slice_subrange(
                                                            vec_as_slice(&*owl_msg1_C31561),
                                                            0 + nonce_size(),
                                                            0 + nonce_size() + key_size(),
                                                        ),
                                                    ),
                                                )
                                                };
                                                let owl__x1437 = arc_clone(&temp_owl__x1437);
                                                let temp_owl__x1509 = { arc_clone(&owl__x1437) };
                                                let owl__x1509 = arc_clone(&temp_owl__x1509);
                                                let temp_owl__x1511 = {
                                                arc_clone(&owl_msg1_timestamp1245)
                                                };
                                                let owl__x1511 = arc_clone(&temp_owl__x1511);
                                                let temp_owl__x1513 = { arc_clone(&owl__x1406) };
                                                let owl__x1513 = arc_clone(&temp_owl__x1513);
                                                let temp_owl__x1515 = {
                                                    {
                                                        let x: Vec<u8> = mk_vec_u8![];
                                                        x
                                                    }
                                                };
                                                let owl__x1515 = arc_new(temp_owl__x1515);
                                                let temp_owl__x1516 = {
                                                owl_dec_st_aead(
                                                    vec_as_slice(&(*arc_clone(&owl__x1509))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1511))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1513))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1515))),
                                                )
                                                };
                                                let owl__x1516 = temp_owl__x1516;
                                                let temp_owl_caseval1556 = { owl__x1516 };
                                                let owl_caseval1556 = temp_owl_caseval1556;
                                                match owl_caseval1556 {
                                                    None => {
                                                        let temp_owl__x1442 = { None };
                                                        let owl__x1442 = temp_owl__x1442;
                                                        (owl__x1442, Tracked(itree))
                                                    },
                                                    Some(temp_owl_msg1_timestamp_dec1443) => {
                                                        let owl_msg1_timestamp_dec1443 = arc_clone(
                                                            &temp_owl_msg1_timestamp_dec1443,
                                                        );
                                                        let temp_owl__x1456 = {
                                                        arc_clone(&owl__x1406)
                                                        };
                                                        let owl__x1456 = arc_clone(
                                                            &temp_owl__x1456,
                                                        );
                                                        let temp_owl__x1458 = {
                                                        arc_clone(&owl_msg1_timestamp_dec1443)
                                                        };
                                                        let owl__x1458 = arc_clone(
                                                            &temp_owl__x1458,
                                                        );
                                                        let temp_owl__x1460 = {
                                                        owl_concat(
                                                            vec_as_slice(
                                                                &(*arc_clone(&owl__x1456)),
                                                            ),
                                                            vec_as_slice(
                                                                &(*arc_clone(&owl__x1458)),
                                                            ),
                                                        )
                                                        };
                                                        let owl__x1460 = arc_new(temp_owl__x1460);
                                                        let temp_owl__x1462 = {
                                                        owl_crh(
                                                            vec_as_slice(
                                                                &(*arc_clone(&owl__x1460)),
                                                            ),
                                                        )
                                                        };
                                                        let owl__x1462 = arc_clone(
                                                            &temp_owl__x1462,
                                                        );
                                                        let temp_owl__x1463 = {
                                                        arc_clone(&owl__x1462)
                                                        };
                                                        let owl__x1463 = arc_clone(
                                                            &temp_owl__x1463,
                                                        );
                                                        let temp_owl__x1482 = {
                                                        arc_clone(&owl__x1429)
                                                        };
                                                        let owl__x1482 = arc_clone(
                                                            &temp_owl__x1482,
                                                        );
                                                        let temp_owl__x1484 = {
                                                        arc_clone(&owl__x1463)
                                                        };
                                                        let owl__x1484 = arc_clone(
                                                            &temp_owl__x1484,
                                                        );
                                                        let temp_owl__x1486 = {
                                                        arc_clone(&owl__x1311)
                                                        };
                                                        let owl__x1486 = arc_clone(
                                                            &temp_owl__x1486,
                                                        );
                                                        let temp_owl__x1488 = {
                                                        arc_clone(&owl__x1524)
                                                        };
                                                        let owl__x1488 = arc_clone(
                                                            &temp_owl__x1488,
                                                        );
                                                        let temp_owl__x1490 = {
                                                        arc_clone(&owl_msg1_sender1248)
                                                        };
                                                        let owl__x1490 = arc_clone(
                                                            &temp_owl__x1490,
                                                        );
                                                        let temp_owl__x1492 = {
                                                        owl_responder_msg1_val {
                                                            owl__responder_msg1_C3: clone_vec_u8(
                                                                &*arc_clone(&owl__x1482),
                                                            ),
                                                            owl__responder_msg1_H4: clone_vec_u8(
                                                                &*arc_clone(&owl__x1484),
                                                            ),
                                                            owl__responder_msg1_ephemeral:
                                                                clone_vec_u8(
                                                                &*arc_clone(&owl__x1486),
                                                            ),
                                                            owl__responder_msg1_sender_pk:
                                                                clone_vec_u8(
                                                                &*arc_clone(&owl__x1488),
                                                            ),
                                                            owl__responder_msg1_sender:
                                                                clone_vec_u8(
                                                                &*arc_clone(&owl__x1490),
                                                            ),
                                                        }
                                                        };
                                                        let owl__x1492 = temp_owl__x1492;
                                                        let temp_owl__x1493 = { owl__x1492 };
                                                        let owl__x1493 = temp_owl__x1493;
                                                        let temp_owl__x1500 = { owl__x1493 };
                                                        let owl__x1500 = temp_owl__x1500;
                                                        let temp_owl__x1502 = { owl__x1500 };
                                                        let owl__x1502 = temp_owl__x1502;
                                                        let temp_owl__x1503 = { owl__x1502 };
                                                        let owl__x1503 = temp_owl__x1503;
                                                        let temp_owl__x1506 = { owl__x1503 };
                                                        let owl__x1506 = temp_owl__x1506;
                                                        let temp_owl__x1507 = { Some(owl__x1506) };
                                                        let owl__x1507 = temp_owl__x1507;
                                                        (owl__x1507, Tracked(itree))
                                                    },
                                                }
                                            } else {
                                                (None, Tracked(itree))
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
                let temp_owl__x1242 = { None };
                let owl__x1242 = temp_owl__x1242;
                (owl__x1242, Tracked(itree))
            }
        };
        Ok(res_inner)
    }
    
    #[verifier(external_body)]
    #[verifier::spinoff_prover]
    pub fn owl_checkpk_resp(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_pk8134: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<Arc<Vec<u8>>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == checkpk_resp_spec(*self, *old(mut_state), owl_pk8134.dview()),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            use x25519_dalek::{PublicKey};
            use std::convert::TryInto;

            let pk: [u8; 32] = (&*owl_pk8134).as_slice().try_into().unwrap();
            let peer_pk = if self.device.has_pk(&pk) {
                    Some(arc_new(pk.to_vec()))
            } else {
                None
            };
            
            (peer_pk, Tracked(itree))

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
        (Arc<Vec<u8>>, Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == timestamp_r_spec(*self, *old(mut_state)),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview(), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let t = crate::wireguard::handshake::timestamp::now().to_vec();
            (arc_new(t), Tracked(itree))
        };
        Ok(res_inner)
    }
    
    #[verifier(external_body)]
    #[verifier::spinoff_prover]
    pub fn owl_get_sender_r(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
    ) -> (res: Result<
        (Arc<Vec<u8>>, Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == get_sender_r_spec(*self, *old(mut_state)),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview(), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            todo!(/* implement owl_get_sender_r */)
        };
        Ok(res_inner)
    }
}

// ------------------------------------
// ------ USER-DEFINED FUNCTIONS ------
// ------------------------------------
#[verifier::opaque]
pub closed spec fn construction() -> Seq<u8> {
    seq![0x4eu8, 0x6fu8, 0x69u8, 0x73u8, 0x65u8, 0x5fu8, 0x49u8, 0x4bu8, 0x70u8, 0x73u8, 0x6bu8, 0x32u8, 0x5fu8, 0x32u8, 0x35u8, 0x35u8, 0x31u8, 0x39u8, 0x5fu8, 0x43u8, 0x68u8, 0x61u8, 0x43u8, 0x68u8, 0x61u8, 0x50u8, 0x6fu8, 0x6cu8, 0x79u8, 0x5fu8, 0x42u8, 0x4cu8, 0x41u8, 0x4bu8, 0x45u8, 0x32u8, 0x73u8, ]
}

pub exec fn owl_construction() -> (res: Vec<u8>)
    ensures
        res.dview() == construction(),
{
    reveal(construction);
    {
        let x: Vec<u8> =
            mk_vec_u8![0x4eu8, 0x6fu8, 0x69u8, 0x73u8, 0x65u8, 0x5fu8, 0x49u8, 0x4bu8, 0x70u8, 0x73u8, 0x6bu8, 0x32u8, 0x5fu8, 0x32u8, 0x35u8, 0x35u8, 0x31u8, 0x39u8, 0x5fu8, 0x43u8, 0x68u8, 0x61u8, 0x43u8, 0x68u8, 0x61u8, 0x50u8, 0x6fu8, 0x6cu8, 0x79u8, 0x5fu8, 0x42u8, 0x4cu8, 0x41u8, 0x4bu8, 0x45u8, 0x32u8, 0x73u8, ];
        x
    }
}

#[verifier::opaque]
pub closed spec fn identifier() -> Seq<u8> {
    seq![0x57u8, 0x69u8, 0x72u8, 0x65u8, 0x47u8, 0x75u8, 0x61u8, 0x72u8, 0x64u8, 0x20u8, 0x76u8, 0x31u8, 0x20u8, 0x7au8, 0x78u8, 0x32u8, 0x63u8, 0x34u8, 0x20u8, 0x4au8, 0x61u8, 0x73u8, 0x6fu8, 0x6eu8, 0x40u8, 0x7au8, 0x78u8, 0x32u8, 0x63u8, 0x34u8, 0x2eu8, 0x63u8, 0x6fu8, 0x6du8, ]
}

pub exec fn owl_identifier() -> (res: Vec<u8>)
    ensures
        res.dview() == identifier(),
{
    reveal(identifier);
    {
        let x: Vec<u8> =
            mk_vec_u8![0x57u8, 0x69u8, 0x72u8, 0x65u8, 0x47u8, 0x75u8, 0x61u8, 0x72u8, 0x64u8, 0x20u8, 0x76u8, 0x31u8, 0x20u8, 0x7au8, 0x78u8, 0x32u8, 0x63u8, 0x34u8, 0x20u8, 0x4au8, 0x61u8, 0x73u8, 0x6fu8, 0x6eu8, 0x40u8, 0x7au8, 0x78u8, 0x32u8, 0x63u8, 0x34u8, 0x2eu8, 0x63u8, 0x6fu8, 0x6du8, ];
        x
    }
}

#[verifier::opaque]
pub closed spec fn mac1() -> Seq<u8> {
    seq![0x6du8, 0x61u8, 0x63u8, 0x31u8, 0x2du8, 0x2du8, 0x2du8, 0x2du8, ]
}

pub exec fn owl_mac1() -> (res: Vec<u8>)
    ensures
        res.dview() == mac1(),
{
    reveal(mac1);
    {
        let x: Vec<u8> =
            mk_vec_u8![0x6du8, 0x61u8, 0x63u8, 0x31u8, 0x2du8, 0x2du8, 0x2du8, 0x2du8, ];
        x
    }
}

#[verifier::opaque]
pub closed spec fn msg1_tag_value() -> Seq<u8> {
    seq![0x01u8, 0x00u8, 0x00u8, 0x00u8, ]
}

pub exec fn owl_msg1_tag_value() -> (res: Vec<u8>)
    ensures
        res.dview() == msg1_tag_value(),
{
    reveal(msg1_tag_value);
    {
        let x: Vec<u8> = mk_vec_u8![0x01u8, 0x00u8, 0x00u8, 0x00u8, ];
        x
    }
}

#[verifier::opaque]
pub closed spec fn msg2_tag_value() -> Seq<u8> {
    seq![0x02u8, 0x00u8, 0x00u8, 0x00u8, ]
}

pub exec fn owl_msg2_tag_value() -> (res: Vec<u8>)
    ensures
        res.dview() == msg2_tag_value(),
{
    reveal(msg2_tag_value);
    {
        let x: Vec<u8> = mk_vec_u8![0x02u8, 0x00u8, 0x00u8, 0x00u8, ];
        x
    }
}

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

#[verifier::opaque]
pub closed spec fn zeros_16() -> Seq<u8> {
    seq![0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, ]
}

pub exec fn owl_zeros_16() -> (res: Vec<u8>)
    ensures
        res.dview() == zeros_16(),
{
    reveal(zeros_16);
    {
        let x: Vec<u8> =
            mk_vec_u8![0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, ];
        x
    }
}

#[verifier::opaque]
pub closed spec fn zeros_32() -> Seq<u8> {
    seq![0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, ]
}

pub exec fn owl_zeros_32() -> (res: Vec<u8>)
    ensures
        res.dview() == zeros_32(),
{
    reveal(zeros_32);
    {
        let x: Vec<u8> =
            mk_vec_u8![0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, ];
        x
    }
}
// ------------------------------------
// ------------ ENTRY POINT -----------
// ------------------------------------
// no entry point

} // verus!


