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

#[verifier::opaque]
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
(ret(dec_st_aead(r2i, pkt, ctr, empty_seq_u8())))) else ((ret (Option::None))))
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
(input (inp, _unused410)) in
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
, e_init_pk
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
    dhpk_S_init: Seq<u8>,
    ss_S_resp_S_init: Seq<u8>,
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
, dhpk_S_init
, owl_aead_counter_msg1_C2
, H2 )))) in
let H3 = ((ret (crh(concat(H2, msg1_static))))) in
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
pub open spec fn transp_recv_resp_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    transp_keys_val: owlSpec_transp_keys,
    c: Seq<u8>,
) -> (res: ITree<(Option<Seq<u8>>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(parse (parse_owlSpec_transp(c)) as (owlSpec_transp{owlSpec__transp_tag : _unused776 , owlSpec__transp_receiver : from , owlSpec__transp_counter : ctr , owlSpec__transp_packet : pkt }) in {
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : initiator_name , owlSpec__transp_keys_responder : _unused777 , owlSpec__transp_keys_init_ephemeral : eph_init , owlSpec__transp_keys_resp_ephemeral : _unused778 , owlSpec__transp_keys_T_init_send : i2r_ , owlSpec__transp_keys_T_resp_send : _unused779 }) in {
(if (c == initiator_name) then (let i2r = ((ret (i2r_))) in
(ret(dec_st_aead(i2r, pkt, ctr, empty_seq_u8())))) else ((ret (Option::None))))
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
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : transp_receiver , owlSpec__transp_keys_responder : _unused857 , owlSpec__transp_keys_init_ephemeral : eph_init , owlSpec__transp_keys_resp_ephemeral : _unused858 , owlSpec__transp_keys_T_init_send : _unused859 , owlSpec__transp_keys_T_resp_send : r2i_ }) in {
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
pub open spec fn receive_msg1_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    dhpk_S_resp: Seq<u8>,
) -> (res: ITree<(Option<Seq<u8>>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(input (inp, _unused1517)) in
(parse (parse_owlSpec_msg1(inp)) as (owlSpec_msg1{owlSpec__msg1_tag : msg1_tag , owlSpec__msg1_sender : msg1_sender , owlSpec__msg1_ephemeral : msg1_ephemeral_ , owlSpec__msg1_static : msg1_static , owlSpec__msg1_timestamp : msg1_timestamp , owlSpec__msg1_mac1 : msg1_mac1 , owlSpec__msg1_mac2 : msg1_mac2 }) in {
(if (length( msg1_sender ) == 4) then ((if (is_group_elem( msg1_ephemeral_ )) then (let C0 = ((ret (crh( construction(  ) )))) in
let H0 = ((ret (crh(concat(C0, identifier()))))) in
let H1 = ((ret (crh(concat(H0, dhpk_S_resp))))) in
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
let caseval = ((ret(dec_st_aead(k0, msg1_static, empty_seq_u8(), H2)))) in
(case (caseval){
| None => {(ret (Option::None))},
| Some (msg1_static_dec) => {let opk = (call(checkpk_resp_spec( cfg
, mut_state
, msg1_static_dec ))) in
let caseval = ((ret (opk))) in
(case (caseval){
| None => {(ret (Option::None))},
| Some (ss_S_init_S_resp_) => {let dhpk_S_init = ((ret (msg1_static_dec))) in
let H3 = ((ret (crh(concat(H2, msg1_static))))) in
let C3 = ((ret(kdf( (0+NONCE_SIZE()+KEY_SIZE()) as usize
, C2
, ss_S_init_S_resp_ ).subrange(0, 0+NONCE_SIZE())))) in
let k1 = ((ret(kdf( (0+NONCE_SIZE()+KEY_SIZE()) as usize
, C2
, ss_S_init_S_resp_ ).subrange(0+NONCE_SIZE(), 0+NONCE_SIZE()+KEY_SIZE())))) in
let caseval = ((ret(dec_st_aead(k1, msg1_timestamp, empty_seq_u8(), H3)))) in
(case (caseval){
| None => {(ret (Option::None))},
| Some (msg1_timestamp_dec) => {let H4 = ((ret (crh( concat( H3
, msg1_timestamp ) )))) in
let retval = ((ret (responder_msg1_val( C3
, H4
, msg1_ephemeral
, dhpk_S_init
, msg1_sender )))) in
let v = ((ret (retval))) in
(ret (Option::Some(v)))},

})},

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
        owl_transp_keys_val11340: owl_transp_keys,
        owl_c11339: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<Arc<Vec<u8>>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_recv_init_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val11340.dview(),
                owl_c11339.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(transp_recv_init_spec);
            let temp_owl__x33 = { arc_clone(&owl_c11339) };
            let owl__x33 = arc_clone(&temp_owl__x33);
            if let Some(parseval) = parse_owl_transp(vec_as_slice(&(*arc_clone(&owl__x33)))) {
                let owl__6 = arc_new(parseval.owl__transp_tag);
                let owl_from5 = arc_new(parseval.owl__transp_receiver);
                let owl_ctr4 = arc_new(parseval.owl__transp_counter);
                let owl_pkt3 = arc_new(parseval.owl__transp_packet);
                {
                    let temp_owl__x32 = { owl_transp_keys_val11340 };
                    let owl__x32 = temp_owl__x32;
                    let parseval = owl__x32;
                    let owl__12 = arc_new(parseval.owl__transp_keys_initiator);
                    let owl_responder_name11 = arc_new(parseval.owl__transp_keys_responder);
                    let owl__10 = arc_new(parseval.owl__transp_keys_init_ephemeral);
                    let owl_eph_resp9 = arc_new(parseval.owl__transp_keys_resp_ephemeral);
                    let owl__8 = arc_new(parseval.owl__transp_keys_T_init_send);
                    let owl_r2i_7 = arc_new(parseval.owl__transp_keys_T_resp_send);
                    {
                        let temp_owl__x28 = { arc_clone(&owl_c11339) };
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
                                    vec_as_slice(&(*arc_clone(&owl__x24))),
                                    vec_as_slice(&(*arc_clone(&owl__x23))),
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
        owl_transp_keys_val9527: owl_transp_keys,
        owl_plaintext9526: Arc<Vec<u8>>,
        obuf: &mut [u8]
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_send_init_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val9527.dview(),
                owl_plaintext9526.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(transp_send_init_spec);
            let temp_owl__x114 = { owl_transp_keys_val9527 };
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
                    let temp_owl__x66 = { arc_clone(&owl_plaintext9526) };
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
        owl_msg1_val5831: owl_initiator_msg1_val,
        owl_dhpk_S_resp5830: Arc<Vec<u8>>,
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
                owl_msg1_val5831.dview(),
                owl_dhpk_S_resp5830.dview(),
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
            let temp_owl__x402 = { arc_clone(&owl_inp122) };
            let owl__x402 = arc_clone(&temp_owl__x402);
            if let Some(parseval) = parse_owl_msg2(vec_as_slice(&(*arc_clone(&owl__x402)))) {
                let owl_msg2_tag130 = arc_new(parseval.owl__msg2_tag);
                let owl_msg2_sender129 = arc_new(parseval.owl__msg2_sender);
                let owl_msg2_receiver128 = arc_new(parseval.owl__msg2_receiver);
                let owl_msg2_ephemeral_127 = arc_new(parseval.owl__msg2_ephemeral);
                let owl_msg2_empty126 = arc_new(parseval.owl__msg2_empty);
                let owl_msg2_mac1125 = arc_new(parseval.owl__msg2_mac1);
                let owl_msg2_mac2124 = arc_new(parseval.owl__msg2_mac2);
                {
                    let temp_owl__x401 = { owl_msg1_val5831 };
                    let owl__x401 = temp_owl__x401;
                    let parseval = owl__x401;
                    let owl_C3132 = arc_new(parseval.owl__initiator_msg1_C3);
                    let owl_H4131 = arc_new(parseval.owl__initiator_msg1_H4);
                    {
                        let temp_owl__x387 = { arc_clone(&owl_msg2_sender129) };
                        let owl__x387 = arc_clone(&temp_owl__x387);
                        let temp_owl__x388 = { vec_length(&(*arc_clone(&owl__x387))) };
                        let owl__x388 = temp_owl__x388;
                        let temp_owl__x390 = { 4 };
                        let owl__x390 = temp_owl__x390;
                        let temp_owl__x391 = { owl__x388 == owl__x390 };
                        let owl__x391 = temp_owl__x391;
                        let temp_owl__x395 = { arc_clone(&owl_msg2_receiver128) };
                        let owl__x395 = arc_clone(&temp_owl__x395);
                        let temp_owl__x396 = { vec_length(&(*arc_clone(&owl__x395))) };
                        let owl__x396 = temp_owl__x396;
                        let temp_owl__x398 = { 4 };
                        let owl__x398 = temp_owl__x398;
                        let temp_owl__x399 = { owl__x396 == owl__x398 };
                        let owl__x399 = temp_owl__x399;
                        let temp_owl__x400 = { owl__x391 && owl__x399 };
                        let owl__x400 = temp_owl__x400;
                        if owl__x400 {
                            let temp_owl__x374 = { arc_clone(&owl_msg2_ephemeral_127) };
                            let owl__x374 = arc_clone(&temp_owl__x374);
                            let temp_owl__x375 = {
                            owl_is_group_elem(vec_as_slice(&(*arc_clone(&owl__x374))))
                            };
                            let owl__x375 = temp_owl__x375;
                            if owl__x375 {
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
                                let owl_msg2_C4405 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x163))),
                                    vec_as_slice(&(*arc_clone(&owl__x165))),
                                );
                                let temp_owl__x166 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C4405),
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
                                let owl_msg2_C5406 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x206))),
                                    vec_as_slice(&(*arc_clone(&owl__x208))),
                                );
                                let temp_owl__x209 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C5406),
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
                                let owl_msg2_C6407 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x216))),
                                    vec_as_slice(&(*arc_clone(&owl__x222))),
                                );
                                let temp_owl__x223 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C6407),
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
                                let owl_msg2_C7408 = owl_extract_expand_to_len(
                                    0 + nonce_size() + nonce_size() + key_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x228))),
                                    vec_as_slice(&(*arc_clone(&owl__x230))),
                                );
                                let temp_owl__x231 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7408),
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
                                            vec_as_slice(&*owl_msg2_C7408),
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
                                            vec_as_slice(&*owl_msg2_C7408),
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
                                let temp_owl__x364 = { arc_clone(&owl__x247) };
                                let owl__x364 = arc_clone(&temp_owl__x364);
                                let temp_owl__x366 = { arc_clone(&owl_msg2_empty126) };
                                let owl__x366 = arc_clone(&temp_owl__x366);
                                let temp_owl__x368 = { arc_clone(&owl__x267) };
                                let owl__x368 = arc_clone(&temp_owl__x368);
                                let temp_owl__x370 = {
                                    {
                                        let x: Vec<u8> = mk_vec_u8![];
                                        x
                                    }
                                };
                                let owl__x370 = arc_new(temp_owl__x370);
                                let temp_owl__x371 = {
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x364))),
                                    vec_as_slice(&(*arc_clone(&owl__x366))),
                                    vec_as_slice(&(*arc_clone(&owl__x370))),
                                    vec_as_slice(&(*arc_clone(&owl__x368))),
                                )
                                };
                                let owl__x371 = temp_owl__x371;
                                let temp_owl_caseval404 = { owl__x371 };
                                let owl_caseval404 = temp_owl_caseval404;
                                match owl_caseval404 {
                                    None => {
                                        let temp_owl__x277 = { None };
                                        let owl__x277 = temp_owl__x277;
                                        (owl__x277, Tracked(itree))
                                    },
                                    Some(temp_owl_msg2_empty_dec278) => {
                                        let owl_msg2_empty_dec278 = arc_clone(
                                            &temp_owl_msg2_empty_dec278,
                                        );
                                        let temp_owl__x359 = { arc_clone(&owl_msg2_empty_dec278) };
                                        let owl__x359 = arc_clone(&temp_owl__x359);
                                        let temp_owl__x361 = { arc_clone(&owl__x272) };
                                        let owl__x361 = arc_clone(&temp_owl__x361);
                                        let temp_owl__x362 = {
                                        rc_vec_eq(&arc_clone(&owl__x359), &arc_clone(&owl__x361))
                                        };
                                        let owl__x362 = temp_owl__x362;
                                        if owl__x362 {
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
                                            let owl_transp_T409 = owl_extract_expand_to_len(
                                                0 + key_size() + key_size(),
                                                vec_as_slice(&(*arc_clone(&owl__x303))),
                                                vec_as_slice(&(*arc_clone(&owl__x305))),
                                            );
                                            let temp_owl__x306 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_transp_T409),
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
                                                        vec_as_slice(&*owl_transp_T409),
                                                        0 + key_size(),
                                                        0 + key_size() + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x314 = arc_clone(&temp_owl__x314);
                                            let temp_owl__x336 = { arc_clone(&owl_msg2_receiver128)
                                            };
                                            let owl__x336 = arc_clone(&temp_owl__x336);
                                            let temp_owl__x338 = { arc_clone(&owl_msg2_sender129) };
                                            let owl__x338 = arc_clone(&temp_owl__x338);
                                            let temp_owl__x340 = { arc_clone(&owl__x158) };
                                            let owl__x340 = arc_clone(&temp_owl__x340);
                                            let temp_owl__x342 = { arc_clone(&owl__x143) };
                                            let owl__x342 = arc_clone(&temp_owl__x342);
                                            let temp_owl__x344 = { arc_clone(&owl__x306) };
                                            let owl__x344 = arc_clone(&temp_owl__x344);
                                            let temp_owl__x346 = { arc_clone(&owl__x314) };
                                            let owl__x346 = arc_clone(&temp_owl__x346);
                                            let temp_owl__x348 = {
                                            owl_transp_keys {
                                                owl__transp_keys_initiator: clone_vec_u8(
                                                    &*arc_clone(&owl__x336),
                                                ),
                                                owl__transp_keys_responder: clone_vec_u8(
                                                    &*arc_clone(&owl__x338),
                                                ),
                                                owl__transp_keys_init_ephemeral: clone_vec_u8(
                                                    &*arc_clone(&owl__x340),
                                                ),
                                                owl__transp_keys_resp_ephemeral: clone_vec_u8(
                                                    &*arc_clone(&owl__x342),
                                                ),
                                                owl__transp_keys_T_init_send: clone_vec_u8(
                                                    &*arc_clone(&owl__x344),
                                                ),
                                                owl__transp_keys_T_resp_send: clone_vec_u8(
                                                    &*arc_clone(&owl__x346),
                                                ),
                                            }
                                            };
                                            let owl__x348 = temp_owl__x348;
                                            let temp_owl__x349 = { owl__x348 };
                                            let owl__x349 = temp_owl__x349;
                                            let temp_owl__x354 = { owl__x349 };
                                            let owl__x354 = temp_owl__x354;
                                            let temp_owl__x355 = { Some(owl__x354) };
                                            let owl__x355 = temp_owl__x355;
                                            (owl__x355, Tracked(itree))
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
    
    pub exec fn owl_generate_msg1_wrapper(&self, s: &mut state_Initiator, dhpk_S_resp: Arc<Vec<u8>>, dhpk_S_init: Arc<Vec<u8>>, ss_S_resp_S_init: Arc<Vec<u8>>, obuf: &mut [u8]) -> (_: owl_initiator_msg1_val) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            generate_msg1_spec_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _): (owl_initiator_msg1_val, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>) =
            self.owl_generate_msg1(Tracked(call_token), s, dhpk_S_resp, dhpk_S_init, ss_S_resp_S_init, obuf).unwrap();
        res
    }
    

    #[verifier::spinoff_prover]
    pub fn owl_generate_msg1(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_dhpk_S_resp5818: Arc<Vec<u8>>,
        owl_dhpk_S_init5817: Arc<Vec<u8>>,
        owl_ss_S_resp_S_init5816: Arc<Vec<u8>>,
        obuf: &mut [u8]
    ) -> (res: Result<
        (owl_initiator_msg1_val, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == generate_msg1_spec(
                *self,
                *old(mut_state),
                owl_dhpk_S_resp5818.dview(),
                owl_dhpk_S_init5817.dview(),
                owl_ss_S_resp_S_init5816.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview().as_seq(), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(generate_msg1_spec);
            let temp_owl__x417 = { owl_construction() };
            let owl__x417 = arc_new(temp_owl__x417);
            let temp_owl__x419 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x417)))) };
            let owl__x419 = arc_clone(&temp_owl__x419);
            let temp_owl__x420 = { arc_clone(&owl__x419) };
            let owl__x420 = arc_clone(&temp_owl__x420);
            let temp_owl__x433 = { arc_clone(&owl__x420) };
            let owl__x433 = arc_clone(&temp_owl__x433);
            let temp_owl__x435 = { owl_identifier() };
            let owl__x435 = arc_new(temp_owl__x435);
            let temp_owl__x437 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x433))),
                vec_as_slice(&(*arc_clone(&owl__x435))),
            )
            };
            let owl__x437 = arc_new(temp_owl__x437);
            let temp_owl__x439 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x437)))) };
            let owl__x439 = arc_clone(&temp_owl__x439);
            let temp_owl__x440 = { arc_clone(&owl__x439) };
            let owl__x440 = arc_clone(&temp_owl__x440);
            let temp_owl__x453 = { arc_clone(&owl__x440) };
            let owl__x453 = arc_clone(&temp_owl__x453);
            let temp_owl__x455 = { arc_clone(&owl_dhpk_S_resp5818) };
            let owl__x455 = arc_clone(&temp_owl__x455);
            let temp_owl__x457 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x453))),
                vec_as_slice(&(*arc_clone(&owl__x455))),
            )
            };
            let owl__x457 = arc_new(temp_owl__x457);
            let temp_owl__x459 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x457)))) };
            let owl__x459 = arc_clone(&temp_owl__x459);
            let temp_owl__x460 = { arc_clone(&owl__x459) };
            let owl__x460 = arc_clone(&temp_owl__x460);
            let temp_owl__x467 = { arc_clone(&self.owl_E_init) };
            let owl__x467 = arc_clone(&temp_owl__x467);
            let temp_owl__x469 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x467)))) };
            let owl__x469 = arc_clone(&temp_owl__x469);
            let temp_owl__x470 = { arc_clone(&owl__x469) };
            let owl__x470 = arc_clone(&temp_owl__x470);
            let temp_owl__x475 = { arc_clone(&owl__x420) };
            let owl__x475 = arc_clone(&temp_owl__x475);
            let temp_owl__x477 = { arc_clone(&owl__x470) };
            let owl__x477 = arc_clone(&temp_owl__x477);
            let owl_msg1_C1738 = owl_extract_expand_to_len(
                0 + nonce_size(),
                vec_as_slice(&(*arc_clone(&owl__x475))),
                vec_as_slice(&(*arc_clone(&owl__x477))),
            );
            let temp_owl__x478 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C1738), 0, 0 + nonce_size())),
            )
            };
            let owl__x478 = arc_clone(&temp_owl__x478);
            let temp_owl__x491 = { arc_clone(&owl__x460) };
            let owl__x491 = arc_clone(&temp_owl__x491);
            let temp_owl__x493 = { arc_clone(&owl__x470) };
            let owl__x493 = arc_clone(&temp_owl__x493);
            let temp_owl__x495 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x491))),
                vec_as_slice(&(*arc_clone(&owl__x493))),
            )
            };
            let owl__x495 = arc_new(temp_owl__x495);
            let temp_owl__x497 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x495)))) };
            let owl__x497 = arc_clone(&temp_owl__x497);
            let temp_owl__x498 = { arc_clone(&owl__x497) };
            let owl__x498 = arc_clone(&temp_owl__x498);
            let temp_owl__x508 = { arc_clone(&owl_dhpk_S_resp5818) };
            let owl__x508 = arc_clone(&temp_owl__x508);
            let temp_owl__x510 = { arc_clone(&self.owl_E_init) };
            let owl__x510 = arc_clone(&temp_owl__x510);
            let temp_owl__x512 = {
            owl_dh_combine(
                vec_as_slice(&(*arc_clone(&owl__x508))),
                vec_as_slice(&(*arc_clone(&owl__x510))),
            )
            };
            let owl__x512 = arc_clone(&temp_owl__x512);
            let temp_owl__x513 = { arc_clone(&owl__x512) };
            let owl__x513 = arc_clone(&temp_owl__x513);
            let temp_owl__x518 = { arc_clone(&owl__x478) };
            let owl__x518 = arc_clone(&temp_owl__x518);
            let temp_owl__x520 = { arc_clone(&owl__x513) };
            let owl__x520 = arc_clone(&temp_owl__x520);
            let owl_msg1_C2739 = owl_extract_expand_to_len(
                0 + nonce_size() + key_size(),
                vec_as_slice(&(*arc_clone(&owl__x518))),
                vec_as_slice(&(*arc_clone(&owl__x520))),
            );
            let temp_owl__x521 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C2739), 0, 0 + nonce_size())),
            )
            };
            let owl__x521 = arc_clone(&temp_owl__x521);
            let temp_owl__x526 = { arc_clone(&owl__x478) };
            let owl__x526 = arc_clone(&temp_owl__x526);
            let temp_owl__x528 = { arc_clone(&owl__x513) };
            let owl__x528 = arc_clone(&temp_owl__x528);
            let temp_owl__x529 = {
            arc_new(
                slice_to_vec(
                    slice_subrange(
                        vec_as_slice(&*owl_msg1_C2739),
                        0 + nonce_size(),
                        0 + nonce_size() + key_size(),
                    ),
                ),
            )
            };
            let owl__x529 = arc_clone(&temp_owl__x529);
            let temp_owl__x536 = { arc_clone(&owl__x529) };
            let owl__x536 = arc_clone(&temp_owl__x536);
            let temp_owl__x539 = { arc_clone(&owl_dhpk_S_init5817) };
            let owl__x539 = arc_clone(&temp_owl__x539);
            let temp_owl__x540 = { arc_clone(&owl__x539) };
            let owl__x540 = arc_clone(&temp_owl__x540);
            let temp_owl__x542 = { arc_clone(&owl__x498) };
            let owl__x542 = arc_clone(&temp_owl__x542);
            let temp_owl__x543 = {
                match owl_enc_st_aead(
                    vec_as_slice(&(*arc_clone(&owl__x536))),
                    vec_as_slice(&(*arc_clone(&owl__x540))),
                    &mut mut_state.owl_aead_counter_msg1_C2,
                    vec_as_slice(&(*arc_clone(&owl__x542))),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x543 = arc_clone(&temp_owl__x543);
            let temp_owl__x556 = { arc_clone(&owl__x498) };
            let owl__x556 = arc_clone(&temp_owl__x556);
            let temp_owl__x558 = { arc_clone(&owl__x543) };
            let owl__x558 = arc_clone(&temp_owl__x558);
            let temp_owl__x560 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x556))),
                vec_as_slice(&(*arc_clone(&owl__x558))),
            )
            };
            let owl__x560 = arc_new(temp_owl__x560);
            let temp_owl__x562 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x560)))) };
            let owl__x562 = arc_clone(&temp_owl__x562);
            let temp_owl__x563 = { arc_clone(&owl__x562) };
            let owl__x563 = arc_clone(&temp_owl__x563);
            let temp_owl__x568 = { arc_clone(&owl__x521) };
            let owl__x568 = arc_clone(&temp_owl__x568);
            let temp_owl__x570 = { arc_clone(&owl_ss_S_resp_S_init5816) };
            let owl__x570 = arc_clone(&temp_owl__x570);
            let owl_msg1_C3740 = owl_extract_expand_to_len(
                0 + nonce_size() + key_size(),
                vec_as_slice(&(*arc_clone(&owl__x568))),
                vec_as_slice(&(*arc_clone(&owl__x570))),
            );
            let temp_owl__x571 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C3740), 0, 0 + nonce_size())),
            )
            };
            let owl__x571 = arc_clone(&temp_owl__x571);
            let temp_owl__x576 = { arc_clone(&owl__x521) };
            let owl__x576 = arc_clone(&temp_owl__x576);
            let temp_owl__x578 = { arc_clone(&owl_ss_S_resp_S_init5816) };
            let owl__x578 = arc_clone(&temp_owl__x578);
            let temp_owl__x579 = {
            arc_new(
                slice_to_vec(
                    slice_subrange(
                        vec_as_slice(&*owl_msg1_C3740),
                        0 + nonce_size(),
                        0 + nonce_size() + key_size(),
                    ),
                ),
            )
            };
            let owl__x579 = arc_clone(&temp_owl__x579);
            let (temp_owl__x581, Tracked(itree)): (
                _,
                Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
            ) = {
                owl_call!( itree
, *mut_state
, timestamp_i_spec(*self, *mut_state)
, self.owl_timestamp_i(mut_state) )
            };
            let owl__x581 = arc_clone(&temp_owl__x581);
            let temp_owl__x587 = { arc_clone(&owl__x579) };
            let owl__x587 = arc_clone(&temp_owl__x587);
            let temp_owl__x589 = { arc_clone(&owl__x581) };
            let owl__x589 = arc_clone(&temp_owl__x589);
            let temp_owl__x591 = { arc_clone(&owl__x563) };
            let owl__x591 = arc_clone(&temp_owl__x591);
            let temp_owl__x592 = {
                match owl_enc_st_aead(
                    vec_as_slice(&(*arc_clone(&owl__x587))),
                    vec_as_slice(&(*arc_clone(&owl__x589))),
                    &mut mut_state.owl_aead_counter_msg1_C3,
                    vec_as_slice(&(*arc_clone(&owl__x591))),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x592 = arc_clone(&temp_owl__x592);
            let temp_owl__x605 = { arc_clone(&owl__x563) };
            let owl__x605 = arc_clone(&temp_owl__x605);
            let temp_owl__x607 = { arc_clone(&owl__x592) };
            let owl__x607 = arc_clone(&temp_owl__x607);
            let temp_owl__x609 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x605))),
                vec_as_slice(&(*arc_clone(&owl__x607))),
            )
            };
            let owl__x609 = arc_new(temp_owl__x609);
            let temp_owl__x611 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x609)))) };
            let owl__x611 = arc_clone(&temp_owl__x611);
            let temp_owl__x612 = { arc_clone(&owl__x611) };
            let owl__x612 = arc_clone(&temp_owl__x612);
            let (temp_owl__x614, Tracked(itree)): (
                _,
                Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
            ) = {
                owl_call!( itree
, *mut_state
, get_sender_i_spec(*self, *mut_state)
, self.owl_get_sender_i(mut_state) )
            };
            let owl__x614 = arc_clone(&temp_owl__x614);
            let temp_owl__x618 = { owl_msg1_tag_value() };
            let owl__x618 = arc_new(temp_owl__x618);
            let temp_owl__x619 = { arc_clone(&owl__x618) };
            let owl__x619 = arc_clone(&temp_owl__x619);
            let temp_owl__x632 = { owl_mac1() };
            let owl__x632 = arc_new(temp_owl__x632);
            let temp_owl__x634 = { arc_clone(&owl_dhpk_S_resp5818) };
            let owl__x634 = arc_clone(&temp_owl__x634);
            let temp_owl__x636 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x632))),
                vec_as_slice(&(*arc_clone(&owl__x634))),
            )
            };
            let owl__x636 = arc_new(temp_owl__x636);
            let temp_owl__x638 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x636)))) };
            let owl__x638 = arc_clone(&temp_owl__x638);
            let temp_owl__x639 = { arc_clone(&owl__x638) };
            let owl__x639 = arc_clone(&temp_owl__x639);
            let temp_owl__x652 = { arc_clone(&owl__x639) };
            let owl__x652 = arc_clone(&temp_owl__x652);
            let temp_owl__x658 = { arc_clone(&owl__x619) };
            let owl__x658 = arc_clone(&temp_owl__x658);
            let temp_owl__x660 = { arc_clone(&owl__x614) };
            let owl__x660 = arc_clone(&temp_owl__x660);
            let temp_owl__x661 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x658))),
                vec_as_slice(&(*arc_clone(&owl__x660))),
            )
            };
            let owl__x661 = arc_new(temp_owl__x661);
            let temp_owl__x663 = { arc_clone(&owl__x470) };
            let owl__x663 = arc_clone(&temp_owl__x663);
            let temp_owl__x664 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x661))),
                vec_as_slice(&(*arc_clone(&owl__x663))),
            )
            };
            let owl__x664 = arc_new(temp_owl__x664);
            let temp_owl__x666 = { arc_clone(&owl__x543) };
            let owl__x666 = arc_clone(&temp_owl__x666);
            let temp_owl__x667 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x664))),
                vec_as_slice(&(*arc_clone(&owl__x666))),
            )
            };
            let owl__x667 = arc_new(temp_owl__x667);
            let temp_owl__x669 = { arc_clone(&owl__x592) };
            let owl__x669 = arc_clone(&temp_owl__x669);
            let temp_owl__x670 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x667))),
                vec_as_slice(&(*arc_clone(&owl__x669))),
            )
            };
            let owl__x670 = arc_new(temp_owl__x670);
            let temp_owl__x671 = {
            owl_mac(
                vec_as_slice(&(*arc_clone(&owl__x652))),
                vec_as_slice(&(*arc_clone(&owl__x670))),
            )
            };
            let owl__x671 = arc_clone(&temp_owl__x671);
            let temp_owl__x675 = { owl_zeros_16() };
            let owl__x675 = arc_new(temp_owl__x675);
            let temp_owl__x676 = { arc_clone(&owl__x675) };
            let owl__x676 = arc_clone(&temp_owl__x676);
            let temp_owl__x701 = { arc_clone(&owl__x619) };
            let owl__x701 = arc_clone(&temp_owl__x701);
            let temp_owl__x703 = { arc_clone(&owl__x614) };
            let owl__x703 = arc_clone(&temp_owl__x703);
            let temp_owl__x705 = { arc_clone(&owl__x470) };
            let owl__x705 = arc_clone(&temp_owl__x705);
            let temp_owl__x707 = { arc_clone(&owl__x543) };
            let owl__x707 = arc_clone(&temp_owl__x707);
            let temp_owl__x709 = { arc_clone(&owl__x592) };
            let owl__x709 = arc_clone(&temp_owl__x709);
            let temp_owl__x711 = { arc_clone(&owl__x671) };
            let owl__x711 = arc_clone(&temp_owl__x711);
            let temp_owl__x713 = { arc_clone(&owl__x676) };
            let owl__x713 = arc_clone(&temp_owl__x713);
            let temp_owl__x715 = {
            owl_msg1 {
                owl__msg1_tag: clone_vec_u8(&*arc_clone(&owl__x701)),
                owl__msg1_sender: clone_vec_u8(&*arc_clone(&owl__x703)),
                owl__msg1_ephemeral: clone_vec_u8(&*arc_clone(&owl__x705)),
                owl__msg1_static: clone_vec_u8(&*arc_clone(&owl__x707)),
                owl__msg1_timestamp: clone_vec_u8(&*arc_clone(&owl__x709)),
                owl__msg1_mac1: clone_vec_u8(&*arc_clone(&owl__x711)),
                owl__msg1_mac2: clone_vec_u8(&*arc_clone(&owl__x713)),
            }
            };
            let owl__x715 = temp_owl__x715;
            let temp_owl__x716 = { owl__x715 };
            let owl__x716 = temp_owl__x716;
            let temp_owl__x720 = { owl__x716 };
            let owl__x720 = temp_owl__x720;
            let temp_owl__x721 = {
            owl_output::<(Seq<u8>, state_Initiator)>(
                Tracked(&mut itree),
                vec_as_slice(&(serialize_owl_msg1(&owl__x720))),
                &Responder_addr(),
                &Initiator_addr(),
                obuf
            )
            };
            let owl__x721 = temp_owl__x721;
            let temp_owl__x731 = { arc_clone(&owl__x571) };
            let owl__x731 = arc_clone(&temp_owl__x731);
            let temp_owl__x733 = { arc_clone(&owl__x612) };
            let owl__x733 = arc_clone(&temp_owl__x733);
            let temp_owl__x735 = {
            owl_initiator_msg1_val {
                owl__initiator_msg1_C3: clone_vec_u8(&*arc_clone(&owl__x731)),
                owl__initiator_msg1_H4: clone_vec_u8(&*arc_clone(&owl__x733)),
            }
            };
            let owl__x735 = temp_owl__x735;
            let temp_owl__x736 = { owl__x735 };
            let owl__x736 = temp_owl__x736;
            let temp_owl__x737 = { owl__x736 };
            let owl__x737 = temp_owl__x737;
            (owl__x737, Tracked(itree))
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
        owl_transp_keys_val14559: owl_transp_keys,
        owl_c14558: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<Arc<Vec<u8>>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_recv_resp_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val14559.dview(),
                owl_c14558.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(transp_recv_resp_spec);
            let temp_owl__x774 = { arc_clone(&owl_c14558) };
            let owl__x774 = arc_clone(&temp_owl__x774);
            if let Some(parseval) = parse_owl_transp(vec_as_slice(&(*arc_clone(&owl__x774)))) {
                let owl__747 = arc_new(parseval.owl__transp_tag);
                let owl_from746 = arc_new(parseval.owl__transp_receiver);
                let owl_ctr745 = arc_new(parseval.owl__transp_counter);
                let owl_pkt744 = arc_new(parseval.owl__transp_packet);
                {
                    let temp_owl__x773 = { owl_transp_keys_val14559 };
                    let owl__x773 = temp_owl__x773;
                    let parseval = owl__x773;
                    let owl_initiator_name753 = arc_new(parseval.owl__transp_keys_initiator);
                    let owl__752 = arc_new(parseval.owl__transp_keys_responder);
                    let owl_eph_init751 = arc_new(parseval.owl__transp_keys_init_ephemeral);
                    let owl__750 = arc_new(parseval.owl__transp_keys_resp_ephemeral);
                    let owl_i2r_749 = arc_new(parseval.owl__transp_keys_T_init_send);
                    let owl__748 = arc_new(parseval.owl__transp_keys_T_resp_send);
                    {
                        let temp_owl__x769 = { arc_clone(&owl_c14558) };
                        let owl__x769 = arc_clone(&temp_owl__x769);
                        let temp_owl__x771 = { arc_clone(&owl_initiator_name753) };
                        let owl__x771 = arc_clone(&temp_owl__x771);
                        let temp_owl__x772 = {
                        rc_vec_eq(&arc_clone(&owl__x769), &arc_clone(&owl__x771))
                        };
                        let owl__x772 = temp_owl__x772;
                        if owl__x772 {
                            let temp_owl__x758 = { arc_clone(&owl_i2r_749) };
                            let owl__x758 = arc_clone(&temp_owl__x758);
                            let temp_owl__x759 = { arc_clone(&owl__x758) };
                            let owl__x759 = arc_clone(&temp_owl__x759);
                            let temp_owl__x762 = { arc_clone(&owl__x759) };
                            let owl__x762 = arc_clone(&temp_owl__x762);
                            let temp_owl__x763 = { arc_clone(&owl_pkt744) };
                            let owl__x763 = arc_clone(&temp_owl__x763);
                            let temp_owl__x764 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x764 = arc_new(temp_owl__x764);
                            let temp_owl__x765 = { arc_clone(&owl_ctr745) };
                            let owl__x765 = arc_clone(&temp_owl__x765);
                            (
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x762))),
                                    vec_as_slice(&(*arc_clone(&owl__x763))),
                                    vec_as_slice(&(*arc_clone(&owl__x765))),
                                    vec_as_slice(&(*arc_clone(&owl__x764))),
                                ),
                                Tracked(itree),
                            )
                        } else {
                            (None, Tracked(itree))
                        }
                    }
                }
            } else {
                let temp_owl__x743 = { None };
                let owl__x743 = temp_owl__x743;
                (owl__x743, Tracked(itree))
            }
        };
        Ok(res_inner)
    }
    
    #[verifier::spinoff_prover]
    pub fn owl_transp_send_resp(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_transp_keys_val12794: owl_transp_keys,
        owl_plaintext12793: Arc<Vec<u8>>,
        obuf: &mut [u8]
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_send_resp_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val12794.dview(),
                owl_plaintext12793.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(transp_send_resp_spec);
            let temp_owl__x855 = { owl_transp_keys_val12794 };
            let owl__x855 = temp_owl__x855;
            let parseval = owl__x855;
            let owl_transp_receiver786 = arc_new(parseval.owl__transp_keys_initiator);
            let owl__785 = arc_new(parseval.owl__transp_keys_responder);
            let owl_eph_init784 = arc_new(parseval.owl__transp_keys_init_ephemeral);
            let owl__783 = arc_new(parseval.owl__transp_keys_resp_ephemeral);
            let owl__782 = arc_new(parseval.owl__transp_keys_T_init_send);
            let owl_r2i_781 = arc_new(parseval.owl__transp_keys_T_resp_send);
            {
                let temp_owl__x791 = { arc_clone(&owl_r2i_781) };
                let owl__x791 = arc_clone(&temp_owl__x791);
                let temp_owl__x792 = { arc_clone(&owl__x791) };
                let owl__x792 = arc_clone(&temp_owl__x792);
                let temp_owl__x794 = { owl_counter_as_bytes(&(mut_state.owl_N_resp_send)) };
                let owl__x794 = arc_new(temp_owl__x794);
                let temp_owl__x798 = { owl_transp_tag_value() };
                let owl__x798 = arc_new(temp_owl__x798);
                let temp_owl__x799 = { arc_clone(&owl__x798) };
                let owl__x799 = arc_clone(&temp_owl__x799);
                let temp_owl__x850 = { arc_clone(&owl_transp_receiver786) };
                let owl__x850 = arc_clone(&temp_owl__x850);
                let temp_owl__x851 = { vec_length(&(*arc_clone(&owl__x850))) };
                let owl__x851 = temp_owl__x851;
                let temp_owl__x853 = { 4 };
                let owl__x853 = temp_owl__x853;
                let temp_owl__x854 = { owl__x851 == owl__x853 };
                let owl__x854 = temp_owl__x854;
                if owl__x854 {
                    let temp_owl__x805 = { arc_clone(&owl__x792) };
                    let owl__x805 = arc_clone(&temp_owl__x805);
                    let temp_owl__x807 = { arc_clone(&owl_plaintext12793) };
                    let owl__x807 = arc_clone(&temp_owl__x807);
                    let temp_owl__x809 = {
                        {
                            let x: Vec<u8> = mk_vec_u8![];
                            x
                        }
                    };
                    let owl__x809 = arc_new(temp_owl__x809);
                    let temp_owl__x810 = {
                        match owl_enc_st_aead(
                            vec_as_slice(&(*arc_clone(&owl__x805))),
                            vec_as_slice(&(*arc_clone(&owl__x807))),
                            &mut mut_state.owl_N_resp_send,
                            vec_as_slice(&(*arc_clone(&owl__x809))),
                        ) {
                            Ok(ctxt) => ctxt,
                            Err(e) => { return Err(e) },
                        }
                    };
                    let owl__x810 = arc_clone(&temp_owl__x810);
                    let temp_owl__x826 = { arc_clone(&owl__x799) };
                    let owl__x826 = arc_clone(&temp_owl__x826);
                    let temp_owl__x828 = { arc_clone(&owl_transp_receiver786) };
                    let owl__x828 = arc_clone(&temp_owl__x828);
                    let temp_owl__x830 = { arc_clone(&owl__x794) };
                    let owl__x830 = arc_clone(&temp_owl__x830);
                    let temp_owl__x832 = { arc_clone(&owl__x810) };
                    let owl__x832 = arc_clone(&temp_owl__x832);
                    let temp_owl__x834 = {
                    owl_transp {
                        owl__transp_tag: clone_vec_u8(&*arc_clone(&owl__x826)),
                        owl__transp_receiver: clone_vec_u8(&*arc_clone(&owl__x828)),
                        owl__transp_counter: clone_vec_u8(&*arc_clone(&owl__x830)),
                        owl__transp_packet: clone_vec_u8(&*arc_clone(&owl__x832)),
                    }
                    };
                    let owl__x834 = temp_owl__x834;
                    let temp_owl__x835 = { owl__x834 };
                    let owl__x835 = temp_owl__x835;
                    let temp_owl__x839 = { owl__x835 };
                    let owl__x839 = temp_owl__x839;
                    let temp_owl__x840 = {
                    owl_output::<(Option<()>, state_Responder)>(
                        Tracked(&mut itree),
                        vec_as_slice(&(serialize_owl_transp(&owl__x839))),
                        &Initiator_addr(),
                        &Responder_addr(),
                        obuf
                    )
                    };
                    let owl__x840 = temp_owl__x840;
                    let temp_owl__x843 = { () };
                    let owl__x843 = temp_owl__x843;
                    let temp_owl__x844 = { Some(owl__x843) };
                    let owl__x844 = temp_owl__x844;
                    (owl__x844, Tracked(itree))
                } else {
                    (None, Tracked(itree))
                }
            }
        };
        Ok(res_inner)
    }
    
    pub exec fn owl_generate_msg2_wrapper(&self, s: &mut state_Responder, msg1_val: owl_responder_msg1_val, obuf: &mut [u8]) -> (_: owl_transp_keys) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            generate_msg1_spec_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_generate_msg2(Tracked(call_token), s, msg1_val, obuf).unwrap();
        res
    }

    #[verifier::spinoff_prover]
    pub fn owl_generate_msg2(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_msg1_val_8321: owl_responder_msg1_val,
        obuf: &mut [u8]
    ) -> (res: Result<
        (owl_transp_keys, Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == generate_msg2_spec(*self, *old(mut_state), owl_msg1_val_8321.dview()),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview().as_seq(), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(generate_msg2_spec);
            let temp_owl__x1201 = { owl_msg1_val_8321 };
            let owl__x1201 = temp_owl__x1201;
            let temp_owl__x1200 = { owl__x1201 };
            let owl__x1200 = temp_owl__x1200;
            let parseval = owl__x1200;
            let owl_C3869 = arc_new(parseval.owl__responder_msg1_C3);
            let owl_H4868 = arc_new(parseval.owl__responder_msg1_H4);
            let owl_ephemeral_867 = arc_new(parseval.owl__responder_msg1_ephemeral);
            let owl_dhpk_S_init866 = arc_new(parseval.owl__responder_msg1_sender_pk);
            let owl_msg2_receiver865 = arc_new(parseval.owl__responder_msg1_sender);
            {
                let temp_owl__x874 = { arc_clone(&owl_ephemeral_867) };
                let owl__x874 = arc_clone(&temp_owl__x874);
                let temp_owl__x875 = { arc_clone(&owl__x874) };
                let owl__x875 = arc_clone(&temp_owl__x875);
                let temp_owl__x882 = { arc_clone(&self.owl_E_resp) };
                let owl__x882 = arc_clone(&temp_owl__x882);
                let temp_owl__x884 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x882)))) };
                let owl__x884 = arc_clone(&temp_owl__x884);
                let temp_owl__x885 = { arc_clone(&owl__x884) };
                let owl__x885 = arc_clone(&temp_owl__x885);
                let temp_owl__x889 = { owl_zeros_32() };
                let owl__x889 = arc_new(temp_owl__x889);
                let temp_owl__x890 = { arc_clone(&owl__x889) };
                let owl__x890 = arc_clone(&temp_owl__x890);
                let temp_owl__x895 = { arc_clone(&owl_C3869) };
                let owl__x895 = arc_clone(&temp_owl__x895);
                let temp_owl__x897 = { arc_clone(&owl__x885) };
                let owl__x897 = arc_clone(&temp_owl__x897);
                let owl_msg2_C41205 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x895))),
                    vec_as_slice(&(*arc_clone(&owl__x897))),
                );
                let temp_owl__x898 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C41205), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x898 = arc_clone(&temp_owl__x898);
                let temp_owl__x911 = { arc_clone(&owl_H4868) };
                let owl__x911 = arc_clone(&temp_owl__x911);
                let temp_owl__x913 = { arc_clone(&owl__x885) };
                let owl__x913 = arc_clone(&temp_owl__x913);
                let temp_owl__x915 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x911))),
                    vec_as_slice(&(*arc_clone(&owl__x913))),
                )
                };
                let owl__x915 = arc_new(temp_owl__x915);
                let temp_owl__x917 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x915)))) };
                let owl__x917 = arc_clone(&temp_owl__x917);
                let temp_owl__x918 = { arc_clone(&owl__x917) };
                let owl__x918 = arc_clone(&temp_owl__x918);
                let temp_owl__x928 = { arc_clone(&owl__x875) };
                let owl__x928 = arc_clone(&temp_owl__x928);
                let temp_owl__x930 = { arc_clone(&self.owl_E_resp) };
                let owl__x930 = arc_clone(&temp_owl__x930);
                let temp_owl__x932 = {
                owl_dh_combine(
                    vec_as_slice(&(*arc_clone(&owl__x928))),
                    vec_as_slice(&(*arc_clone(&owl__x930))),
                )
                };
                let owl__x932 = arc_clone(&temp_owl__x932);
                let temp_owl__x933 = { arc_clone(&owl__x932) };
                let owl__x933 = arc_clone(&temp_owl__x933);
                let temp_owl__x938 = { arc_clone(&owl__x898) };
                let owl__x938 = arc_clone(&temp_owl__x938);
                let temp_owl__x940 = { arc_clone(&owl__x933) };
                let owl__x940 = arc_clone(&temp_owl__x940);
                let owl_msg2_C51206 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x938))),
                    vec_as_slice(&(*arc_clone(&owl__x940))),
                );
                let temp_owl__x941 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C51206), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x941 = arc_clone(&temp_owl__x941);
                let temp_owl__x948 = { arc_clone(&owl__x941) };
                let owl__x948 = arc_clone(&temp_owl__x948);
                let temp_owl__x951 = { arc_clone(&owl_dhpk_S_init866) };
                let owl__x951 = arc_clone(&temp_owl__x951);
                let temp_owl__x953 = { arc_clone(&self.owl_E_resp) };
                let owl__x953 = arc_clone(&temp_owl__x953);
                let temp_owl__x954 = {
                owl_dh_combine(
                    vec_as_slice(&(*arc_clone(&owl__x951))),
                    vec_as_slice(&(*arc_clone(&owl__x953))),
                )
                };
                let owl__x954 = arc_clone(&temp_owl__x954);
                let owl_msg2_C61207 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x948))),
                    vec_as_slice(&(*arc_clone(&owl__x954))),
                );
                let temp_owl__x955 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C61207), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x955 = arc_clone(&temp_owl__x955);
                let temp_owl__x960 = { arc_clone(&owl__x955) };
                let owl__x960 = arc_clone(&temp_owl__x960);
                let temp_owl__x962 = { arc_clone(&owl__x890) };
                let owl__x962 = arc_clone(&temp_owl__x962);
                let owl_msg2_C71208 = owl_extract_expand_to_len(
                    0 + nonce_size() + nonce_size() + key_size(),
                    vec_as_slice(&(*arc_clone(&owl__x960))),
                    vec_as_slice(&(*arc_clone(&owl__x962))),
                );
                let temp_owl__x963 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C71208), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x963 = arc_clone(&temp_owl__x963);
                let temp_owl__x968 = { arc_clone(&owl__x955) };
                let owl__x968 = arc_clone(&temp_owl__x968);
                let temp_owl__x970 = { arc_clone(&owl__x890) };
                let owl__x970 = arc_clone(&temp_owl__x970);
                let temp_owl__x971 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_msg2_C71208),
                            0 + nonce_size(),
                            0 + nonce_size() + nonce_size(),
                        ),
                    ),
                )
                };
                let owl__x971 = arc_clone(&temp_owl__x971);
                let temp_owl__x976 = { arc_clone(&owl__x955) };
                let owl__x976 = arc_clone(&temp_owl__x976);
                let temp_owl__x978 = { arc_clone(&owl__x890) };
                let owl__x978 = arc_clone(&temp_owl__x978);
                let temp_owl__x979 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_msg2_C71208),
                            0 + nonce_size() + nonce_size(),
                            0 + nonce_size() + nonce_size() + key_size(),
                        ),
                    ),
                )
                };
                let owl__x979 = arc_clone(&temp_owl__x979);
                let temp_owl__x992 = { arc_clone(&owl__x918) };
                let owl__x992 = arc_clone(&temp_owl__x992);
                let temp_owl__x994 = { arc_clone(&owl__x971) };
                let owl__x994 = arc_clone(&temp_owl__x994);
                let temp_owl__x996 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x992))),
                    vec_as_slice(&(*arc_clone(&owl__x994))),
                )
                };
                let owl__x996 = arc_new(temp_owl__x996);
                let temp_owl__x998 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x996)))) };
                let owl__x998 = arc_clone(&temp_owl__x998);
                let temp_owl__x999 = { arc_clone(&owl__x998) };
                let owl__x999 = arc_clone(&temp_owl__x999);
                let temp_owl__x1003 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1003 = arc_new(temp_owl__x1003);
                let temp_owl__x1004 = { arc_clone(&owl__x1003) };
                let owl__x1004 = arc_clone(&temp_owl__x1004);
                let temp_owl__x1010 = { arc_clone(&owl__x979) };
                let owl__x1010 = arc_clone(&temp_owl__x1010);
                let temp_owl__x1012 = { arc_clone(&owl__x1004) };
                let owl__x1012 = arc_clone(&temp_owl__x1012);
                let temp_owl__x1014 = { arc_clone(&owl__x999) };
                let owl__x1014 = arc_clone(&temp_owl__x1014);
                let temp_owl__x1015 = {
                    match owl_enc_st_aead(
                        vec_as_slice(&(*arc_clone(&owl__x1010))),
                        vec_as_slice(&(*arc_clone(&owl__x1012))),
                        &mut mut_state.owl_aead_counter_msg2_C7,
                        vec_as_slice(&(*arc_clone(&owl__x1014))),
                    ) {
                        Ok(ctxt) => ctxt,
                        Err(e) => { return Err(e) },
                    }
                };
                let owl__x1015 = arc_clone(&temp_owl__x1015);
                let temp_owl__x1028 = { arc_clone(&owl__x999) };
                let owl__x1028 = arc_clone(&temp_owl__x1028);
                let temp_owl__x1030 = { arc_clone(&owl__x1015) };
                let owl__x1030 = arc_clone(&temp_owl__x1030);
                let temp_owl__x1032 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1028))),
                    vec_as_slice(&(*arc_clone(&owl__x1030))),
                )
                };
                let owl__x1032 = arc_new(temp_owl__x1032);
                let temp_owl__x1034 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x1032)))) };
                let owl__x1034 = arc_clone(&temp_owl__x1034);
                let temp_owl__x1035 = { arc_clone(&owl__x1034) };
                let owl__x1035 = arc_clone(&temp_owl__x1035);
                let (temp_owl__x1037, Tracked(itree)): (
                    _,
                    Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
                ) = {
                    owl_call!( itree
, *mut_state
, get_sender_r_spec(*self, *mut_state)
, self.owl_get_sender_r(mut_state) )
                };
                let owl__x1037 = arc_clone(&temp_owl__x1037);
                let temp_owl__x1041 = { owl_msg2_tag_value() };
                let owl__x1041 = arc_new(temp_owl__x1041);
                let temp_owl__x1042 = { arc_clone(&owl__x1041) };
                let owl__x1042 = arc_clone(&temp_owl__x1042);
                let temp_owl__x1055 = { owl_mac1() };
                let owl__x1055 = arc_new(temp_owl__x1055);
                let temp_owl__x1057 = { arc_clone(&owl_dhpk_S_init866) };
                let owl__x1057 = arc_clone(&temp_owl__x1057);
                let temp_owl__x1059 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1055))),
                    vec_as_slice(&(*arc_clone(&owl__x1057))),
                )
                };
                let owl__x1059 = arc_new(temp_owl__x1059);
                let temp_owl__x1061 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x1059)))) };
                let owl__x1061 = arc_clone(&temp_owl__x1061);
                let temp_owl__x1062 = { arc_clone(&owl__x1061) };
                let owl__x1062 = arc_clone(&temp_owl__x1062);
                let temp_owl__x1075 = { arc_clone(&owl__x1062) };
                let owl__x1075 = arc_clone(&temp_owl__x1075);
                let temp_owl__x1081 = { arc_clone(&owl__x1042) };
                let owl__x1081 = arc_clone(&temp_owl__x1081);
                let temp_owl__x1083 = { arc_clone(&owl__x1037) };
                let owl__x1083 = arc_clone(&temp_owl__x1083);
                let temp_owl__x1084 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1081))),
                    vec_as_slice(&(*arc_clone(&owl__x1083))),
                )
                };
                let owl__x1084 = arc_new(temp_owl__x1084);
                let temp_owl__x1086 = { arc_clone(&owl_msg2_receiver865) };
                let owl__x1086 = arc_clone(&temp_owl__x1086);
                let temp_owl__x1087 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1084))),
                    vec_as_slice(&(*arc_clone(&owl__x1086))),
                )
                };
                let owl__x1087 = arc_new(temp_owl__x1087);
                let temp_owl__x1089 = { arc_clone(&owl__x885) };
                let owl__x1089 = arc_clone(&temp_owl__x1089);
                let temp_owl__x1090 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1087))),
                    vec_as_slice(&(*arc_clone(&owl__x1089))),
                )
                };
                let owl__x1090 = arc_new(temp_owl__x1090);
                let temp_owl__x1092 = { arc_clone(&owl__x1015) };
                let owl__x1092 = arc_clone(&temp_owl__x1092);
                let temp_owl__x1093 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1090))),
                    vec_as_slice(&(*arc_clone(&owl__x1092))),
                )
                };
                let owl__x1093 = arc_new(temp_owl__x1093);
                let temp_owl__x1094 = {
                owl_mac(
                    vec_as_slice(&(*arc_clone(&owl__x1075))),
                    vec_as_slice(&(*arc_clone(&owl__x1093))),
                )
                };
                let owl__x1094 = arc_clone(&temp_owl__x1094);
                let temp_owl__x1098 = { owl_zeros_16() };
                let owl__x1098 = arc_new(temp_owl__x1098);
                let temp_owl__x1099 = { arc_clone(&owl__x1098) };
                let owl__x1099 = arc_clone(&temp_owl__x1099);
                let temp_owl__x1124 = { arc_clone(&owl__x1042) };
                let owl__x1124 = arc_clone(&temp_owl__x1124);
                let temp_owl__x1126 = { arc_clone(&owl__x1037) };
                let owl__x1126 = arc_clone(&temp_owl__x1126);
                let temp_owl__x1128 = { arc_clone(&owl_msg2_receiver865) };
                let owl__x1128 = arc_clone(&temp_owl__x1128);
                let temp_owl__x1130 = { arc_clone(&owl__x885) };
                let owl__x1130 = arc_clone(&temp_owl__x1130);
                let temp_owl__x1132 = { arc_clone(&owl__x1015) };
                let owl__x1132 = arc_clone(&temp_owl__x1132);
                let temp_owl__x1134 = { arc_clone(&owl__x1094) };
                let owl__x1134 = arc_clone(&temp_owl__x1134);
                let temp_owl__x1136 = { arc_clone(&owl__x1099) };
                let owl__x1136 = arc_clone(&temp_owl__x1136);
                let temp_owl__x1138 = {
                owl_msg2 {
                    owl__msg2_tag: clone_vec_u8(&*arc_clone(&owl__x1124)),
                    owl__msg2_sender: clone_vec_u8(&*arc_clone(&owl__x1126)),
                    owl__msg2_receiver: clone_vec_u8(&*arc_clone(&owl__x1128)),
                    owl__msg2_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1130)),
                    owl__msg2_empty: clone_vec_u8(&*arc_clone(&owl__x1132)),
                    owl__msg2_mac1: clone_vec_u8(&*arc_clone(&owl__x1134)),
                    owl__msg2_mac2: clone_vec_u8(&*arc_clone(&owl__x1136)),
                }
                };
                let owl__x1138 = temp_owl__x1138;
                let temp_owl__x1139 = { owl__x1138 };
                let owl__x1139 = temp_owl__x1139;
                let temp_owl__x1143 = { owl__x1139 };
                let owl__x1143 = temp_owl__x1143;
                let temp_owl__x1144 = {
                owl_output::<(Seq<u8>, state_Responder)>(
                    Tracked(&mut itree),
                    vec_as_slice(&(serialize_owl_msg2(&owl__x1143))),
                    &Initiator_addr(),
                    &Responder_addr(),
                    obuf
                )
                };
                let owl__x1144 = temp_owl__x1144;
                let temp_owl__x1149 = { arc_clone(&owl__x963) };
                let owl__x1149 = arc_clone(&temp_owl__x1149);
                let temp_owl__x1151 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1151 = arc_new(temp_owl__x1151);
                let owl_transp_T1209 = owl_extract_expand_to_len(
                    0 + key_size() + key_size(),
                    vec_as_slice(&(*arc_clone(&owl__x1149))),
                    vec_as_slice(&(*arc_clone(&owl__x1151))),
                );
                let temp_owl__x1152 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_transp_T1209), 0, 0 + key_size()),
                    ),
                )
                };
                let owl__x1152 = arc_clone(&temp_owl__x1152);
                let temp_owl__x1157 = { arc_clone(&owl__x963) };
                let owl__x1157 = arc_clone(&temp_owl__x1157);
                let temp_owl__x1159 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1159 = arc_new(temp_owl__x1159);
                let temp_owl__x1160 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_transp_T1209),
                            0 + key_size(),
                            0 + key_size() + key_size(),
                        ),
                    ),
                )
                };
                let owl__x1160 = arc_clone(&temp_owl__x1160);
                let temp_owl__x1182 = { arc_clone(&owl_msg2_receiver865) };
                let owl__x1182 = arc_clone(&temp_owl__x1182);
                let temp_owl__x1184 = { arc_clone(&owl__x1037) };
                let owl__x1184 = arc_clone(&temp_owl__x1184);
                let temp_owl__x1186 = { arc_clone(&owl__x875) };
                let owl__x1186 = arc_clone(&temp_owl__x1186);
                let temp_owl__x1188 = { arc_clone(&owl__x885) };
                let owl__x1188 = arc_clone(&temp_owl__x1188);
                let temp_owl__x1190 = { arc_clone(&owl__x1152) };
                let owl__x1190 = arc_clone(&temp_owl__x1190);
                let temp_owl__x1192 = { arc_clone(&owl__x1160) };
                let owl__x1192 = arc_clone(&temp_owl__x1192);
                let temp_owl__x1194 = {
                owl_transp_keys {
                    owl__transp_keys_initiator: clone_vec_u8(&*arc_clone(&owl__x1182)),
                    owl__transp_keys_responder: clone_vec_u8(&*arc_clone(&owl__x1184)),
                    owl__transp_keys_init_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1186)),
                    owl__transp_keys_resp_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1188)),
                    owl__transp_keys_T_init_send: clone_vec_u8(&*arc_clone(&owl__x1190)),
                    owl__transp_keys_T_resp_send: clone_vec_u8(&*arc_clone(&owl__x1192)),
                }
                };
                let owl__x1194 = temp_owl__x1194;
                let temp_owl__x1195 = { owl__x1194 };
                let owl__x1195 = temp_owl__x1195;
                let temp_owl__x1198 = { owl__x1195 };
                let owl__x1198 = temp_owl__x1198;
                let temp_owl__x1199 = { owl__x1198 };
                let owl__x1199 = temp_owl__x1199;
                (owl__x1199, Tracked(itree))
            }
        };
        Ok(res_inner)
    }   
    
    pub exec fn owl_receive_msg1_wrapper(&self, s: &mut state_Responder, dhpk_S_resp: Arc<Vec<u8>>, ibuf: &[u8]) -> (_: Option<owl_responder_msg1_val>) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            receive_msg1_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_receive_msg1(Tracked(call_token), s, dhpk_S_resp, ibuf).unwrap();
        res
    }
    
    #[verifier::spinoff_prover]
    pub fn owl_receive_msg1(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_dhpk_S_resp8149: Arc<Vec<u8>>,
        ibuf: &[u8]
    ) -> (res: Result<
        (
            Option<owl_responder_msg1_val>,
            Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>,
        ),
        OwlError,
    >)
        requires
            itree.view() == receive_msg1_spec(*self, *old(mut_state), owl_dhpk_S_resp8149.dview()),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (option_as_seq(dview_option(res.get_Ok_0().0)), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            reveal(receive_msg1_spec);
            let (temp_owl_inp1218, owl__1217) = owl_input::<(Option<Seq<u8>>, state_Responder)>(
                Tracked(&mut itree),
                ibuf,
            );
            let owl_inp1218 = arc_new(temp_owl_inp1218);
            let temp_owl__x1506 = { arc_clone(&owl_inp1218) };
            let owl__x1506 = arc_clone(&temp_owl__x1506);
            if let Some(parseval) = parse_owl_msg1(vec_as_slice(&(*arc_clone(&owl__x1506)))) {
                let owl_msg1_tag1226 = arc_new(parseval.owl__msg1_tag);
                let owl_msg1_sender1225 = arc_new(parseval.owl__msg1_sender);
                let owl_msg1_ephemeral_1224 = arc_new(parseval.owl__msg1_ephemeral);
                let owl_msg1_static1223 = arc_new(parseval.owl__msg1_static);
                let owl_msg1_timestamp1222 = arc_new(parseval.owl__msg1_timestamp);
                let owl_msg1_mac11221 = arc_new(parseval.owl__msg1_mac1);
                let owl_msg1_mac21220 = arc_new(parseval.owl__msg1_mac2);
                {
                    let temp_owl__x1501 = { arc_clone(&owl_msg1_sender1225) };
                    let owl__x1501 = arc_clone(&temp_owl__x1501);
                    let temp_owl__x1502 = { vec_length(&(*arc_clone(&owl__x1501))) };
                    let owl__x1502 = temp_owl__x1502;
                    let temp_owl__x1504 = { 4 };
                    let owl__x1504 = temp_owl__x1504;
                    let temp_owl__x1505 = { owl__x1502 == owl__x1504 };
                    let owl__x1505 = temp_owl__x1505;
                    if owl__x1505 {
                        let temp_owl__x1494 = { arc_clone(&owl_msg1_ephemeral_1224) };
                        let owl__x1494 = arc_clone(&temp_owl__x1494);
                        let temp_owl__x1495 = {
                        owl_is_group_elem(vec_as_slice(&(*arc_clone(&owl__x1494))))
                        };
                        let owl__x1495 = temp_owl__x1495;
                        if owl__x1495 {
                            let temp_owl__x1233 = { owl_construction() };
                            let owl__x1233 = arc_new(temp_owl__x1233);
                            let temp_owl__x1235 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1233))))
                            };
                            let owl__x1235 = arc_clone(&temp_owl__x1235);
                            let temp_owl__x1236 = { arc_clone(&owl__x1235) };
                            let owl__x1236 = arc_clone(&temp_owl__x1236);
                            let temp_owl__x1249 = { arc_clone(&owl__x1236) };
                            let owl__x1249 = arc_clone(&temp_owl__x1249);
                            let temp_owl__x1251 = { owl_identifier() };
                            let owl__x1251 = arc_new(temp_owl__x1251);
                            let temp_owl__x1253 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1249))),
                                vec_as_slice(&(*arc_clone(&owl__x1251))),
                            )
                            };
                            let owl__x1253 = arc_new(temp_owl__x1253);
                            let temp_owl__x1255 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1253))))
                            };
                            let owl__x1255 = arc_clone(&temp_owl__x1255);
                            let temp_owl__x1256 = { arc_clone(&owl__x1255) };
                            let owl__x1256 = arc_clone(&temp_owl__x1256);
                            let temp_owl__x1269 = { arc_clone(&owl__x1256) };
                            let owl__x1269 = arc_clone(&temp_owl__x1269);
                            let temp_owl__x1271 = { arc_clone(&owl_dhpk_S_resp8149) };
                            let owl__x1271 = arc_clone(&temp_owl__x1271);
                            let temp_owl__x1273 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1269))),
                                vec_as_slice(&(*arc_clone(&owl__x1271))),
                            )
                            };
                            let owl__x1273 = arc_new(temp_owl__x1273);
                            let temp_owl__x1275 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1273))))
                            };
                            let owl__x1275 = arc_clone(&temp_owl__x1275);
                            let temp_owl__x1276 = { arc_clone(&owl__x1275) };
                            let owl__x1276 = arc_clone(&temp_owl__x1276);
                            let temp_owl__x1282 = { arc_clone(&owl_msg1_ephemeral_1224) };
                            let owl__x1282 = arc_clone(&temp_owl__x1282);
                            let temp_owl__x1283 = { arc_clone(&owl__x1282) };
                            let owl__x1283 = arc_clone(&temp_owl__x1283);
                            let temp_owl__x1288 = { arc_clone(&owl__x1236) };
                            let owl__x1288 = arc_clone(&temp_owl__x1288);
                            let temp_owl__x1290 = { arc_clone(&owl__x1283) };
                            let owl__x1290 = arc_clone(&temp_owl__x1290);
                            let owl_msg1_C11514 = owl_extract_expand_to_len(
                                0 + nonce_size(),
                                vec_as_slice(&(*arc_clone(&owl__x1288))),
                                vec_as_slice(&(*arc_clone(&owl__x1290))),
                            );
                            let temp_owl__x1291 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C11514),
                                        0,
                                        0 + nonce_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1291 = arc_clone(&temp_owl__x1291);
                            let temp_owl__x1304 = { arc_clone(&owl__x1276) };
                            let owl__x1304 = arc_clone(&temp_owl__x1304);
                            let temp_owl__x1306 = { arc_clone(&owl__x1283) };
                            let owl__x1306 = arc_clone(&temp_owl__x1306);
                            let temp_owl__x1308 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1304))),
                                vec_as_slice(&(*arc_clone(&owl__x1306))),
                            )
                            };
                            let owl__x1308 = arc_new(temp_owl__x1308);
                            let temp_owl__x1310 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1308))))
                            };
                            let owl__x1310 = arc_clone(&temp_owl__x1310);
                            let temp_owl__x1311 = { arc_clone(&owl__x1310) };
                            let owl__x1311 = arc_clone(&temp_owl__x1311);
                            let temp_owl__x1321 = { arc_clone(&owl__x1283) };
                            let owl__x1321 = arc_clone(&temp_owl__x1321);
                            let temp_owl__x1323 = { arc_clone(&self.owl_S_resp) };
                            let owl__x1323 = arc_clone(&temp_owl__x1323);
                            let temp_owl__x1325 = {
                            owl_dh_combine(
                                vec_as_slice(&(*arc_clone(&owl__x1321))),
                                vec_as_slice(&(*arc_clone(&owl__x1323))),
                            )
                            };
                            let owl__x1325 = arc_clone(&temp_owl__x1325);
                            let temp_owl__x1326 = { arc_clone(&owl__x1325) };
                            let owl__x1326 = arc_clone(&temp_owl__x1326);
                            let temp_owl__x1331 = { arc_clone(&owl__x1291) };
                            let owl__x1331 = arc_clone(&temp_owl__x1331);
                            let temp_owl__x1333 = { arc_clone(&owl__x1326) };
                            let owl__x1333 = arc_clone(&temp_owl__x1333);
                            let owl_msg1_C21515 = owl_extract_expand_to_len(
                                0 + nonce_size() + key_size(),
                                vec_as_slice(&(*arc_clone(&owl__x1331))),
                                vec_as_slice(&(*arc_clone(&owl__x1333))),
                            );
                            let temp_owl__x1334 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C21515),
                                        0,
                                        0 + nonce_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1334 = arc_clone(&temp_owl__x1334);
                            let temp_owl__x1339 = { arc_clone(&owl__x1291) };
                            let owl__x1339 = arc_clone(&temp_owl__x1339);
                            let temp_owl__x1341 = { arc_clone(&owl__x1326) };
                            let owl__x1341 = arc_clone(&temp_owl__x1341);
                            let temp_owl__x1342 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C21515),
                                        0 + nonce_size(),
                                        0 + nonce_size() + key_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1342 = arc_clone(&temp_owl__x1342);
                            let temp_owl__x1484 = { arc_clone(&owl__x1342) };
                            let owl__x1484 = arc_clone(&temp_owl__x1484);
                            let temp_owl__x1486 = { arc_clone(&owl_msg1_static1223) };
                            let owl__x1486 = arc_clone(&temp_owl__x1486);
                            let temp_owl__x1488 = { arc_clone(&owl__x1311) };
                            let owl__x1488 = arc_clone(&temp_owl__x1488);
                            let temp_owl__x1490 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x1490 = arc_new(temp_owl__x1490);
                            let temp_owl__x1491 = {
                            owl_dec_st_aead(
                                vec_as_slice(&(*arc_clone(&owl__x1484))),
                                vec_as_slice(&(*arc_clone(&owl__x1486))),
                                vec_as_slice(&(*arc_clone(&owl__x1490))),
                                vec_as_slice(&(*arc_clone(&owl__x1488))),
                            )
                            };
                            let owl__x1491 = temp_owl__x1491;
                            let temp_owl_caseval1513 = { owl__x1491 };
                            let owl_caseval1513 = temp_owl_caseval1513;
                            match owl_caseval1513 {
                                None => {
                                    let temp_owl__x1347 = { None };
                                    let owl__x1347 = temp_owl__x1347;
                                    (owl__x1347, Tracked(itree))
                                },
                                Some(temp_owl_msg1_static_dec1348) => {
                                    let owl_msg1_static_dec1348 = arc_clone(
                                        &temp_owl_msg1_static_dec1348,
                                    );
                                    let temp_owl__x1352 = { arc_clone(&owl_msg1_static_dec1348) };
                                    let owl__x1352 = arc_clone(&temp_owl__x1352);
                                    let (temp_owl__x1353, Tracked(itree)): (
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
, checkpk_resp_spec(*self, *mut_state, (&owl__x1352).dview())
, self.owl_checkpk_resp(mut_state, arc_clone(&owl__x1352)) )
                                    };
                                    let owl__x1353 = temp_owl__x1353;
                                    let temp_owl__x1481 = { owl__x1353 };
                                    let owl__x1481 = temp_owl__x1481;
                                    let temp_owl__x1482 = { owl__x1481 };
                                    let owl__x1482 = temp_owl__x1482;
                                    let temp_owl_caseval1512 = { owl__x1482 };
                                    let owl_caseval1512 = temp_owl_caseval1512;
                                    match owl_caseval1512 {
                                        None => {
                                            let temp_owl__x1355 = { None };
                                            let owl__x1355 = temp_owl__x1355;
                                            (owl__x1355, Tracked(itree))
                                        },
                                        Some(temp_owl_ss_S_init_S_resp_1356) => {
                                            let owl_ss_S_init_S_resp_1356 = arc_clone(
                                                &temp_owl_ss_S_init_S_resp_1356,
                                            );
                                            let temp_owl__x1479 = {
                                            arc_clone(&owl_ss_S_init_S_resp_1356)
                                            };
                                            let owl__x1479 = arc_clone(&temp_owl__x1479);
                                            let temp_owl__x1362 = {
                                            arc_clone(&owl_msg1_static_dec1348)
                                            };
                                            let owl__x1362 = arc_clone(&temp_owl__x1362);
                                            let temp_owl__x1363 = { arc_clone(&owl__x1362) };
                                            let owl__x1363 = arc_clone(&temp_owl__x1363);
                                            let temp_owl__x1376 = { arc_clone(&owl__x1311) };
                                            let owl__x1376 = arc_clone(&temp_owl__x1376);
                                            let temp_owl__x1378 = { arc_clone(&owl_msg1_static1223)
                                            };
                                            let owl__x1378 = arc_clone(&temp_owl__x1378);
                                            let temp_owl__x1380 = {
                                            owl_concat(
                                                vec_as_slice(&(*arc_clone(&owl__x1376))),
                                                vec_as_slice(&(*arc_clone(&owl__x1378))),
                                            )
                                            };
                                            let owl__x1380 = arc_new(temp_owl__x1380);
                                            let temp_owl__x1382 = {
                                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1380))))
                                            };
                                            let owl__x1382 = arc_clone(&temp_owl__x1382);
                                            let temp_owl__x1383 = { arc_clone(&owl__x1382) };
                                            let owl__x1383 = arc_clone(&temp_owl__x1383);
                                            let temp_owl__x1388 = { arc_clone(&owl__x1334) };
                                            let owl__x1388 = arc_clone(&temp_owl__x1388);
                                            let temp_owl__x1390 = { arc_clone(&owl__x1479) };
                                            let owl__x1390 = arc_clone(&temp_owl__x1390);
                                            let owl_msg1_C31516 = owl_extract_expand_to_len(
                                                0 + nonce_size() + key_size(),
                                                vec_as_slice(&(*arc_clone(&owl__x1388))),
                                                vec_as_slice(&(*arc_clone(&owl__x1390))),
                                            );
                                            let temp_owl__x1391 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_msg1_C31516),
                                                        0,
                                                        0 + nonce_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x1391 = arc_clone(&temp_owl__x1391);
                                            let temp_owl__x1396 = { arc_clone(&owl__x1334) };
                                            let owl__x1396 = arc_clone(&temp_owl__x1396);
                                            let temp_owl__x1398 = { arc_clone(&owl__x1479) };
                                            let owl__x1398 = arc_clone(&temp_owl__x1398);
                                            let temp_owl__x1399 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_msg1_C31516),
                                                        0 + nonce_size(),
                                                        0 + nonce_size() + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x1399 = arc_clone(&temp_owl__x1399);
                                            let temp_owl__x1471 = { arc_clone(&owl__x1399) };
                                            let owl__x1471 = arc_clone(&temp_owl__x1471);
                                            let temp_owl__x1473 = {
                                            arc_clone(&owl_msg1_timestamp1222)
                                            };
                                            let owl__x1473 = arc_clone(&temp_owl__x1473);
                                            let temp_owl__x1475 = { arc_clone(&owl__x1383) };
                                            let owl__x1475 = arc_clone(&temp_owl__x1475);
                                            let temp_owl__x1477 = {
                                                {
                                                    let x: Vec<u8> = mk_vec_u8![];
                                                    x
                                                }
                                            };
                                            let owl__x1477 = arc_new(temp_owl__x1477);
                                            let temp_owl__x1478 = {
                                            owl_dec_st_aead(
                                                vec_as_slice(&(*arc_clone(&owl__x1471))),
                                                vec_as_slice(&(*arc_clone(&owl__x1473))),
                                                vec_as_slice(&(*arc_clone(&owl__x1477))),
                                                vec_as_slice(&(*arc_clone(&owl__x1475))),
                                            )
                                            };
                                            let owl__x1478 = temp_owl__x1478;
                                            let temp_owl_caseval1511 = { owl__x1478 };
                                            let owl_caseval1511 = temp_owl_caseval1511;
                                            match owl_caseval1511 {
                                                None => {
                                                    let temp_owl__x1404 = { None };
                                                    let owl__x1404 = temp_owl__x1404;
                                                    (owl__x1404, Tracked(itree))
                                                },
                                                Some(temp_owl_msg1_timestamp_dec1405) => {
                                                    let owl_msg1_timestamp_dec1405 = arc_clone(
                                                        &temp_owl_msg1_timestamp_dec1405,
                                                    );
                                                    let temp_owl__x1418 = { arc_clone(&owl__x1383)
                                                    };
                                                    let owl__x1418 = arc_clone(&temp_owl__x1418);
                                                    let temp_owl__x1420 = {
                                                    arc_clone(&owl_msg1_timestamp1222)
                                                    };
                                                    let owl__x1420 = arc_clone(&temp_owl__x1420);
                                                    let temp_owl__x1422 = {
                                                    owl_concat(
                                                        vec_as_slice(&(*arc_clone(&owl__x1418))),
                                                        vec_as_slice(&(*arc_clone(&owl__x1420))),
                                                    )
                                                    };
                                                    let owl__x1422 = arc_new(temp_owl__x1422);
                                                    let temp_owl__x1424 = {
                                                    owl_crh(
                                                        vec_as_slice(&(*arc_clone(&owl__x1422))),
                                                    )
                                                    };
                                                    let owl__x1424 = arc_clone(&temp_owl__x1424);
                                                    let temp_owl__x1425 = { arc_clone(&owl__x1424)
                                                    };
                                                    let owl__x1425 = arc_clone(&temp_owl__x1425);
                                                    let temp_owl__x1444 = { arc_clone(&owl__x1391)
                                                    };
                                                    let owl__x1444 = arc_clone(&temp_owl__x1444);
                                                    let temp_owl__x1446 = { arc_clone(&owl__x1425)
                                                    };
                                                    let owl__x1446 = arc_clone(&temp_owl__x1446);
                                                    let temp_owl__x1448 = { arc_clone(&owl__x1283)
                                                    };
                                                    let owl__x1448 = arc_clone(&temp_owl__x1448);
                                                    let temp_owl__x1450 = { arc_clone(&owl__x1363)
                                                    };
                                                    let owl__x1450 = arc_clone(&temp_owl__x1450);
                                                    let temp_owl__x1452 = {
                                                    arc_clone(&owl_msg1_sender1225)
                                                    };
                                                    let owl__x1452 = arc_clone(&temp_owl__x1452);
                                                    let temp_owl__x1454 = {
                                                    owl_responder_msg1_val {
                                                        owl__responder_msg1_C3: clone_vec_u8(
                                                            &*arc_clone(&owl__x1444),
                                                        ),
                                                        owl__responder_msg1_H4: clone_vec_u8(
                                                            &*arc_clone(&owl__x1446),
                                                        ),
                                                        owl__responder_msg1_ephemeral: clone_vec_u8(
                                                            &*arc_clone(&owl__x1448),
                                                        ),
                                                        owl__responder_msg1_sender_pk: clone_vec_u8(
                                                            &*arc_clone(&owl__x1450),
                                                        ),
                                                        owl__responder_msg1_sender: clone_vec_u8(
                                                            &*arc_clone(&owl__x1452),
                                                        ),
                                                    }
                                                    };
                                                    let owl__x1454 = temp_owl__x1454;
                                                    let temp_owl__x1455 = { owl__x1454 };
                                                    let owl__x1455 = temp_owl__x1455;
                                                    let temp_owl__x1462 = { owl__x1455 };
                                                    let owl__x1462 = temp_owl__x1462;
                                                    let temp_owl__x1464 = { owl__x1462 };
                                                    let owl__x1464 = temp_owl__x1464;
                                                    let temp_owl__x1465 = { owl__x1464 };
                                                    let owl__x1465 = temp_owl__x1465;
                                                    let temp_owl__x1468 = { owl__x1465 };
                                                    let owl__x1468 = temp_owl__x1468;
                                                    let temp_owl__x1469 = { Some(owl__x1468) };
                                                    let owl__x1469 = temp_owl__x1469;
                                                    (owl__x1469, Tracked(itree))
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
                let temp_owl__x1219 = { None };
                let owl__x1219 = temp_owl__x1219;
                (owl__x1219, Tracked(itree))
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
        owl_pk8139: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<Arc<Vec<u8>>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == checkpk_resp_spec(*self, *old(mut_state), owl_pk8139.dview()),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            use x25519_dalek::{PublicKey};
            use std::convert::TryInto;

            let pk: [u8; 32] = (&*owl_pk8139).as_slice().try_into().unwrap();
            (self.device.get_ss(&pk)
                .map(|ss| Arc::new(ss.to_vec())),
            Tracked(itree))
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
            let v = self.device.get_singleton_id();
            (Arc::new(v.to_le_bytes().to_vec()), Tracked(itree))
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
fn main() { /* entrypoint() */ }


