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
    pub owlSpec__transp_keys_T_init_send: Seq<u8>,
    pub owlSpec__transp_keys_T_resp_send: Seq<u8>,
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_transp_keys(x: Seq<u8>) -> Option<owlSpec_transp_keys> {
    let stream = parse_serialize::SpecStream { data: x, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::spec_parse_owl_transp_keys(stream) {
        let (
            (
                (owlSpec__transp_keys_initiator, owlSpec__transp_keys_responder),
                owlSpec__transp_keys_T_init_send,
            ),
            owlSpec__transp_keys_T_resp_send,
        ) = parsed;
        Some(
            owlSpec_transp_keys {
                owlSpec__transp_keys_initiator,
                owlSpec__transp_keys_responder,
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
    if no_usize_overflows_spec![ x.owlSpec__transp_keys_initiator.len(), x.owlSpec__transp_keys_responder.len(), x.owlSpec__transp_keys_T_init_send.len(), x.owlSpec__transp_keys_T_resp_send.len() ] {
        let stream = parse_serialize::SpecStream {
            data: seq_u8_of_len(
                x.owlSpec__transp_keys_initiator.len() + x.owlSpec__transp_keys_responder.len()
                    + x.owlSpec__transp_keys_T_init_send.len()
                    + x.owlSpec__transp_keys_T_resp_send.len(),
            ),
            start: 0,
        };
        if let Ok((serialized, n)) = parse_serialize::spec_serialize_owl_transp_keys(
            stream,
            ((
                (
                    (x.owlSpec__transp_keys_initiator, x.owlSpec__transp_keys_responder),
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
    arg__transp_keys_T_init_send: Seq<u8>,
    arg__transp_keys_T_resp_send: Seq<u8>,
) -> Seq<u8> {
    serialize_owlSpec_transp_keys(
        owlSpec_transp_keys {
            owlSpec__transp_keys_initiator: arg__transp_keys_initiator,
            owlSpec__transp_keys_responder: arg__transp_keys_responder,
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
pub open spec fn Initiator_main_spec(cfg: cfg_Initiator, mut_state: state_Initiator) -> (res: ITree<
    ((), state_Initiator),
    Endpoint,
>) {
    owl_spec!(mut_state,state_Initiator,
(ret (()))
)
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
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : _unused36 , owlSpec__transp_keys_responder : responder_name , owlSpec__transp_keys_T_init_send : _unused37 , owlSpec__transp_keys_T_resp_send : r2i_ }) in {
(if (from == responder_name) then (let r2i = ((ret (r2i_))) in
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
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : _unused115 , owlSpec__transp_keys_responder : transp_receiver , owlSpec__transp_keys_T_init_send : i2r_ , owlSpec__transp_keys_T_resp_send : _unused116 }) in {
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
(input (inp, _unused357)) in
(parse (parse_owlSpec_msg2(inp)) as (owlSpec_msg2{owlSpec__msg2_tag : msg2_tag , owlSpec__msg2_sender : msg2_sender , owlSpec__msg2_receiver : msg2_receiver , owlSpec__msg2_ephemeral : msg2_ephemeral_ , owlSpec__msg2_empty : msg2_empty , owlSpec__msg2_mac1 : msg2_mac1 , owlSpec__msg2_mac2 : msg2_mac2 }) in {
(parse (msg1_val) as (owlSpec_initiator_msg1_val{owlSpec__initiator_msg1_C3 : C3 , owlSpec__initiator_msg1_H4 : H4 }) in {
(if (andb( length(msg2_sender) == 4
, length( msg2_receiver ) == 4 )) then ((if (is_group_elem( msg2_ephemeral_ )) then (let psk = ((ret (zeros_32(  )))) in
let msg2_ephemeral = ((ret (msg2_ephemeral_))) in
let e_init = ((ret ((*cfg.owl_E_init).dview()))) in
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
(parse (parse_owlSpec_transp(c)) as (owlSpec_transp{owlSpec__transp_tag : _unused723 , owlSpec__transp_receiver : from , owlSpec__transp_counter : ctr , owlSpec__transp_packet : pkt }) in {
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : initiator_name , owlSpec__transp_keys_responder : _unused724 , owlSpec__transp_keys_T_init_send : i2r_ , owlSpec__transp_keys_T_resp_send : _unused725 }) in {
(if (from == initiator_name) then (let i2r = ((ret (i2r_))) in
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
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : transp_receiver , owlSpec__transp_keys_responder : _unused803 , owlSpec__transp_keys_T_init_send : _unused804 , owlSpec__transp_keys_T_resp_send : r2i_ }) in {
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
(input (inp, _unused1462)) in
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

#[verifier::opaque]
pub open spec fn dummy_main_spec(cfg: cfg_dummy, mut_state: state_dummy) -> (res: ITree<
    ((), state_dummy),
    Endpoint,
>) {
    owl_spec!(mut_state,state_dummy,
(ret (()))
)
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
    pub owl__transp_keys_T_init_send: Vec<u8>,
    pub owl__transp_keys_T_resp_send: Vec<u8>,
}

impl DView for owl_transp_keys {
    type V = owlSpec_transp_keys;
    
    open spec fn dview(&self) -> owlSpec_transp_keys {
        owlSpec_transp_keys {
            owlSpec__transp_keys_initiator: self.owl__transp_keys_initiator.dview().as_seq(),
            owlSpec__transp_keys_responder: self.owl__transp_keys_responder.dview().as_seq(),
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
                (owl__transp_keys_initiator, owl__transp_keys_responder),
                owl__transp_keys_T_init_send,
            ),
            owl__transp_keys_T_resp_send,
        ) = parsed;
        Some(
            owl_transp_keys {
                owl__transp_keys_initiator,
                owl__transp_keys_responder,
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
    if no_usize_overflows![ vec_length(&arg.owl__transp_keys_initiator), vec_length(&arg.owl__transp_keys_responder), vec_length(&arg.owl__transp_keys_T_init_send), vec_length(&arg.owl__transp_keys_T_resp_send) ] {
        let stream = parse_serialize::Stream {
            data: vec_u8_of_len(
                vec_length(&arg.owl__transp_keys_initiator) + vec_length(
                    &arg.owl__transp_keys_responder,
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
                        clone_vec_u8(&arg.owl__transp_keys_initiator),
                        clone_vec_u8(&arg.owl__transp_keys_responder),
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
    pub device: Option<crate::wireguard::handshake::device::DeviceInner<O>>,
}

impl<O> cfg_Initiator<O> {    

    pub exec fn owl_transp_recv_init_wrapper(
        &self,         
        mut_state: &mut state_Initiator,
        owl_transp_keys_val: owl_transp_keys,
        owl_c: Arc<Vec<u8>>,
    ) -> (_: Option<Arc<Vec<u8>>>) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_transp_recv_init(Tracked(call_token), mut_state, owl_transp_keys_val, owl_c).unwrap();
        res
    }
    
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
                    let owl__8 = arc_new(parseval.owl__transp_keys_T_init_send);
                    let owl_r2i_7 = arc_new(parseval.owl__transp_keys_T_resp_send);
                    {
                        let temp_owl__x28 = { arc_clone(&owl_from5) };
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
    
    pub exec fn owl_transp_send_init_wrapper(
        &self,         
        mut_state: &mut state_Initiator,
        owl_transp_keys_val: owl_transp_keys,
        owl_plaintext: Arc<Vec<u8>>,
        obuf: &mut [u8]
    ) -> (_: Option<()>) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_transp_send_init(Tracked(call_token), mut_state, owl_transp_keys_val, owl_plaintext, obuf).unwrap();
        res
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
            let temp_owl__x113 = { owl_transp_keys_val9527 };
            let owl__x113 = temp_owl__x113;
            let parseval = owl__x113;
            let owl__44 = arc_new(parseval.owl__transp_keys_initiator);
            let owl_transp_receiver43 = arc_new(parseval.owl__transp_keys_responder);
            let owl_i2r_40 = arc_new(parseval.owl__transp_keys_T_init_send);
            let owl__39 = arc_new(parseval.owl__transp_keys_T_resp_send);
            {
                let temp_owl__x49 = { arc_clone(&owl_i2r_40) };
                let owl__x49 = arc_clone(&temp_owl__x49);
                let temp_owl__x50 = { arc_clone(&owl__x49) };
                let owl__x50 = arc_clone(&temp_owl__x50);
                let temp_owl__x52 = { owl_counter_as_bytes(&(mut_state.owl_N_init_send)) };
                let owl__x52 = arc_new(temp_owl__x52);
                let temp_owl__x56 = { owl_transp_tag_value() };
                let owl__x56 = arc_new(temp_owl__x56);
                let temp_owl__x57 = { arc_clone(&owl__x56) };
                let owl__x57 = arc_clone(&temp_owl__x57);
                let temp_owl__x108 = { arc_clone(&owl_transp_receiver43) };
                let owl__x108 = arc_clone(&temp_owl__x108);
                let temp_owl__x109 = { vec_length(&(*arc_clone(&owl__x108))) };
                let owl__x109 = temp_owl__x109;
                let temp_owl__x111 = { 4 };
                let owl__x111 = temp_owl__x111;
                let temp_owl__x112 = { owl__x109 == owl__x111 };
                let owl__x112 = temp_owl__x112;
                if owl__x112 {
                    let temp_owl__x63 = { arc_clone(&owl__x50) };
                    let owl__x63 = arc_clone(&temp_owl__x63);
                    let temp_owl__x65 = { arc_clone(&owl_plaintext9526) };
                    let owl__x65 = arc_clone(&temp_owl__x65);
                    let temp_owl__x67 = {
                        {
                            let x: Vec<u8> = mk_vec_u8![];
                            x
                        }
                    };
                    let owl__x67 = arc_new(temp_owl__x67);
                    let temp_owl__x68 = {
                        match owl_enc_st_aead(
                            vec_as_slice(&(*arc_clone(&owl__x63))),
                            vec_as_slice(&(*arc_clone(&owl__x65))),
                            &mut mut_state.owl_N_init_send,
                            vec_as_slice(&(*arc_clone(&owl__x67))),
                        ) {
                            Ok(ctxt) => ctxt,
                            Err(e) => { return Err(e) },
                        }
                    };
                    let owl__x68 = arc_clone(&temp_owl__x68);
                    let temp_owl__x84 = { arc_clone(&owl__x57) };
                    let owl__x84 = arc_clone(&temp_owl__x84);
                    let temp_owl__x86 = { arc_clone(&owl_transp_receiver43) };
                    let owl__x86 = arc_clone(&temp_owl__x86);
                    let temp_owl__x88 = { arc_clone(&owl__x52) };
                    let owl__x88 = arc_clone(&temp_owl__x88);
                    let temp_owl__x90 = { arc_clone(&owl__x68) };
                    let owl__x90 = arc_clone(&temp_owl__x90);
                    let temp_owl__x92 = {
                    owl_transp {
                        owl__transp_tag: clone_vec_u8(&*arc_clone(&owl__x84)),
                        owl__transp_receiver: clone_vec_u8(&*arc_clone(&owl__x86)),
                        owl__transp_counter: clone_vec_u8(&*arc_clone(&owl__x88)),
                        owl__transp_packet: clone_vec_u8(&*arc_clone(&owl__x90)),
                    }
                    };
                    let owl__x92 = temp_owl__x92;
                    let temp_owl__x93 = { owl__x92 };
                    let owl__x93 = temp_owl__x93;
                    let temp_owl__x97 = { owl__x93 };
                    let owl__x97 = temp_owl__x97;
                    let temp_owl__x98 = {
                    owl_output::<(Option<()>, state_Initiator)>(
                        Tracked(&mut itree),
                        vec_as_slice(&(serialize_owl_transp(&owl__x97))),
                        &Responder_addr(),
                        &Initiator_addr(),
                        obuf
                    )
                    };
                    let owl__x98 = temp_owl__x98;
                    let temp_owl__x101 = { () };
                    let owl__x101 = temp_owl__x101;
                    let temp_owl__x102 = { Some(owl__x101) };
                    let owl__x102 = temp_owl__x102;
                    (owl__x102, Tracked(itree))
                } else {
                    (None, Tracked(itree))
                }
            }
        };
        Ok(res_inner)
    }

    pub fn owl_transp_send_init_inplace(
        &self,
        mut_state: &mut state_Initiator,
        owl_transp_keys_val: owl_transp_keys,
        buf: &mut [u8]
    ) -> (_: Option<()>) {
        reveal(transp_send_init_spec);
        let temp_owl__x113 = { owl_transp_keys_val };
        let owl__x113 = temp_owl__x113;
        let parseval = owl__x113;
        let owl__44 = arc_new(parseval.owl__transp_keys_initiator);
        let owl_transp_receiver43 = arc_new(parseval.owl__transp_keys_responder);
        let owl_i2r_40 = arc_new(parseval.owl__transp_keys_T_init_send);
        let owl__39 = arc_new(parseval.owl__transp_keys_T_resp_send);
        {
            let temp_owl__x49 = { arc_clone(&owl_i2r_40) };
            let owl__x49 = arc_clone(&temp_owl__x49);
            let temp_owl__x50 = { arc_clone(&owl__x49) };
            let owl__x50 = arc_clone(&temp_owl__x50);
            let temp_owl__x52 = { owl_counter_as_bytes(&(mut_state.owl_N_init_send)) };
            let owl__x52 = arc_new(temp_owl__x52);
            let temp_owl__x56 = { owl_transp_tag_value() };
            let owl__x56 = arc_new(temp_owl__x56);
            let temp_owl__x57 = { arc_clone(&owl__x56) };
            let owl__x57 = arc_clone(&temp_owl__x57);
            let temp_owl__x108 = { arc_clone(&owl_transp_receiver43) };
            let owl__x108 = arc_clone(&temp_owl__x108);
            let temp_owl__x109 = { vec_length(&(*arc_clone(&owl__x108))) };
            let owl__x109 = temp_owl__x109;
            let temp_owl__x111 = { 4 };
            let owl__x111 = temp_owl__x111;
            let temp_owl__x112 = { owl__x109 == owl__x111 };
            let owl__x112 = temp_owl__x112;
            if owl__x112 {
                let temp_owl__x63 = { arc_clone(&owl__x50) };
                let owl__x63 = arc_clone(&temp_owl__x63);
                let temp_owl__x67 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x67 = arc_new(temp_owl__x67);
                let temp_owl__x68 = {
                    let len = buf.len();
                    match owl_enc_st_aead_inplace(
                        vec_as_slice(&(*arc_clone(&owl__x63))),
                        &mut buf[16..],
                        &mut mut_state.owl_N_init_send,
                        vec_as_slice(&(*arc_clone(&owl__x67))),
                    ) {
                        Ok(ctxt) => ctxt,
                        Err(e) => { panic!() },
                    };
                    // arc_new(buf[16..].to_vec())
                };
                // let owl__x68 = arc_clone(&temp_owl__x68);
                let temp_owl__x84 = { arc_clone(&owl__x57) };
                let owl__x84 = arc_clone(&temp_owl__x84);
                let temp_owl__x86 = { arc_clone(&owl_transp_receiver43) };
                let owl__x86 = arc_clone(&temp_owl__x86);
                let temp_owl__x88 = { arc_clone(&owl__x52) };
                let owl__x88 = arc_clone(&temp_owl__x88);
                // let temp_owl__x90 = { arc_clone(&owl__x68) };
                // let owl__x90 = arc_clone(&temp_owl__x90);
                // let temp_owl__x92 = {
                // owl_transp {
                //     owl__transp_tag: clone_vec_u8(&*arc_clone(&owl__x84)),
                //     owl__transp_receiver: clone_vec_u8(&*arc_clone(&owl__x86)),
                //     owl__transp_counter: clone_vec_u8(&*arc_clone(&owl__x88)),
                //     owl__transp_packet: buf[16..].to_vec(),
                // }
                // };
                // let owl__x92 = temp_owl__x92;
                // let temp_owl__x93 = { owl__x92 };
                // let owl__x93 = temp_owl__x93;
                // let temp_owl__x97 = { owl__x93 };
                // let owl__x97 = temp_owl__x97;
                buf[0..4].copy_from_slice(&*arc_clone(&owl__x84));
                buf[4..8].copy_from_slice(&*arc_clone(&owl__x86));
                buf[8..16].copy_from_slice(&*arc_clone(&owl__x88));                
                // let temp_owl__x98 = {
                // owl_output::<(Option<()>, state_Initiator)>(
                //     Tracked(&mut itree),
                //     vec_as_slice(&(serialize_owl_transp(&owl__x97))),
                //     &Responder_addr(),
                //     &Initiator_addr(),
                //     buf
                // )
                // };
                // let owl__x98 = temp_owl__x98;
                let temp_owl__x101 = { () };
                let owl__x101 = temp_owl__x101;
                let temp_owl__x102 = { Some(owl__x101) };
                let owl__x102 = temp_owl__x102;
                owl__x102
            } else {
                None
            }
        }
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
            let (temp_owl_inp120, owl__119) = owl_input::<(Option<Seq<u8>>, state_Initiator)>(
                Tracked(&mut itree),
                ibuf,
            );
            let owl_inp120 = arc_new(temp_owl_inp120);
            let temp_owl__x349 = { arc_clone(&owl_inp120) };
            let owl__x349 = arc_clone(&temp_owl__x349);
            if let Some(parseval) = parse_owl_msg2(vec_as_slice(&(*arc_clone(&owl__x349)))) {
                let owl_msg2_tag128 = arc_new(parseval.owl__msg2_tag);
                let owl_msg2_sender127 = arc_new(parseval.owl__msg2_sender);
                let owl_msg2_receiver126 = arc_new(parseval.owl__msg2_receiver);
                let owl_msg2_ephemeral_125 = arc_new(parseval.owl__msg2_ephemeral);
                let owl_msg2_empty124 = arc_new(parseval.owl__msg2_empty);
                let owl_msg2_mac1123 = arc_new(parseval.owl__msg2_mac1);
                let owl_msg2_mac2122 = arc_new(parseval.owl__msg2_mac2);
                {
                    let temp_owl__x348 = { owl_msg1_val5831 };
                    let owl__x348 = temp_owl__x348;
                    let parseval = owl__x348;
                    let owl_C3130 = arc_new(parseval.owl__initiator_msg1_C3);
                    let owl_H4129 = arc_new(parseval.owl__initiator_msg1_H4);
                    {
                        let temp_owl__x334 = { arc_clone(&owl_msg2_sender127) };
                        let owl__x334 = arc_clone(&temp_owl__x334);
                        let temp_owl__x335 = { vec_length(&(*arc_clone(&owl__x334))) };
                        let owl__x335 = temp_owl__x335;
                        let temp_owl__x337 = { 4 };
                        let owl__x337 = temp_owl__x337;
                        let temp_owl__x338 = { owl__x335 == owl__x337 };
                        let owl__x338 = temp_owl__x338;
                        let temp_owl__x342 = { arc_clone(&owl_msg2_receiver126) };
                        let owl__x342 = arc_clone(&temp_owl__x342);
                        let temp_owl__x343 = { vec_length(&(*arc_clone(&owl__x342))) };
                        let owl__x343 = temp_owl__x343;
                        let temp_owl__x345 = { 4 };
                        let owl__x345 = temp_owl__x345;
                        let temp_owl__x346 = { owl__x343 == owl__x345 };
                        let owl__x346 = temp_owl__x346;
                        let temp_owl__x347 = { owl__x338 && owl__x346 };
                        let owl__x347 = temp_owl__x347;
                        if owl__x347 {
                            let temp_owl__x321 = { arc_clone(&owl_msg2_ephemeral_125) };
                            let owl__x321 = arc_clone(&temp_owl__x321);
                            let temp_owl__x322 = {
                            owl_is_group_elem(vec_as_slice(&(*arc_clone(&owl__x321))))
                            };
                            let owl__x322 = temp_owl__x322;
                            if owl__x322 {
                                let temp_owl__x134 = { owl_zeros_32() };
                                let owl__x134 = arc_new(temp_owl__x134);
                                let temp_owl__x135 = { arc_clone(&owl__x134) };
                                let owl__x135 = arc_clone(&temp_owl__x135);
                                let temp_owl__x140 = { arc_clone(&owl_msg2_ephemeral_125) };
                                let owl__x140 = arc_clone(&temp_owl__x140);
                                let temp_owl__x141 = { arc_clone(&owl__x140) };
                                let owl__x141 = arc_clone(&temp_owl__x141);
                                let temp_owl__x145 = { arc_clone(&self.owl_E_init) };
                                let owl__x145 = arc_clone(&temp_owl__x145);
                                let temp_owl__x146 = { arc_clone(&owl__x145) };
                                let owl__x146 = arc_clone(&temp_owl__x146);
                                let temp_owl__x151 = { arc_clone(&owl_C3130) };
                                let owl__x151 = arc_clone(&temp_owl__x151);
                                let temp_owl__x153 = { arc_clone(&owl__x141) };
                                let owl__x153 = arc_clone(&temp_owl__x153);
                                let owl_msg2_C4352 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x151))),
                                    vec_as_slice(&(*arc_clone(&owl__x153))),
                                );
                                let temp_owl__x154 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C4352),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x154 = arc_clone(&temp_owl__x154);
                                let temp_owl__x167 = { arc_clone(&owl_H4129) };
                                let owl__x167 = arc_clone(&temp_owl__x167);
                                let temp_owl__x169 = { arc_clone(&owl__x141) };
                                let owl__x169 = arc_clone(&temp_owl__x169);
                                let temp_owl__x171 = {
                                owl_concat(
                                    vec_as_slice(&(*arc_clone(&owl__x167))),
                                    vec_as_slice(&(*arc_clone(&owl__x169))),
                                )
                                };
                                let owl__x171 = arc_new(temp_owl__x171);
                                let temp_owl__x173 = {
                                owl_crh(vec_as_slice(&(*arc_clone(&owl__x171))))
                                };
                                let owl__x173 = arc_clone(&temp_owl__x173);
                                let temp_owl__x174 = { arc_clone(&owl__x173) };
                                let owl__x174 = arc_clone(&temp_owl__x174);
                                let temp_owl__x184 = { arc_clone(&owl__x141) };
                                let owl__x184 = arc_clone(&temp_owl__x184);
                                let temp_owl__x186 = { arc_clone(&owl__x146) };
                                let owl__x186 = arc_clone(&temp_owl__x186);
                                let temp_owl__x188 = {
                                owl_dh_combine(
                                    vec_as_slice(&(*arc_clone(&owl__x184))),
                                    vec_as_slice(&(*arc_clone(&owl__x186))),
                                )
                                };
                                let owl__x188 = arc_clone(&temp_owl__x188);
                                let temp_owl__x189 = { arc_clone(&owl__x188) };
                                let owl__x189 = arc_clone(&temp_owl__x189);
                                let temp_owl__x194 = { arc_clone(&owl__x154) };
                                let owl__x194 = arc_clone(&temp_owl__x194);
                                let temp_owl__x196 = { arc_clone(&owl__x189) };
                                let owl__x196 = arc_clone(&temp_owl__x196);
                                let owl_msg2_C5353 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x194))),
                                    vec_as_slice(&(*arc_clone(&owl__x196))),
                                );
                                let temp_owl__x197 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C5353),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x197 = arc_clone(&temp_owl__x197);
                                let temp_owl__x204 = { arc_clone(&owl__x197) };
                                let owl__x204 = arc_clone(&temp_owl__x204);
                                let temp_owl__x207 = { arc_clone(&owl__x141) };
                                let owl__x207 = arc_clone(&temp_owl__x207);
                                let temp_owl__x209 = { arc_clone(&self.owl_S_init) };
                                let owl__x209 = arc_clone(&temp_owl__x209);
                                let temp_owl__x210 = {
                                owl_dh_combine(
                                    vec_as_slice(&(*arc_clone(&owl__x207))),
                                    vec_as_slice(&(*arc_clone(&owl__x209))),
                                )
                                };
                                let owl__x210 = arc_clone(&temp_owl__x210);
                                let owl_msg2_C6354 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x204))),
                                    vec_as_slice(&(*arc_clone(&owl__x210))),
                                );
                                let temp_owl__x211 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C6354),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x211 = arc_clone(&temp_owl__x211);
                                let temp_owl__x216 = { arc_clone(&owl__x211) };
                                let owl__x216 = arc_clone(&temp_owl__x216);
                                let temp_owl__x218 = { arc_clone(&owl__x135) };
                                let owl__x218 = arc_clone(&temp_owl__x218);
                                let owl_msg2_C7355 = owl_extract_expand_to_len(
                                    0 + nonce_size() + nonce_size() + key_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x216))),
                                    vec_as_slice(&(*arc_clone(&owl__x218))),
                                );
                                let temp_owl__x219 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7355),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x219 = arc_clone(&temp_owl__x219);
                                let temp_owl__x224 = { arc_clone(&owl__x211) };
                                let owl__x224 = arc_clone(&temp_owl__x224);
                                let temp_owl__x226 = { arc_clone(&owl__x135) };
                                let owl__x226 = arc_clone(&temp_owl__x226);
                                let temp_owl__x227 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7355),
                                            0 + nonce_size(),
                                            0 + nonce_size() + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x227 = arc_clone(&temp_owl__x227);
                                let temp_owl__x232 = { arc_clone(&owl__x211) };
                                let owl__x232 = arc_clone(&temp_owl__x232);
                                let temp_owl__x234 = { arc_clone(&owl__x135) };
                                let owl__x234 = arc_clone(&temp_owl__x234);
                                let temp_owl__x235 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7355),
                                            0 + nonce_size() + nonce_size(),
                                            0 + nonce_size() + nonce_size() + key_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x235 = arc_clone(&temp_owl__x235);
                                let temp_owl__x248 = { arc_clone(&owl__x174) };
                                let owl__x248 = arc_clone(&temp_owl__x248);
                                let temp_owl__x250 = { arc_clone(&owl__x227) };
                                let owl__x250 = arc_clone(&temp_owl__x250);
                                let temp_owl__x252 = {
                                owl_concat(
                                    vec_as_slice(&(*arc_clone(&owl__x248))),
                                    vec_as_slice(&(*arc_clone(&owl__x250))),
                                )
                                };
                                let owl__x252 = arc_new(temp_owl__x252);
                                let temp_owl__x254 = {
                                owl_crh(vec_as_slice(&(*arc_clone(&owl__x252))))
                                };
                                let owl__x254 = arc_clone(&temp_owl__x254);
                                let temp_owl__x255 = { arc_clone(&owl__x254) };
                                let owl__x255 = arc_clone(&temp_owl__x255);
                                let temp_owl__x259 = {
                                    {
                                        let x: Vec<u8> = mk_vec_u8![];
                                        x
                                    }
                                };
                                let owl__x259 = arc_new(temp_owl__x259);
                                let temp_owl__x260 = { arc_clone(&owl__x259) };
                                let owl__x260 = arc_clone(&temp_owl__x260);
                                let temp_owl__x311 = { arc_clone(&owl__x235) };
                                let owl__x311 = arc_clone(&temp_owl__x311);
                                let temp_owl__x313 = { arc_clone(&owl_msg2_empty124) };
                                let owl__x313 = arc_clone(&temp_owl__x313);
                                let temp_owl__x315 = { arc_clone(&owl__x255) };
                                let owl__x315 = arc_clone(&temp_owl__x315);
                                let temp_owl__x317 = {
                                    {
                                        let x: Vec<u8> = mk_vec_u8![];
                                        x
                                    }
                                };
                                let owl__x317 = arc_new(temp_owl__x317);
                                let temp_owl__x318 = {
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x311))),
                                    vec_as_slice(&(*arc_clone(&owl__x313))),
                                    vec_as_slice(&(*arc_clone(&owl__x317))),
                                    vec_as_slice(&(*arc_clone(&owl__x315))),
                                )
                                };
                                let owl__x318 = temp_owl__x318;
                                let temp_owl_caseval351 = { owl__x318 };
                                let owl_caseval351 = temp_owl_caseval351;
                                match owl_caseval351 {
                                    None => {
                                        let temp_owl__x265 = { None };
                                        let owl__x265 = temp_owl__x265;
                                        (owl__x265, Tracked(itree))
                                    },
                                    Some(temp_owl_msg2_empty_dec266) => {
                                        let owl_msg2_empty_dec266 = arc_clone(
                                            &temp_owl_msg2_empty_dec266,
                                        );
                                        let temp_owl__x306 = { arc_clone(&owl_msg2_empty_dec266) };
                                        let owl__x306 = arc_clone(&temp_owl__x306);
                                        let temp_owl__x308 = { arc_clone(&owl__x260) };
                                        let owl__x308 = arc_clone(&temp_owl__x308);
                                        let temp_owl__x309 = {
                                        rc_vec_eq(&arc_clone(&owl__x306), &arc_clone(&owl__x308))
                                        };
                                        let owl__x309 = temp_owl__x309;
                                        if owl__x309 {
                                            let temp_owl__x279 = { arc_clone(&owl__x255) };
                                            let owl__x279 = arc_clone(&temp_owl__x279);
                                            let temp_owl__x281 = { arc_clone(&owl_msg2_empty124) };
                                            let owl__x281 = arc_clone(&temp_owl__x281);
                                            let temp_owl__x283 = {
                                            owl_concat(
                                                vec_as_slice(&(*arc_clone(&owl__x279))),
                                                vec_as_slice(&(*arc_clone(&owl__x281))),
                                            )
                                            };
                                            let owl__x283 = arc_new(temp_owl__x283);
                                            let temp_owl__x285 = {
                                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x283))))
                                            };
                                            let owl__x285 = arc_clone(&temp_owl__x285);
                                            let temp_owl__x286 = { arc_clone(&owl__x285) };
                                            let owl__x286 = arc_clone(&temp_owl__x286);
                                            let temp_owl__x291 = { arc_clone(&owl__x219) };
                                            let owl__x291 = arc_clone(&temp_owl__x291);
                                            let temp_owl__x293 = {
                                                {
                                                    let x: Vec<u8> = mk_vec_u8![];
                                                    x
                                                }
                                            };
                                            let owl__x293 = arc_new(temp_owl__x293);
                                            let owl_transp_T356 = owl_extract_expand_to_len(
                                                0 + key_size() + key_size(),
                                                vec_as_slice(&(*arc_clone(&owl__x291))),
                                                vec_as_slice(&(*arc_clone(&owl__x293))),
                                            );
                                            let temp_owl__x294 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_transp_T356),
                                                        0,
                                                        0 + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x294 = arc_clone(&temp_owl__x294);
                                            let temp_owl__x299 = { arc_clone(&owl__x219) };
                                            let owl__x299 = arc_clone(&temp_owl__x299);
                                            let temp_owl__x301 = {
                                                {
                                                    let x: Vec<u8> = mk_vec_u8![];
                                                    x
                                                }
                                            };
                                            let owl__x301 = arc_new(temp_owl__x301);
                                            let temp_owl__x302 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_transp_T356),
                                                        0 + key_size(),
                                                        0 + key_size() + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x302 = arc_clone(&temp_owl__x302);
                                            let temp_owl_retval202 = {
                                            owl_transp_keys {
                                                owl__transp_keys_initiator: clone_vec_u8(
                                                    &*arc_clone(&owl_msg2_receiver126),
                                                ),
                                                owl__transp_keys_responder: clone_vec_u8(
                                                    &*arc_clone(&owl_msg2_sender127),
                                                ),
                                                owl__transp_keys_T_init_send: clone_vec_u8(
                                                    &*arc_clone(&owl__x294),
                                                ),
                                                owl__transp_keys_T_resp_send: clone_vec_u8(
                                                    &*arc_clone(&owl__x302),
                                                ),
                                            }
                                            };
                                            let owl_retval202 = temp_owl_retval202;
                                            (Some(owl_retval202), Tracked(itree))
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
                let temp_owl__x121 = { None };
                let owl__x121 = temp_owl__x121;
                (owl__x121, Tracked(itree))
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
            let temp_owl__x364 = { owl_construction() };
            let owl__x364 = arc_new(temp_owl__x364);
            let temp_owl__x366 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x364)))) };
            let owl__x366 = arc_clone(&temp_owl__x366);
            let temp_owl__x367 = { arc_clone(&owl__x366) };
            let owl__x367 = arc_clone(&temp_owl__x367);
            let temp_owl__x380 = { arc_clone(&owl__x367) };
            let owl__x380 = arc_clone(&temp_owl__x380);
            let temp_owl__x382 = { owl_identifier() };
            let owl__x382 = arc_new(temp_owl__x382);
            let temp_owl__x384 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x380))),
                vec_as_slice(&(*arc_clone(&owl__x382))),
            )
            };
            let owl__x384 = arc_new(temp_owl__x384);
            let temp_owl__x386 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x384)))) };
            let owl__x386 = arc_clone(&temp_owl__x386);
            let temp_owl__x387 = { arc_clone(&owl__x386) };
            let owl__x387 = arc_clone(&temp_owl__x387);
            let temp_owl__x400 = { arc_clone(&owl__x387) };
            let owl__x400 = arc_clone(&temp_owl__x400);
            let temp_owl__x402 = { arc_clone(&owl_dhpk_S_resp5818) };
            let owl__x402 = arc_clone(&temp_owl__x402);
            let temp_owl__x404 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x400))),
                vec_as_slice(&(*arc_clone(&owl__x402))),
            )
            };
            let owl__x404 = arc_new(temp_owl__x404);
            let temp_owl__x406 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x404)))) };
            let owl__x406 = arc_clone(&temp_owl__x406);
            let temp_owl__x407 = { arc_clone(&owl__x406) };
            let owl__x407 = arc_clone(&temp_owl__x407);
            let temp_owl__x414 = { arc_clone(&self.owl_E_init) };
            let owl__x414 = arc_clone(&temp_owl__x414);
            let temp_owl__x416 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x414)))) };
            let owl__x416 = arc_clone(&temp_owl__x416);
            let temp_owl__x417 = { arc_clone(&owl__x416) };
            let owl__x417 = arc_clone(&temp_owl__x417);
            let temp_owl__x422 = { arc_clone(&owl__x367) };
            let owl__x422 = arc_clone(&temp_owl__x422);
            let temp_owl__x424 = { arc_clone(&owl__x417) };
            let owl__x424 = arc_clone(&temp_owl__x424);
            let owl_msg1_C1685 = owl_extract_expand_to_len(
                0 + nonce_size(),
                vec_as_slice(&(*arc_clone(&owl__x422))),
                vec_as_slice(&(*arc_clone(&owl__x424))),
            );
            let temp_owl__x425 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C1685), 0, 0 + nonce_size())),
            )
            };
            let owl__x425 = arc_clone(&temp_owl__x425);
            let temp_owl__x438 = { arc_clone(&owl__x407) };
            let owl__x438 = arc_clone(&temp_owl__x438);
            let temp_owl__x440 = { arc_clone(&owl__x417) };
            let owl__x440 = arc_clone(&temp_owl__x440);
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
            let temp_owl__x455 = { arc_clone(&owl_dhpk_S_resp5818) };
            let owl__x455 = arc_clone(&temp_owl__x455);
            let temp_owl__x457 = { arc_clone(&self.owl_E_init) };
            let owl__x457 = arc_clone(&temp_owl__x457);
            let temp_owl__x459 = {
            owl_dh_combine(
                vec_as_slice(&(*arc_clone(&owl__x455))),
                vec_as_slice(&(*arc_clone(&owl__x457))),
            )
            };
            let owl__x459 = arc_clone(&temp_owl__x459);
            let temp_owl__x460 = { arc_clone(&owl__x459) };
            let owl__x460 = arc_clone(&temp_owl__x460);
            let temp_owl__x465 = { arc_clone(&owl__x425) };
            let owl__x465 = arc_clone(&temp_owl__x465);
            let temp_owl__x467 = { arc_clone(&owl__x460) };
            let owl__x467 = arc_clone(&temp_owl__x467);
            let owl_msg1_C2686 = owl_extract_expand_to_len(
                0 + nonce_size() + key_size(),
                vec_as_slice(&(*arc_clone(&owl__x465))),
                vec_as_slice(&(*arc_clone(&owl__x467))),
            );
            let temp_owl__x468 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C2686), 0, 0 + nonce_size())),
            )
            };
            let owl__x468 = arc_clone(&temp_owl__x468);
            let temp_owl__x473 = { arc_clone(&owl__x425) };
            let owl__x473 = arc_clone(&temp_owl__x473);
            let temp_owl__x475 = { arc_clone(&owl__x460) };
            let owl__x475 = arc_clone(&temp_owl__x475);
            let temp_owl__x476 = {
            arc_new(
                slice_to_vec(
                    slice_subrange(
                        vec_as_slice(&*owl_msg1_C2686),
                        0 + nonce_size(),
                        0 + nonce_size() + key_size(),
                    ),
                ),
            )
            };
            let owl__x476 = arc_clone(&temp_owl__x476);
            let temp_owl__x483 = { arc_clone(&owl__x476) };
            let owl__x483 = arc_clone(&temp_owl__x483);
            let temp_owl__x486 = { arc_clone(&owl_dhpk_S_init5817) };
            let owl__x486 = arc_clone(&temp_owl__x486);
            let temp_owl__x487 = { arc_clone(&owl__x486) };
            let owl__x487 = arc_clone(&temp_owl__x487);
            let temp_owl__x489 = { arc_clone(&owl__x445) };
            let owl__x489 = arc_clone(&temp_owl__x489);
            let temp_owl__x490 = {
                match owl_enc_st_aead(
                    vec_as_slice(&(*arc_clone(&owl__x483))),
                    vec_as_slice(&(*arc_clone(&owl__x487))),
                    &mut mut_state.owl_aead_counter_msg1_C2,
                    vec_as_slice(&(*arc_clone(&owl__x489))),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x490 = arc_clone(&temp_owl__x490);
            let temp_owl__x503 = { arc_clone(&owl__x445) };
            let owl__x503 = arc_clone(&temp_owl__x503);
            let temp_owl__x505 = { arc_clone(&owl__x490) };
            let owl__x505 = arc_clone(&temp_owl__x505);
            let temp_owl__x507 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x503))),
                vec_as_slice(&(*arc_clone(&owl__x505))),
            )
            };
            let owl__x507 = arc_new(temp_owl__x507);
            let temp_owl__x509 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x507)))) };
            let owl__x509 = arc_clone(&temp_owl__x509);
            let temp_owl__x510 = { arc_clone(&owl__x509) };
            let owl__x510 = arc_clone(&temp_owl__x510);
            let temp_owl__x515 = { arc_clone(&owl__x468) };
            let owl__x515 = arc_clone(&temp_owl__x515);
            let temp_owl__x517 = { arc_clone(&owl_ss_S_resp_S_init5816) };
            let owl__x517 = arc_clone(&temp_owl__x517);
            let owl_msg1_C3687 = owl_extract_expand_to_len(
                0 + nonce_size() + key_size(),
                vec_as_slice(&(*arc_clone(&owl__x515))),
                vec_as_slice(&(*arc_clone(&owl__x517))),
            );
            let temp_owl__x518 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C3687), 0, 0 + nonce_size())),
            )
            };
            let owl__x518 = arc_clone(&temp_owl__x518);
            let temp_owl__x523 = { arc_clone(&owl__x468) };
            let owl__x523 = arc_clone(&temp_owl__x523);
            let temp_owl__x525 = { arc_clone(&owl_ss_S_resp_S_init5816) };
            let owl__x525 = arc_clone(&temp_owl__x525);
            let temp_owl__x526 = {
            arc_new(
                slice_to_vec(
                    slice_subrange(
                        vec_as_slice(&*owl_msg1_C3687),
                        0 + nonce_size(),
                        0 + nonce_size() + key_size(),
                    ),
                ),
            )
            };
            let owl__x526 = arc_clone(&temp_owl__x526);
            let (temp_owl__x528, Tracked(itree)): (
                _,
                Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
            ) = {
                owl_call!( itree
, *mut_state
, timestamp_i_spec(*self, *mut_state)
, self.owl_timestamp_i(mut_state) )
            };
            let owl__x528 = arc_clone(&temp_owl__x528);
            let temp_owl__x534 = { arc_clone(&owl__x526) };
            let owl__x534 = arc_clone(&temp_owl__x534);
            let temp_owl__x536 = { arc_clone(&owl__x528) };
            let owl__x536 = arc_clone(&temp_owl__x536);
            let temp_owl__x538 = { arc_clone(&owl__x510) };
            let owl__x538 = arc_clone(&temp_owl__x538);
            let temp_owl__x539 = {
                match owl_enc_st_aead(
                    vec_as_slice(&(*arc_clone(&owl__x534))),
                    vec_as_slice(&(*arc_clone(&owl__x536))),
                    &mut mut_state.owl_aead_counter_msg1_C3,
                    vec_as_slice(&(*arc_clone(&owl__x538))),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x539 = arc_clone(&temp_owl__x539);
            let temp_owl__x552 = { arc_clone(&owl__x510) };
            let owl__x552 = arc_clone(&temp_owl__x552);
            let temp_owl__x554 = { arc_clone(&owl__x539) };
            let owl__x554 = arc_clone(&temp_owl__x554);
            let temp_owl__x556 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x552))),
                vec_as_slice(&(*arc_clone(&owl__x554))),
            )
            };
            let owl__x556 = arc_new(temp_owl__x556);
            let temp_owl__x558 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x556)))) };
            let owl__x558 = arc_clone(&temp_owl__x558);
            let temp_owl__x559 = { arc_clone(&owl__x558) };
            let owl__x559 = arc_clone(&temp_owl__x559);
            let (temp_owl__x561, Tracked(itree)): (
                _,
                Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
            ) = {
                owl_call!( itree
, *mut_state
, get_sender_i_spec(*self, *mut_state)
, self.owl_get_sender_i(mut_state) )
            };
            let owl__x561 = arc_clone(&temp_owl__x561);
            let temp_owl__x565 = { owl_msg1_tag_value() };
            let owl__x565 = arc_new(temp_owl__x565);
            let temp_owl__x566 = { arc_clone(&owl__x565) };
            let owl__x566 = arc_clone(&temp_owl__x566);
            let temp_owl__x579 = { owl_mac1() };
            let owl__x579 = arc_new(temp_owl__x579);
            let temp_owl__x581 = { arc_clone(&owl_dhpk_S_resp5818) };
            let owl__x581 = arc_clone(&temp_owl__x581);
            let temp_owl__x583 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x579))),
                vec_as_slice(&(*arc_clone(&owl__x581))),
            )
            };
            let owl__x583 = arc_new(temp_owl__x583);
            let temp_owl__x585 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x583)))) };
            let owl__x585 = arc_clone(&temp_owl__x585);
            let temp_owl__x586 = { arc_clone(&owl__x585) };
            let owl__x586 = arc_clone(&temp_owl__x586);
            let temp_owl__x599 = { arc_clone(&owl__x586) };
            let owl__x599 = arc_clone(&temp_owl__x599);
            let temp_owl__x605 = { arc_clone(&owl__x566) };
            let owl__x605 = arc_clone(&temp_owl__x605);
            let temp_owl__x607 = { arc_clone(&owl__x561) };
            let owl__x607 = arc_clone(&temp_owl__x607);
            let temp_owl__x608 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x605))),
                vec_as_slice(&(*arc_clone(&owl__x607))),
            )
            };
            let owl__x608 = arc_new(temp_owl__x608);
            let temp_owl__x610 = { arc_clone(&owl__x417) };
            let owl__x610 = arc_clone(&temp_owl__x610);
            let temp_owl__x611 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x608))),
                vec_as_slice(&(*arc_clone(&owl__x610))),
            )
            };
            let owl__x611 = arc_new(temp_owl__x611);
            let temp_owl__x613 = { arc_clone(&owl__x490) };
            let owl__x613 = arc_clone(&temp_owl__x613);
            let temp_owl__x614 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x611))),
                vec_as_slice(&(*arc_clone(&owl__x613))),
            )
            };
            let owl__x614 = arc_new(temp_owl__x614);
            let temp_owl__x616 = { arc_clone(&owl__x539) };
            let owl__x616 = arc_clone(&temp_owl__x616);
            let temp_owl__x617 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x614))),
                vec_as_slice(&(*arc_clone(&owl__x616))),
            )
            };
            let owl__x617 = arc_new(temp_owl__x617);
            let temp_owl__x618 = {
            owl_mac(
                vec_as_slice(&(*arc_clone(&owl__x599))),
                vec_as_slice(&(*arc_clone(&owl__x617))),
            )
            };
            let owl__x618 = arc_clone(&temp_owl__x618);
            let temp_owl__x622 = { owl_zeros_16() };
            let owl__x622 = arc_new(temp_owl__x622);
            let temp_owl__x623 = { arc_clone(&owl__x622) };
            let owl__x623 = arc_clone(&temp_owl__x623);
            let temp_owl__x648 = { arc_clone(&owl__x566) };
            let owl__x648 = arc_clone(&temp_owl__x648);
            let temp_owl__x650 = { arc_clone(&owl__x561) };
            let owl__x650 = arc_clone(&temp_owl__x650);
            let temp_owl__x652 = { arc_clone(&owl__x417) };
            let owl__x652 = arc_clone(&temp_owl__x652);
            let temp_owl__x654 = { arc_clone(&owl__x490) };
            let owl__x654 = arc_clone(&temp_owl__x654);
            let temp_owl__x656 = { arc_clone(&owl__x539) };
            let owl__x656 = arc_clone(&temp_owl__x656);
            let temp_owl__x658 = { arc_clone(&owl__x618) };
            let owl__x658 = arc_clone(&temp_owl__x658);
            let temp_owl__x660 = { arc_clone(&owl__x623) };
            let owl__x660 = arc_clone(&temp_owl__x660);
            let temp_owl__x662 = {
            owl_msg1 {
                owl__msg1_tag: clone_vec_u8(&*arc_clone(&owl__x648)),
                owl__msg1_sender: clone_vec_u8(&*arc_clone(&owl__x650)),
                owl__msg1_ephemeral: clone_vec_u8(&*arc_clone(&owl__x652)),
                owl__msg1_static: clone_vec_u8(&*arc_clone(&owl__x654)),
                owl__msg1_timestamp: clone_vec_u8(&*arc_clone(&owl__x656)),
                owl__msg1_mac1: clone_vec_u8(&*arc_clone(&owl__x658)),
                owl__msg1_mac2: clone_vec_u8(&*arc_clone(&owl__x660)),
            }
            };
            let owl__x662 = temp_owl__x662;
            let temp_owl__x663 = { owl__x662 };
            let owl__x663 = temp_owl__x663;
            let temp_owl__x667 = { owl__x663 };
            let owl__x667 = temp_owl__x667;
            let temp_owl__x668 = {
            owl_output::<(Seq<u8>, state_Initiator)>(
                Tracked(&mut itree),
                vec_as_slice(&(serialize_owl_msg1(&owl__x667))),
                &Responder_addr(),
                &Initiator_addr(),
                obuf
            )
            };
            let owl__x668 = temp_owl__x668;
            let temp_owl__x678 = { arc_clone(&owl__x518) };
            let owl__x678 = arc_clone(&temp_owl__x678);
            let temp_owl__x680 = { arc_clone(&owl__x559) };
            let owl__x680 = arc_clone(&temp_owl__x680);
            let temp_owl__x682 = {
            owl_initiator_msg1_val {
                owl__initiator_msg1_C3: clone_vec_u8(&*arc_clone(&owl__x678)),
                owl__initiator_msg1_H4: clone_vec_u8(&*arc_clone(&owl__x680)),
            }
            };
            let owl__x682 = temp_owl__x682;
            let temp_owl__x683 = { owl__x682 };
            let owl__x683 = temp_owl__x683;
            let temp_owl__x684 = { owl__x683 };
            let owl__x684 = temp_owl__x684;
            (owl__x684, Tracked(itree))
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
            let v = self.device.as_ref().unwrap().get_singleton_id();
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
    pub device: Option<crate::wireguard::handshake::device::DeviceInner<O>>,
}

impl<O> cfg_Responder<O> { 

    pub exec fn owl_transp_recv_resp_wrapper(
        &self,         
        mut_state: &mut state_Responder,
        owl_transp_keys_val: owl_transp_keys,
        owl_c: Arc<Vec<u8>>,
    ) -> (_: Option<Arc<Vec<u8>>>) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_recv_resp_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_transp_recv_resp(Tracked(call_token), mut_state, owl_transp_keys_val, owl_c).unwrap();
        res
    }
    
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
            let temp_owl__x721 = { arc_clone(&owl_c14558) };
            let owl__x721 = arc_clone(&temp_owl__x721);
            if let Some(parseval) = parse_owl_transp(vec_as_slice(&(*arc_clone(&owl__x721)))) {
                let owl__694 = arc_new(parseval.owl__transp_tag);
                let owl_from693 = arc_new(parseval.owl__transp_receiver);
                let owl_ctr692 = arc_new(parseval.owl__transp_counter);
                let owl_pkt691 = arc_new(parseval.owl__transp_packet);
                {
                    let temp_owl__x720 = { owl_transp_keys_val14559 };
                    let owl__x720 = temp_owl__x720;
                    let parseval = owl__x720;
                    let owl_initiator_name700 = arc_new(parseval.owl__transp_keys_initiator);
                    let owl__699 = arc_new(parseval.owl__transp_keys_responder);
                    let owl_i2r_696 = arc_new(parseval.owl__transp_keys_T_init_send);
                    let owl__695 = arc_new(parseval.owl__transp_keys_T_resp_send);
                    {
                        let temp_owl__x716 = { arc_clone(&owl_from693) };
                        let owl__x716 = arc_clone(&temp_owl__x716);
                        let temp_owl__x718 = { arc_clone(&owl_initiator_name700) };
                        let owl__x718 = arc_clone(&temp_owl__x718);
                        // let temp_owl__x719 = {
                        // rc_vec_eq(&arc_clone(&owl__x716), &arc_clone(&owl__x718))
                        // };
                        // let owl__x719 = temp_owl__x719;
                        //if owl__x719 {
                            let temp_owl__x705 = { arc_clone(&owl_i2r_696) };
                            let owl__x705 = arc_clone(&temp_owl__x705);
                            let temp_owl__x706 = { arc_clone(&owl__x705) };
                            let owl__x706 = arc_clone(&temp_owl__x706);
                            let temp_owl__x709 = { arc_clone(&owl__x706) };
                            let owl__x709 = arc_clone(&temp_owl__x709);
                            let temp_owl__x710 = { arc_clone(&owl_pkt691) };
                            let owl__x710 = arc_clone(&temp_owl__x710);
                            let temp_owl__x711 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x711 = arc_new(temp_owl__x711);
                            let temp_owl__x712 = { arc_clone(&owl_ctr692) };
                            let owl__x712 = arc_clone(&temp_owl__x712);
                            (
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x709))),
                                    vec_as_slice(&(*arc_clone(&owl__x710))),
                                    vec_as_slice(&(*arc_clone(&owl__x712))),
                                    vec_as_slice(&(*arc_clone(&owl__x711))),
                                ),
                                Tracked(itree),
                            )
                        // } else {
                        //     (None, Tracked(itree))
                        // }
                    }
                }
            } else {
                let temp_owl__x690 = { None };
                let owl__x690 = temp_owl__x690;
                (owl__x690, Tracked(itree))
            }
        };
        Ok(res_inner)
    }
    
    pub exec fn owl_transp_send_resp_wrapper(
        &self,         
        mut_state: &mut state_Responder,
        owl_transp_keys_val: owl_transp_keys,
        owl_plaintext: Arc<Vec<u8>>,
        obuf: &mut [u8]
    ) -> (_: Option<()>) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            transp_send_init_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _) =
            self.owl_transp_send_resp(Tracked(call_token), mut_state, owl_transp_keys_val, owl_plaintext, obuf).unwrap();
        res
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
            let temp_owl__x801 = { owl_transp_keys_val12794 };
            let owl__x801 = temp_owl__x801;
            let parseval = owl__x801;
            let owl_transp_receiver732 = arc_new(parseval.owl__transp_keys_initiator);
            let owl__731 = arc_new(parseval.owl__transp_keys_responder);
            let owl__728 = arc_new(parseval.owl__transp_keys_T_init_send);
            let owl_r2i_727 = arc_new(parseval.owl__transp_keys_T_resp_send);
            {
                let temp_owl__x737 = { arc_clone(&owl_r2i_727) };
                let owl__x737 = arc_clone(&temp_owl__x737);
                let temp_owl__x738 = { arc_clone(&owl__x737) };
                let owl__x738 = arc_clone(&temp_owl__x738);
                let temp_owl__x740 = { owl_counter_as_bytes(&(mut_state.owl_N_resp_send)) };
                let owl__x740 = arc_new(temp_owl__x740);
                let temp_owl__x744 = { owl_transp_tag_value() };
                let owl__x744 = arc_new(temp_owl__x744);
                let temp_owl__x745 = { arc_clone(&owl__x744) };
                let owl__x745 = arc_clone(&temp_owl__x745);
                let temp_owl__x796 = { arc_clone(&owl_transp_receiver732) };
                let owl__x796 = arc_clone(&temp_owl__x796);
                let temp_owl__x797 = { vec_length(&(*arc_clone(&owl__x796))) };
                let owl__x797 = temp_owl__x797;
                let temp_owl__x799 = { 4 };
                let owl__x799 = temp_owl__x799;
                let temp_owl__x800 = { owl__x797 == owl__x799 };
                let owl__x800 = temp_owl__x800;
                if owl__x800 {
                    let temp_owl__x751 = { arc_clone(&owl__x738) };
                    let owl__x751 = arc_clone(&temp_owl__x751);
                    let temp_owl__x753 = { arc_clone(&owl_plaintext12793) };
                    let owl__x753 = arc_clone(&temp_owl__x753);
                    let temp_owl__x755 = {
                        {
                            let x: Vec<u8> = mk_vec_u8![];
                            x
                        }
                    };
                    let owl__x755 = arc_new(temp_owl__x755);
                    let temp_owl__x756 = {
                        match owl_enc_st_aead(
                            vec_as_slice(&(*arc_clone(&owl__x751))),
                            vec_as_slice(&(*arc_clone(&owl__x753))),
                            &mut mut_state.owl_N_resp_send,
                            vec_as_slice(&(*arc_clone(&owl__x755))),
                        ) {
                            Ok(ctxt) => ctxt,
                            Err(e) => { return Err(e) },
                        }
                    };
                    let owl__x756 = arc_clone(&temp_owl__x756);
                    let temp_owl__x772 = { arc_clone(&owl__x745) };
                    let owl__x772 = arc_clone(&temp_owl__x772);
                    let temp_owl__x774 = { arc_clone(&owl_transp_receiver732) };
                    let owl__x774 = arc_clone(&temp_owl__x774);
                    let temp_owl__x776 = { arc_clone(&owl__x740) };
                    let owl__x776 = arc_clone(&temp_owl__x776);
                    let temp_owl__x778 = { arc_clone(&owl__x756) };
                    let owl__x778 = arc_clone(&temp_owl__x778);
                    let temp_owl__x780 = {
                    owl_transp {
                        owl__transp_tag: clone_vec_u8(&*arc_clone(&owl__x772)),
                        owl__transp_receiver: clone_vec_u8(&*arc_clone(&owl__x774)),
                        owl__transp_counter: clone_vec_u8(&*arc_clone(&owl__x776)),
                        owl__transp_packet: clone_vec_u8(&*arc_clone(&owl__x778)),
                    }
                    };
                    let owl__x780 = temp_owl__x780;
                    let temp_owl__x781 = { owl__x780 };
                    let owl__x781 = temp_owl__x781;
                    let temp_owl__x785 = { owl__x781 };
                    let owl__x785 = temp_owl__x785;
                    let temp_owl__x786 = {
                    owl_output::<(Option<()>, state_Responder)>(
                        Tracked(&mut itree),
                        vec_as_slice(&(serialize_owl_transp(&owl__x785))),
                        &Initiator_addr(),
                        &Responder_addr(),
                        obuf
                    )
                    };
                    let owl__x786 = temp_owl__x786;
                    let temp_owl__x789 = { () };
                    let owl__x789 = temp_owl__x789;
                    let temp_owl__x790 = { Some(owl__x789) };
                    let owl__x790 = temp_owl__x790;
                    (owl__x790, Tracked(itree))
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
            let temp_owl__x1146 = { owl_msg1_val_8321 };
            let owl__x1146 = temp_owl__x1146;
            let temp_owl__x1145 = { owl__x1146 };
            let owl__x1145 = temp_owl__x1145;
            let parseval = owl__x1145;
            let owl_C3814 = arc_new(parseval.owl__responder_msg1_C3);
            let owl_H4813 = arc_new(parseval.owl__responder_msg1_H4);
            let owl_ephemeral_812 = arc_new(parseval.owl__responder_msg1_ephemeral);
            let owl_dhpk_S_init811 = arc_new(parseval.owl__responder_msg1_sender_pk);
            let owl_msg2_receiver810 = arc_new(parseval.owl__responder_msg1_sender);
            {
                let temp_owl__x819 = { arc_clone(&owl_ephemeral_812) };
                let owl__x819 = arc_clone(&temp_owl__x819);
                let temp_owl__x820 = { arc_clone(&owl__x819) };
                let owl__x820 = arc_clone(&temp_owl__x820);
                let temp_owl__x827 = { arc_clone(&self.owl_E_resp) };
                let owl__x827 = arc_clone(&temp_owl__x827);
                let temp_owl__x829 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x827)))) };
                let owl__x829 = arc_clone(&temp_owl__x829);
                let temp_owl__x830 = { arc_clone(&owl__x829) };
                let owl__x830 = arc_clone(&temp_owl__x830);
                let temp_owl__x834 = { owl_zeros_32() };
                let owl__x834 = arc_new(temp_owl__x834);
                let temp_owl__x835 = { arc_clone(&owl__x834) };
                let owl__x835 = arc_clone(&temp_owl__x835);
                let temp_owl__x840 = { arc_clone(&owl_C3814) };
                let owl__x840 = arc_clone(&temp_owl__x840);
                let temp_owl__x842 = { arc_clone(&owl__x830) };
                let owl__x842 = arc_clone(&temp_owl__x842);
                let owl_msg2_C41150 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x840))),
                    vec_as_slice(&(*arc_clone(&owl__x842))),
                );
                let temp_owl__x843 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C41150), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x843 = arc_clone(&temp_owl__x843);
                let temp_owl__x856 = { arc_clone(&owl_H4813) };
                let owl__x856 = arc_clone(&temp_owl__x856);
                let temp_owl__x858 = { arc_clone(&owl__x830) };
                let owl__x858 = arc_clone(&temp_owl__x858);
                let temp_owl__x860 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x856))),
                    vec_as_slice(&(*arc_clone(&owl__x858))),
                )
                };
                let owl__x860 = arc_new(temp_owl__x860);
                let temp_owl__x862 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x860)))) };
                let owl__x862 = arc_clone(&temp_owl__x862);
                let temp_owl__x863 = { arc_clone(&owl__x862) };
                let owl__x863 = arc_clone(&temp_owl__x863);
                let temp_owl__x873 = { arc_clone(&owl__x820) };
                let owl__x873 = arc_clone(&temp_owl__x873);
                let temp_owl__x875 = { arc_clone(&self.owl_E_resp) };
                let owl__x875 = arc_clone(&temp_owl__x875);
                let temp_owl__x877 = {
                owl_dh_combine(
                    vec_as_slice(&(*arc_clone(&owl__x873))),
                    vec_as_slice(&(*arc_clone(&owl__x875))),
                )
                };
                let owl__x877 = arc_clone(&temp_owl__x877);
                let temp_owl__x878 = { arc_clone(&owl__x877) };
                let owl__x878 = arc_clone(&temp_owl__x878);
                let temp_owl__x883 = { arc_clone(&owl__x843) };
                let owl__x883 = arc_clone(&temp_owl__x883);
                let temp_owl__x885 = { arc_clone(&owl__x878) };
                let owl__x885 = arc_clone(&temp_owl__x885);
                let owl_msg2_C51151 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x883))),
                    vec_as_slice(&(*arc_clone(&owl__x885))),
                );
                let temp_owl__x886 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C51151), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x886 = arc_clone(&temp_owl__x886);
                let temp_owl__x893 = { arc_clone(&owl__x886) };
                let owl__x893 = arc_clone(&temp_owl__x893);
                let temp_owl__x896 = { arc_clone(&owl_dhpk_S_init811) };
                let owl__x896 = arc_clone(&temp_owl__x896);
                let temp_owl__x898 = { arc_clone(&self.owl_E_resp) };
                let owl__x898 = arc_clone(&temp_owl__x898);
                let temp_owl__x899 = {
                owl_dh_combine(
                    vec_as_slice(&(*arc_clone(&owl__x896))),
                    vec_as_slice(&(*arc_clone(&owl__x898))),
                )
                };
                let owl__x899 = arc_clone(&temp_owl__x899);
                let owl_msg2_C61152 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x893))),
                    vec_as_slice(&(*arc_clone(&owl__x899))),
                );
                let temp_owl__x900 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C61152), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x900 = arc_clone(&temp_owl__x900);
                let temp_owl__x905 = { arc_clone(&owl__x900) };
                let owl__x905 = arc_clone(&temp_owl__x905);
                let temp_owl__x907 = { arc_clone(&owl__x835) };
                let owl__x907 = arc_clone(&temp_owl__x907);
                let owl_msg2_C71153 = owl_extract_expand_to_len(
                    0 + nonce_size() + nonce_size() + key_size(),
                    vec_as_slice(&(*arc_clone(&owl__x905))),
                    vec_as_slice(&(*arc_clone(&owl__x907))),
                );
                let temp_owl__x908 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C71153), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x908 = arc_clone(&temp_owl__x908);
                let temp_owl__x913 = { arc_clone(&owl__x900) };
                let owl__x913 = arc_clone(&temp_owl__x913);
                let temp_owl__x915 = { arc_clone(&owl__x835) };
                let owl__x915 = arc_clone(&temp_owl__x915);
                let temp_owl__x916 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_msg2_C71153),
                            0 + nonce_size(),
                            0 + nonce_size() + nonce_size(),
                        ),
                    ),
                )
                };
                let owl__x916 = arc_clone(&temp_owl__x916);
                let temp_owl__x921 = { arc_clone(&owl__x900) };
                let owl__x921 = arc_clone(&temp_owl__x921);
                let temp_owl__x923 = { arc_clone(&owl__x835) };
                let owl__x923 = arc_clone(&temp_owl__x923);
                let temp_owl__x924 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_msg2_C71153),
                            0 + nonce_size() + nonce_size(),
                            0 + nonce_size() + nonce_size() + key_size(),
                        ),
                    ),
                )
                };
                let owl__x924 = arc_clone(&temp_owl__x924);
                let temp_owl__x937 = { arc_clone(&owl__x863) };
                let owl__x937 = arc_clone(&temp_owl__x937);
                let temp_owl__x939 = { arc_clone(&owl__x916) };
                let owl__x939 = arc_clone(&temp_owl__x939);
                let temp_owl__x941 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x937))),
                    vec_as_slice(&(*arc_clone(&owl__x939))),
                )
                };
                let owl__x941 = arc_new(temp_owl__x941);
                let temp_owl__x943 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x941)))) };
                let owl__x943 = arc_clone(&temp_owl__x943);
                let temp_owl__x944 = { arc_clone(&owl__x943) };
                let owl__x944 = arc_clone(&temp_owl__x944);
                let temp_owl__x948 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x948 = arc_new(temp_owl__x948);
                let temp_owl__x949 = { arc_clone(&owl__x948) };
                let owl__x949 = arc_clone(&temp_owl__x949);
                let temp_owl__x955 = { arc_clone(&owl__x924) };
                let owl__x955 = arc_clone(&temp_owl__x955);
                let temp_owl__x957 = { arc_clone(&owl__x949) };
                let owl__x957 = arc_clone(&temp_owl__x957);
                let temp_owl__x959 = { arc_clone(&owl__x944) };
                let owl__x959 = arc_clone(&temp_owl__x959);
                let temp_owl__x960 = {
                    match owl_enc_st_aead(
                        vec_as_slice(&(*arc_clone(&owl__x955))),
                        vec_as_slice(&(*arc_clone(&owl__x957))),
                        &mut mut_state.owl_aead_counter_msg2_C7,
                        vec_as_slice(&(*arc_clone(&owl__x959))),
                    ) {
                        Ok(ctxt) => ctxt,
                        Err(e) => { return Err(e) },
                    }
                };
                let owl__x960 = arc_clone(&temp_owl__x960);
                let temp_owl__x973 = { arc_clone(&owl__x944) };
                let owl__x973 = arc_clone(&temp_owl__x973);
                let temp_owl__x975 = { arc_clone(&owl__x960) };
                let owl__x975 = arc_clone(&temp_owl__x975);
                let temp_owl__x977 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x973))),
                    vec_as_slice(&(*arc_clone(&owl__x975))),
                )
                };
                let owl__x977 = arc_new(temp_owl__x977);
                let temp_owl__x979 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x977)))) };
                let owl__x979 = arc_clone(&temp_owl__x979);
                let temp_owl__x980 = { arc_clone(&owl__x979) };
                let owl__x980 = arc_clone(&temp_owl__x980);
                let (temp_owl__x982, Tracked(itree)): (
                    _,
                    Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
                ) = {
                    owl_call!( itree
, *mut_state
, get_sender_r_spec(*self, *mut_state)
, self.owl_get_sender_r(mut_state) )
                };
                let owl__x982 = arc_clone(&temp_owl__x982);
                let temp_owl__x986 = { owl_msg2_tag_value() };
                let owl__x986 = arc_new(temp_owl__x986);
                let temp_owl__x987 = { arc_clone(&owl__x986) };
                let owl__x987 = arc_clone(&temp_owl__x987);
                let temp_owl__x1000 = { owl_mac1() };
                let owl__x1000 = arc_new(temp_owl__x1000);
                let temp_owl__x1002 = { arc_clone(&owl_dhpk_S_init811) };
                let owl__x1002 = arc_clone(&temp_owl__x1002);
                let temp_owl__x1004 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1000))),
                    vec_as_slice(&(*arc_clone(&owl__x1002))),
                )
                };
                let owl__x1004 = arc_new(temp_owl__x1004);
                let temp_owl__x1006 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x1004)))) };
                let owl__x1006 = arc_clone(&temp_owl__x1006);
                let temp_owl__x1007 = { arc_clone(&owl__x1006) };
                let owl__x1007 = arc_clone(&temp_owl__x1007);
                let temp_owl__x1020 = { arc_clone(&owl__x1007) };
                let owl__x1020 = arc_clone(&temp_owl__x1020);
                let temp_owl__x1026 = { arc_clone(&owl__x987) };
                let owl__x1026 = arc_clone(&temp_owl__x1026);
                let temp_owl__x1028 = { arc_clone(&owl__x982) };
                let owl__x1028 = arc_clone(&temp_owl__x1028);
                let temp_owl__x1029 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1026))),
                    vec_as_slice(&(*arc_clone(&owl__x1028))),
                )
                };
                let owl__x1029 = arc_new(temp_owl__x1029);
                let temp_owl__x1031 = { arc_clone(&owl_msg2_receiver810) };
                let owl__x1031 = arc_clone(&temp_owl__x1031);
                let temp_owl__x1032 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1029))),
                    vec_as_slice(&(*arc_clone(&owl__x1031))),
                )
                };
                let owl__x1032 = arc_new(temp_owl__x1032);
                let temp_owl__x1034 = { arc_clone(&owl__x830) };
                let owl__x1034 = arc_clone(&temp_owl__x1034);
                let temp_owl__x1035 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1032))),
                    vec_as_slice(&(*arc_clone(&owl__x1034))),
                )
                };
                let owl__x1035 = arc_new(temp_owl__x1035);
                let temp_owl__x1037 = { arc_clone(&owl__x960) };
                let owl__x1037 = arc_clone(&temp_owl__x1037);
                let temp_owl__x1038 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1035))),
                    vec_as_slice(&(*arc_clone(&owl__x1037))),
                )
                };
                let owl__x1038 = arc_new(temp_owl__x1038);
                let temp_owl__x1039 = {
                owl_mac(
                    vec_as_slice(&(*arc_clone(&owl__x1020))),
                    vec_as_slice(&(*arc_clone(&owl__x1038))),
                )
                };
                let owl__x1039 = arc_clone(&temp_owl__x1039);
                let temp_owl__x1043 = { owl_zeros_16() };
                let owl__x1043 = arc_new(temp_owl__x1043);
                let temp_owl__x1044 = { arc_clone(&owl__x1043) };
                let owl__x1044 = arc_clone(&temp_owl__x1044);
                let temp_owl__x1069 = { arc_clone(&owl__x987) };
                let owl__x1069 = arc_clone(&temp_owl__x1069);
                let temp_owl__x1071 = { arc_clone(&owl__x982) };
                let owl__x1071 = arc_clone(&temp_owl__x1071);
                let temp_owl__x1073 = { arc_clone(&owl_msg2_receiver810) };
                let owl__x1073 = arc_clone(&temp_owl__x1073);
                let temp_owl__x1075 = { arc_clone(&owl__x830) };
                let owl__x1075 = arc_clone(&temp_owl__x1075);
                let temp_owl__x1077 = { arc_clone(&owl__x960) };
                let owl__x1077 = arc_clone(&temp_owl__x1077);
                let temp_owl__x1079 = { arc_clone(&owl__x1039) };
                let owl__x1079 = arc_clone(&temp_owl__x1079);
                let temp_owl__x1081 = { arc_clone(&owl__x1044) };
                let owl__x1081 = arc_clone(&temp_owl__x1081);
                let temp_owl__x1083 = {
                owl_msg2 {
                    owl__msg2_tag: clone_vec_u8(&*arc_clone(&owl__x1069)),
                    owl__msg2_sender: clone_vec_u8(&*arc_clone(&owl__x1071)),
                    owl__msg2_receiver: clone_vec_u8(&*arc_clone(&owl__x1073)),
                    owl__msg2_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1075)),
                    owl__msg2_empty: clone_vec_u8(&*arc_clone(&owl__x1077)),
                    owl__msg2_mac1: clone_vec_u8(&*arc_clone(&owl__x1079)),
                    owl__msg2_mac2: clone_vec_u8(&*arc_clone(&owl__x1081)),
                }
                };
                let owl__x1083 = temp_owl__x1083;
                let temp_owl__x1084 = { owl__x1083 };
                let owl__x1084 = temp_owl__x1084;
                let temp_owl__x1088 = { owl__x1084 };
                let owl__x1088 = temp_owl__x1088;
                let temp_owl__x1089 = {
                owl_output::<(Seq<u8>, state_Responder)>(
                    Tracked(&mut itree),
                    vec_as_slice(&(serialize_owl_msg2(&owl__x1088))),
                    &Initiator_addr(),
                    &Responder_addr(),
                    obuf
                )
                };
                let owl__x1089 = temp_owl__x1089;
                let temp_owl__x1094 = { arc_clone(&owl__x908) };
                let owl__x1094 = arc_clone(&temp_owl__x1094);
                let temp_owl__x1096 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1096 = arc_new(temp_owl__x1096);
                let owl_transp_T1154 = owl_extract_expand_to_len(
                    0 + key_size() + key_size(),
                    vec_as_slice(&(*arc_clone(&owl__x1094))),
                    vec_as_slice(&(*arc_clone(&owl__x1096))),
                );
                let temp_owl__x1097 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_transp_T1154), 0, 0 + key_size()),
                    ),
                )
                };
                let owl__x1097 = arc_clone(&temp_owl__x1097);
                let temp_owl__x1102 = { arc_clone(&owl__x908) };
                let owl__x1102 = arc_clone(&temp_owl__x1102);
                let temp_owl__x1104 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1104 = arc_new(temp_owl__x1104);
                let temp_owl__x1105 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_transp_T1154),
                            0 + key_size(),
                            0 + key_size() + key_size(),
                        ),
                    ),
                )
                };
                let owl__x1105 = arc_clone(&temp_owl__x1105);
                let temp_owl__x1127 = { arc_clone(&owl_msg2_receiver810) };
                let owl__x1127 = arc_clone(&temp_owl__x1127);
                let temp_owl__x1129 = { arc_clone(&owl__x982) };
                let owl__x1129 = arc_clone(&temp_owl__x1129);
                let temp_owl__x1131 = { arc_clone(&owl__x820) };
                let owl__x1131 = arc_clone(&temp_owl__x1131);
                let temp_owl__x1133 = { arc_clone(&owl__x830) };
                let owl__x1133 = arc_clone(&temp_owl__x1133);
                let temp_owl__x1135 = { arc_clone(&owl__x1097) };
                let owl__x1135 = arc_clone(&temp_owl__x1135);
                let temp_owl__x1137 = { arc_clone(&owl__x1105) };
                let owl__x1137 = arc_clone(&temp_owl__x1137);
                let temp_owl__x1139 = {
                owl_transp_keys {
                    owl__transp_keys_initiator: clone_vec_u8(&*arc_clone(&owl__x1127)),
                    owl__transp_keys_responder: clone_vec_u8(&*arc_clone(&owl__x1129)),
                    owl__transp_keys_T_init_send: clone_vec_u8(&*arc_clone(&owl__x1135)),
                    owl__transp_keys_T_resp_send: clone_vec_u8(&*arc_clone(&owl__x1137)),
                }
                };
                let owl__x1139 = temp_owl__x1139;
                let temp_owl__x1140 = { owl__x1139 };
                let owl__x1140 = temp_owl__x1140;
                let temp_owl__x1143 = { owl__x1140 };
                let owl__x1143 = temp_owl__x1143;
                let temp_owl__x1144 = { owl__x1143 };
                let owl__x1144 = temp_owl__x1144;
                (owl__x1144, Tracked(itree))
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
            let (temp_owl_inp1163, owl__1162) = owl_input::<(Option<Seq<u8>>, state_Responder)>(
                Tracked(&mut itree),
                ibuf,
            );
            let owl_inp1163 = arc_new(temp_owl_inp1163);
            let temp_owl__x1451 = { arc_clone(&owl_inp1163) };
            let owl__x1451 = arc_clone(&temp_owl__x1451);
            if let Some(parseval) = parse_owl_msg1(vec_as_slice(&(*arc_clone(&owl__x1451)))) {
                let owl_msg1_tag1171 = arc_new(parseval.owl__msg1_tag);
                let owl_msg1_sender1170 = arc_new(parseval.owl__msg1_sender);
                let owl_msg1_ephemeral_1169 = arc_new(parseval.owl__msg1_ephemeral);
                let owl_msg1_static1168 = arc_new(parseval.owl__msg1_static);
                let owl_msg1_timestamp1167 = arc_new(parseval.owl__msg1_timestamp);
                let owl_msg1_mac11166 = arc_new(parseval.owl__msg1_mac1);
                let owl_msg1_mac21165 = arc_new(parseval.owl__msg1_mac2);
                {
                    let temp_owl__x1446 = { arc_clone(&owl_msg1_sender1170) };
                    let owl__x1446 = arc_clone(&temp_owl__x1446);
                    let temp_owl__x1447 = { vec_length(&(*arc_clone(&owl__x1446))) };
                    let owl__x1447 = temp_owl__x1447;
                    let temp_owl__x1449 = { 4 };
                    let owl__x1449 = temp_owl__x1449;
                    let temp_owl__x1450 = { owl__x1447 == owl__x1449 };
                    let owl__x1450 = temp_owl__x1450;
                    if owl__x1450 {
                        let temp_owl__x1439 = { arc_clone(&owl_msg1_ephemeral_1169) };
                        let owl__x1439 = arc_clone(&temp_owl__x1439);
                        let temp_owl__x1440 = {
                        owl_is_group_elem(vec_as_slice(&(*arc_clone(&owl__x1439))))
                        };
                        let owl__x1440 = temp_owl__x1440;
                        if owl__x1440 {
                            let temp_owl__x1178 = { owl_construction() };
                            let owl__x1178 = arc_new(temp_owl__x1178);
                            let temp_owl__x1180 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1178))))
                            };
                            let owl__x1180 = arc_clone(&temp_owl__x1180);
                            let temp_owl__x1181 = { arc_clone(&owl__x1180) };
                            let owl__x1181 = arc_clone(&temp_owl__x1181);
                            let temp_owl__x1194 = { arc_clone(&owl__x1181) };
                            let owl__x1194 = arc_clone(&temp_owl__x1194);
                            let temp_owl__x1196 = { owl_identifier() };
                            let owl__x1196 = arc_new(temp_owl__x1196);
                            let temp_owl__x1198 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1194))),
                                vec_as_slice(&(*arc_clone(&owl__x1196))),
                            )
                            };
                            let owl__x1198 = arc_new(temp_owl__x1198);
                            let temp_owl__x1200 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1198))))
                            };
                            let owl__x1200 = arc_clone(&temp_owl__x1200);
                            let temp_owl__x1201 = { arc_clone(&owl__x1200) };
                            let owl__x1201 = arc_clone(&temp_owl__x1201);
                            let temp_owl__x1214 = { arc_clone(&owl__x1201) };
                            let owl__x1214 = arc_clone(&temp_owl__x1214);
                            let temp_owl__x1216 = { arc_clone(&owl_dhpk_S_resp8149) };
                            let owl__x1216 = arc_clone(&temp_owl__x1216);
                            let temp_owl__x1218 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1214))),
                                vec_as_slice(&(*arc_clone(&owl__x1216))),
                            )
                            };
                            let owl__x1218 = arc_new(temp_owl__x1218);
                            let temp_owl__x1220 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1218))))
                            };
                            let owl__x1220 = arc_clone(&temp_owl__x1220);
                            let temp_owl__x1221 = { arc_clone(&owl__x1220) };
                            let owl__x1221 = arc_clone(&temp_owl__x1221);
                            let temp_owl__x1227 = { arc_clone(&owl_msg1_ephemeral_1169) };
                            let owl__x1227 = arc_clone(&temp_owl__x1227);
                            let temp_owl__x1228 = { arc_clone(&owl__x1227) };
                            let owl__x1228 = arc_clone(&temp_owl__x1228);
                            let temp_owl__x1233 = { arc_clone(&owl__x1181) };
                            let owl__x1233 = arc_clone(&temp_owl__x1233);
                            let temp_owl__x1235 = { arc_clone(&owl__x1228) };
                            let owl__x1235 = arc_clone(&temp_owl__x1235);
                            let owl_msg1_C11459 = owl_extract_expand_to_len(
                                0 + nonce_size(),
                                vec_as_slice(&(*arc_clone(&owl__x1233))),
                                vec_as_slice(&(*arc_clone(&owl__x1235))),
                            );
                            let temp_owl__x1236 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C11459),
                                        0,
                                        0 + nonce_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1236 = arc_clone(&temp_owl__x1236);
                            let temp_owl__x1249 = { arc_clone(&owl__x1221) };
                            let owl__x1249 = arc_clone(&temp_owl__x1249);
                            let temp_owl__x1251 = { arc_clone(&owl__x1228) };
                            let owl__x1251 = arc_clone(&temp_owl__x1251);
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
                            let temp_owl__x1266 = { arc_clone(&owl__x1228) };
                            let owl__x1266 = arc_clone(&temp_owl__x1266);
                            let temp_owl__x1268 = { arc_clone(&self.owl_S_resp) };
                            let owl__x1268 = arc_clone(&temp_owl__x1268);
                            let temp_owl__x1270 = {
                            owl_dh_combine(
                                vec_as_slice(&(*arc_clone(&owl__x1266))),
                                vec_as_slice(&(*arc_clone(&owl__x1268))),
                            )
                            };
                            let owl__x1270 = arc_clone(&temp_owl__x1270);
                            let temp_owl__x1271 = { arc_clone(&owl__x1270) };
                            let owl__x1271 = arc_clone(&temp_owl__x1271);
                            let temp_owl__x1276 = { arc_clone(&owl__x1236) };
                            let owl__x1276 = arc_clone(&temp_owl__x1276);
                            let temp_owl__x1278 = { arc_clone(&owl__x1271) };
                            let owl__x1278 = arc_clone(&temp_owl__x1278);
                            let owl_msg1_C21460 = owl_extract_expand_to_len(
                                0 + nonce_size() + key_size(),
                                vec_as_slice(&(*arc_clone(&owl__x1276))),
                                vec_as_slice(&(*arc_clone(&owl__x1278))),
                            );
                            let temp_owl__x1279 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C21460),
                                        0,
                                        0 + nonce_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1279 = arc_clone(&temp_owl__x1279);
                            let temp_owl__x1284 = { arc_clone(&owl__x1236) };
                            let owl__x1284 = arc_clone(&temp_owl__x1284);
                            let temp_owl__x1286 = { arc_clone(&owl__x1271) };
                            let owl__x1286 = arc_clone(&temp_owl__x1286);
                            let temp_owl__x1287 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C21460),
                                        0 + nonce_size(),
                                        0 + nonce_size() + key_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1287 = arc_clone(&temp_owl__x1287);
                            let temp_owl__x1429 = { arc_clone(&owl__x1287) };
                            let owl__x1429 = arc_clone(&temp_owl__x1429);
                            let temp_owl__x1431 = { arc_clone(&owl_msg1_static1168) };
                            let owl__x1431 = arc_clone(&temp_owl__x1431);
                            let temp_owl__x1433 = { arc_clone(&owl__x1256) };
                            let owl__x1433 = arc_clone(&temp_owl__x1433);
                            let temp_owl__x1435 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x1435 = arc_new(temp_owl__x1435);
                            let temp_owl__x1436 = {
                            owl_dec_st_aead(
                                vec_as_slice(&(*arc_clone(&owl__x1429))),
                                vec_as_slice(&(*arc_clone(&owl__x1431))),
                                vec_as_slice(&(*arc_clone(&owl__x1435))),
                                vec_as_slice(&(*arc_clone(&owl__x1433))),
                            )
                            };
                            let owl__x1436 = temp_owl__x1436;
                            let temp_owl_caseval1458 = { owl__x1436 };
                            let owl_caseval1458 = temp_owl_caseval1458;
                            match owl_caseval1458 {
                                None => {
                                    let temp_owl__x1292 = { None };
                                    let owl__x1292 = temp_owl__x1292;
                                    (owl__x1292, Tracked(itree))
                                },
                                Some(temp_owl_msg1_static_dec1293) => {
                                    let owl_msg1_static_dec1293 = arc_clone(
                                        &temp_owl_msg1_static_dec1293,
                                    );
                                    let temp_owl__x1297 = { arc_clone(&owl_msg1_static_dec1293) };
                                    let owl__x1297 = arc_clone(&temp_owl__x1297);
                                    let (temp_owl__x1298, Tracked(itree)): (
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
, checkpk_resp_spec(*self, *mut_state, (&owl__x1297).dview())
, self.owl_checkpk_resp(mut_state, arc_clone(&owl__x1297)) )
                                    };
                                    let owl__x1298 = temp_owl__x1298;
                                    let temp_owl__x1426 = { owl__x1298 };
                                    let owl__x1426 = temp_owl__x1426;
                                    let temp_owl__x1427 = { owl__x1426 };
                                    let owl__x1427 = temp_owl__x1427;
                                    let temp_owl_caseval1457 = { owl__x1427 };
                                    let owl_caseval1457 = temp_owl_caseval1457;
                                    match owl_caseval1457 {
                                        None => {
                                            let temp_owl__x1300 = { None };
                                            let owl__x1300 = temp_owl__x1300;
                                            (owl__x1300, Tracked(itree))
                                        },
                                        Some(temp_owl_ss_S_init_S_resp_1301) => {
                                            let owl_ss_S_init_S_resp_1301 = arc_clone(
                                                &temp_owl_ss_S_init_S_resp_1301,
                                            );
                                            let temp_owl__x1424 = {
                                            arc_clone(&owl_ss_S_init_S_resp_1301)
                                            };
                                            let owl__x1424 = arc_clone(&temp_owl__x1424);
                                            let temp_owl__x1307 = {
                                            arc_clone(&owl_msg1_static_dec1293)
                                            };
                                            let owl__x1307 = arc_clone(&temp_owl__x1307);
                                            let temp_owl__x1308 = { arc_clone(&owl__x1307) };
                                            let owl__x1308 = arc_clone(&temp_owl__x1308);
                                            let temp_owl__x1321 = { arc_clone(&owl__x1256) };
                                            let owl__x1321 = arc_clone(&temp_owl__x1321);
                                            let temp_owl__x1323 = { arc_clone(&owl_msg1_static1168)
                                            };
                                            let owl__x1323 = arc_clone(&temp_owl__x1323);
                                            let temp_owl__x1325 = {
                                            owl_concat(
                                                vec_as_slice(&(*arc_clone(&owl__x1321))),
                                                vec_as_slice(&(*arc_clone(&owl__x1323))),
                                            )
                                            };
                                            let owl__x1325 = arc_new(temp_owl__x1325);
                                            let temp_owl__x1327 = {
                                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1325))))
                                            };
                                            let owl__x1327 = arc_clone(&temp_owl__x1327);
                                            let temp_owl__x1328 = { arc_clone(&owl__x1327) };
                                            let owl__x1328 = arc_clone(&temp_owl__x1328);
                                            let temp_owl__x1333 = { arc_clone(&owl__x1279) };
                                            let owl__x1333 = arc_clone(&temp_owl__x1333);
                                            let temp_owl__x1335 = { arc_clone(&owl__x1424) };
                                            let owl__x1335 = arc_clone(&temp_owl__x1335);
                                            let owl_msg1_C31461 = owl_extract_expand_to_len(
                                                0 + nonce_size() + key_size(),
                                                vec_as_slice(&(*arc_clone(&owl__x1333))),
                                                vec_as_slice(&(*arc_clone(&owl__x1335))),
                                            );
                                            let temp_owl__x1336 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_msg1_C31461),
                                                        0,
                                                        0 + nonce_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x1336 = arc_clone(&temp_owl__x1336);
                                            let temp_owl__x1341 = { arc_clone(&owl__x1279) };
                                            let owl__x1341 = arc_clone(&temp_owl__x1341);
                                            let temp_owl__x1343 = { arc_clone(&owl__x1424) };
                                            let owl__x1343 = arc_clone(&temp_owl__x1343);
                                            let temp_owl__x1344 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_msg1_C31461),
                                                        0 + nonce_size(),
                                                        0 + nonce_size() + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x1344 = arc_clone(&temp_owl__x1344);
                                            let temp_owl__x1416 = { arc_clone(&owl__x1344) };
                                            let owl__x1416 = arc_clone(&temp_owl__x1416);
                                            let temp_owl__x1418 = {
                                            arc_clone(&owl_msg1_timestamp1167)
                                            };
                                            let owl__x1418 = arc_clone(&temp_owl__x1418);
                                            let temp_owl__x1420 = { arc_clone(&owl__x1328) };
                                            let owl__x1420 = arc_clone(&temp_owl__x1420);
                                            let temp_owl__x1422 = {
                                                {
                                                    let x: Vec<u8> = mk_vec_u8![];
                                                    x
                                                }
                                            };
                                            let owl__x1422 = arc_new(temp_owl__x1422);
                                            let temp_owl__x1423 = {
                                            owl_dec_st_aead(
                                                vec_as_slice(&(*arc_clone(&owl__x1416))),
                                                vec_as_slice(&(*arc_clone(&owl__x1418))),
                                                vec_as_slice(&(*arc_clone(&owl__x1422))),
                                                vec_as_slice(&(*arc_clone(&owl__x1420))),
                                            )
                                            };
                                            let owl__x1423 = temp_owl__x1423;
                                            let temp_owl_caseval1456 = { owl__x1423 };
                                            let owl_caseval1456 = temp_owl_caseval1456;
                                            match owl_caseval1456 {
                                                None => {
                                                    let temp_owl__x1349 = { None };
                                                    let owl__x1349 = temp_owl__x1349;
                                                    (owl__x1349, Tracked(itree))
                                                },
                                                Some(temp_owl_msg1_timestamp_dec1350) => {
                                                    let owl_msg1_timestamp_dec1350 = arc_clone(
                                                        &temp_owl_msg1_timestamp_dec1350,
                                                    );
                                                    let temp_owl__x1363 = { arc_clone(&owl__x1328)
                                                    };
                                                    let owl__x1363 = arc_clone(&temp_owl__x1363);
                                                    let temp_owl__x1365 = {
                                                    arc_clone(&owl_msg1_timestamp1167)
                                                    };
                                                    let owl__x1365 = arc_clone(&temp_owl__x1365);
                                                    let temp_owl__x1367 = {
                                                    owl_concat(
                                                        vec_as_slice(&(*arc_clone(&owl__x1363))),
                                                        vec_as_slice(&(*arc_clone(&owl__x1365))),
                                                    )
                                                    };
                                                    let owl__x1367 = arc_new(temp_owl__x1367);
                                                    let temp_owl__x1369 = {
                                                    owl_crh(
                                                        vec_as_slice(&(*arc_clone(&owl__x1367))),
                                                    )
                                                    };
                                                    let owl__x1369 = arc_clone(&temp_owl__x1369);
                                                    let temp_owl__x1370 = { arc_clone(&owl__x1369)
                                                    };
                                                    let owl__x1370 = arc_clone(&temp_owl__x1370);
                                                    let temp_owl__x1389 = { arc_clone(&owl__x1336)
                                                    };
                                                    let owl__x1389 = arc_clone(&temp_owl__x1389);
                                                    let temp_owl__x1391 = { arc_clone(&owl__x1370)
                                                    };
                                                    let owl__x1391 = arc_clone(&temp_owl__x1391);
                                                    let temp_owl__x1393 = { arc_clone(&owl__x1228)
                                                    };
                                                    let owl__x1393 = arc_clone(&temp_owl__x1393);
                                                    let temp_owl__x1395 = { arc_clone(&owl__x1308)
                                                    };
                                                    let owl__x1395 = arc_clone(&temp_owl__x1395);
                                                    let temp_owl__x1397 = {
                                                    arc_clone(&owl_msg1_sender1170)
                                                    };
                                                    let owl__x1397 = arc_clone(&temp_owl__x1397);
                                                    let temp_owl__x1399 = {
                                                    owl_responder_msg1_val {
                                                        owl__responder_msg1_C3: clone_vec_u8(
                                                            &*arc_clone(&owl__x1389),
                                                        ),
                                                        owl__responder_msg1_H4: clone_vec_u8(
                                                            &*arc_clone(&owl__x1391),
                                                        ),
                                                        owl__responder_msg1_ephemeral: clone_vec_u8(
                                                            &*arc_clone(&owl__x1393),
                                                        ),
                                                        owl__responder_msg1_sender_pk: clone_vec_u8(
                                                            &*arc_clone(&owl__x1395),
                                                        ),
                                                        owl__responder_msg1_sender: clone_vec_u8(
                                                            &*arc_clone(&owl__x1397),
                                                        ),
                                                    }
                                                    };
                                                    let owl__x1399 = temp_owl__x1399;
                                                    let temp_owl__x1400 = { owl__x1399 };
                                                    let owl__x1400 = temp_owl__x1400;
                                                    let temp_owl__x1407 = { owl__x1400 };
                                                    let owl__x1407 = temp_owl__x1407;
                                                    let temp_owl__x1409 = { owl__x1407 };
                                                    let owl__x1409 = temp_owl__x1409;
                                                    let temp_owl__x1410 = { owl__x1409 };
                                                    let owl__x1410 = temp_owl__x1410;
                                                    let temp_owl__x1413 = { owl__x1410 };
                                                    let owl__x1413 = temp_owl__x1413;
                                                    let temp_owl__x1414 = { Some(owl__x1413) };
                                                    let owl__x1414 = temp_owl__x1414;
                                                    (owl__x1414, Tracked(itree))
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
                let temp_owl__x1164 = { None };
                let owl__x1164 = temp_owl__x1164;
                (owl__x1164, Tracked(itree))
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
            (self.device.as_ref().unwrap().get_ss(&pk)
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
            let v = self.device.as_ref().unwrap().get_singleton_id();
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


