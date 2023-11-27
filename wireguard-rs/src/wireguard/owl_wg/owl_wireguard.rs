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
pub open spec fn transp_recv_init_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    transp_keys_val: owlSpec_transp_keys,
    c: Seq<u8>,
) -> (res: ITree<(Option<Seq<u8>>, state_Initiator), Endpoint>) {
    owl_spec!(mut_state,state_Initiator,
(parse (parse_owlSpec_transp(c)) as (owlSpec_transp{owlSpec__transp_tag : _unused35 , owlSpec__transp_receiver : from , owlSpec__transp_counter : ctr , owlSpec__transp_packet : pkt }) in {
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : _unused36 , owlSpec__transp_keys_responder : responder_name , owlSpec__transp_keys_T_init_send : _unused37 , owlSpec__transp_keys_T_resp_send : r2i_ }) in {
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
(input (inp, _unused403)) in
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
pub open spec fn transp_recv_resp_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    transp_keys_val: owlSpec_transp_keys,
    c: Seq<u8>,
) -> (res: ITree<(Option<Seq<u8>>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(parse (parse_owlSpec_transp(c)) as (owlSpec_transp{owlSpec__transp_tag : _unused769 , owlSpec__transp_receiver : from , owlSpec__transp_counter : ctr , owlSpec__transp_packet : pkt }) in {
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : initiator_name , owlSpec__transp_keys_responder : _unused770 , owlSpec__transp_keys_T_init_send : i2r_ , owlSpec__transp_keys_T_resp_send : _unused771 }) in {
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
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : transp_receiver , owlSpec__transp_keys_responder : _unused849 , owlSpec__transp_keys_T_init_send : _unused850 , owlSpec__transp_keys_T_resp_send : r2i_ }) in {
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
(input (inp, _unused1508)) in
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
            let temp_owl__x395 = { arc_clone(&owl_inp120) };
            let owl__x395 = arc_clone(&temp_owl__x395);
            if let Some(parseval) = parse_owl_msg2(vec_as_slice(&(*arc_clone(&owl__x395)))) {
                let owl_msg2_tag128 = arc_new(parseval.owl__msg2_tag);
                let owl_msg2_sender127 = arc_new(parseval.owl__msg2_sender);
                let owl_msg2_receiver126 = arc_new(parseval.owl__msg2_receiver);
                let owl_msg2_ephemeral_125 = arc_new(parseval.owl__msg2_ephemeral);
                let owl_msg2_empty124 = arc_new(parseval.owl__msg2_empty);
                let owl_msg2_mac1123 = arc_new(parseval.owl__msg2_mac1);
                let owl_msg2_mac2122 = arc_new(parseval.owl__msg2_mac2);
                {
                    let temp_owl__x394 = { owl_msg1_val5831 };
                    let owl__x394 = temp_owl__x394;
                    let parseval = owl__x394;
                    let owl_C3130 = arc_new(parseval.owl__initiator_msg1_C3);
                    let owl_H4129 = arc_new(parseval.owl__initiator_msg1_H4);
                    {
                        let temp_owl__x380 = { arc_clone(&owl_msg2_sender127) };
                        let owl__x380 = arc_clone(&temp_owl__x380);
                        let temp_owl__x381 = { vec_length(&(*arc_clone(&owl__x380))) };
                        let owl__x381 = temp_owl__x381;
                        let temp_owl__x383 = { 4 };
                        let owl__x383 = temp_owl__x383;
                        let temp_owl__x384 = { owl__x381 == owl__x383 };
                        let owl__x384 = temp_owl__x384;
                        let temp_owl__x388 = { arc_clone(&owl_msg2_receiver126) };
                        let owl__x388 = arc_clone(&temp_owl__x388);
                        let temp_owl__x389 = { vec_length(&(*arc_clone(&owl__x388))) };
                        let owl__x389 = temp_owl__x389;
                        let temp_owl__x391 = { 4 };
                        let owl__x391 = temp_owl__x391;
                        let temp_owl__x392 = { owl__x389 == owl__x391 };
                        let owl__x392 = temp_owl__x392;
                        let temp_owl__x393 = { owl__x384 && owl__x392 };
                        let owl__x393 = temp_owl__x393;
                        if owl__x393 {
                            let temp_owl__x367 = { arc_clone(&owl_msg2_ephemeral_125) };
                            let owl__x367 = arc_clone(&temp_owl__x367);
                            let temp_owl__x368 = {
                            owl_is_group_elem(vec_as_slice(&(*arc_clone(&owl__x367))))
                            };
                            let owl__x368 = temp_owl__x368;
                            if owl__x368 {
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
                                let owl_msg2_C4398 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x151))),
                                    vec_as_slice(&(*arc_clone(&owl__x153))),
                                );
                                let temp_owl__x154 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C4398),
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
                                let owl_msg2_C5399 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x194))),
                                    vec_as_slice(&(*arc_clone(&owl__x196))),
                                );
                                let temp_owl__x197 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C5399),
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
                                let owl_msg2_C6400 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x204))),
                                    vec_as_slice(&(*arc_clone(&owl__x210))),
                                );
                                let temp_owl__x211 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C6400),
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
                                let owl_msg2_C7401 = owl_extract_expand_to_len(
                                    0 + nonce_size() + nonce_size() + key_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x216))),
                                    vec_as_slice(&(*arc_clone(&owl__x218))),
                                );
                                let temp_owl__x219 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7401),
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
                                            vec_as_slice(&*owl_msg2_C7401),
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
                                            vec_as_slice(&*owl_msg2_C7401),
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
                                let temp_owl__x357 = { arc_clone(&owl__x235) };
                                let owl__x357 = arc_clone(&temp_owl__x357);
                                let temp_owl__x359 = { arc_clone(&owl_msg2_empty124) };
                                let owl__x359 = arc_clone(&temp_owl__x359);
                                let temp_owl__x361 = { arc_clone(&owl__x255) };
                                let owl__x361 = arc_clone(&temp_owl__x361);
                                let temp_owl__x363 = {
                                    {
                                        let x: Vec<u8> = mk_vec_u8![];
                                        x
                                    }
                                };
                                let owl__x363 = arc_new(temp_owl__x363);
                                let temp_owl__x364 = {
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x357))),
                                    vec_as_slice(&(*arc_clone(&owl__x359))),
                                    vec_as_slice(&(*arc_clone(&owl__x363))),
                                    vec_as_slice(&(*arc_clone(&owl__x361))),
                                )
                                };
                                let owl__x364 = temp_owl__x364;
                                let temp_owl_caseval397 = { owl__x364 };
                                let owl_caseval397 = temp_owl_caseval397;
                                match owl_caseval397 {
                                    None => {
                                        let temp_owl__x265 = { None };
                                        let owl__x265 = temp_owl__x265;
                                        (owl__x265, Tracked(itree))
                                    },
                                    Some(temp_owl_msg2_empty_dec266) => {
                                        let owl_msg2_empty_dec266 = arc_clone(
                                            &temp_owl_msg2_empty_dec266,
                                        );
                                        let temp_owl__x352 = { arc_clone(&owl_msg2_empty_dec266) };
                                        let owl__x352 = arc_clone(&temp_owl__x352);
                                        let temp_owl__x354 = { arc_clone(&owl__x260) };
                                        let owl__x354 = arc_clone(&temp_owl__x354);
                                        let temp_owl__x355 = {
                                        rc_vec_eq(&arc_clone(&owl__x352), &arc_clone(&owl__x354))
                                        };
                                        let owl__x355 = temp_owl__x355;
                                        if owl__x355 {
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
                                            let owl_transp_T402 = owl_extract_expand_to_len(
                                                0 + key_size() + key_size(),
                                                vec_as_slice(&(*arc_clone(&owl__x291))),
                                                vec_as_slice(&(*arc_clone(&owl__x293))),
                                            );
                                            let temp_owl__x294 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_transp_T402),
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
                                                        vec_as_slice(&*owl_transp_T402),
                                                        0 + key_size(),
                                                        0 + key_size() + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x302 = arc_clone(&temp_owl__x302);
                                            let temp_owl__x327 = { arc_clone(&owl_msg2_receiver126)
                                            };
                                            let owl__x327 = arc_clone(&temp_owl__x327);
                                            let temp_owl__x329 = { arc_clone(&owl_msg2_sender127) };
                                            let owl__x329 = arc_clone(&temp_owl__x329);
                                            let temp_owl__x331 = { arc_clone(&self.owl_E_init) };
                                            let owl__x331 = arc_clone(&temp_owl__x331);
                                            let temp_owl__x333 = {
                                            owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x331))))
                                            };
                                            let owl__x333 = arc_clone(&temp_owl__x333);
                                            let temp_owl__x335 = { arc_clone(&owl__x141) };
                                            let owl__x335 = arc_clone(&temp_owl__x335);
                                            let temp_owl__x337 = { arc_clone(&owl__x294) };
                                            let owl__x337 = arc_clone(&temp_owl__x337);
                                            let temp_owl__x339 = { arc_clone(&owl__x302) };
                                            let owl__x339 = arc_clone(&temp_owl__x339);
                                            let temp_owl__x341 = {
                                            owl_transp_keys {
                                                owl__transp_keys_initiator: clone_vec_u8(
                                                    &*arc_clone(&owl__x327),
                                                ),
                                                owl__transp_keys_responder: clone_vec_u8(
                                                    &*arc_clone(&owl__x329),
                                                ),
                                                owl__transp_keys_T_init_send: clone_vec_u8(
                                                    &*arc_clone(&owl__x337),
                                                ),
                                                owl__transp_keys_T_resp_send: clone_vec_u8(
                                                    &*arc_clone(&owl__x339),
                                                ),
                                            }
                                            };
                                            let owl__x341 = temp_owl__x341;
                                            let temp_owl__x342 = { owl__x341 };
                                            let owl__x342 = temp_owl__x342;
                                            let temp_owl__x347 = { owl__x342 };
                                            let owl__x347 = temp_owl__x347;
                                            let temp_owl__x348 = { Some(owl__x347) };
                                            let owl__x348 = temp_owl__x348;
                                            (owl__x348, Tracked(itree))
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
            let temp_owl__x410 = { owl_construction() };
            let owl__x410 = arc_new(temp_owl__x410);
            let temp_owl__x412 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x410)))) };
            let owl__x412 = arc_clone(&temp_owl__x412);
            let temp_owl__x413 = { arc_clone(&owl__x412) };
            let owl__x413 = arc_clone(&temp_owl__x413);
            let temp_owl__x426 = { arc_clone(&owl__x413) };
            let owl__x426 = arc_clone(&temp_owl__x426);
            let temp_owl__x428 = { owl_identifier() };
            let owl__x428 = arc_new(temp_owl__x428);
            let temp_owl__x430 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x426))),
                vec_as_slice(&(*arc_clone(&owl__x428))),
            )
            };
            let owl__x430 = arc_new(temp_owl__x430);
            let temp_owl__x432 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x430)))) };
            let owl__x432 = arc_clone(&temp_owl__x432);
            let temp_owl__x433 = { arc_clone(&owl__x432) };
            let owl__x433 = arc_clone(&temp_owl__x433);
            let temp_owl__x446 = { arc_clone(&owl__x433) };
            let owl__x446 = arc_clone(&temp_owl__x446);
            let temp_owl__x448 = { arc_clone(&owl_dhpk_S_resp5818) };
            let owl__x448 = arc_clone(&temp_owl__x448);
            let temp_owl__x450 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x446))),
                vec_as_slice(&(*arc_clone(&owl__x448))),
            )
            };
            let owl__x450 = arc_new(temp_owl__x450);
            let temp_owl__x452 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x450)))) };
            let owl__x452 = arc_clone(&temp_owl__x452);
            let temp_owl__x453 = { arc_clone(&owl__x452) };
            let owl__x453 = arc_clone(&temp_owl__x453);
            let temp_owl__x460 = { arc_clone(&self.owl_E_init) };
            let owl__x460 = arc_clone(&temp_owl__x460);
            let temp_owl__x462 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x460)))) };
            let owl__x462 = arc_clone(&temp_owl__x462);
            let temp_owl__x463 = { arc_clone(&owl__x462) };
            let owl__x463 = arc_clone(&temp_owl__x463);
            let temp_owl__x468 = { arc_clone(&owl__x413) };
            let owl__x468 = arc_clone(&temp_owl__x468);
            let temp_owl__x470 = { arc_clone(&owl__x463) };
            let owl__x470 = arc_clone(&temp_owl__x470);
            let owl_msg1_C1731 = owl_extract_expand_to_len(
                0 + nonce_size(),
                vec_as_slice(&(*arc_clone(&owl__x468))),
                vec_as_slice(&(*arc_clone(&owl__x470))),
            );
            let temp_owl__x471 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C1731), 0, 0 + nonce_size())),
            )
            };
            let owl__x471 = arc_clone(&temp_owl__x471);
            let temp_owl__x484 = { arc_clone(&owl__x453) };
            let owl__x484 = arc_clone(&temp_owl__x484);
            let temp_owl__x486 = { arc_clone(&owl__x463) };
            let owl__x486 = arc_clone(&temp_owl__x486);
            let temp_owl__x488 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x484))),
                vec_as_slice(&(*arc_clone(&owl__x486))),
            )
            };
            let owl__x488 = arc_new(temp_owl__x488);
            let temp_owl__x490 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x488)))) };
            let owl__x490 = arc_clone(&temp_owl__x490);
            let temp_owl__x491 = { arc_clone(&owl__x490) };
            let owl__x491 = arc_clone(&temp_owl__x491);
            let temp_owl__x501 = { arc_clone(&owl_dhpk_S_resp5818) };
            let owl__x501 = arc_clone(&temp_owl__x501);
            let temp_owl__x503 = { arc_clone(&self.owl_E_init) };
            let owl__x503 = arc_clone(&temp_owl__x503);
            let temp_owl__x505 = {
            owl_dh_combine(
                vec_as_slice(&(*arc_clone(&owl__x501))),
                vec_as_slice(&(*arc_clone(&owl__x503))),
            )
            };
            let owl__x505 = arc_clone(&temp_owl__x505);
            let temp_owl__x506 = { arc_clone(&owl__x505) };
            let owl__x506 = arc_clone(&temp_owl__x506);
            let temp_owl__x511 = { arc_clone(&owl__x471) };
            let owl__x511 = arc_clone(&temp_owl__x511);
            let temp_owl__x513 = { arc_clone(&owl__x506) };
            let owl__x513 = arc_clone(&temp_owl__x513);
            let owl_msg1_C2732 = owl_extract_expand_to_len(
                0 + nonce_size() + key_size(),
                vec_as_slice(&(*arc_clone(&owl__x511))),
                vec_as_slice(&(*arc_clone(&owl__x513))),
            );
            let temp_owl__x514 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C2732), 0, 0 + nonce_size())),
            )
            };
            let owl__x514 = arc_clone(&temp_owl__x514);
            let temp_owl__x519 = { arc_clone(&owl__x471) };
            let owl__x519 = arc_clone(&temp_owl__x519);
            let temp_owl__x521 = { arc_clone(&owl__x506) };
            let owl__x521 = arc_clone(&temp_owl__x521);
            let temp_owl__x522 = {
            arc_new(
                slice_to_vec(
                    slice_subrange(
                        vec_as_slice(&*owl_msg1_C2732),
                        0 + nonce_size(),
                        0 + nonce_size() + key_size(),
                    ),
                ),
            )
            };
            let owl__x522 = arc_clone(&temp_owl__x522);
            let temp_owl__x529 = { arc_clone(&owl__x522) };
            let owl__x529 = arc_clone(&temp_owl__x529);
            let temp_owl__x532 = { arc_clone(&owl_dhpk_S_init5817) };
            let owl__x532 = arc_clone(&temp_owl__x532);
            let temp_owl__x533 = { arc_clone(&owl__x532) };
            let owl__x533 = arc_clone(&temp_owl__x533);
            let temp_owl__x535 = { arc_clone(&owl__x491) };
            let owl__x535 = arc_clone(&temp_owl__x535);
            let temp_owl__x536 = {
                match owl_enc_st_aead(
                    vec_as_slice(&(*arc_clone(&owl__x529))),
                    vec_as_slice(&(*arc_clone(&owl__x533))),
                    &mut mut_state.owl_aead_counter_msg1_C2,
                    vec_as_slice(&(*arc_clone(&owl__x535))),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x536 = arc_clone(&temp_owl__x536);
            let temp_owl__x549 = { arc_clone(&owl__x491) };
            let owl__x549 = arc_clone(&temp_owl__x549);
            let temp_owl__x551 = { arc_clone(&owl__x536) };
            let owl__x551 = arc_clone(&temp_owl__x551);
            let temp_owl__x553 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x549))),
                vec_as_slice(&(*arc_clone(&owl__x551))),
            )
            };
            let owl__x553 = arc_new(temp_owl__x553);
            let temp_owl__x555 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x553)))) };
            let owl__x555 = arc_clone(&temp_owl__x555);
            let temp_owl__x556 = { arc_clone(&owl__x555) };
            let owl__x556 = arc_clone(&temp_owl__x556);
            let temp_owl__x561 = { arc_clone(&owl__x514) };
            let owl__x561 = arc_clone(&temp_owl__x561);
            let temp_owl__x563 = { arc_clone(&owl_ss_S_resp_S_init5816) };
            let owl__x563 = arc_clone(&temp_owl__x563);
            let owl_msg1_C3733 = owl_extract_expand_to_len(
                0 + nonce_size() + key_size(),
                vec_as_slice(&(*arc_clone(&owl__x561))),
                vec_as_slice(&(*arc_clone(&owl__x563))),
            );
            let temp_owl__x564 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C3733), 0, 0 + nonce_size())),
            )
            };
            let owl__x564 = arc_clone(&temp_owl__x564);
            let temp_owl__x569 = { arc_clone(&owl__x514) };
            let owl__x569 = arc_clone(&temp_owl__x569);
            let temp_owl__x571 = { arc_clone(&owl_ss_S_resp_S_init5816) };
            let owl__x571 = arc_clone(&temp_owl__x571);
            let temp_owl__x572 = {
            arc_new(
                slice_to_vec(
                    slice_subrange(
                        vec_as_slice(&*owl_msg1_C3733),
                        0 + nonce_size(),
                        0 + nonce_size() + key_size(),
                    ),
                ),
            )
            };
            let owl__x572 = arc_clone(&temp_owl__x572);
            let (temp_owl__x574, Tracked(itree)): (
                _,
                Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
            ) = {
                owl_call!( itree
, *mut_state
, timestamp_i_spec(*self, *mut_state)
, self.owl_timestamp_i(mut_state) )
            };
            let owl__x574 = arc_clone(&temp_owl__x574);
            let temp_owl__x580 = { arc_clone(&owl__x572) };
            let owl__x580 = arc_clone(&temp_owl__x580);
            let temp_owl__x582 = { arc_clone(&owl__x574) };
            let owl__x582 = arc_clone(&temp_owl__x582);
            let temp_owl__x584 = { arc_clone(&owl__x556) };
            let owl__x584 = arc_clone(&temp_owl__x584);
            let temp_owl__x585 = {
                match owl_enc_st_aead(
                    vec_as_slice(&(*arc_clone(&owl__x580))),
                    vec_as_slice(&(*arc_clone(&owl__x582))),
                    &mut mut_state.owl_aead_counter_msg1_C3,
                    vec_as_slice(&(*arc_clone(&owl__x584))),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x585 = arc_clone(&temp_owl__x585);
            let temp_owl__x598 = { arc_clone(&owl__x556) };
            let owl__x598 = arc_clone(&temp_owl__x598);
            let temp_owl__x600 = { arc_clone(&owl__x585) };
            let owl__x600 = arc_clone(&temp_owl__x600);
            let temp_owl__x602 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x598))),
                vec_as_slice(&(*arc_clone(&owl__x600))),
            )
            };
            let owl__x602 = arc_new(temp_owl__x602);
            let temp_owl__x604 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x602)))) };
            let owl__x604 = arc_clone(&temp_owl__x604);
            let temp_owl__x605 = { arc_clone(&owl__x604) };
            let owl__x605 = arc_clone(&temp_owl__x605);
            let (temp_owl__x607, Tracked(itree)): (
                _,
                Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
            ) = {
                owl_call!( itree
, *mut_state
, get_sender_i_spec(*self, *mut_state)
, self.owl_get_sender_i(mut_state) )
            };
            let owl__x607 = arc_clone(&temp_owl__x607);
            let temp_owl__x611 = { owl_msg1_tag_value() };
            let owl__x611 = arc_new(temp_owl__x611);
            let temp_owl__x612 = { arc_clone(&owl__x611) };
            let owl__x612 = arc_clone(&temp_owl__x612);
            let temp_owl__x625 = { owl_mac1() };
            let owl__x625 = arc_new(temp_owl__x625);
            let temp_owl__x627 = { arc_clone(&owl_dhpk_S_resp5818) };
            let owl__x627 = arc_clone(&temp_owl__x627);
            let temp_owl__x629 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x625))),
                vec_as_slice(&(*arc_clone(&owl__x627))),
            )
            };
            let owl__x629 = arc_new(temp_owl__x629);
            let temp_owl__x631 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x629)))) };
            let owl__x631 = arc_clone(&temp_owl__x631);
            let temp_owl__x632 = { arc_clone(&owl__x631) };
            let owl__x632 = arc_clone(&temp_owl__x632);
            let temp_owl__x645 = { arc_clone(&owl__x632) };
            let owl__x645 = arc_clone(&temp_owl__x645);
            let temp_owl__x651 = { arc_clone(&owl__x612) };
            let owl__x651 = arc_clone(&temp_owl__x651);
            let temp_owl__x653 = { arc_clone(&owl__x607) };
            let owl__x653 = arc_clone(&temp_owl__x653);
            let temp_owl__x654 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x651))),
                vec_as_slice(&(*arc_clone(&owl__x653))),
            )
            };
            let owl__x654 = arc_new(temp_owl__x654);
            let temp_owl__x656 = { arc_clone(&owl__x463) };
            let owl__x656 = arc_clone(&temp_owl__x656);
            let temp_owl__x657 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x654))),
                vec_as_slice(&(*arc_clone(&owl__x656))),
            )
            };
            let owl__x657 = arc_new(temp_owl__x657);
            let temp_owl__x659 = { arc_clone(&owl__x536) };
            let owl__x659 = arc_clone(&temp_owl__x659);
            let temp_owl__x660 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x657))),
                vec_as_slice(&(*arc_clone(&owl__x659))),
            )
            };
            let owl__x660 = arc_new(temp_owl__x660);
            let temp_owl__x662 = { arc_clone(&owl__x585) };
            let owl__x662 = arc_clone(&temp_owl__x662);
            let temp_owl__x663 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x660))),
                vec_as_slice(&(*arc_clone(&owl__x662))),
            )
            };
            let owl__x663 = arc_new(temp_owl__x663);
            let temp_owl__x664 = {
            owl_mac(
                vec_as_slice(&(*arc_clone(&owl__x645))),
                vec_as_slice(&(*arc_clone(&owl__x663))),
            )
            };
            let owl__x664 = arc_clone(&temp_owl__x664);
            let temp_owl__x668 = { owl_zeros_16() };
            let owl__x668 = arc_new(temp_owl__x668);
            let temp_owl__x669 = { arc_clone(&owl__x668) };
            let owl__x669 = arc_clone(&temp_owl__x669);
            let temp_owl__x694 = { arc_clone(&owl__x612) };
            let owl__x694 = arc_clone(&temp_owl__x694);
            let temp_owl__x696 = { arc_clone(&owl__x607) };
            let owl__x696 = arc_clone(&temp_owl__x696);
            let temp_owl__x698 = { arc_clone(&owl__x463) };
            let owl__x698 = arc_clone(&temp_owl__x698);
            let temp_owl__x700 = { arc_clone(&owl__x536) };
            let owl__x700 = arc_clone(&temp_owl__x700);
            let temp_owl__x702 = { arc_clone(&owl__x585) };
            let owl__x702 = arc_clone(&temp_owl__x702);
            let temp_owl__x704 = { arc_clone(&owl__x664) };
            let owl__x704 = arc_clone(&temp_owl__x704);
            let temp_owl__x706 = { arc_clone(&owl__x669) };
            let owl__x706 = arc_clone(&temp_owl__x706);
            let temp_owl__x708 = {
            owl_msg1 {
                owl__msg1_tag: clone_vec_u8(&*arc_clone(&owl__x694)),
                owl__msg1_sender: clone_vec_u8(&*arc_clone(&owl__x696)),
                owl__msg1_ephemeral: clone_vec_u8(&*arc_clone(&owl__x698)),
                owl__msg1_static: clone_vec_u8(&*arc_clone(&owl__x700)),
                owl__msg1_timestamp: clone_vec_u8(&*arc_clone(&owl__x702)),
                owl__msg1_mac1: clone_vec_u8(&*arc_clone(&owl__x704)),
                owl__msg1_mac2: clone_vec_u8(&*arc_clone(&owl__x706)),
            }
            };
            let owl__x708 = temp_owl__x708;
            let temp_owl__x709 = { owl__x708 };
            let owl__x709 = temp_owl__x709;
            let temp_owl__x713 = { owl__x709 };
            let owl__x713 = temp_owl__x713;
            let temp_owl__x714 = {
            owl_output::<(Seq<u8>, state_Initiator)>(
                Tracked(&mut itree),
                vec_as_slice(&(serialize_owl_msg1(&owl__x713))),
                &Responder_addr(),
                &Initiator_addr(),
                obuf
            )
            };
            let owl__x714 = temp_owl__x714;
            let temp_owl__x724 = { arc_clone(&owl__x564) };
            let owl__x724 = arc_clone(&temp_owl__x724);
            let temp_owl__x726 = { arc_clone(&owl__x605) };
            let owl__x726 = arc_clone(&temp_owl__x726);
            let temp_owl__x728 = {
            owl_initiator_msg1_val {
                owl__initiator_msg1_C3: clone_vec_u8(&*arc_clone(&owl__x724)),
                owl__initiator_msg1_H4: clone_vec_u8(&*arc_clone(&owl__x726)),
            }
            };
            let owl__x728 = temp_owl__x728;
            let temp_owl__x729 = { owl__x728 };
            let owl__x729 = temp_owl__x729;
            let temp_owl__x730 = { owl__x729 };
            let owl__x730 = temp_owl__x730;
            (owl__x730, Tracked(itree))
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
            let temp_owl__x767 = { arc_clone(&owl_c14558) };
            let owl__x767 = arc_clone(&temp_owl__x767);
            if let Some(parseval) = parse_owl_transp(vec_as_slice(&(*arc_clone(&owl__x767)))) {
                let owl__740 = arc_new(parseval.owl__transp_tag);
                let owl_from739 = arc_new(parseval.owl__transp_receiver);
                let owl_ctr738 = arc_new(parseval.owl__transp_counter);
                let owl_pkt737 = arc_new(parseval.owl__transp_packet);
                {
                    let temp_owl__x766 = { owl_transp_keys_val14559 };
                    let owl__x766 = temp_owl__x766;
                    let parseval = owl__x766;
                    let owl_initiator_name746 = arc_new(parseval.owl__transp_keys_initiator);
                    let owl__745 = arc_new(parseval.owl__transp_keys_responder);
                    let owl_i2r_742 = arc_new(parseval.owl__transp_keys_T_init_send);
                    let owl__741 = arc_new(parseval.owl__transp_keys_T_resp_send);
                    {
                        let temp_owl__x762 = { arc_clone(&owl_c14558) };
                        let owl__x762 = arc_clone(&temp_owl__x762);
                        let temp_owl__x764 = { arc_clone(&owl_initiator_name746) };
                        let owl__x764 = arc_clone(&temp_owl__x764);
                        let temp_owl__x765 = {
                        rc_vec_eq(&arc_clone(&owl__x762), &arc_clone(&owl__x764))
                        };
                        let owl__x765 = temp_owl__x765;
                        if owl__x765 {
                            let temp_owl__x751 = { arc_clone(&owl_i2r_742) };
                            let owl__x751 = arc_clone(&temp_owl__x751);
                            let temp_owl__x752 = { arc_clone(&owl__x751) };
                            let owl__x752 = arc_clone(&temp_owl__x752);
                            let temp_owl__x755 = { arc_clone(&owl__x752) };
                            let owl__x755 = arc_clone(&temp_owl__x755);
                            let temp_owl__x756 = { arc_clone(&owl_pkt737) };
                            let owl__x756 = arc_clone(&temp_owl__x756);
                            let temp_owl__x757 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x757 = arc_new(temp_owl__x757);
                            let temp_owl__x758 = { arc_clone(&owl_ctr738) };
                            let owl__x758 = arc_clone(&temp_owl__x758);
                            (
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x755))),
                                    vec_as_slice(&(*arc_clone(&owl__x756))),
                                    vec_as_slice(&(*arc_clone(&owl__x758))),
                                    vec_as_slice(&(*arc_clone(&owl__x757))),
                                ),
                                Tracked(itree),
                            )
                        } else {
                            (None, Tracked(itree))
                        }
                    }
                }
            } else {
                let temp_owl__x736 = { None };
                let owl__x736 = temp_owl__x736;
                (owl__x736, Tracked(itree))
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
            let temp_owl__x847 = { owl_transp_keys_val12794 };
            let owl__x847 = temp_owl__x847;
            let parseval = owl__x847;
            let owl_transp_receiver778 = arc_new(parseval.owl__transp_keys_initiator);
            let owl__777 = arc_new(parseval.owl__transp_keys_responder);
            let owl__774 = arc_new(parseval.owl__transp_keys_T_init_send);
            let owl_r2i_773 = arc_new(parseval.owl__transp_keys_T_resp_send);
            {
                let temp_owl__x783 = { arc_clone(&owl_r2i_773) };
                let owl__x783 = arc_clone(&temp_owl__x783);
                let temp_owl__x784 = { arc_clone(&owl__x783) };
                let owl__x784 = arc_clone(&temp_owl__x784);
                let temp_owl__x786 = { owl_counter_as_bytes(&(mut_state.owl_N_resp_send)) };
                let owl__x786 = arc_new(temp_owl__x786);
                let temp_owl__x790 = { owl_transp_tag_value() };
                let owl__x790 = arc_new(temp_owl__x790);
                let temp_owl__x791 = { arc_clone(&owl__x790) };
                let owl__x791 = arc_clone(&temp_owl__x791);
                let temp_owl__x842 = { arc_clone(&owl_transp_receiver778) };
                let owl__x842 = arc_clone(&temp_owl__x842);
                let temp_owl__x843 = { vec_length(&(*arc_clone(&owl__x842))) };
                let owl__x843 = temp_owl__x843;
                let temp_owl__x845 = { 4 };
                let owl__x845 = temp_owl__x845;
                let temp_owl__x846 = { owl__x843 == owl__x845 };
                let owl__x846 = temp_owl__x846;
                if owl__x846 {
                    let temp_owl__x797 = { arc_clone(&owl__x784) };
                    let owl__x797 = arc_clone(&temp_owl__x797);
                    let temp_owl__x799 = { arc_clone(&owl_plaintext12793) };
                    let owl__x799 = arc_clone(&temp_owl__x799);
                    let temp_owl__x801 = {
                        {
                            let x: Vec<u8> = mk_vec_u8![];
                            x
                        }
                    };
                    let owl__x801 = arc_new(temp_owl__x801);
                    let temp_owl__x802 = {
                        match owl_enc_st_aead(
                            vec_as_slice(&(*arc_clone(&owl__x797))),
                            vec_as_slice(&(*arc_clone(&owl__x799))),
                            &mut mut_state.owl_N_resp_send,
                            vec_as_slice(&(*arc_clone(&owl__x801))),
                        ) {
                            Ok(ctxt) => ctxt,
                            Err(e) => { return Err(e) },
                        }
                    };
                    let owl__x802 = arc_clone(&temp_owl__x802);
                    let temp_owl__x818 = { arc_clone(&owl__x791) };
                    let owl__x818 = arc_clone(&temp_owl__x818);
                    let temp_owl__x820 = { arc_clone(&owl_transp_receiver778) };
                    let owl__x820 = arc_clone(&temp_owl__x820);
                    let temp_owl__x822 = { arc_clone(&owl__x786) };
                    let owl__x822 = arc_clone(&temp_owl__x822);
                    let temp_owl__x824 = { arc_clone(&owl__x802) };
                    let owl__x824 = arc_clone(&temp_owl__x824);
                    let temp_owl__x826 = {
                    owl_transp {
                        owl__transp_tag: clone_vec_u8(&*arc_clone(&owl__x818)),
                        owl__transp_receiver: clone_vec_u8(&*arc_clone(&owl__x820)),
                        owl__transp_counter: clone_vec_u8(&*arc_clone(&owl__x822)),
                        owl__transp_packet: clone_vec_u8(&*arc_clone(&owl__x824)),
                    }
                    };
                    let owl__x826 = temp_owl__x826;
                    let temp_owl__x827 = { owl__x826 };
                    let owl__x827 = temp_owl__x827;
                    let temp_owl__x831 = { owl__x827 };
                    let owl__x831 = temp_owl__x831;
                    let temp_owl__x832 = {
                    owl_output::<(Option<()>, state_Responder)>(
                        Tracked(&mut itree),
                        vec_as_slice(&(serialize_owl_transp(&owl__x831))),
                        &Initiator_addr(),
                        &Responder_addr(),
                        obuf
                    )
                    };
                    let owl__x832 = temp_owl__x832;
                    let temp_owl__x835 = { () };
                    let owl__x835 = temp_owl__x835;
                    let temp_owl__x836 = { Some(owl__x835) };
                    let owl__x836 = temp_owl__x836;
                    (owl__x836, Tracked(itree))
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
            let temp_owl__x1192 = { owl_msg1_val_8321 };
            let owl__x1192 = temp_owl__x1192;
            let temp_owl__x1191 = { owl__x1192 };
            let owl__x1191 = temp_owl__x1191;
            let parseval = owl__x1191;
            let owl_C3860 = arc_new(parseval.owl__responder_msg1_C3);
            let owl_H4859 = arc_new(parseval.owl__responder_msg1_H4);
            let owl_ephemeral_858 = arc_new(parseval.owl__responder_msg1_ephemeral);
            let owl_dhpk_S_init857 = arc_new(parseval.owl__responder_msg1_sender_pk);
            let owl_msg2_receiver856 = arc_new(parseval.owl__responder_msg1_sender);
            {
                let temp_owl__x865 = { arc_clone(&owl_ephemeral_858) };
                let owl__x865 = arc_clone(&temp_owl__x865);
                let temp_owl__x866 = { arc_clone(&owl__x865) };
                let owl__x866 = arc_clone(&temp_owl__x866);
                let temp_owl__x873 = { arc_clone(&self.owl_E_resp) };
                let owl__x873 = arc_clone(&temp_owl__x873);
                let temp_owl__x875 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x873)))) };
                let owl__x875 = arc_clone(&temp_owl__x875);
                let temp_owl__x876 = { arc_clone(&owl__x875) };
                let owl__x876 = arc_clone(&temp_owl__x876);
                let temp_owl__x880 = { owl_zeros_32() };
                let owl__x880 = arc_new(temp_owl__x880);
                let temp_owl__x881 = { arc_clone(&owl__x880) };
                let owl__x881 = arc_clone(&temp_owl__x881);
                let temp_owl__x886 = { arc_clone(&owl_C3860) };
                let owl__x886 = arc_clone(&temp_owl__x886);
                let temp_owl__x888 = { arc_clone(&owl__x876) };
                let owl__x888 = arc_clone(&temp_owl__x888);
                let owl_msg2_C41196 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x886))),
                    vec_as_slice(&(*arc_clone(&owl__x888))),
                );
                let temp_owl__x889 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C41196), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x889 = arc_clone(&temp_owl__x889);
                let temp_owl__x902 = { arc_clone(&owl_H4859) };
                let owl__x902 = arc_clone(&temp_owl__x902);
                let temp_owl__x904 = { arc_clone(&owl__x876) };
                let owl__x904 = arc_clone(&temp_owl__x904);
                let temp_owl__x906 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x902))),
                    vec_as_slice(&(*arc_clone(&owl__x904))),
                )
                };
                let owl__x906 = arc_new(temp_owl__x906);
                let temp_owl__x908 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x906)))) };
                let owl__x908 = arc_clone(&temp_owl__x908);
                let temp_owl__x909 = { arc_clone(&owl__x908) };
                let owl__x909 = arc_clone(&temp_owl__x909);
                let temp_owl__x919 = { arc_clone(&owl__x866) };
                let owl__x919 = arc_clone(&temp_owl__x919);
                let temp_owl__x921 = { arc_clone(&self.owl_E_resp) };
                let owl__x921 = arc_clone(&temp_owl__x921);
                let temp_owl__x923 = {
                owl_dh_combine(
                    vec_as_slice(&(*arc_clone(&owl__x919))),
                    vec_as_slice(&(*arc_clone(&owl__x921))),
                )
                };
                let owl__x923 = arc_clone(&temp_owl__x923);
                let temp_owl__x924 = { arc_clone(&owl__x923) };
                let owl__x924 = arc_clone(&temp_owl__x924);
                let temp_owl__x929 = { arc_clone(&owl__x889) };
                let owl__x929 = arc_clone(&temp_owl__x929);
                let temp_owl__x931 = { arc_clone(&owl__x924) };
                let owl__x931 = arc_clone(&temp_owl__x931);
                let owl_msg2_C51197 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x929))),
                    vec_as_slice(&(*arc_clone(&owl__x931))),
                );
                let temp_owl__x932 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C51197), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x932 = arc_clone(&temp_owl__x932);
                let temp_owl__x939 = { arc_clone(&owl__x932) };
                let owl__x939 = arc_clone(&temp_owl__x939);
                let temp_owl__x942 = { arc_clone(&owl_dhpk_S_init857) };
                let owl__x942 = arc_clone(&temp_owl__x942);
                let temp_owl__x944 = { arc_clone(&self.owl_E_resp) };
                let owl__x944 = arc_clone(&temp_owl__x944);
                let temp_owl__x945 = {
                owl_dh_combine(
                    vec_as_slice(&(*arc_clone(&owl__x942))),
                    vec_as_slice(&(*arc_clone(&owl__x944))),
                )
                };
                let owl__x945 = arc_clone(&temp_owl__x945);
                let owl_msg2_C61198 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x939))),
                    vec_as_slice(&(*arc_clone(&owl__x945))),
                );
                let temp_owl__x946 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C61198), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x946 = arc_clone(&temp_owl__x946);
                let temp_owl__x951 = { arc_clone(&owl__x946) };
                let owl__x951 = arc_clone(&temp_owl__x951);
                let temp_owl__x953 = { arc_clone(&owl__x881) };
                let owl__x953 = arc_clone(&temp_owl__x953);
                let owl_msg2_C71199 = owl_extract_expand_to_len(
                    0 + nonce_size() + nonce_size() + key_size(),
                    vec_as_slice(&(*arc_clone(&owl__x951))),
                    vec_as_slice(&(*arc_clone(&owl__x953))),
                );
                let temp_owl__x954 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C71199), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x954 = arc_clone(&temp_owl__x954);
                let temp_owl__x959 = { arc_clone(&owl__x946) };
                let owl__x959 = arc_clone(&temp_owl__x959);
                let temp_owl__x961 = { arc_clone(&owl__x881) };
                let owl__x961 = arc_clone(&temp_owl__x961);
                let temp_owl__x962 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_msg2_C71199),
                            0 + nonce_size(),
                            0 + nonce_size() + nonce_size(),
                        ),
                    ),
                )
                };
                let owl__x962 = arc_clone(&temp_owl__x962);
                let temp_owl__x967 = { arc_clone(&owl__x946) };
                let owl__x967 = arc_clone(&temp_owl__x967);
                let temp_owl__x969 = { arc_clone(&owl__x881) };
                let owl__x969 = arc_clone(&temp_owl__x969);
                let temp_owl__x970 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_msg2_C71199),
                            0 + nonce_size() + nonce_size(),
                            0 + nonce_size() + nonce_size() + key_size(),
                        ),
                    ),
                )
                };
                let owl__x970 = arc_clone(&temp_owl__x970);
                let temp_owl__x983 = { arc_clone(&owl__x909) };
                let owl__x983 = arc_clone(&temp_owl__x983);
                let temp_owl__x985 = { arc_clone(&owl__x962) };
                let owl__x985 = arc_clone(&temp_owl__x985);
                let temp_owl__x987 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x983))),
                    vec_as_slice(&(*arc_clone(&owl__x985))),
                )
                };
                let owl__x987 = arc_new(temp_owl__x987);
                let temp_owl__x989 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x987)))) };
                let owl__x989 = arc_clone(&temp_owl__x989);
                let temp_owl__x990 = { arc_clone(&owl__x989) };
                let owl__x990 = arc_clone(&temp_owl__x990);
                let temp_owl__x994 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x994 = arc_new(temp_owl__x994);
                let temp_owl__x995 = { arc_clone(&owl__x994) };
                let owl__x995 = arc_clone(&temp_owl__x995);
                let temp_owl__x1001 = { arc_clone(&owl__x970) };
                let owl__x1001 = arc_clone(&temp_owl__x1001);
                let temp_owl__x1003 = { arc_clone(&owl__x995) };
                let owl__x1003 = arc_clone(&temp_owl__x1003);
                let temp_owl__x1005 = { arc_clone(&owl__x990) };
                let owl__x1005 = arc_clone(&temp_owl__x1005);
                let temp_owl__x1006 = {
                    match owl_enc_st_aead(
                        vec_as_slice(&(*arc_clone(&owl__x1001))),
                        vec_as_slice(&(*arc_clone(&owl__x1003))),
                        &mut mut_state.owl_aead_counter_msg2_C7,
                        vec_as_slice(&(*arc_clone(&owl__x1005))),
                    ) {
                        Ok(ctxt) => ctxt,
                        Err(e) => { return Err(e) },
                    }
                };
                let owl__x1006 = arc_clone(&temp_owl__x1006);
                let temp_owl__x1019 = { arc_clone(&owl__x990) };
                let owl__x1019 = arc_clone(&temp_owl__x1019);
                let temp_owl__x1021 = { arc_clone(&owl__x1006) };
                let owl__x1021 = arc_clone(&temp_owl__x1021);
                let temp_owl__x1023 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1019))),
                    vec_as_slice(&(*arc_clone(&owl__x1021))),
                )
                };
                let owl__x1023 = arc_new(temp_owl__x1023);
                let temp_owl__x1025 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x1023)))) };
                let owl__x1025 = arc_clone(&temp_owl__x1025);
                let temp_owl__x1026 = { arc_clone(&owl__x1025) };
                let owl__x1026 = arc_clone(&temp_owl__x1026);
                let (temp_owl__x1028, Tracked(itree)): (
                    _,
                    Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
                ) = {
                    owl_call!( itree
, *mut_state
, get_sender_r_spec(*self, *mut_state)
, self.owl_get_sender_r(mut_state) )
                };
                let owl__x1028 = arc_clone(&temp_owl__x1028);
                let temp_owl__x1032 = { owl_msg2_tag_value() };
                let owl__x1032 = arc_new(temp_owl__x1032);
                let temp_owl__x1033 = { arc_clone(&owl__x1032) };
                let owl__x1033 = arc_clone(&temp_owl__x1033);
                let temp_owl__x1046 = { owl_mac1() };
                let owl__x1046 = arc_new(temp_owl__x1046);
                let temp_owl__x1048 = { arc_clone(&owl_dhpk_S_init857) };
                let owl__x1048 = arc_clone(&temp_owl__x1048);
                let temp_owl__x1050 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1046))),
                    vec_as_slice(&(*arc_clone(&owl__x1048))),
                )
                };
                let owl__x1050 = arc_new(temp_owl__x1050);
                let temp_owl__x1052 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x1050)))) };
                let owl__x1052 = arc_clone(&temp_owl__x1052);
                let temp_owl__x1053 = { arc_clone(&owl__x1052) };
                let owl__x1053 = arc_clone(&temp_owl__x1053);
                let temp_owl__x1066 = { arc_clone(&owl__x1053) };
                let owl__x1066 = arc_clone(&temp_owl__x1066);
                let temp_owl__x1072 = { arc_clone(&owl__x1033) };
                let owl__x1072 = arc_clone(&temp_owl__x1072);
                let temp_owl__x1074 = { arc_clone(&owl__x1028) };
                let owl__x1074 = arc_clone(&temp_owl__x1074);
                let temp_owl__x1075 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1072))),
                    vec_as_slice(&(*arc_clone(&owl__x1074))),
                )
                };
                let owl__x1075 = arc_new(temp_owl__x1075);
                let temp_owl__x1077 = { arc_clone(&owl_msg2_receiver856) };
                let owl__x1077 = arc_clone(&temp_owl__x1077);
                let temp_owl__x1078 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1075))),
                    vec_as_slice(&(*arc_clone(&owl__x1077))),
                )
                };
                let owl__x1078 = arc_new(temp_owl__x1078);
                let temp_owl__x1080 = { arc_clone(&owl__x876) };
                let owl__x1080 = arc_clone(&temp_owl__x1080);
                let temp_owl__x1081 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1078))),
                    vec_as_slice(&(*arc_clone(&owl__x1080))),
                )
                };
                let owl__x1081 = arc_new(temp_owl__x1081);
                let temp_owl__x1083 = { arc_clone(&owl__x1006) };
                let owl__x1083 = arc_clone(&temp_owl__x1083);
                let temp_owl__x1084 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1081))),
                    vec_as_slice(&(*arc_clone(&owl__x1083))),
                )
                };
                let owl__x1084 = arc_new(temp_owl__x1084);
                let temp_owl__x1085 = {
                owl_mac(
                    vec_as_slice(&(*arc_clone(&owl__x1066))),
                    vec_as_slice(&(*arc_clone(&owl__x1084))),
                )
                };
                let owl__x1085 = arc_clone(&temp_owl__x1085);
                let temp_owl__x1089 = { owl_zeros_16() };
                let owl__x1089 = arc_new(temp_owl__x1089);
                let temp_owl__x1090 = { arc_clone(&owl__x1089) };
                let owl__x1090 = arc_clone(&temp_owl__x1090);
                let temp_owl__x1115 = { arc_clone(&owl__x1033) };
                let owl__x1115 = arc_clone(&temp_owl__x1115);
                let temp_owl__x1117 = { arc_clone(&owl__x1028) };
                let owl__x1117 = arc_clone(&temp_owl__x1117);
                let temp_owl__x1119 = { arc_clone(&owl_msg2_receiver856) };
                let owl__x1119 = arc_clone(&temp_owl__x1119);
                let temp_owl__x1121 = { arc_clone(&owl__x876) };
                let owl__x1121 = arc_clone(&temp_owl__x1121);
                let temp_owl__x1123 = { arc_clone(&owl__x1006) };
                let owl__x1123 = arc_clone(&temp_owl__x1123);
                let temp_owl__x1125 = { arc_clone(&owl__x1085) };
                let owl__x1125 = arc_clone(&temp_owl__x1125);
                let temp_owl__x1127 = { arc_clone(&owl__x1090) };
                let owl__x1127 = arc_clone(&temp_owl__x1127);
                let temp_owl__x1129 = {
                owl_msg2 {
                    owl__msg2_tag: clone_vec_u8(&*arc_clone(&owl__x1115)),
                    owl__msg2_sender: clone_vec_u8(&*arc_clone(&owl__x1117)),
                    owl__msg2_receiver: clone_vec_u8(&*arc_clone(&owl__x1119)),
                    owl__msg2_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1121)),
                    owl__msg2_empty: clone_vec_u8(&*arc_clone(&owl__x1123)),
                    owl__msg2_mac1: clone_vec_u8(&*arc_clone(&owl__x1125)),
                    owl__msg2_mac2: clone_vec_u8(&*arc_clone(&owl__x1127)),
                }
                };
                let owl__x1129 = temp_owl__x1129;
                let temp_owl__x1130 = { owl__x1129 };
                let owl__x1130 = temp_owl__x1130;
                let temp_owl__x1134 = { owl__x1130 };
                let owl__x1134 = temp_owl__x1134;
                let temp_owl__x1135 = {
                owl_output::<(Seq<u8>, state_Responder)>(
                    Tracked(&mut itree),
                    vec_as_slice(&(serialize_owl_msg2(&owl__x1134))),
                    &Initiator_addr(),
                    &Responder_addr(),
                    obuf
                )
                };
                let owl__x1135 = temp_owl__x1135;
                let temp_owl__x1140 = { arc_clone(&owl__x954) };
                let owl__x1140 = arc_clone(&temp_owl__x1140);
                let temp_owl__x1142 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1142 = arc_new(temp_owl__x1142);
                let owl_transp_T1200 = owl_extract_expand_to_len(
                    0 + key_size() + key_size(),
                    vec_as_slice(&(*arc_clone(&owl__x1140))),
                    vec_as_slice(&(*arc_clone(&owl__x1142))),
                );
                let temp_owl__x1143 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_transp_T1200), 0, 0 + key_size()),
                    ),
                )
                };
                let owl__x1143 = arc_clone(&temp_owl__x1143);
                let temp_owl__x1148 = { arc_clone(&owl__x954) };
                let owl__x1148 = arc_clone(&temp_owl__x1148);
                let temp_owl__x1150 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1150 = arc_new(temp_owl__x1150);
                let temp_owl__x1151 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_transp_T1200),
                            0 + key_size(),
                            0 + key_size() + key_size(),
                        ),
                    ),
                )
                };
                let owl__x1151 = arc_clone(&temp_owl__x1151);
                let temp_owl__x1173 = { arc_clone(&owl_msg2_receiver856) };
                let owl__x1173 = arc_clone(&temp_owl__x1173);
                let temp_owl__x1175 = { arc_clone(&owl__x1028) };
                let owl__x1175 = arc_clone(&temp_owl__x1175);
                let temp_owl__x1177 = { arc_clone(&owl__x866) };
                let owl__x1177 = arc_clone(&temp_owl__x1177);
                let temp_owl__x1179 = { arc_clone(&owl__x876) };
                let owl__x1179 = arc_clone(&temp_owl__x1179);
                let temp_owl__x1181 = { arc_clone(&owl__x1143) };
                let owl__x1181 = arc_clone(&temp_owl__x1181);
                let temp_owl__x1183 = { arc_clone(&owl__x1151) };
                let owl__x1183 = arc_clone(&temp_owl__x1183);
                let temp_owl__x1185 = {
                owl_transp_keys {
                    owl__transp_keys_initiator: clone_vec_u8(&*arc_clone(&owl__x1173)),
                    owl__transp_keys_responder: clone_vec_u8(&*arc_clone(&owl__x1175)),
                    owl__transp_keys_T_init_send: clone_vec_u8(&*arc_clone(&owl__x1181)),
                    owl__transp_keys_T_resp_send: clone_vec_u8(&*arc_clone(&owl__x1183)),
                }
                };
                let owl__x1185 = temp_owl__x1185;
                let temp_owl__x1186 = { owl__x1185 };
                let owl__x1186 = temp_owl__x1186;
                let temp_owl__x1189 = { owl__x1186 };
                let owl__x1189 = temp_owl__x1189;
                let temp_owl__x1190 = { owl__x1189 };
                let owl__x1190 = temp_owl__x1190;
                (owl__x1190, Tracked(itree))
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
            let (temp_owl_inp1209, owl__1208) = owl_input::<(Option<Seq<u8>>, state_Responder)>(
                Tracked(&mut itree),
                ibuf,
            );
            let owl_inp1209 = arc_new(temp_owl_inp1209);
            let temp_owl__x1497 = { arc_clone(&owl_inp1209) };
            let owl__x1497 = arc_clone(&temp_owl__x1497);
            if let Some(parseval) = parse_owl_msg1(vec_as_slice(&(*arc_clone(&owl__x1497)))) {
                let owl_msg1_tag1217 = arc_new(parseval.owl__msg1_tag);
                let owl_msg1_sender1216 = arc_new(parseval.owl__msg1_sender);
                let owl_msg1_ephemeral_1215 = arc_new(parseval.owl__msg1_ephemeral);
                let owl_msg1_static1214 = arc_new(parseval.owl__msg1_static);
                let owl_msg1_timestamp1213 = arc_new(parseval.owl__msg1_timestamp);
                let owl_msg1_mac11212 = arc_new(parseval.owl__msg1_mac1);
                let owl_msg1_mac21211 = arc_new(parseval.owl__msg1_mac2);
                {
                    let temp_owl__x1492 = { arc_clone(&owl_msg1_sender1216) };
                    let owl__x1492 = arc_clone(&temp_owl__x1492);
                    let temp_owl__x1493 = { vec_length(&(*arc_clone(&owl__x1492))) };
                    let owl__x1493 = temp_owl__x1493;
                    let temp_owl__x1495 = { 4 };
                    let owl__x1495 = temp_owl__x1495;
                    let temp_owl__x1496 = { owl__x1493 == owl__x1495 };
                    let owl__x1496 = temp_owl__x1496;
                    if owl__x1496 {
                        let temp_owl__x1485 = { arc_clone(&owl_msg1_ephemeral_1215) };
                        let owl__x1485 = arc_clone(&temp_owl__x1485);
                        let temp_owl__x1486 = {
                        owl_is_group_elem(vec_as_slice(&(*arc_clone(&owl__x1485))))
                        };
                        let owl__x1486 = temp_owl__x1486;
                        if owl__x1486 {
                            let temp_owl__x1224 = { owl_construction() };
                            let owl__x1224 = arc_new(temp_owl__x1224);
                            let temp_owl__x1226 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1224))))
                            };
                            let owl__x1226 = arc_clone(&temp_owl__x1226);
                            let temp_owl__x1227 = { arc_clone(&owl__x1226) };
                            let owl__x1227 = arc_clone(&temp_owl__x1227);
                            let temp_owl__x1240 = { arc_clone(&owl__x1227) };
                            let owl__x1240 = arc_clone(&temp_owl__x1240);
                            let temp_owl__x1242 = { owl_identifier() };
                            let owl__x1242 = arc_new(temp_owl__x1242);
                            let temp_owl__x1244 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1240))),
                                vec_as_slice(&(*arc_clone(&owl__x1242))),
                            )
                            };
                            let owl__x1244 = arc_new(temp_owl__x1244);
                            let temp_owl__x1246 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1244))))
                            };
                            let owl__x1246 = arc_clone(&temp_owl__x1246);
                            let temp_owl__x1247 = { arc_clone(&owl__x1246) };
                            let owl__x1247 = arc_clone(&temp_owl__x1247);
                            let temp_owl__x1260 = { arc_clone(&owl__x1247) };
                            let owl__x1260 = arc_clone(&temp_owl__x1260);
                            let temp_owl__x1262 = { arc_clone(&owl_dhpk_S_resp8149) };
                            let owl__x1262 = arc_clone(&temp_owl__x1262);
                            let temp_owl__x1264 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1260))),
                                vec_as_slice(&(*arc_clone(&owl__x1262))),
                            )
                            };
                            let owl__x1264 = arc_new(temp_owl__x1264);
                            let temp_owl__x1266 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1264))))
                            };
                            let owl__x1266 = arc_clone(&temp_owl__x1266);
                            let temp_owl__x1267 = { arc_clone(&owl__x1266) };
                            let owl__x1267 = arc_clone(&temp_owl__x1267);
                            let temp_owl__x1273 = { arc_clone(&owl_msg1_ephemeral_1215) };
                            let owl__x1273 = arc_clone(&temp_owl__x1273);
                            let temp_owl__x1274 = { arc_clone(&owl__x1273) };
                            let owl__x1274 = arc_clone(&temp_owl__x1274);
                            let temp_owl__x1279 = { arc_clone(&owl__x1227) };
                            let owl__x1279 = arc_clone(&temp_owl__x1279);
                            let temp_owl__x1281 = { arc_clone(&owl__x1274) };
                            let owl__x1281 = arc_clone(&temp_owl__x1281);
                            let owl_msg1_C11505 = owl_extract_expand_to_len(
                                0 + nonce_size(),
                                vec_as_slice(&(*arc_clone(&owl__x1279))),
                                vec_as_slice(&(*arc_clone(&owl__x1281))),
                            );
                            let temp_owl__x1282 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C11505),
                                        0,
                                        0 + nonce_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1282 = arc_clone(&temp_owl__x1282);
                            let temp_owl__x1295 = { arc_clone(&owl__x1267) };
                            let owl__x1295 = arc_clone(&temp_owl__x1295);
                            let temp_owl__x1297 = { arc_clone(&owl__x1274) };
                            let owl__x1297 = arc_clone(&temp_owl__x1297);
                            let temp_owl__x1299 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1295))),
                                vec_as_slice(&(*arc_clone(&owl__x1297))),
                            )
                            };
                            let owl__x1299 = arc_new(temp_owl__x1299);
                            let temp_owl__x1301 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1299))))
                            };
                            let owl__x1301 = arc_clone(&temp_owl__x1301);
                            let temp_owl__x1302 = { arc_clone(&owl__x1301) };
                            let owl__x1302 = arc_clone(&temp_owl__x1302);
                            let temp_owl__x1312 = { arc_clone(&owl__x1274) };
                            let owl__x1312 = arc_clone(&temp_owl__x1312);
                            let temp_owl__x1314 = { arc_clone(&self.owl_S_resp) };
                            let owl__x1314 = arc_clone(&temp_owl__x1314);
                            let temp_owl__x1316 = {
                            owl_dh_combine(
                                vec_as_slice(&(*arc_clone(&owl__x1312))),
                                vec_as_slice(&(*arc_clone(&owl__x1314))),
                            )
                            };
                            let owl__x1316 = arc_clone(&temp_owl__x1316);
                            let temp_owl__x1317 = { arc_clone(&owl__x1316) };
                            let owl__x1317 = arc_clone(&temp_owl__x1317);
                            let temp_owl__x1322 = { arc_clone(&owl__x1282) };
                            let owl__x1322 = arc_clone(&temp_owl__x1322);
                            let temp_owl__x1324 = { arc_clone(&owl__x1317) };
                            let owl__x1324 = arc_clone(&temp_owl__x1324);
                            let owl_msg1_C21506 = owl_extract_expand_to_len(
                                0 + nonce_size() + key_size(),
                                vec_as_slice(&(*arc_clone(&owl__x1322))),
                                vec_as_slice(&(*arc_clone(&owl__x1324))),
                            );
                            let temp_owl__x1325 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C21506),
                                        0,
                                        0 + nonce_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1325 = arc_clone(&temp_owl__x1325);
                            let temp_owl__x1330 = { arc_clone(&owl__x1282) };
                            let owl__x1330 = arc_clone(&temp_owl__x1330);
                            let temp_owl__x1332 = { arc_clone(&owl__x1317) };
                            let owl__x1332 = arc_clone(&temp_owl__x1332);
                            let temp_owl__x1333 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C21506),
                                        0 + nonce_size(),
                                        0 + nonce_size() + key_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1333 = arc_clone(&temp_owl__x1333);
                            let temp_owl__x1475 = { arc_clone(&owl__x1333) };
                            let owl__x1475 = arc_clone(&temp_owl__x1475);
                            let temp_owl__x1477 = { arc_clone(&owl_msg1_static1214) };
                            let owl__x1477 = arc_clone(&temp_owl__x1477);
                            let temp_owl__x1479 = { arc_clone(&owl__x1302) };
                            let owl__x1479 = arc_clone(&temp_owl__x1479);
                            let temp_owl__x1481 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x1481 = arc_new(temp_owl__x1481);
                            let temp_owl__x1482 = {
                            owl_dec_st_aead(
                                vec_as_slice(&(*arc_clone(&owl__x1475))),
                                vec_as_slice(&(*arc_clone(&owl__x1477))),
                                vec_as_slice(&(*arc_clone(&owl__x1481))),
                                vec_as_slice(&(*arc_clone(&owl__x1479))),
                            )
                            };
                            let owl__x1482 = temp_owl__x1482;
                            let temp_owl_caseval1504 = { owl__x1482 };
                            let owl_caseval1504 = temp_owl_caseval1504;
                            match owl_caseval1504 {
                                None => {
                                    let temp_owl__x1338 = { None };
                                    let owl__x1338 = temp_owl__x1338;
                                    (owl__x1338, Tracked(itree))
                                },
                                Some(temp_owl_msg1_static_dec1339) => {
                                    let owl_msg1_static_dec1339 = arc_clone(
                                        &temp_owl_msg1_static_dec1339,
                                    );
                                    let temp_owl__x1343 = { arc_clone(&owl_msg1_static_dec1339) };
                                    let owl__x1343 = arc_clone(&temp_owl__x1343);
                                    let (temp_owl__x1344, Tracked(itree)): (
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
, checkpk_resp_spec(*self, *mut_state, (&owl__x1343).dview())
, self.owl_checkpk_resp(mut_state, arc_clone(&owl__x1343)) )
                                    };
                                    let owl__x1344 = temp_owl__x1344;
                                    let temp_owl__x1472 = { owl__x1344 };
                                    let owl__x1472 = temp_owl__x1472;
                                    let temp_owl__x1473 = { owl__x1472 };
                                    let owl__x1473 = temp_owl__x1473;
                                    let temp_owl_caseval1503 = { owl__x1473 };
                                    let owl_caseval1503 = temp_owl_caseval1503;
                                    match owl_caseval1503 {
                                        None => {
                                            let temp_owl__x1346 = { None };
                                            let owl__x1346 = temp_owl__x1346;
                                            (owl__x1346, Tracked(itree))
                                        },
                                        Some(temp_owl_ss_S_init_S_resp_1347) => {
                                            let owl_ss_S_init_S_resp_1347 = arc_clone(
                                                &temp_owl_ss_S_init_S_resp_1347,
                                            );
                                            let temp_owl__x1470 = {
                                            arc_clone(&owl_ss_S_init_S_resp_1347)
                                            };
                                            let owl__x1470 = arc_clone(&temp_owl__x1470);
                                            let temp_owl__x1353 = {
                                            arc_clone(&owl_msg1_static_dec1339)
                                            };
                                            let owl__x1353 = arc_clone(&temp_owl__x1353);
                                            let temp_owl__x1354 = { arc_clone(&owl__x1353) };
                                            let owl__x1354 = arc_clone(&temp_owl__x1354);
                                            let temp_owl__x1367 = { arc_clone(&owl__x1302) };
                                            let owl__x1367 = arc_clone(&temp_owl__x1367);
                                            let temp_owl__x1369 = { arc_clone(&owl_msg1_static1214)
                                            };
                                            let owl__x1369 = arc_clone(&temp_owl__x1369);
                                            let temp_owl__x1371 = {
                                            owl_concat(
                                                vec_as_slice(&(*arc_clone(&owl__x1367))),
                                                vec_as_slice(&(*arc_clone(&owl__x1369))),
                                            )
                                            };
                                            let owl__x1371 = arc_new(temp_owl__x1371);
                                            let temp_owl__x1373 = {
                                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1371))))
                                            };
                                            let owl__x1373 = arc_clone(&temp_owl__x1373);
                                            let temp_owl__x1374 = { arc_clone(&owl__x1373) };
                                            let owl__x1374 = arc_clone(&temp_owl__x1374);
                                            let temp_owl__x1379 = { arc_clone(&owl__x1325) };
                                            let owl__x1379 = arc_clone(&temp_owl__x1379);
                                            let temp_owl__x1381 = { arc_clone(&owl__x1470) };
                                            let owl__x1381 = arc_clone(&temp_owl__x1381);
                                            let owl_msg1_C31507 = owl_extract_expand_to_len(
                                                0 + nonce_size() + key_size(),
                                                vec_as_slice(&(*arc_clone(&owl__x1379))),
                                                vec_as_slice(&(*arc_clone(&owl__x1381))),
                                            );
                                            let temp_owl__x1382 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_msg1_C31507),
                                                        0,
                                                        0 + nonce_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x1382 = arc_clone(&temp_owl__x1382);
                                            let temp_owl__x1387 = { arc_clone(&owl__x1325) };
                                            let owl__x1387 = arc_clone(&temp_owl__x1387);
                                            let temp_owl__x1389 = { arc_clone(&owl__x1470) };
                                            let owl__x1389 = arc_clone(&temp_owl__x1389);
                                            let temp_owl__x1390 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_msg1_C31507),
                                                        0 + nonce_size(),
                                                        0 + nonce_size() + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x1390 = arc_clone(&temp_owl__x1390);
                                            let temp_owl__x1462 = { arc_clone(&owl__x1390) };
                                            let owl__x1462 = arc_clone(&temp_owl__x1462);
                                            let temp_owl__x1464 = {
                                            arc_clone(&owl_msg1_timestamp1213)
                                            };
                                            let owl__x1464 = arc_clone(&temp_owl__x1464);
                                            let temp_owl__x1466 = { arc_clone(&owl__x1374) };
                                            let owl__x1466 = arc_clone(&temp_owl__x1466);
                                            let temp_owl__x1468 = {
                                                {
                                                    let x: Vec<u8> = mk_vec_u8![];
                                                    x
                                                }
                                            };
                                            let owl__x1468 = arc_new(temp_owl__x1468);
                                            let temp_owl__x1469 = {
                                            owl_dec_st_aead(
                                                vec_as_slice(&(*arc_clone(&owl__x1462))),
                                                vec_as_slice(&(*arc_clone(&owl__x1464))),
                                                vec_as_slice(&(*arc_clone(&owl__x1468))),
                                                vec_as_slice(&(*arc_clone(&owl__x1466))),
                                            )
                                            };
                                            let owl__x1469 = temp_owl__x1469;
                                            let temp_owl_caseval1502 = { owl__x1469 };
                                            let owl_caseval1502 = temp_owl_caseval1502;
                                            match owl_caseval1502 {
                                                None => {
                                                    let temp_owl__x1395 = { None };
                                                    let owl__x1395 = temp_owl__x1395;
                                                    (owl__x1395, Tracked(itree))
                                                },
                                                Some(temp_owl_msg1_timestamp_dec1396) => {
                                                    let owl_msg1_timestamp_dec1396 = arc_clone(
                                                        &temp_owl_msg1_timestamp_dec1396,
                                                    );
                                                    let temp_owl__x1409 = { arc_clone(&owl__x1374)
                                                    };
                                                    let owl__x1409 = arc_clone(&temp_owl__x1409);
                                                    let temp_owl__x1411 = {
                                                    arc_clone(&owl_msg1_timestamp1213)
                                                    };
                                                    let owl__x1411 = arc_clone(&temp_owl__x1411);
                                                    let temp_owl__x1413 = {
                                                    owl_concat(
                                                        vec_as_slice(&(*arc_clone(&owl__x1409))),
                                                        vec_as_slice(&(*arc_clone(&owl__x1411))),
                                                    )
                                                    };
                                                    let owl__x1413 = arc_new(temp_owl__x1413);
                                                    let temp_owl__x1415 = {
                                                    owl_crh(
                                                        vec_as_slice(&(*arc_clone(&owl__x1413))),
                                                    )
                                                    };
                                                    let owl__x1415 = arc_clone(&temp_owl__x1415);
                                                    let temp_owl__x1416 = { arc_clone(&owl__x1415)
                                                    };
                                                    let owl__x1416 = arc_clone(&temp_owl__x1416);
                                                    let temp_owl__x1435 = { arc_clone(&owl__x1382)
                                                    };
                                                    let owl__x1435 = arc_clone(&temp_owl__x1435);
                                                    let temp_owl__x1437 = { arc_clone(&owl__x1416)
                                                    };
                                                    let owl__x1437 = arc_clone(&temp_owl__x1437);
                                                    let temp_owl__x1439 = { arc_clone(&owl__x1274)
                                                    };
                                                    let owl__x1439 = arc_clone(&temp_owl__x1439);
                                                    let temp_owl__x1441 = { arc_clone(&owl__x1354)
                                                    };
                                                    let owl__x1441 = arc_clone(&temp_owl__x1441);
                                                    let temp_owl__x1443 = {
                                                    arc_clone(&owl_msg1_sender1216)
                                                    };
                                                    let owl__x1443 = arc_clone(&temp_owl__x1443);
                                                    let temp_owl__x1445 = {
                                                    owl_responder_msg1_val {
                                                        owl__responder_msg1_C3: clone_vec_u8(
                                                            &*arc_clone(&owl__x1435),
                                                        ),
                                                        owl__responder_msg1_H4: clone_vec_u8(
                                                            &*arc_clone(&owl__x1437),
                                                        ),
                                                        owl__responder_msg1_ephemeral: clone_vec_u8(
                                                            &*arc_clone(&owl__x1439),
                                                        ),
                                                        owl__responder_msg1_sender_pk: clone_vec_u8(
                                                            &*arc_clone(&owl__x1441),
                                                        ),
                                                        owl__responder_msg1_sender: clone_vec_u8(
                                                            &*arc_clone(&owl__x1443),
                                                        ),
                                                    }
                                                    };
                                                    let owl__x1445 = temp_owl__x1445;
                                                    let temp_owl__x1446 = { owl__x1445 };
                                                    let owl__x1446 = temp_owl__x1446;
                                                    let temp_owl__x1453 = { owl__x1446 };
                                                    let owl__x1453 = temp_owl__x1453;
                                                    let temp_owl__x1455 = { owl__x1453 };
                                                    let owl__x1455 = temp_owl__x1455;
                                                    let temp_owl__x1456 = { owl__x1455 };
                                                    let owl__x1456 = temp_owl__x1456;
                                                    let temp_owl__x1459 = { owl__x1456 };
                                                    let owl__x1459 = temp_owl__x1459;
                                                    let temp_owl__x1460 = { Some(owl__x1459) };
                                                    let owl__x1460 = temp_owl__x1460;
                                                    (owl__x1460, Tracked(itree))
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
                let temp_owl__x1210 = { None };
                let owl__x1210 = temp_owl__x1210;
                (owl__x1210, Tracked(itree))
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


