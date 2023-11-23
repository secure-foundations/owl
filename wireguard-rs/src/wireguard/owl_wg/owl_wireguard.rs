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
)
    requires
        old(t).view().is_output(x.dview(), endpoint_of_addr(dest_addr.view())),
    ensures
        t.view() == old(t).view().give_output(),
{
    todo!()
}

#[verifier(external_body)]
pub fn owl_input<A>(
    Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
) -> (ie: (Vec<u8>, String))
    requires
        old(t).view().is_input(),
    ensures
        t.view() == old(t).view().take_input(ie.0.dview(), endpoint_of_addr(ie.1.view())),
{
    todo!()
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
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_msg1(x: Seq<u8>) -> Option<owlSpec_msg1> {
    let stream = parse_serialize::SpecStream { data: x, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::spec_parse_owl_msg1(stream) {
        let (
            (
                (
                    ((owlSpec__msg1_tag, owlSpec__msg1_sender), owlSpec__msg1_ephemeral),
                    owlSpec__msg1_static,
                ),
                owlSpec__msg1_timestamp,
            ),
            owlSpec__msg1_mac1,
        ) = parsed;
        Some(
            owlSpec_msg1 {
                owlSpec__msg1_tag,
                owlSpec__msg1_sender,
                owlSpec__msg1_ephemeral,
                owlSpec__msg1_static,
                owlSpec__msg1_timestamp,
                owlSpec__msg1_mac1,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_msg1_inner(x: owlSpec_msg1) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__msg1_tag.len(), x.owlSpec__msg1_sender.len(), x.owlSpec__msg1_ephemeral.len(), x.owlSpec__msg1_static.len(), x.owlSpec__msg1_timestamp.len(), x.owlSpec__msg1_mac1.len() ] {
        let stream = parse_serialize::SpecStream {
            data: seq_u8_of_len(
                x.owlSpec__msg1_tag.len() + x.owlSpec__msg1_sender.len()
                    + x.owlSpec__msg1_ephemeral.len() + x.owlSpec__msg1_static.len()
                    + x.owlSpec__msg1_timestamp.len() + x.owlSpec__msg1_mac1.len(),
            ),
            start: 0,
        };
        if let Ok((serialized, n)) = parse_serialize::spec_serialize_owl_msg1(
            stream,
            ((
                (
                    (
                        ((x.owlSpec__msg1_tag, x.owlSpec__msg1_sender), x.owlSpec__msg1_ephemeral),
                        x.owlSpec__msg1_static,
                    ),
                    x.owlSpec__msg1_timestamp,
                ),
                x.owlSpec__msg1_mac1,
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
) -> Seq<u8> {
    serialize_owlSpec_msg1(
        owlSpec_msg1 {
            owlSpec__msg1_tag: arg__msg1_tag,
            owlSpec__msg1_sender: arg__msg1_sender,
            owlSpec__msg1_ephemeral: arg__msg1_ephemeral,
            owlSpec__msg1_static: arg__msg1_static,
            owlSpec__msg1_timestamp: arg__msg1_timestamp,
            owlSpec__msg1_mac1: arg__msg1_mac1,
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
}

#[verifier::opaque]
pub closed spec fn parse_owlSpec_msg2(x: Seq<u8>) -> Option<owlSpec_msg2> {
    let stream = parse_serialize::SpecStream { data: x, start: 0 };
    if let Ok((_, _, parsed)) = parse_serialize::spec_parse_owl_msg2(stream) {
        let (
            (
                (
                    ((owlSpec__msg2_tag, owlSpec__msg2_sender), owlSpec__msg2_receiver),
                    owlSpec__msg2_ephemeral,
                ),
                owlSpec__msg2_empty,
            ),
            owlSpec__msg2_mac1,
        ) = parsed;
        Some(
            owlSpec_msg2 {
                owlSpec__msg2_tag,
                owlSpec__msg2_sender,
                owlSpec__msg2_receiver,
                owlSpec__msg2_ephemeral,
                owlSpec__msg2_empty,
                owlSpec__msg2_mac1,
            },
        )
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn serialize_owlSpec_msg2_inner(x: owlSpec_msg2) -> Option<Seq<u8>> {
    if no_usize_overflows_spec![ x.owlSpec__msg2_tag.len(), x.owlSpec__msg2_sender.len(), x.owlSpec__msg2_receiver.len(), x.owlSpec__msg2_ephemeral.len(), x.owlSpec__msg2_empty.len(), x.owlSpec__msg2_mac1.len() ] {
        let stream = parse_serialize::SpecStream {
            data: seq_u8_of_len(
                x.owlSpec__msg2_tag.len() + x.owlSpec__msg2_sender.len()
                    + x.owlSpec__msg2_receiver.len() + x.owlSpec__msg2_ephemeral.len()
                    + x.owlSpec__msg2_empty.len() + x.owlSpec__msg2_mac1.len(),
            ),
            start: 0,
        };
        if let Ok((serialized, n)) = parse_serialize::spec_serialize_owl_msg2(
            stream,
            ((
                (
                    (
                        ((x.owlSpec__msg2_tag, x.owlSpec__msg2_sender), x.owlSpec__msg2_receiver),
                        x.owlSpec__msg2_ephemeral,
                    ),
                    x.owlSpec__msg2_empty,
                ),
                x.owlSpec__msg2_mac1,
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
) -> Seq<u8> {
    serialize_owlSpec_msg2(
        owlSpec_msg2 {
            owlSpec__msg2_tag: arg__msg2_tag,
            owlSpec__msg2_sender: arg__msg2_sender,
            owlSpec__msg2_receiver: arg__msg2_receiver,
            owlSpec__msg2_ephemeral: arg__msg2_ephemeral,
            owlSpec__msg2_empty: arg__msg2_empty,
            owlSpec__msg2_mac1: arg__msg2_mac1,
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
(ret(dec_st_aead(r2i, pkt, ctr, empty_seq_u8())))) else ((ret (Option::None))))
} )
} otherwise ((ret (Option::None))))
)
}

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

pub open spec fn receive_msg2_spec(
    cfg: cfg_Initiator,
    mut_state: state_Initiator,
    msg1_val: owlSpec_initiator_msg1_val,
    dhpk_S_resp: Seq<u8>,
) -> (res: ITree<(Option<Seq<u8>>, state_Initiator), Endpoint>) {
    owl_spec!(mut_state,state_Initiator,
(input (inp, _unused414)) in
(parse (parse_owlSpec_msg2(inp)) as (owlSpec_msg2{owlSpec__msg2_tag : msg2_tag , owlSpec__msg2_sender : msg2_sender , owlSpec__msg2_receiver : msg2_receiver , owlSpec__msg2_ephemeral : msg2_ephemeral_ , owlSpec__msg2_empty : msg2_empty , owlSpec__msg2_mac1 : msg2_mac2 }) in {
(parse (msg1_val) as (owlSpec_initiator_msg1_val{owlSpec__initiator_msg1_C3 : C3 , owlSpec__initiator_msg1_H4 : H4 }) in {
(if (andb( length(msg2_sender) == 4
, length( msg2_receiver ) == 4 )) then ((if (is_group_elem( msg2_ephemeral_ )) then (let psk = ((ret (seq![0x00u8, 0x00u8, 0x00u8, 0x00u8, ]))) in
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
let caseval = ((ret(dec_st_aead(k0, msg2_empty, H6, empty_seq_u8())))) in
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
let H4 = ((ret (crh(concat(H3, timestamp))))) in
let msg1_sender = (call(get_sender_i_spec(cfg, mut_state))) in
let msg1_tag = ((ret (msg1_tag_value()))) in
let msg1_mac1_k = ((ret(kdf( (0+MACKEY_SIZE()) as usize
, mac1()
, dhpk_S_resp ).subrange(0, 0+MACKEY_SIZE())))) in
let msg1_mac1 = ((ret(mac( msg1_mac1_k
, concat( concat(concat(concat(msg1_tag, msg1_sender), e_init), msg1_static)
, msg1_timestamp ) )))) in
let msg1_output = ((ret (msg1( msg1_tag
, msg1_sender
, e_init
, msg1_static
, msg1_timestamp
, msg1_mac1 )))) in
(output (msg1_output) to (Endpoint::Loc_Responder)) in
let retval = ((ret (initiator_msg1_val(C3, H4)))) in
(ret (retval))
)
}

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

pub open spec fn transp_recv_resp_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    transp_keys_val: owlSpec_transp_keys,
    c: Seq<u8>,
) -> (res: ITree<(Option<Seq<u8>>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(parse (parse_owlSpec_transp(c)) as (owlSpec_transp{owlSpec__transp_tag : _unused777 , owlSpec__transp_receiver : from , owlSpec__transp_counter : ctr , owlSpec__transp_packet : pkt }) in {
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : initiator_name , owlSpec__transp_keys_responder : _unused778 , owlSpec__transp_keys_init_ephemeral : eph_init , owlSpec__transp_keys_resp_ephemeral : _unused779 , owlSpec__transp_keys_T_init_send : i2r_ , owlSpec__transp_keys_T_resp_send : _unused780 }) in {
(if (c == initiator_name) then (let i2r = ((ret (i2r_))) in
(ret(dec_st_aead(i2r, pkt, ctr, empty_seq_u8())))) else ((ret (Option::None))))
} )
} otherwise ((ret (Option::None))))
)
}

pub open spec fn transp_send_resp_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    transp_keys_val: owlSpec_transp_keys,
    plaintext: Seq<u8>,
) -> (res: ITree<(Option<()>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(parse (transp_keys_val) as (owlSpec_transp_keys{owlSpec__transp_keys_initiator : transp_receiver , owlSpec__transp_keys_responder : _unused858 , owlSpec__transp_keys_init_ephemeral : eph_init , owlSpec__transp_keys_resp_ephemeral : _unused859 , owlSpec__transp_keys_T_init_send : _unused860 , owlSpec__transp_keys_T_resp_send : r2i_ }) in {
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

pub open spec fn generate_msg2_spec(
    cfg: cfg_Responder,
    mut_state: state_Responder,
    msg1_val_: owlSpec_responder_msg1_val,
) -> (res: ITree<(Seq<u8>, state_Responder), Endpoint>) {
    owl_spec!(mut_state,state_Responder,
(parse (msg1_val_) as (owlSpec_responder_msg1_val{owlSpec__responder_msg1_C3 : C3 , owlSpec__responder_msg1_H4 : H4 , owlSpec__responder_msg1_ephemeral : ephemeral_ , owlSpec__responder_msg1_sender_pk : dhpk_S_init , owlSpec__responder_msg1_sender : msg2_receiver }) in {
let ephemeral = ((ret (ephemeral_))) in
let e_resp_pk = ((ret (dhpk((*cfg.owl_E_resp).dview())))) in
let psk = ((ret (seq![0x00u8, 0x00u8, 0x00u8, 0x00u8, ]))) in
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
let msg2_mac1_k = ((ret(kdf( (0+MACKEY_SIZE()) as usize
, mac1()
, dhpk_S_init ).subrange(0, 0+MACKEY_SIZE())))) in
let msg2_mac1 = ((ret(mac( msg2_mac1_k
, concat( concat( concat(concat(msg2_tag, msg2_sender), msg2_receiver)
, e_resp_pk )
, msg2_empty ) )))) in
let msg2_output = ((ret (msg2( msg2_tag
, msg2_sender
, msg2_receiver
, e_resp_pk
, msg2_empty
, msg2_mac1 )))) in
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

pub open spec fn receive_msg1_spec(cfg: cfg_Responder, mut_state: state_Responder) -> (res: ITree<
    (Option<Seq<u8>>, state_Responder),
    Endpoint,
>) {
    owl_spec!(mut_state,state_Responder,
(input (inp, _unused1518)) in
(parse (parse_owlSpec_msg1(inp)) as (owlSpec_msg1{owlSpec__msg1_tag : msg1_tag , owlSpec__msg1_sender : msg1_sender , owlSpec__msg1_ephemeral : msg1_ephemeral_ , owlSpec__msg1_static : msg1_static , owlSpec__msg1_timestamp : msg1_timestamp , owlSpec__msg1_mac1 : msg1_mac1 }) in {
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
let caseval = ((ret(dec_st_aead(k0, msg1_static, empty_seq_u8(), H2)))) in
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
let caseval = ((ret(dec_st_aead(k1, msg1_timestamp, empty_seq_u8(), H3)))) in
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
#[derive(Debug)]
pub struct owl_msg1 {
    pub owl__msg1_tag: Vec<u8>,
    pub owl__msg1_sender: Vec<u8>,
    pub owl__msg1_ephemeral: Vec<u8>,
    pub owl__msg1_static: Vec<u8>,
    pub owl__msg1_timestamp: Vec<u8>,
    pub owl__msg1_mac1: Vec<u8>,
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
                (((owl__msg1_tag, owl__msg1_sender), owl__msg1_ephemeral), owl__msg1_static),
                owl__msg1_timestamp,
            ),
            owl__msg1_mac1,
        ) = parsed;
        Some(
            owl_msg1 {
                owl__msg1_tag,
                owl__msg1_sender,
                owl__msg1_ephemeral,
                owl__msg1_static,
                owl__msg1_timestamp,
                owl__msg1_mac1,
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
    if no_usize_overflows![ vec_length(&arg.owl__msg1_tag), vec_length(&arg.owl__msg1_sender), vec_length(&arg.owl__msg1_ephemeral), vec_length(&arg.owl__msg1_static), vec_length(&arg.owl__msg1_timestamp), vec_length(&arg.owl__msg1_mac1) ] {
        let stream = parse_serialize::Stream {
            data: vec_u8_of_len(
                vec_length(&arg.owl__msg1_tag) + vec_length(&arg.owl__msg1_sender) + vec_length(
                    &arg.owl__msg1_ephemeral,
                ) + vec_length(&arg.owl__msg1_static) + vec_length(&arg.owl__msg1_timestamp)
                    + vec_length(&arg.owl__msg1_mac1),
            ),
            start: 0,
        };
        dbg!(arg.owl__msg1_tag.len());
        dbg!(arg.owl__msg1_sender.len());
        dbg!(arg.owl__msg1_ephemeral.len());
        dbg!(arg.owl__msg1_static.len());
        dbg!(arg.owl__msg1_timestamp.len());
        dbg!(arg.owl__msg1_mac1.len());
        let ser_result = parse_serialize::serialize_owl_msg1(
            stream,
            ((
                (
                    (
                        (
                            (clone_vec_u8(&arg.owl__msg1_tag), clone_vec_u8(&arg.owl__msg1_sender)),
                            clone_vec_u8(&arg.owl__msg1_ephemeral),
                        ),
                        clone_vec_u8(&arg.owl__msg1_static),
                    ),
                    clone_vec_u8(&arg.owl__msg1_timestamp),
                ),
                clone_vec_u8(&arg.owl__msg1_mac1),
            )),
        );
        if let Ok((mut serialized, n)) = ser_result {
            vec_truncate(&mut serialized.data, n);
            Some(serialized.data)
        } else {
            println!("serialize failed");
            None
        }
    } else {
        println!("serialize_owl_msg1_inner: overflow");
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
                (((owl__msg2_tag, owl__msg2_sender), owl__msg2_receiver), owl__msg2_ephemeral),
                owl__msg2_empty,
            ),
            owl__msg2_mac1,
        ) = parsed;
        Some(
            owl_msg2 {
                owl__msg2_tag,
                owl__msg2_sender,
                owl__msg2_receiver,
                owl__msg2_ephemeral,
                owl__msg2_empty,
                owl__msg2_mac1,
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
    if no_usize_overflows![ vec_length(&arg.owl__msg2_tag), vec_length(&arg.owl__msg2_sender), vec_length(&arg.owl__msg2_receiver), vec_length(&arg.owl__msg2_ephemeral), vec_length(&arg.owl__msg2_empty), vec_length(&arg.owl__msg2_mac1) ] {
        let stream = parse_serialize::Stream {
            data: vec_u8_of_len(
                vec_length(&arg.owl__msg2_tag) + vec_length(&arg.owl__msg2_sender) + vec_length(
                    &arg.owl__msg2_receiver,
                ) + vec_length(&arg.owl__msg2_ephemeral) + vec_length(&arg.owl__msg2_empty)
                    + vec_length(&arg.owl__msg2_mac1),
            ),
            start: 0,
        };
        let ser_result = parse_serialize::serialize_owl_msg2(
            stream,
            ((
                (
                    (
                        (
                            (clone_vec_u8(&arg.owl__msg2_tag), clone_vec_u8(&arg.owl__msg2_sender)),
                            clone_vec_u8(&arg.owl__msg2_receiver),
                        ),
                        clone_vec_u8(&arg.owl__msg2_ephemeral),
                    ),
                    clone_vec_u8(&arg.owl__msg2_empty),
                ),
                clone_vec_u8(&arg.owl__msg2_mac1),
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
        owl_transp_keys_val30639: owl_transp_keys,
        owl_c30638: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<Arc<Vec<u8>>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_recv_init_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val30639.dview(),
                owl_c30638.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let temp_owl__x33 = { arc_clone(&owl_c30638) };
            let owl__x33 = arc_clone(&temp_owl__x33);
            if let Some(parseval) = parse_owl_transp(vec_as_slice(&(*arc_clone(&owl__x33)))) {
                let owl__6 = arc_new(parseval.owl__transp_tag);
                let owl_from5 = arc_new(parseval.owl__transp_receiver);
                let owl_ctr4 = arc_new(parseval.owl__transp_counter);
                let owl_pkt3 = arc_new(parseval.owl__transp_packet);
                {
                    let temp_owl__x32 = { owl_transp_keys_val30639 };
                    let owl__x32 = temp_owl__x32;
                    let parseval = owl__x32;
                    let owl__12 = arc_new(parseval.owl__transp_keys_initiator);
                    let owl_responder_name11 = arc_new(parseval.owl__transp_keys_responder);
                    let owl__10 = arc_new(parseval.owl__transp_keys_init_ephemeral);
                    let owl_eph_resp9 = arc_new(parseval.owl__transp_keys_resp_ephemeral);
                    let owl__8 = arc_new(parseval.owl__transp_keys_T_init_send);
                    let owl_r2i_7 = arc_new(parseval.owl__transp_keys_T_resp_send);
                    {
                        let temp_owl__x28 = { arc_clone(&owl_c30638) };
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
        owl_transp_keys_val28826: owl_transp_keys,
        owl_plaintext28825: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_send_init_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val28826.dview(),
                owl_plaintext28825.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let temp_owl__x114 = { owl_transp_keys_val28826 };
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
                    let temp_owl__x66 = { arc_clone(&owl_plaintext28825) };
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
    
    #[verifier::spinoff_prover]
    pub fn owl_receive_msg2(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_msg1_val25135: owl_initiator_msg1_val,
        owl_dhpk_S_resp25134: Arc<Vec<u8>>,
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
                owl_msg1_val25135.dview(),
                owl_dhpk_S_resp25134.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (option_as_seq(dview_option(res.get_Ok_0().0)), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let (temp_owl_inp122, owl__121) = owl_input::<(Option<Seq<u8>>, state_Initiator)>(
                Tracked(&mut itree),
            );
            let owl_inp122 = arc_new(temp_owl_inp122);
            let temp_owl__x406 = { arc_clone(&owl_inp122) };
            let owl__x406 = arc_clone(&temp_owl__x406);
            if let Some(parseval) = parse_owl_msg2(vec_as_slice(&(*arc_clone(&owl__x406)))) {
                let owl_msg2_tag129 = arc_new(parseval.owl__msg2_tag);
                let owl_msg2_sender128 = arc_new(parseval.owl__msg2_sender);
                let owl_msg2_receiver127 = arc_new(parseval.owl__msg2_receiver);
                let owl_msg2_ephemeral_126 = arc_new(parseval.owl__msg2_ephemeral);
                let owl_msg2_empty125 = arc_new(parseval.owl__msg2_empty);
                let owl_msg2_mac2124 = arc_new(parseval.owl__msg2_mac1);
                {
                    let temp_owl__x405 = { owl_msg1_val25135 };
                    let owl__x405 = temp_owl__x405;
                    let parseval = owl__x405;
                    let owl_C3131 = arc_new(parseval.owl__initiator_msg1_C3);
                    let owl_H4130 = arc_new(parseval.owl__initiator_msg1_H4);
                    {
                        let temp_owl__x391 = { arc_clone(&owl_msg2_sender128) };
                        let owl__x391 = arc_clone(&temp_owl__x391);
                        let temp_owl__x392 = { vec_length(&(*arc_clone(&owl__x391))) };
                        let owl__x392 = temp_owl__x392;
                        let temp_owl__x394 = { 4 };
                        let owl__x394 = temp_owl__x394;
                        let temp_owl__x395 = { owl__x392 == owl__x394 };
                        let owl__x395 = temp_owl__x395;
                        let temp_owl__x399 = { arc_clone(&owl_msg2_receiver127) };
                        let owl__x399 = arc_clone(&temp_owl__x399);
                        let temp_owl__x400 = { vec_length(&(*arc_clone(&owl__x399))) };
                        let owl__x400 = temp_owl__x400;
                        let temp_owl__x402 = { 4 };
                        let owl__x402 = temp_owl__x402;
                        let temp_owl__x403 = { owl__x400 == owl__x402 };
                        let owl__x403 = temp_owl__x403;
                        let temp_owl__x404 = { owl__x395 && owl__x403 };
                        let owl__x404 = temp_owl__x404;
                        if owl__x404 {
                            let temp_owl__x378 = { arc_clone(&owl_msg2_ephemeral_126) };
                            let owl__x378 = arc_clone(&temp_owl__x378);
                            let temp_owl__x379 = {
                            owl_is_group_elem(vec_as_slice(&(*arc_clone(&owl__x378))))
                            };
                            let owl__x379 = temp_owl__x379;
                            if owl__x379 {
                                let temp_owl__x135 = {
                                    {
                                        let x: Vec<u8> =
                                            mk_vec_u8![0x00u8, 0x00u8, 0x00u8, 0x00u8, ];
                                        x
                                    }
                                };
                                let owl__x135 = arc_new(temp_owl__x135);
                                let temp_owl__x136 = { arc_clone(&owl__x135) };
                                let owl__x136 = arc_clone(&temp_owl__x136);
                                let temp_owl__x141 = { arc_clone(&owl_msg2_ephemeral_126) };
                                let owl__x141 = arc_clone(&temp_owl__x141);
                                let temp_owl__x142 = { arc_clone(&owl__x141) };
                                let owl__x142 = arc_clone(&temp_owl__x142);
                                let temp_owl__x146 = { arc_clone(&self.owl_E_init) };
                                let owl__x146 = arc_clone(&temp_owl__x146);
                                let temp_owl__x147 = { arc_clone(&owl__x146) };
                                let owl__x147 = arc_clone(&temp_owl__x147);
                                let temp_owl__x154 = { arc_clone(&owl__x147) };
                                let owl__x154 = arc_clone(&temp_owl__x154);
                                let temp_owl__x156 = {
                                owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x154))))
                                };
                                let owl__x156 = arc_clone(&temp_owl__x156);
                                let temp_owl__x157 = { arc_clone(&owl__x156) };
                                let owl__x157 = arc_clone(&temp_owl__x157);
                                let temp_owl__x162 = { arc_clone(&owl_C3131) };
                                let owl__x162 = arc_clone(&temp_owl__x162);
                                let temp_owl__x164 = { arc_clone(&owl__x142) };
                                let owl__x164 = arc_clone(&temp_owl__x164);
                                let owl_msg2_C4409 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x162))),
                                    vec_as_slice(&(*arc_clone(&owl__x164))),
                                );
                                let temp_owl__x165 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C4409),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x165 = arc_clone(&temp_owl__x165);
                                let temp_owl__x178 = { arc_clone(&owl_H4130) };
                                let owl__x178 = arc_clone(&temp_owl__x178);
                                let temp_owl__x180 = { arc_clone(&owl__x142) };
                                let owl__x180 = arc_clone(&temp_owl__x180);
                                let temp_owl__x182 = {
                                owl_concat(
                                    vec_as_slice(&(*arc_clone(&owl__x178))),
                                    vec_as_slice(&(*arc_clone(&owl__x180))),
                                )
                                };
                                let owl__x182 = arc_new(temp_owl__x182);
                                let temp_owl__x184 = {
                                owl_crh(vec_as_slice(&(*arc_clone(&owl__x182))))
                                };
                                let owl__x184 = arc_clone(&temp_owl__x184);
                                let temp_owl__x185 = { arc_clone(&owl__x184) };
                                let owl__x185 = arc_clone(&temp_owl__x185);
                                let temp_owl__x195 = { arc_clone(&owl__x142) };
                                let owl__x195 = arc_clone(&temp_owl__x195);
                                let temp_owl__x197 = { arc_clone(&owl__x147) };
                                let owl__x197 = arc_clone(&temp_owl__x197);
                                let temp_owl__x199 = {
                                owl_dh_combine(
                                    vec_as_slice(&(*arc_clone(&owl__x195))),
                                    vec_as_slice(&(*arc_clone(&owl__x197))),
                                )
                                };
                                let owl__x199 = arc_clone(&temp_owl__x199);
                                let temp_owl__x200 = { arc_clone(&owl__x199) };
                                let owl__x200 = arc_clone(&temp_owl__x200);
                                let temp_owl__x205 = { arc_clone(&owl__x165) };
                                let owl__x205 = arc_clone(&temp_owl__x205);
                                let temp_owl__x207 = { arc_clone(&owl__x200) };
                                let owl__x207 = arc_clone(&temp_owl__x207);
                                let owl_msg2_C5410 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x205))),
                                    vec_as_slice(&(*arc_clone(&owl__x207))),
                                );
                                let temp_owl__x208 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C5410),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x208 = arc_clone(&temp_owl__x208);
                                let temp_owl__x215 = { arc_clone(&owl__x208) };
                                let owl__x215 = arc_clone(&temp_owl__x215);
                                let temp_owl__x218 = { arc_clone(&owl__x142) };
                                let owl__x218 = arc_clone(&temp_owl__x218);
                                let temp_owl__x220 = { arc_clone(&self.owl_S_init) };
                                let owl__x220 = arc_clone(&temp_owl__x220);
                                let temp_owl__x221 = {
                                owl_dh_combine(
                                    vec_as_slice(&(*arc_clone(&owl__x218))),
                                    vec_as_slice(&(*arc_clone(&owl__x220))),
                                )
                                };
                                let owl__x221 = arc_clone(&temp_owl__x221);
                                let owl_msg2_C6411 = owl_extract_expand_to_len(
                                    0 + nonce_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x215))),
                                    vec_as_slice(&(*arc_clone(&owl__x221))),
                                );
                                let temp_owl__x222 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C6411),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x222 = arc_clone(&temp_owl__x222);
                                let temp_owl__x227 = { arc_clone(&owl__x222) };
                                let owl__x227 = arc_clone(&temp_owl__x227);
                                let temp_owl__x229 = { arc_clone(&owl__x136) };
                                let owl__x229 = arc_clone(&temp_owl__x229);
                                let owl_msg2_C7412 = owl_extract_expand_to_len(
                                    0 + nonce_size() + nonce_size() + key_size(),
                                    vec_as_slice(&(*arc_clone(&owl__x227))),
                                    vec_as_slice(&(*arc_clone(&owl__x229))),
                                );
                                let temp_owl__x230 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7412),
                                            0,
                                            0 + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x230 = arc_clone(&temp_owl__x230);
                                let temp_owl__x235 = { arc_clone(&owl__x222) };
                                let owl__x235 = arc_clone(&temp_owl__x235);
                                let temp_owl__x237 = { arc_clone(&owl__x136) };
                                let owl__x237 = arc_clone(&temp_owl__x237);
                                let temp_owl__x238 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7412),
                                            0 + nonce_size(),
                                            0 + nonce_size() + nonce_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x238 = arc_clone(&temp_owl__x238);
                                let temp_owl__x243 = { arc_clone(&owl__x222) };
                                let owl__x243 = arc_clone(&temp_owl__x243);
                                let temp_owl__x245 = { arc_clone(&owl__x136) };
                                let owl__x245 = arc_clone(&temp_owl__x245);
                                let temp_owl__x246 = {
                                arc_new(
                                    slice_to_vec(
                                        slice_subrange(
                                            vec_as_slice(&*owl_msg2_C7412),
                                            0 + nonce_size() + nonce_size(),
                                            0 + nonce_size() + nonce_size() + key_size(),
                                        ),
                                    ),
                                )
                                };
                                let owl__x246 = arc_clone(&temp_owl__x246);
                                let temp_owl__x259 = { arc_clone(&owl__x185) };
                                let owl__x259 = arc_clone(&temp_owl__x259);
                                let temp_owl__x261 = { arc_clone(&owl__x238) };
                                let owl__x261 = arc_clone(&temp_owl__x261);
                                let temp_owl__x263 = {
                                owl_concat(
                                    vec_as_slice(&(*arc_clone(&owl__x259))),
                                    vec_as_slice(&(*arc_clone(&owl__x261))),
                                )
                                };
                                let owl__x263 = arc_new(temp_owl__x263);
                                let temp_owl__x265 = {
                                owl_crh(vec_as_slice(&(*arc_clone(&owl__x263))))
                                };
                                let owl__x265 = arc_clone(&temp_owl__x265);
                                let temp_owl__x266 = { arc_clone(&owl__x265) };
                                let owl__x266 = arc_clone(&temp_owl__x266);
                                let temp_owl__x270 = {
                                    {
                                        let x: Vec<u8> = mk_vec_u8![];
                                        x
                                    }
                                };
                                let owl__x270 = arc_new(temp_owl__x270);
                                let temp_owl__x271 = { arc_clone(&owl__x270) };
                                let owl__x271 = arc_clone(&temp_owl__x271);
                                let temp_owl__x368 = { arc_clone(&owl__x246) };
                                let owl__x368 = arc_clone(&temp_owl__x368);
                                let temp_owl__x370 = { arc_clone(&owl_msg2_empty125) };
                                let owl__x370 = arc_clone(&temp_owl__x370);
                                let temp_owl__x372 = {
                                    {
                                        let x: Vec<u8> = mk_vec_u8![];
                                        x
                                    }
                                };
                                let owl__x372 = arc_new(temp_owl__x372);
                                let temp_owl__x374 = { arc_clone(&owl__x266) };
                                let owl__x374 = arc_clone(&temp_owl__x374);
                                let temp_owl__x375 = {
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x368))),
                                    vec_as_slice(&(*arc_clone(&owl__x370))),
                                    vec_as_slice(&(*arc_clone(&owl__x374))),
                                    vec_as_slice(&(*arc_clone(&owl__x372))),
                                )
                                };
                                let owl__x375 = temp_owl__x375;
                                let temp_owl_caseval408 = { owl__x375 };
                                let owl_caseval408 = temp_owl_caseval408;
                                match owl_caseval408 {
                                    None => {
                                        let temp_owl__x276 = { None };
                                        let owl__x276 = temp_owl__x276;
                                        (owl__x276, Tracked(itree))
                                    },
                                    Some(temp_owl_msg2_empty_dec277) => {
                                        let owl_msg2_empty_dec277 = arc_clone(
                                            &temp_owl_msg2_empty_dec277,
                                        );
                                        let temp_owl__x363 = { arc_clone(&owl_msg2_empty_dec277) };
                                        let owl__x363 = arc_clone(&temp_owl__x363);
                                        let temp_owl__x365 = { arc_clone(&owl__x271) };
                                        let owl__x365 = arc_clone(&temp_owl__x365);
                                        let temp_owl__x366 = {
                                        rc_vec_eq(&arc_clone(&owl__x363), &arc_clone(&owl__x365))
                                        };
                                        let owl__x366 = temp_owl__x366;
                                        if owl__x366 {
                                            let temp_owl__x290 = { arc_clone(&owl__x266) };
                                            let owl__x290 = arc_clone(&temp_owl__x290);
                                            let temp_owl__x292 = { arc_clone(&owl_msg2_empty125) };
                                            let owl__x292 = arc_clone(&temp_owl__x292);
                                            let temp_owl__x294 = {
                                            owl_concat(
                                                vec_as_slice(&(*arc_clone(&owl__x290))),
                                                vec_as_slice(&(*arc_clone(&owl__x292))),
                                            )
                                            };
                                            let owl__x294 = arc_new(temp_owl__x294);
                                            let temp_owl__x296 = {
                                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x294))))
                                            };
                                            let owl__x296 = arc_clone(&temp_owl__x296);
                                            let temp_owl__x297 = { arc_clone(&owl__x296) };
                                            let owl__x297 = arc_clone(&temp_owl__x297);
                                            let temp_owl__x302 = { arc_clone(&owl__x230) };
                                            let owl__x302 = arc_clone(&temp_owl__x302);
                                            let temp_owl__x304 = {
                                                {
                                                    let x: Vec<u8> = mk_vec_u8![];
                                                    x
                                                }
                                            };
                                            let owl__x304 = arc_new(temp_owl__x304);
                                            let owl_transp_T413 = owl_extract_expand_to_len(
                                                0 + key_size() + key_size(),
                                                vec_as_slice(&(*arc_clone(&owl__x302))),
                                                vec_as_slice(&(*arc_clone(&owl__x304))),
                                            );
                                            let temp_owl__x305 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_transp_T413),
                                                        0,
                                                        0 + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x305 = arc_clone(&temp_owl__x305);
                                            let temp_owl__x310 = { arc_clone(&owl__x230) };
                                            let owl__x310 = arc_clone(&temp_owl__x310);
                                            let temp_owl__x312 = {
                                                {
                                                    let x: Vec<u8> = mk_vec_u8![];
                                                    x
                                                }
                                            };
                                            let owl__x312 = arc_new(temp_owl__x312);
                                            let temp_owl__x313 = {
                                            arc_new(
                                                slice_to_vec(
                                                    slice_subrange(
                                                        vec_as_slice(&*owl_transp_T413),
                                                        0 + key_size(),
                                                        0 + key_size() + key_size(),
                                                    ),
                                                ),
                                            )
                                            };
                                            let owl__x313 = arc_clone(&temp_owl__x313);
                                            let temp_owl__x338 = { arc_clone(&owl_msg2_receiver127)
                                            };
                                            let owl__x338 = arc_clone(&temp_owl__x338);
                                            let temp_owl__x340 = { arc_clone(&owl_msg2_sender128) };
                                            let owl__x340 = arc_clone(&temp_owl__x340);
                                            let temp_owl__x342 = { arc_clone(&owl__x147) };
                                            let owl__x342 = arc_clone(&temp_owl__x342);
                                            let temp_owl__x344 = {
                                            owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x342))))
                                            };
                                            let owl__x344 = arc_clone(&temp_owl__x344);
                                            let temp_owl__x346 = { arc_clone(&owl__x142) };
                                            let owl__x346 = arc_clone(&temp_owl__x346);
                                            let temp_owl__x348 = { arc_clone(&owl__x305) };
                                            let owl__x348 = arc_clone(&temp_owl__x348);
                                            let temp_owl__x350 = { arc_clone(&owl__x313) };
                                            let owl__x350 = arc_clone(&temp_owl__x350);
                                            let temp_owl__x352 = {
                                            owl_transp_keys {
                                                owl__transp_keys_initiator: clone_vec_u8(
                                                    &*arc_clone(&owl__x338),
                                                ),
                                                owl__transp_keys_responder: clone_vec_u8(
                                                    &*arc_clone(&owl__x340),
                                                ),
                                                owl__transp_keys_init_ephemeral: clone_vec_u8(
                                                    &*arc_clone(&owl__x344),
                                                ),
                                                owl__transp_keys_resp_ephemeral: clone_vec_u8(
                                                    &*arc_clone(&owl__x346),
                                                ),
                                                owl__transp_keys_T_init_send: clone_vec_u8(
                                                    &*arc_clone(&owl__x348),
                                                ),
                                                owl__transp_keys_T_resp_send: clone_vec_u8(
                                                    &*arc_clone(&owl__x350),
                                                ),
                                            }
                                            };
                                            let owl__x352 = temp_owl__x352;
                                            let temp_owl__x353 = { owl__x352 };
                                            let owl__x353 = temp_owl__x353;
                                            let temp_owl__x358 = { owl__x353 };
                                            let owl__x358 = temp_owl__x358;
                                            let temp_owl__x359 = { Some(owl__x358) };
                                            let owl__x359 = temp_owl__x359;
                                            (owl__x359, Tracked(itree))
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
    
    pub exec fn owl_generate_msg1_wrapper(&self, s: &mut state_Initiator, dhpk_S_resp: Arc<Vec<u8>>) -> (_: owl_initiator_msg1_val) {
        let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<
            (),
            Endpoint,
        >::dummy_itree_token();
        let tracked (Tracked(call_token), _) = split_bind(
            dummy_tok,
            generate_msg1_spec_spec(*self, *s, dhpk_S_resp.dview()),
        );
        let (res, _): (owl_initiator_msg1_val, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>) =
            self.owl_generate_msg1(Tracked(call_token), s, dhpk_S_resp).unwrap();
        res
    }
    

    #[verifier::spinoff_prover]
    pub fn owl_generate_msg1(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
        mut_state: &mut state_Initiator,
        owl_dhpk_S_resp25125: Arc<Vec<u8>>,
    ) -> (res: Result<
        (owl_initiator_msg1_val, Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == generate_msg1_spec(
                *self,
                *old(mut_state),
                owl_dhpk_S_resp25125.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview().as_seq(), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let temp_owl__x421 = { owl_construction() };
            let owl__x421 = arc_new(temp_owl__x421);
            let temp_owl__x423 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x421)))) };
            let owl__x423 = arc_clone(&temp_owl__x423);
            let temp_owl__x424 = { arc_clone(&owl__x423) };
            let owl__x424 = arc_clone(&temp_owl__x424);
            let temp_owl__x437 = { arc_clone(&owl__x424) };
            let owl__x437 = arc_clone(&temp_owl__x437);
            let temp_owl__x439 = { owl_identifier() };
            let owl__x439 = arc_new(temp_owl__x439);
            let temp_owl__x441 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x437))),
                vec_as_slice(&(*arc_clone(&owl__x439))),
            )
            };
            let owl__x441 = arc_new(temp_owl__x441);
            let temp_owl__x443 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x441)))) };
            let owl__x443 = arc_clone(&temp_owl__x443);
            let temp_owl__x444 = { arc_clone(&owl__x443) };
            let owl__x444 = arc_clone(&temp_owl__x444);
            let temp_owl__x457 = { arc_clone(&owl__x444) };
            let owl__x457 = arc_clone(&temp_owl__x457);
            let temp_owl__x459 = { arc_clone(&owl_dhpk_S_resp25125) };
            let owl__x459 = arc_clone(&temp_owl__x459);
            let temp_owl__x461 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x457))),
                vec_as_slice(&(*arc_clone(&owl__x459))),
            )
            };
            let owl__x461 = arc_new(temp_owl__x461);
            let temp_owl__x463 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x461)))) };
            let owl__x463 = arc_clone(&temp_owl__x463);
            let temp_owl__x464 = { arc_clone(&owl__x463) };
            let owl__x464 = arc_clone(&temp_owl__x464);
            let temp_owl__x471 = { arc_clone(&self.owl_E_init) };
            let owl__x471 = arc_clone(&temp_owl__x471);
            let temp_owl__x473 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x471)))) };
            let owl__x473 = arc_clone(&temp_owl__x473);
            let temp_owl__x474 = { arc_clone(&owl__x473) };
            let owl__x474 = arc_clone(&temp_owl__x474);
            let temp_owl__x479 = { arc_clone(&owl__x424) };
            let owl__x479 = arc_clone(&temp_owl__x479);
            let temp_owl__x481 = { arc_clone(&owl__x474) };
            let owl__x481 = arc_clone(&temp_owl__x481);
            let owl_msg1_C1738 = owl_extract_expand_to_len(
                0 + nonce_size(),
                vec_as_slice(&(*arc_clone(&owl__x479))),
                vec_as_slice(&(*arc_clone(&owl__x481))),
            );
            let temp_owl__x482 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C1738), 0, 0 + nonce_size())),
            )
            };
            let owl__x482 = arc_clone(&temp_owl__x482);
            let temp_owl__x495 = { arc_clone(&owl__x464) };
            let owl__x495 = arc_clone(&temp_owl__x495);
            let temp_owl__x497 = { arc_clone(&owl__x474) };
            let owl__x497 = arc_clone(&temp_owl__x497);
            let temp_owl__x499 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x495))),
                vec_as_slice(&(*arc_clone(&owl__x497))),
            )
            };
            let owl__x499 = arc_new(temp_owl__x499);
            let temp_owl__x501 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x499)))) };
            let owl__x501 = arc_clone(&temp_owl__x501);
            let temp_owl__x502 = { arc_clone(&owl__x501) };
            let owl__x502 = arc_clone(&temp_owl__x502);
            let temp_owl__x512 = { arc_clone(&owl_dhpk_S_resp25125) };
            let owl__x512 = arc_clone(&temp_owl__x512);
            let temp_owl__x514 = { arc_clone(&self.owl_E_init) };
            let owl__x514 = arc_clone(&temp_owl__x514);
            let temp_owl__x516 = {
            owl_dh_combine(
                vec_as_slice(&(*arc_clone(&owl__x512))),
                vec_as_slice(&(*arc_clone(&owl__x514))),
            )
            };
            let owl__x516 = arc_clone(&temp_owl__x516);
            let temp_owl__x517 = { arc_clone(&owl__x516) };
            let owl__x517 = arc_clone(&temp_owl__x517);
            let temp_owl__x522 = { arc_clone(&owl__x482) };
            let owl__x522 = arc_clone(&temp_owl__x522);
            let temp_owl__x524 = { arc_clone(&owl__x517) };
            let owl__x524 = arc_clone(&temp_owl__x524);
            let owl_msg1_C2739 = owl_extract_expand_to_len(
                0 + nonce_size() + key_size(),
                vec_as_slice(&(*arc_clone(&owl__x522))),
                vec_as_slice(&(*arc_clone(&owl__x524))),
            );
            let temp_owl__x525 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C2739), 0, 0 + nonce_size())),
            )
            };
            let owl__x525 = arc_clone(&temp_owl__x525);
            let temp_owl__x530 = { arc_clone(&owl__x482) };
            let owl__x530 = arc_clone(&temp_owl__x530);
            let temp_owl__x532 = { arc_clone(&owl__x517) };
            let owl__x532 = arc_clone(&temp_owl__x532);
            let temp_owl__x533 = {
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
            let owl__x533 = arc_clone(&temp_owl__x533);
            let temp_owl__x541 = { arc_clone(&owl__x533) };
            let owl__x541 = arc_clone(&temp_owl__x541);
            let temp_owl__x545 = { arc_clone(&self.owl_S_init) };
            let owl__x545 = arc_clone(&temp_owl__x545);
            let temp_owl__x546 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x545)))) };
            let owl__x546 = arc_clone(&temp_owl__x546);
            let temp_owl__x547 = { arc_clone(&owl__x546) };
            let owl__x547 = arc_clone(&temp_owl__x547);
            let temp_owl__x549 = { arc_clone(&owl__x502) };
            let owl__x549 = arc_clone(&temp_owl__x549);
            let temp_owl__x550 = {
                match owl_enc_st_aead(
                    vec_as_slice(&(*arc_clone(&owl__x541))),
                    vec_as_slice(&(*arc_clone(&owl__x547))),
                    &mut mut_state.owl_aead_counter_msg1_C2,
                    vec_as_slice(&(*arc_clone(&owl__x549))),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x550 = arc_clone(&temp_owl__x550);
            let temp_owl__x563 = { arc_clone(&owl__x502) };
            let owl__x563 = arc_clone(&temp_owl__x563);
            let temp_owl__x565 = { arc_clone(&owl__x550) };
            let owl__x565 = arc_clone(&temp_owl__x565);
            let temp_owl__x567 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x563))),
                vec_as_slice(&(*arc_clone(&owl__x565))),
            )
            };
            let owl__x567 = arc_new(temp_owl__x567);
            let temp_owl__x569 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x567)))) };
            let owl__x569 = arc_clone(&temp_owl__x569);
            let temp_owl__x570 = { arc_clone(&owl__x569) };
            let owl__x570 = arc_clone(&temp_owl__x570);
            let temp_owl__x580 = { arc_clone(&owl_dhpk_S_resp25125) };
            let owl__x580 = arc_clone(&temp_owl__x580);
            let temp_owl__x582 = { arc_clone(&self.owl_S_init) };
            let owl__x582 = arc_clone(&temp_owl__x582);
            let temp_owl__x584 = {
            owl_dh_combine(
                vec_as_slice(&(*arc_clone(&owl__x580))),
                vec_as_slice(&(*arc_clone(&owl__x582))),
            )
            };
            let owl__x584 = arc_clone(&temp_owl__x584);
            let temp_owl__x585 = { arc_clone(&owl__x584) };
            let owl__x585 = arc_clone(&temp_owl__x585);
            let temp_owl__x590 = { arc_clone(&owl__x525) };
            let owl__x590 = arc_clone(&temp_owl__x590);
            let temp_owl__x592 = { arc_clone(&owl__x585) };
            let owl__x592 = arc_clone(&temp_owl__x592);
            let owl_msg1_C3740 = owl_extract_expand_to_len(
                0 + nonce_size() + key_size(),
                vec_as_slice(&(*arc_clone(&owl__x590))),
                vec_as_slice(&(*arc_clone(&owl__x592))),
            );
            let temp_owl__x593 = {
            arc_new(
                slice_to_vec(slice_subrange(vec_as_slice(&*owl_msg1_C3740), 0, 0 + nonce_size())),
            )
            };
            let owl__x593 = arc_clone(&temp_owl__x593);
            let temp_owl__x598 = { arc_clone(&owl__x525) };
            let owl__x598 = arc_clone(&temp_owl__x598);
            let temp_owl__x600 = { arc_clone(&owl__x585) };
            let owl__x600 = arc_clone(&temp_owl__x600);
            let temp_owl__x601 = {
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
            let owl__x601 = arc_clone(&temp_owl__x601);
            let (temp_owl__x603, Tracked(itree)): (
                _,
                Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
            ) = {
                owl_call!( itree
, *mut_state
, timestamp_i_spec(*self, *mut_state)
, self.owl_timestamp_i(mut_state) )
            };
            let owl__x603 = arc_clone(&temp_owl__x603);
            let temp_owl__x609 = { arc_clone(&owl__x601) };
            let owl__x609 = arc_clone(&temp_owl__x609);
            let temp_owl__x611 = { arc_clone(&owl__x603) };
            let owl__x611 = arc_clone(&temp_owl__x611);
            let temp_owl__x613 = { arc_clone(&owl__x570) };
            let owl__x613 = arc_clone(&temp_owl__x613);
            let temp_owl__x614 = {
                match owl_enc_st_aead(
                    vec_as_slice(&(*arc_clone(&owl__x609))),
                    vec_as_slice(&(*arc_clone(&owl__x611))),
                    &mut mut_state.owl_aead_counter_msg1_C3,
                    vec_as_slice(&(*arc_clone(&owl__x613))),
                ) {
                    Ok(ctxt) => ctxt,
                    Err(e) => { return Err(e) },
                }
            };
            let owl__x614 = arc_clone(&temp_owl__x614);
            let temp_owl__x627 = { arc_clone(&owl__x570) };
            let owl__x627 = arc_clone(&temp_owl__x627);
            let temp_owl__x629 = { arc_clone(&owl__x603) };
            let owl__x629 = arc_clone(&temp_owl__x629);
            let temp_owl__x631 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x627))),
                vec_as_slice(&(*arc_clone(&owl__x629))),
            )
            };
            let owl__x631 = arc_new(temp_owl__x631);
            let temp_owl__x633 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x631)))) };
            let owl__x633 = arc_clone(&temp_owl__x633);
            let temp_owl__x634 = { arc_clone(&owl__x633) };
            let owl__x634 = arc_clone(&temp_owl__x634);
            let (temp_owl__x636, Tracked(itree)): (
                _,
                Tracked<ITreeToken<(Seq<u8>, state_Initiator), Endpoint>>,
            ) = {
                owl_call!( itree
, *mut_state
, get_sender_i_spec(*self, *mut_state)
, self.owl_get_sender_i(mut_state) )
            };
            let owl__x636 = arc_clone(&temp_owl__x636);
            let temp_owl__x640 = { owl_msg1_tag_value() };
            let owl__x640 = arc_new(temp_owl__x640);
            let temp_owl__x641 = { arc_clone(&owl__x640) };
            let owl__x641 = arc_clone(&temp_owl__x641);
            let temp_owl__x646 = { owl_mac1() };
            let owl__x646 = arc_new(temp_owl__x646);
            let temp_owl__x648 = { arc_clone(&owl_dhpk_S_resp25125) };
            let owl__x648 = arc_clone(&temp_owl__x648);
            let owl_msg1_mac1_key741 = owl_extract_expand_to_len(
                0 + mackey_size(),
                vec_as_slice(&(*arc_clone(&owl__x646))),
                vec_as_slice(&(*arc_clone(&owl__x648))),
            );
            let temp_owl__x649 = {
            arc_new(
                slice_to_vec(
                    slice_subrange(vec_as_slice(&*owl_msg1_mac1_key741), 0, 0 + mackey_size()),
                ),
            )
            };
            let owl__x649 = arc_clone(&temp_owl__x649);
            let temp_owl__x662 = { arc_clone(&owl__x649) };
            let owl__x662 = arc_clone(&temp_owl__x662);
            let temp_owl__x668 = { arc_clone(&owl__x641) };
            let owl__x668 = arc_clone(&temp_owl__x668);
            let temp_owl__x670 = { arc_clone(&owl__x636) };
            let owl__x670 = arc_clone(&temp_owl__x670);
            let temp_owl__x671 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x668))),
                vec_as_slice(&(*arc_clone(&owl__x670))),
            )
            };
            let owl__x671 = arc_new(temp_owl__x671);
            let temp_owl__x673 = { arc_clone(&owl__x474) };
            let owl__x673 = arc_clone(&temp_owl__x673);
            let temp_owl__x674 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x671))),
                vec_as_slice(&(*arc_clone(&owl__x673))),
            )
            };
            let owl__x674 = arc_new(temp_owl__x674);
            let temp_owl__x676 = { arc_clone(&owl__x550) };
            let owl__x676 = arc_clone(&temp_owl__x676);
            let temp_owl__x677 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x674))),
                vec_as_slice(&(*arc_clone(&owl__x676))),
            )
            };
            let owl__x677 = arc_new(temp_owl__x677);
            let temp_owl__x679 = { arc_clone(&owl__x614) };
            let owl__x679 = arc_clone(&temp_owl__x679);
            let temp_owl__x680 = {
            owl_concat(
                vec_as_slice(&(*arc_clone(&owl__x677))),
                vec_as_slice(&(*arc_clone(&owl__x679))),
            )
            };
            let owl__x680 = arc_new(temp_owl__x680);
            let temp_owl__x681 = {
            owl_mac(
                vec_as_slice(&(*arc_clone(&owl__x662))),
                vec_as_slice(&(*arc_clone(&owl__x680))),
            )
            };
            let owl__x681 = arc_clone(&temp_owl__x681);
            let temp_owl__x703 = { arc_clone(&owl__x641) };
            let owl__x703 = arc_clone(&temp_owl__x703);
            let temp_owl__x705 = { arc_clone(&owl__x636) };
            let owl__x705 = arc_clone(&temp_owl__x705);
            let temp_owl__x707 = { arc_clone(&owl__x474) };
            let owl__x707 = arc_clone(&temp_owl__x707);
            let temp_owl__x709 = { arc_clone(&owl__x550) };
            let owl__x709 = arc_clone(&temp_owl__x709);
            let temp_owl__x711 = { arc_clone(&owl__x614) };
            let owl__x711 = arc_clone(&temp_owl__x711);
            let temp_owl__x713 = { arc_clone(&owl__x681) };
            let owl__x713 = arc_clone(&temp_owl__x713);
            let temp_owl__x715 = {
            owl_msg1 {
                owl__msg1_tag: clone_vec_u8(&*arc_clone(&owl__x703)),
                owl__msg1_sender: clone_vec_u8(&*arc_clone(&owl__x705)),
                owl__msg1_ephemeral: clone_vec_u8(&*arc_clone(&owl__x707)),
                owl__msg1_static: clone_vec_u8(&*arc_clone(&owl__x709)),
                owl__msg1_timestamp: clone_vec_u8(&*arc_clone(&owl__x711)),
                owl__msg1_mac1: clone_vec_u8(&*arc_clone(&owl__x713)),
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
            )
            };
            let owl__x721 = temp_owl__x721;
            let temp_owl__x731 = { arc_clone(&owl__x593) };
            let owl__x731 = arc_clone(&temp_owl__x731);
            let temp_owl__x733 = { arc_clone(&owl__x634) };
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
            (Arc::new(v.to_be_bytes().to_vec()), Tracked(itree))
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
        owl_transp_keys_val33858: owl_transp_keys,
        owl_c33857: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<Arc<Vec<u8>>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_recv_resp_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val33858.dview(),
                owl_c33857.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let temp_owl__x775 = { arc_clone(&owl_c33857) };
            let owl__x775 = arc_clone(&temp_owl__x775);
            if let Some(parseval) = parse_owl_transp(vec_as_slice(&(*arc_clone(&owl__x775)))) {
                let owl__748 = arc_new(parseval.owl__transp_tag);
                let owl_from747 = arc_new(parseval.owl__transp_receiver);
                let owl_ctr746 = arc_new(parseval.owl__transp_counter);
                let owl_pkt745 = arc_new(parseval.owl__transp_packet);
                {
                    let temp_owl__x774 = { owl_transp_keys_val33858 };
                    let owl__x774 = temp_owl__x774;
                    let parseval = owl__x774;
                    let owl_initiator_name754 = arc_new(parseval.owl__transp_keys_initiator);
                    let owl__753 = arc_new(parseval.owl__transp_keys_responder);
                    let owl_eph_init752 = arc_new(parseval.owl__transp_keys_init_ephemeral);
                    let owl__751 = arc_new(parseval.owl__transp_keys_resp_ephemeral);
                    let owl_i2r_750 = arc_new(parseval.owl__transp_keys_T_init_send);
                    let owl__749 = arc_new(parseval.owl__transp_keys_T_resp_send);
                    {
                        let temp_owl__x770 = { arc_clone(&owl_c33857) };
                        let owl__x770 = arc_clone(&temp_owl__x770);
                        let temp_owl__x772 = { arc_clone(&owl_initiator_name754) };
                        let owl__x772 = arc_clone(&temp_owl__x772);
                        let temp_owl__x773 = {
                        rc_vec_eq(&arc_clone(&owl__x770), &arc_clone(&owl__x772))
                        };
                        let owl__x773 = temp_owl__x773;
                        if owl__x773 {
                            let temp_owl__x759 = { arc_clone(&owl_i2r_750) };
                            let owl__x759 = arc_clone(&temp_owl__x759);
                            let temp_owl__x760 = { arc_clone(&owl__x759) };
                            let owl__x760 = arc_clone(&temp_owl__x760);
                            let temp_owl__x763 = { arc_clone(&owl__x760) };
                            let owl__x763 = arc_clone(&temp_owl__x763);
                            let temp_owl__x764 = { arc_clone(&owl_pkt745) };
                            let owl__x764 = arc_clone(&temp_owl__x764);
                            let temp_owl__x765 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x765 = arc_new(temp_owl__x765);
                            let temp_owl__x766 = { arc_clone(&owl_ctr746) };
                            let owl__x766 = arc_clone(&temp_owl__x766);
                            (
                                owl_dec_st_aead(
                                    vec_as_slice(&(*arc_clone(&owl__x763))),
                                    vec_as_slice(&(*arc_clone(&owl__x764))),
                                    vec_as_slice(&(*arc_clone(&owl__x766))),
                                    vec_as_slice(&(*arc_clone(&owl__x765))),
                                ),
                                Tracked(itree),
                            )
                        } else {
                            (None, Tracked(itree))
                        }
                    }
                }
            } else {
                let temp_owl__x744 = { None };
                let owl__x744 = temp_owl__x744;
                (owl__x744, Tracked(itree))
            }
        };
        Ok(res_inner)
    }
    
    #[verifier::spinoff_prover]
    pub fn owl_transp_send_resp(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
        owl_transp_keys_val32093: owl_transp_keys,
        owl_plaintext32092: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<()>, Tracked<ITreeToken<(Option<()>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == transp_send_resp_spec(
                *self,
                *old(mut_state),
                owl_transp_keys_val32093.dview(),
                owl_plaintext32092.dview(),
            ),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let temp_owl__x856 = { owl_transp_keys_val32093 };
            let owl__x856 = temp_owl__x856;
            let parseval = owl__x856;
            let owl_transp_receiver787 = arc_new(parseval.owl__transp_keys_initiator);
            let owl__786 = arc_new(parseval.owl__transp_keys_responder);
            let owl_eph_init785 = arc_new(parseval.owl__transp_keys_init_ephemeral);
            let owl__784 = arc_new(parseval.owl__transp_keys_resp_ephemeral);
            let owl__783 = arc_new(parseval.owl__transp_keys_T_init_send);
            let owl_r2i_782 = arc_new(parseval.owl__transp_keys_T_resp_send);
            {
                let temp_owl__x792 = { arc_clone(&owl_r2i_782) };
                let owl__x792 = arc_clone(&temp_owl__x792);
                let temp_owl__x793 = { arc_clone(&owl__x792) };
                let owl__x793 = arc_clone(&temp_owl__x793);
                let temp_owl__x795 = { owl_counter_as_bytes(&(mut_state.owl_N_resp_send)) };
                let owl__x795 = arc_new(temp_owl__x795);
                let temp_owl__x799 = { owl_transp_tag_value() };
                let owl__x799 = arc_new(temp_owl__x799);
                let temp_owl__x800 = { arc_clone(&owl__x799) };
                let owl__x800 = arc_clone(&temp_owl__x800);
                let temp_owl__x851 = { arc_clone(&owl_transp_receiver787) };
                let owl__x851 = arc_clone(&temp_owl__x851);
                let temp_owl__x852 = { vec_length(&(*arc_clone(&owl__x851))) };
                let owl__x852 = temp_owl__x852;
                let temp_owl__x854 = { 4 };
                let owl__x854 = temp_owl__x854;
                let temp_owl__x855 = { owl__x852 == owl__x854 };
                let owl__x855 = temp_owl__x855;
                if owl__x855 {
                    let temp_owl__x806 = { arc_clone(&owl__x793) };
                    let owl__x806 = arc_clone(&temp_owl__x806);
                    let temp_owl__x808 = { arc_clone(&owl_plaintext32092) };
                    let owl__x808 = arc_clone(&temp_owl__x808);
                    let temp_owl__x810 = {
                        {
                            let x: Vec<u8> = mk_vec_u8![];
                            x
                        }
                    };
                    let owl__x810 = arc_new(temp_owl__x810);
                    let temp_owl__x811 = {
                        match owl_enc_st_aead(
                            vec_as_slice(&(*arc_clone(&owl__x806))),
                            vec_as_slice(&(*arc_clone(&owl__x808))),
                            &mut mut_state.owl_N_resp_send,
                            vec_as_slice(&(*arc_clone(&owl__x810))),
                        ) {
                            Ok(ctxt) => ctxt,
                            Err(e) => { return Err(e) },
                        }
                    };
                    let owl__x811 = arc_clone(&temp_owl__x811);
                    let temp_owl__x827 = { arc_clone(&owl__x800) };
                    let owl__x827 = arc_clone(&temp_owl__x827);
                    let temp_owl__x829 = { arc_clone(&owl_transp_receiver787) };
                    let owl__x829 = arc_clone(&temp_owl__x829);
                    let temp_owl__x831 = { arc_clone(&owl__x795) };
                    let owl__x831 = arc_clone(&temp_owl__x831);
                    let temp_owl__x833 = { arc_clone(&owl__x811) };
                    let owl__x833 = arc_clone(&temp_owl__x833);
                    let temp_owl__x835 = {
                    owl_transp {
                        owl__transp_tag: clone_vec_u8(&*arc_clone(&owl__x827)),
                        owl__transp_receiver: clone_vec_u8(&*arc_clone(&owl__x829)),
                        owl__transp_counter: clone_vec_u8(&*arc_clone(&owl__x831)),
                        owl__transp_packet: clone_vec_u8(&*arc_clone(&owl__x833)),
                    }
                    };
                    let owl__x835 = temp_owl__x835;
                    let temp_owl__x836 = { owl__x835 };
                    let owl__x836 = temp_owl__x836;
                    let temp_owl__x840 = { owl__x836 };
                    let owl__x840 = temp_owl__x840;
                    let temp_owl__x841 = {
                    owl_output::<(Option<()>, state_Responder)>(
                        Tracked(&mut itree),
                        vec_as_slice(&(serialize_owl_transp(&owl__x840))),
                        &Initiator_addr(),
                        &Responder_addr(),
                    )
                    };
                    let owl__x841 = temp_owl__x841;
                    let temp_owl__x844 = { () };
                    let owl__x844 = temp_owl__x844;
                    let temp_owl__x845 = { Some(owl__x844) };
                    let owl__x845 = temp_owl__x845;
                    (owl__x845, Tracked(itree))
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
        owl_msg1_val_27620: owl_responder_msg1_val,
    ) -> (res: Result<
        (owl_transp_keys, Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == generate_msg2_spec(*self, *old(mut_state), owl_msg1_val_27620.dview()),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (res.get_Ok_0().0.dview().as_seq(), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            let temp_owl__x1180 = { owl_msg1_val_27620 };
            let owl__x1180 = temp_owl__x1180;
            let temp_owl__x1179 = { owl__x1180 };
            let owl__x1179 = temp_owl__x1179;
            let parseval = owl__x1179;
            let owl_C3870 = arc_new(parseval.owl__responder_msg1_C3);
            let owl_H4869 = arc_new(parseval.owl__responder_msg1_H4);
            let owl_ephemeral_868 = arc_new(parseval.owl__responder_msg1_ephemeral);
            let owl_dhpk_S_init867 = arc_new(parseval.owl__responder_msg1_sender_pk);
            let owl_msg2_receiver866 = arc_new(parseval.owl__responder_msg1_sender);
            {
                let temp_owl__x875 = { arc_clone(&owl_ephemeral_868) };
                let owl__x875 = arc_clone(&temp_owl__x875);
                let temp_owl__x876 = { arc_clone(&owl__x875) };
                let owl__x876 = arc_clone(&temp_owl__x876);
                let temp_owl__x883 = { arc_clone(&self.owl_E_resp) };
                let owl__x883 = arc_clone(&temp_owl__x883);
                let temp_owl__x885 = { owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x883)))) };
                let owl__x885 = arc_clone(&temp_owl__x885);
                let temp_owl__x886 = { arc_clone(&owl__x885) };
                let owl__x886 = arc_clone(&temp_owl__x886);
                let temp_owl__x890 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![0x00u8, 0x00u8, 0x00u8, 0x00u8, ];
                        x
                    }
                };
                let owl__x890 = arc_new(temp_owl__x890);
                let temp_owl__x891 = { arc_clone(&owl__x890) };
                let owl__x891 = arc_clone(&temp_owl__x891);
                let temp_owl__x896 = { arc_clone(&owl_C3870) };
                let owl__x896 = arc_clone(&temp_owl__x896);
                let temp_owl__x898 = { arc_clone(&owl__x886) };
                let owl__x898 = arc_clone(&temp_owl__x898);
                let owl_msg2_C41184 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x896))),
                    vec_as_slice(&(*arc_clone(&owl__x898))),
                );
                let temp_owl__x899 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C41184), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x899 = arc_clone(&temp_owl__x899);
                let temp_owl__x912 = { arc_clone(&owl_H4869) };
                let owl__x912 = arc_clone(&temp_owl__x912);
                let temp_owl__x914 = { arc_clone(&owl__x886) };
                let owl__x914 = arc_clone(&temp_owl__x914);
                let temp_owl__x916 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x912))),
                    vec_as_slice(&(*arc_clone(&owl__x914))),
                )
                };
                let owl__x916 = arc_new(temp_owl__x916);
                let temp_owl__x918 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x916)))) };
                let owl__x918 = arc_clone(&temp_owl__x918);
                let temp_owl__x919 = { arc_clone(&owl__x918) };
                let owl__x919 = arc_clone(&temp_owl__x919);
                let temp_owl__x929 = { arc_clone(&owl__x876) };
                let owl__x929 = arc_clone(&temp_owl__x929);
                let temp_owl__x931 = { arc_clone(&self.owl_E_resp) };
                let owl__x931 = arc_clone(&temp_owl__x931);
                let temp_owl__x933 = {
                owl_dh_combine(
                    vec_as_slice(&(*arc_clone(&owl__x929))),
                    vec_as_slice(&(*arc_clone(&owl__x931))),
                )
                };
                let owl__x933 = arc_clone(&temp_owl__x933);
                let temp_owl__x934 = { arc_clone(&owl__x933) };
                let owl__x934 = arc_clone(&temp_owl__x934);
                let temp_owl__x939 = { arc_clone(&owl__x899) };
                let owl__x939 = arc_clone(&temp_owl__x939);
                let temp_owl__x941 = { arc_clone(&owl__x934) };
                let owl__x941 = arc_clone(&temp_owl__x941);
                let owl_msg2_C51185 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x939))),
                    vec_as_slice(&(*arc_clone(&owl__x941))),
                );
                let temp_owl__x942 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C51185), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x942 = arc_clone(&temp_owl__x942);
                let temp_owl__x949 = { arc_clone(&owl__x942) };
                let owl__x949 = arc_clone(&temp_owl__x949);
                let temp_owl__x952 = { arc_clone(&owl_dhpk_S_init867) };
                let owl__x952 = arc_clone(&temp_owl__x952);
                let temp_owl__x954 = { arc_clone(&self.owl_E_resp) };
                let owl__x954 = arc_clone(&temp_owl__x954);
                let temp_owl__x955 = {
                owl_dh_combine(
                    vec_as_slice(&(*arc_clone(&owl__x952))),
                    vec_as_slice(&(*arc_clone(&owl__x954))),
                )
                };
                let owl__x955 = arc_clone(&temp_owl__x955);
                let owl_msg2_C61186 = owl_extract_expand_to_len(
                    0 + nonce_size(),
                    vec_as_slice(&(*arc_clone(&owl__x949))),
                    vec_as_slice(&(*arc_clone(&owl__x955))),
                );
                let temp_owl__x956 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C61186), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x956 = arc_clone(&temp_owl__x956);
                let temp_owl__x961 = { arc_clone(&owl__x956) };
                let owl__x961 = arc_clone(&temp_owl__x961);
                let temp_owl__x963 = { arc_clone(&owl__x891) };
                let owl__x963 = arc_clone(&temp_owl__x963);
                let owl_msg2_C71187 = owl_extract_expand_to_len(
                    0 + nonce_size() + nonce_size() + key_size(),
                    vec_as_slice(&(*arc_clone(&owl__x961))),
                    vec_as_slice(&(*arc_clone(&owl__x963))),
                );
                let temp_owl__x964 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_C71187), 0, 0 + nonce_size()),
                    ),
                )
                };
                let owl__x964 = arc_clone(&temp_owl__x964);
                let temp_owl__x969 = { arc_clone(&owl__x956) };
                let owl__x969 = arc_clone(&temp_owl__x969);
                let temp_owl__x971 = { arc_clone(&owl__x891) };
                let owl__x971 = arc_clone(&temp_owl__x971);
                let temp_owl__x972 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_msg2_C71187),
                            0 + nonce_size(),
                            0 + nonce_size() + nonce_size(),
                        ),
                    ),
                )
                };
                let owl__x972 = arc_clone(&temp_owl__x972);
                let temp_owl__x977 = { arc_clone(&owl__x956) };
                let owl__x977 = arc_clone(&temp_owl__x977);
                let temp_owl__x979 = { arc_clone(&owl__x891) };
                let owl__x979 = arc_clone(&temp_owl__x979);
                let temp_owl__x980 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_msg2_C71187),
                            0 + nonce_size() + nonce_size(),
                            0 + nonce_size() + nonce_size() + key_size(),
                        ),
                    ),
                )
                };
                let owl__x980 = arc_clone(&temp_owl__x980);
                let temp_owl__x993 = { arc_clone(&owl__x919) };
                let owl__x993 = arc_clone(&temp_owl__x993);
                let temp_owl__x995 = { arc_clone(&owl__x972) };
                let owl__x995 = arc_clone(&temp_owl__x995);
                let temp_owl__x997 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x993))),
                    vec_as_slice(&(*arc_clone(&owl__x995))),
                )
                };
                let owl__x997 = arc_new(temp_owl__x997);
                let temp_owl__x999 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x997)))) };
                let owl__x999 = arc_clone(&temp_owl__x999);
                let temp_owl__x1000 = { arc_clone(&owl__x999) };
                let owl__x1000 = arc_clone(&temp_owl__x1000);
                let temp_owl__x1004 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1004 = arc_new(temp_owl__x1004);
                let temp_owl__x1005 = { arc_clone(&owl__x1004) };
                let owl__x1005 = arc_clone(&temp_owl__x1005);
                let temp_owl__x1011 = { arc_clone(&owl__x980) };
                let owl__x1011 = arc_clone(&temp_owl__x1011);
                let temp_owl__x1013 = { arc_clone(&owl__x1005) };
                let owl__x1013 = arc_clone(&temp_owl__x1013);
                let temp_owl__x1015 = { arc_clone(&owl__x1000) };
                let owl__x1015 = arc_clone(&temp_owl__x1015);
                let temp_owl__x1016 = {
                    match owl_enc_st_aead(
                        vec_as_slice(&(*arc_clone(&owl__x1011))),
                        vec_as_slice(&(*arc_clone(&owl__x1013))),
                        &mut mut_state.owl_aead_counter_msg2_C7,
                        vec_as_slice(&(*arc_clone(&owl__x1015))),
                    ) {
                        Ok(ctxt) => ctxt,
                        Err(e) => { return Err(e) },
                    }
                };
                let owl__x1016 = arc_clone(&temp_owl__x1016);
                let temp_owl__x1029 = { arc_clone(&owl__x1000) };
                let owl__x1029 = arc_clone(&temp_owl__x1029);
                let temp_owl__x1031 = { arc_clone(&owl__x1016) };
                let owl__x1031 = arc_clone(&temp_owl__x1031);
                let temp_owl__x1033 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1029))),
                    vec_as_slice(&(*arc_clone(&owl__x1031))),
                )
                };
                let owl__x1033 = arc_new(temp_owl__x1033);
                let temp_owl__x1035 = { owl_crh(vec_as_slice(&(*arc_clone(&owl__x1033)))) };
                let owl__x1035 = arc_clone(&temp_owl__x1035);
                let temp_owl__x1036 = { arc_clone(&owl__x1035) };
                let owl__x1036 = arc_clone(&temp_owl__x1036);
                let (temp_owl__x1038, Tracked(itree)): (
                    _,
                    Tracked<ITreeToken<(Seq<u8>, state_Responder), Endpoint>>,
                ) = {
                    owl_call!( itree
, *mut_state
, get_sender_r_spec(*self, *mut_state)
, self.owl_get_sender_r(mut_state) )
                };
                let owl__x1038 = arc_clone(&temp_owl__x1038);
                let temp_owl__x1042 = { owl_msg2_tag_value() };
                let owl__x1042 = arc_new(temp_owl__x1042);
                let temp_owl__x1043 = { arc_clone(&owl__x1042) };
                let owl__x1043 = arc_clone(&temp_owl__x1043);
                let temp_owl__x1048 = { owl_mac1() };
                let owl__x1048 = arc_new(temp_owl__x1048);
                let temp_owl__x1050 = { arc_clone(&owl_dhpk_S_init867) };
                let owl__x1050 = arc_clone(&temp_owl__x1050);
                let owl_msg2_mac1_key1188 = owl_extract_expand_to_len(
                    0 + mackey_size(),
                    vec_as_slice(&(*arc_clone(&owl__x1048))),
                    vec_as_slice(&(*arc_clone(&owl__x1050))),
                );
                let temp_owl__x1051 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_msg2_mac1_key1188), 0, 0 + mackey_size()),
                    ),
                )
                };
                let owl__x1051 = arc_clone(&temp_owl__x1051);
                let temp_owl__x1064 = { arc_clone(&owl__x1051) };
                let owl__x1064 = arc_clone(&temp_owl__x1064);
                let temp_owl__x1070 = { arc_clone(&owl__x1043) };
                let owl__x1070 = arc_clone(&temp_owl__x1070);
                let temp_owl__x1072 = { arc_clone(&owl__x1038) };
                let owl__x1072 = arc_clone(&temp_owl__x1072);
                let temp_owl__x1073 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1070))),
                    vec_as_slice(&(*arc_clone(&owl__x1072))),
                )
                };
                let owl__x1073 = arc_new(temp_owl__x1073);
                let temp_owl__x1075 = { arc_clone(&owl_msg2_receiver866) };
                let owl__x1075 = arc_clone(&temp_owl__x1075);
                let temp_owl__x1076 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1073))),
                    vec_as_slice(&(*arc_clone(&owl__x1075))),
                )
                };
                let owl__x1076 = arc_new(temp_owl__x1076);
                let temp_owl__x1078 = { arc_clone(&owl__x886) };
                let owl__x1078 = arc_clone(&temp_owl__x1078);
                let temp_owl__x1079 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1076))),
                    vec_as_slice(&(*arc_clone(&owl__x1078))),
                )
                };
                let owl__x1079 = arc_new(temp_owl__x1079);
                let temp_owl__x1081 = { arc_clone(&owl__x1016) };
                let owl__x1081 = arc_clone(&temp_owl__x1081);
                let temp_owl__x1082 = {
                owl_concat(
                    vec_as_slice(&(*arc_clone(&owl__x1079))),
                    vec_as_slice(&(*arc_clone(&owl__x1081))),
                )
                };
                let owl__x1082 = arc_new(temp_owl__x1082);
                let temp_owl__x1083 = {
                owl_mac(
                    vec_as_slice(&(*arc_clone(&owl__x1064))),
                    vec_as_slice(&(*arc_clone(&owl__x1082))),
                )
                };
                let owl__x1083 = arc_clone(&temp_owl__x1083);
                let temp_owl__x1105 = { arc_clone(&owl__x1043) };
                let owl__x1105 = arc_clone(&temp_owl__x1105);
                let temp_owl__x1107 = { arc_clone(&owl__x1038) };
                let owl__x1107 = arc_clone(&temp_owl__x1107);
                let temp_owl__x1109 = { arc_clone(&owl_msg2_receiver866) };
                let owl__x1109 = arc_clone(&temp_owl__x1109);
                let temp_owl__x1111 = { arc_clone(&owl__x886) };
                let owl__x1111 = arc_clone(&temp_owl__x1111);
                let temp_owl__x1113 = { arc_clone(&owl__x1016) };
                let owl__x1113 = arc_clone(&temp_owl__x1113);
                let temp_owl__x1115 = { arc_clone(&owl__x1083) };
                let owl__x1115 = arc_clone(&temp_owl__x1115);
                let temp_owl__x1117 = {
                owl_msg2 {
                    owl__msg2_tag: clone_vec_u8(&*arc_clone(&owl__x1105)),
                    owl__msg2_sender: clone_vec_u8(&*arc_clone(&owl__x1107)),
                    owl__msg2_receiver: clone_vec_u8(&*arc_clone(&owl__x1109)),
                    owl__msg2_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1111)),
                    owl__msg2_empty: clone_vec_u8(&*arc_clone(&owl__x1113)),
                    owl__msg2_mac1: clone_vec_u8(&*arc_clone(&owl__x1115)),
                }
                };
                let owl__x1117 = temp_owl__x1117;
                let temp_owl__x1118 = { owl__x1117 };
                let owl__x1118 = temp_owl__x1118;
                let temp_owl__x1122 = { owl__x1118 };
                let owl__x1122 = temp_owl__x1122;
                let temp_owl__x1123 = {
                owl_output::<(Seq<u8>, state_Responder)>(
                    Tracked(&mut itree),
                    vec_as_slice(&(serialize_owl_msg2(&owl__x1122))),
                    &Initiator_addr(),
                    &Responder_addr(),
                )
                };
                let owl__x1123 = temp_owl__x1123;
                let temp_owl__x1128 = { arc_clone(&owl__x964) };
                let owl__x1128 = arc_clone(&temp_owl__x1128);
                let temp_owl__x1130 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1130 = arc_new(temp_owl__x1130);
                let owl_transp_T1189 = owl_extract_expand_to_len(
                    0 + key_size() + key_size(),
                    vec_as_slice(&(*arc_clone(&owl__x1128))),
                    vec_as_slice(&(*arc_clone(&owl__x1130))),
                );
                let temp_owl__x1131 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(vec_as_slice(&*owl_transp_T1189), 0, 0 + key_size()),
                    ),
                )
                };
                let owl__x1131 = arc_clone(&temp_owl__x1131);
                let temp_owl__x1136 = { arc_clone(&owl__x964) };
                let owl__x1136 = arc_clone(&temp_owl__x1136);
                let temp_owl__x1138 = {
                    {
                        let x: Vec<u8> = mk_vec_u8![];
                        x
                    }
                };
                let owl__x1138 = arc_new(temp_owl__x1138);
                let temp_owl__x1139 = {
                arc_new(
                    slice_to_vec(
                        slice_subrange(
                            vec_as_slice(&*owl_transp_T1189),
                            0 + key_size(),
                            0 + key_size() + key_size(),
                        ),
                    ),
                )
                };
                let owl__x1139 = arc_clone(&temp_owl__x1139);
                let temp_owl__x1161 = { arc_clone(&owl_msg2_receiver866) };
                let owl__x1161 = arc_clone(&temp_owl__x1161);
                let temp_owl__x1163 = { arc_clone(&owl__x1038) };
                let owl__x1163 = arc_clone(&temp_owl__x1163);
                let temp_owl__x1165 = { arc_clone(&owl__x876) };
                let owl__x1165 = arc_clone(&temp_owl__x1165);
                let temp_owl__x1167 = { arc_clone(&owl__x886) };
                let owl__x1167 = arc_clone(&temp_owl__x1167);
                let temp_owl__x1169 = { arc_clone(&owl__x1131) };
                let owl__x1169 = arc_clone(&temp_owl__x1169);
                let temp_owl__x1171 = { arc_clone(&owl__x1139) };
                let owl__x1171 = arc_clone(&temp_owl__x1171);
                let temp_owl__x1173 = {
                owl_transp_keys {
                    owl__transp_keys_initiator: clone_vec_u8(&*arc_clone(&owl__x1161)),
                    owl__transp_keys_responder: clone_vec_u8(&*arc_clone(&owl__x1163)),
                    owl__transp_keys_init_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1165)),
                    owl__transp_keys_resp_ephemeral: clone_vec_u8(&*arc_clone(&owl__x1167)),
                    owl__transp_keys_T_init_send: clone_vec_u8(&*arc_clone(&owl__x1169)),
                    owl__transp_keys_T_resp_send: clone_vec_u8(&*arc_clone(&owl__x1171)),
                }
                };
                let owl__x1173 = temp_owl__x1173;
                let temp_owl__x1174 = { owl__x1173 };
                let owl__x1174 = temp_owl__x1174;
                let temp_owl__x1177 = { owl__x1174 };
                let owl__x1177 = temp_owl__x1177;
                let temp_owl__x1178 = { owl__x1177 };
                let owl__x1178 = temp_owl__x1178;
                (owl__x1178, Tracked(itree))
            }
        };
        Ok(res_inner)
    }
    
    #[verifier::spinoff_prover]
    pub fn owl_receive_msg1(
        &self,
        Tracked(itree): Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>,
        mut_state: &mut state_Responder,
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
            let (temp_owl_inp1198, owl__1197) = owl_input::<(Option<Seq<u8>>, state_Responder)>(
                Tracked(&mut itree),
            );
            let owl_inp1198 = arc_new(temp_owl_inp1198);
            let temp_owl__x1507 = { arc_clone(&owl_inp1198) };
            let owl__x1507 = arc_clone(&temp_owl__x1507);
            if let Some(parseval) = parse_owl_msg1(vec_as_slice(&(*arc_clone(&owl__x1507)))) {
                let owl_msg1_tag1205 = arc_new(parseval.owl__msg1_tag);
                let owl_msg1_sender1204 = arc_new(parseval.owl__msg1_sender);
                let owl_msg1_ephemeral_1203 = arc_new(parseval.owl__msg1_ephemeral);
                let owl_msg1_static1202 = arc_new(parseval.owl__msg1_static);
                let owl_msg1_timestamp1201 = arc_new(parseval.owl__msg1_timestamp);
                let owl_msg1_mac11200 = arc_new(parseval.owl__msg1_mac1);
                {
                    let temp_owl__x1502 = { arc_clone(&owl_msg1_sender1204) };
                    let owl__x1502 = arc_clone(&temp_owl__x1502);
                    let temp_owl__x1503 = { vec_length(&(*arc_clone(&owl__x1502))) };
                    let owl__x1503 = temp_owl__x1503;
                    let temp_owl__x1505 = { 4 };
                    let owl__x1505 = temp_owl__x1505;
                    let temp_owl__x1506 = { owl__x1503 == owl__x1505 };
                    let owl__x1506 = temp_owl__x1506;
                    if owl__x1506 {
                        let temp_owl__x1495 = { arc_clone(&owl_msg1_ephemeral_1203) };
                        let owl__x1495 = arc_clone(&temp_owl__x1495);
                        let temp_owl__x1496 = {
                        owl_is_group_elem(vec_as_slice(&(*arc_clone(&owl__x1495))))
                        };
                        let owl__x1496 = temp_owl__x1496;
                        if owl__x1496 {
                            let temp_owl__x1212 = { owl_construction() };
                            let owl__x1212 = arc_new(temp_owl__x1212);
                            let temp_owl__x1214 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1212))))
                            };
                            let owl__x1214 = arc_clone(&temp_owl__x1214);
                            let temp_owl__x1215 = { arc_clone(&owl__x1214) };
                            let owl__x1215 = arc_clone(&temp_owl__x1215);
                            let temp_owl__x1228 = { arc_clone(&owl__x1215) };
                            let owl__x1228 = arc_clone(&temp_owl__x1228);
                            let temp_owl__x1230 = { owl_identifier() };
                            let owl__x1230 = arc_new(temp_owl__x1230);
                            let temp_owl__x1232 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1228))),
                                vec_as_slice(&(*arc_clone(&owl__x1230))),
                            )
                            };
                            let owl__x1232 = arc_new(temp_owl__x1232);
                            let temp_owl__x1234 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1232))))
                            };
                            let owl__x1234 = arc_clone(&temp_owl__x1234);
                            let temp_owl__x1235 = { arc_clone(&owl__x1234) };
                            let owl__x1235 = arc_clone(&temp_owl__x1235);
                            let temp_owl__x1251 = { arc_clone(&owl__x1235) };
                            let owl__x1251 = arc_clone(&temp_owl__x1251);
                            let temp_owl__x1253 = { arc_clone(&self.owl_S_resp) };
                            let owl__x1253 = arc_clone(&temp_owl__x1253);
                            let temp_owl__x1255 = {
                            owl_dhpk(vec_as_slice(&(*arc_clone(&owl__x1253))))
                            };
                            let owl__x1255 = arc_clone(&temp_owl__x1255);
                            let temp_owl__x1257 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1251))),
                                vec_as_slice(&(*arc_clone(&owl__x1255))),
                            )
                            };
                            let owl__x1257 = arc_new(temp_owl__x1257);
                            let temp_owl__x1259 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1257))))
                            };
                            let owl__x1259 = arc_clone(&temp_owl__x1259);
                            let temp_owl__x1260 = { arc_clone(&owl__x1259) };
                            let owl__x1260 = arc_clone(&temp_owl__x1260);
                            let temp_owl__x1266 = { arc_clone(&owl_msg1_ephemeral_1203) };
                            let owl__x1266 = arc_clone(&temp_owl__x1266);
                            let temp_owl__x1267 = { arc_clone(&owl__x1266) };
                            let owl__x1267 = arc_clone(&temp_owl__x1267);
                            let temp_owl__x1272 = { arc_clone(&owl__x1215) };
                            let owl__x1272 = arc_clone(&temp_owl__x1272);
                            let temp_owl__x1274 = { arc_clone(&owl__x1267) };
                            let owl__x1274 = arc_clone(&temp_owl__x1274);
                            let owl_msg1_C11515 = owl_extract_expand_to_len(
                                0 + nonce_size(),
                                vec_as_slice(&(*arc_clone(&owl__x1272))),
                                vec_as_slice(&(*arc_clone(&owl__x1274))),
                            );
                            let temp_owl__x1275 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C11515),
                                        0,
                                        0 + nonce_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1275 = arc_clone(&temp_owl__x1275);
                            let temp_owl__x1288 = { arc_clone(&owl__x1260) };
                            let owl__x1288 = arc_clone(&temp_owl__x1288);
                            let temp_owl__x1290 = { arc_clone(&owl__x1267) };
                            let owl__x1290 = arc_clone(&temp_owl__x1290);
                            let temp_owl__x1292 = {
                            owl_concat(
                                vec_as_slice(&(*arc_clone(&owl__x1288))),
                                vec_as_slice(&(*arc_clone(&owl__x1290))),
                            )
                            };
                            let owl__x1292 = arc_new(temp_owl__x1292);
                            let temp_owl__x1294 = {
                            owl_crh(vec_as_slice(&(*arc_clone(&owl__x1292))))
                            };
                            let owl__x1294 = arc_clone(&temp_owl__x1294);
                            let temp_owl__x1295 = { arc_clone(&owl__x1294) };
                            let owl__x1295 = arc_clone(&temp_owl__x1295);
                            let temp_owl__x1305 = { arc_clone(&owl__x1267) };
                            let owl__x1305 = arc_clone(&temp_owl__x1305);
                            let temp_owl__x1307 = { arc_clone(&self.owl_S_resp) };
                            let owl__x1307 = arc_clone(&temp_owl__x1307);
                            let temp_owl__x1309 = {
                            owl_dh_combine(
                                vec_as_slice(&(*arc_clone(&owl__x1305))),
                                vec_as_slice(&(*arc_clone(&owl__x1307))),
                            )
                            };
                            let owl__x1309 = arc_clone(&temp_owl__x1309);
                            let temp_owl__x1310 = { arc_clone(&owl__x1309) };
                            let owl__x1310 = arc_clone(&temp_owl__x1310);
                            let temp_owl__x1315 = { arc_clone(&owl__x1275) };
                            let owl__x1315 = arc_clone(&temp_owl__x1315);
                            let temp_owl__x1317 = { arc_clone(&owl__x1310) };
                            let owl__x1317 = arc_clone(&temp_owl__x1317);
                            let owl_msg1_C21516 = owl_extract_expand_to_len(
                                0 + nonce_size() + key_size(),
                                vec_as_slice(&(*arc_clone(&owl__x1315))),
                                vec_as_slice(&(*arc_clone(&owl__x1317))),
                            );
                            let temp_owl__x1318 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C21516),
                                        0,
                                        0 + nonce_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1318 = arc_clone(&temp_owl__x1318);
                            let temp_owl__x1323 = { arc_clone(&owl__x1275) };
                            let owl__x1323 = arc_clone(&temp_owl__x1323);
                            let temp_owl__x1325 = { arc_clone(&owl__x1310) };
                            let owl__x1325 = arc_clone(&temp_owl__x1325);
                            let temp_owl__x1326 = {
                            arc_new(
                                slice_to_vec(
                                    slice_subrange(
                                        vec_as_slice(&*owl_msg1_C21516),
                                        0 + nonce_size(),
                                        0 + nonce_size() + key_size(),
                                    ),
                                ),
                            )
                            };
                            let owl__x1326 = arc_clone(&temp_owl__x1326);
                            let temp_owl__x1485 = { arc_clone(&owl__x1326) };
                            let owl__x1485 = arc_clone(&temp_owl__x1485);
                            let temp_owl__x1487 = { arc_clone(&owl_msg1_static1202) };
                            let owl__x1487 = arc_clone(&temp_owl__x1487);
                            let temp_owl__x1489 = { arc_clone(&owl__x1295) };
                            let owl__x1489 = arc_clone(&temp_owl__x1489);
                            let temp_owl__x1491 = {
                                {
                                    let x: Vec<u8> = mk_vec_u8![];
                                    x
                                }
                            };
                            let owl__x1491 = arc_new(temp_owl__x1491);
                            let temp_owl__x1492 = {
                            owl_dec_st_aead(
                                vec_as_slice(&(*arc_clone(&owl__x1485))),
                                vec_as_slice(&(*arc_clone(&owl__x1487))),
                                vec_as_slice(&(*arc_clone(&owl__x1491))),
                                vec_as_slice(&(*arc_clone(&owl__x1489))),
                            )
                            };
                            let owl__x1492 = temp_owl__x1492;
                            let temp_owl_caseval1514 = { owl__x1492 };
                            let owl_caseval1514 = temp_owl_caseval1514;
                            match owl_caseval1514 {
                                None => {
                                    let temp_owl__x1331 = { None };
                                    let owl__x1331 = temp_owl__x1331;
                                    (owl__x1331, Tracked(itree))
                                },
                                Some(temp_owl_msg1_static_dec1332) => {
                                    let owl_msg1_static_dec1332 = arc_clone(
                                        &temp_owl_msg1_static_dec1332,
                                    );
                                    let temp_owl__x1336 = { arc_clone(&owl_msg1_static_dec1332) };
                                    let owl__x1336 = arc_clone(&temp_owl__x1336);
                                    let (temp_owl__x1337, Tracked(itree)): (
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
, checkpk_resp_spec(*self, *mut_state, (&owl__x1336).dview())
, self.owl_checkpk_resp(mut_state, arc_clone(&owl__x1336)) )
                                    };
                                    let owl__x1337 = temp_owl__x1337;
                                    let temp_owl__x1482 = { owl__x1337 };
                                    let owl__x1482 = temp_owl__x1482;
                                    let temp_owl__x1483 = { owl__x1482 };
                                    let owl__x1483 = temp_owl__x1483;
                                    let temp_owl_caseval1513 = { owl__x1483 };
                                    let owl_caseval1513 = temp_owl_caseval1513;
                                    match owl_caseval1513 {
                                        None => {
                                            let temp_owl__x1339 = { None };
                                            let owl__x1339 = temp_owl__x1339;
                                            (owl__x1339, Tracked(itree))
                                        },
                                        Some(temp_owl_dhpk_S_init_1340) => {
                                            let owl_dhpk_S_init_1340 = arc_clone(
                                                &temp_owl_dhpk_S_init_1340,
                                            );
                                            let temp_owl__x1480 = { arc_clone(&owl_dhpk_S_init_1340)
                                            };
                                            let owl__x1480 = arc_clone(&temp_owl__x1480);
                                            let temp_owl__x1476 = {
                                            arc_clone(&owl_msg1_static_dec1332)
                                            };
                                            let owl__x1476 = arc_clone(&temp_owl__x1476);
                                            let temp_owl__x1478 = { arc_clone(&owl__x1480) };
                                            let owl__x1478 = arc_clone(&temp_owl__x1478);
                                            let temp_owl__x1479 = {
                                            rc_vec_eq(
                                                &arc_clone(&owl__x1476),
                                                &arc_clone(&owl__x1478),
                                            )
                                            };
                                            let owl__x1479 = temp_owl__x1479;
                                            if owl__x1479 {
                                                let temp_owl__x1355 = { arc_clone(&owl__x1295) };
                                                let owl__x1355 = arc_clone(&temp_owl__x1355);
                                                let temp_owl__x1357 = {
                                                arc_clone(&owl_msg1_static1202)
                                                };
                                                let owl__x1357 = arc_clone(&temp_owl__x1357);
                                                let temp_owl__x1359 = {
                                                owl_concat(
                                                    vec_as_slice(&(*arc_clone(&owl__x1355))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1357))),
                                                )
                                                };
                                                let owl__x1359 = arc_new(temp_owl__x1359);
                                                let temp_owl__x1361 = {
                                                owl_crh(vec_as_slice(&(*arc_clone(&owl__x1359))))
                                                };
                                                let owl__x1361 = arc_clone(&temp_owl__x1361);
                                                let temp_owl__x1362 = { arc_clone(&owl__x1361) };
                                                let owl__x1362 = arc_clone(&temp_owl__x1362);
                                                let temp_owl__x1372 = { arc_clone(&owl__x1480) };
                                                let owl__x1372 = arc_clone(&temp_owl__x1372);
                                                let temp_owl__x1374 = { arc_clone(&self.owl_S_resp)
                                                };
                                                let owl__x1374 = arc_clone(&temp_owl__x1374);
                                                let temp_owl__x1376 = {
                                                owl_dh_combine(
                                                    vec_as_slice(&(*arc_clone(&owl__x1372))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1374))),
                                                )
                                                };
                                                let owl__x1376 = arc_clone(&temp_owl__x1376);
                                                let temp_owl__x1377 = { arc_clone(&owl__x1376) };
                                                let owl__x1377 = arc_clone(&temp_owl__x1377);
                                                let temp_owl__x1382 = { arc_clone(&owl__x1318) };
                                                let owl__x1382 = arc_clone(&temp_owl__x1382);
                                                let temp_owl__x1384 = { arc_clone(&owl__x1377) };
                                                let owl__x1384 = arc_clone(&temp_owl__x1384);
                                                let owl_msg1_C31517 = owl_extract_expand_to_len(
                                                    0 + nonce_size() + key_size(),
                                                    vec_as_slice(&(*arc_clone(&owl__x1382))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1384))),
                                                );
                                                let temp_owl__x1385 = {
                                                arc_new(
                                                    slice_to_vec(
                                                        slice_subrange(
                                                            vec_as_slice(&*owl_msg1_C31517),
                                                            0,
                                                            0 + nonce_size(),
                                                        ),
                                                    ),
                                                )
                                                };
                                                let owl__x1385 = arc_clone(&temp_owl__x1385);
                                                let temp_owl__x1390 = { arc_clone(&owl__x1318) };
                                                let owl__x1390 = arc_clone(&temp_owl__x1390);
                                                let temp_owl__x1392 = { arc_clone(&owl__x1377) };
                                                let owl__x1392 = arc_clone(&temp_owl__x1392);
                                                let temp_owl__x1393 = {
                                                arc_new(
                                                    slice_to_vec(
                                                        slice_subrange(
                                                            vec_as_slice(&*owl_msg1_C31517),
                                                            0 + nonce_size(),
                                                            0 + nonce_size() + key_size(),
                                                        ),
                                                    ),
                                                )
                                                };
                                                let owl__x1393 = arc_clone(&temp_owl__x1393);
                                                let temp_owl__x1465 = { arc_clone(&owl__x1393) };
                                                let owl__x1465 = arc_clone(&temp_owl__x1465);
                                                let temp_owl__x1467 = {
                                                arc_clone(&owl_msg1_timestamp1201)
                                                };
                                                let owl__x1467 = arc_clone(&temp_owl__x1467);
                                                let temp_owl__x1469 = { arc_clone(&owl__x1362) };
                                                let owl__x1469 = arc_clone(&temp_owl__x1469);
                                                let temp_owl__x1471 = {
                                                    {
                                                        let x: Vec<u8> = mk_vec_u8![];
                                                        x
                                                    }
                                                };
                                                let owl__x1471 = arc_new(temp_owl__x1471);
                                                let temp_owl__x1472 = {
                                                owl_dec_st_aead(
                                                    vec_as_slice(&(*arc_clone(&owl__x1465))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1467))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1471))),
                                                    vec_as_slice(&(*arc_clone(&owl__x1469))),
                                                )
                                                };
                                                let owl__x1472 = temp_owl__x1472;
                                                let temp_owl_caseval1512 = { owl__x1472 };
                                                let owl_caseval1512 = temp_owl_caseval1512;
                                                match owl_caseval1512 {
                                                    None => {
                                                        let temp_owl__x1398 = { None };
                                                        let owl__x1398 = temp_owl__x1398;
                                                        (owl__x1398, Tracked(itree))
                                                    },
                                                    Some(temp_owl_msg1_timestamp_dec1399) => {
                                                        let owl_msg1_timestamp_dec1399 = arc_clone(
                                                            &temp_owl_msg1_timestamp_dec1399,
                                                        );
                                                        let temp_owl__x1412 = {
                                                        arc_clone(&owl__x1362)
                                                        };
                                                        let owl__x1412 = arc_clone(
                                                            &temp_owl__x1412,
                                                        );
                                                        let temp_owl__x1414 = {
                                                        arc_clone(&owl_msg1_timestamp_dec1399)
                                                        };
                                                        let owl__x1414 = arc_clone(
                                                            &temp_owl__x1414,
                                                        );
                                                        let temp_owl__x1416 = {
                                                        owl_concat(
                                                            vec_as_slice(
                                                                &(*arc_clone(&owl__x1412)),
                                                            ),
                                                            vec_as_slice(
                                                                &(*arc_clone(&owl__x1414)),
                                                            ),
                                                        )
                                                        };
                                                        let owl__x1416 = arc_new(temp_owl__x1416);
                                                        let temp_owl__x1418 = {
                                                        owl_crh(
                                                            vec_as_slice(
                                                                &(*arc_clone(&owl__x1416)),
                                                            ),
                                                        )
                                                        };
                                                        let owl__x1418 = arc_clone(
                                                            &temp_owl__x1418,
                                                        );
                                                        let temp_owl__x1419 = {
                                                        arc_clone(&owl__x1418)
                                                        };
                                                        let owl__x1419 = arc_clone(
                                                            &temp_owl__x1419,
                                                        );
                                                        let temp_owl__x1438 = {
                                                        arc_clone(&owl__x1385)
                                                        };
                                                        let owl__x1438 = arc_clone(
                                                            &temp_owl__x1438,
                                                        );
                                                        let temp_owl__x1440 = {
                                                        arc_clone(&owl__x1419)
                                                        };
                                                        let owl__x1440 = arc_clone(
                                                            &temp_owl__x1440,
                                                        );
                                                        let temp_owl__x1442 = {
                                                        arc_clone(&owl__x1267)
                                                        };
                                                        let owl__x1442 = arc_clone(
                                                            &temp_owl__x1442,
                                                        );
                                                        let temp_owl__x1444 = {
                                                        arc_clone(&owl__x1480)
                                                        };
                                                        let owl__x1444 = arc_clone(
                                                            &temp_owl__x1444,
                                                        );
                                                        let temp_owl__x1446 = {
                                                        arc_clone(&owl_msg1_sender1204)
                                                        };
                                                        let owl__x1446 = arc_clone(
                                                            &temp_owl__x1446,
                                                        );
                                                        let temp_owl__x1448 = {
                                                        owl_responder_msg1_val {
                                                            owl__responder_msg1_C3: clone_vec_u8(
                                                                &*arc_clone(&owl__x1438),
                                                            ),
                                                            owl__responder_msg1_H4: clone_vec_u8(
                                                                &*arc_clone(&owl__x1440),
                                                            ),
                                                            owl__responder_msg1_ephemeral:
                                                                clone_vec_u8(
                                                                &*arc_clone(&owl__x1442),
                                                            ),
                                                            owl__responder_msg1_sender_pk:
                                                                clone_vec_u8(
                                                                &*arc_clone(&owl__x1444),
                                                            ),
                                                            owl__responder_msg1_sender:
                                                                clone_vec_u8(
                                                                &*arc_clone(&owl__x1446),
                                                            ),
                                                        }
                                                        };
                                                        let owl__x1448 = temp_owl__x1448;
                                                        let temp_owl__x1449 = { owl__x1448 };
                                                        let owl__x1449 = temp_owl__x1449;
                                                        let temp_owl__x1456 = { owl__x1449 };
                                                        let owl__x1456 = temp_owl__x1456;
                                                        let temp_owl__x1458 = { owl__x1456 };
                                                        let owl__x1458 = temp_owl__x1458;
                                                        let temp_owl__x1459 = { owl__x1458 };
                                                        let owl__x1459 = temp_owl__x1459;
                                                        let temp_owl__x1462 = { owl__x1459 };
                                                        let owl__x1462 = temp_owl__x1462;
                                                        let temp_owl__x1463 = { Some(owl__x1462) };
                                                        let owl__x1463 = temp_owl__x1463;
                                                        (owl__x1463, Tracked(itree))
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
                let temp_owl__x1199 = { None };
                let owl__x1199 = temp_owl__x1199;
                (owl__x1199, Tracked(itree))
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
        owl_pk27443: Arc<Vec<u8>>,
    ) -> (res: Result<
        (Option<Arc<Vec<u8>>>, Tracked<ITreeToken<(Option<Seq<u8>>, state_Responder), Endpoint>>),
        OwlError,
    >)
        requires
            itree.view() == checkpk_resp_spec(*self, *old(mut_state), owl_pk27443.dview()),
        ensures
            res.is_Ok() ==> (res.get_Ok_0().1).view().view().results_in(
                (dview_option(res.get_Ok_0().0), *mut_state),
            ),
    {
        let tracked mut itree = itree;
        let res_inner = {
            use x25519_dalek::{PublicKey};
            use std::convert::TryInto;

            let pk: [u8; 32] = (&*owl_pk27443).as_slice().try_into().unwrap();
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
pub closed spec fn construction() -> Seq<u8> {
    seq![0x63u8, 0x6fu8, 0x6eu8, 0x73u8, 0x74u8, 0x72u8, 0x75u8, 0x63u8, 0x74u8, 0x69u8, 0x6fu8, 0x6eu8, ]
}

pub exec fn owl_construction() -> (res: Vec<u8>)
    ensures
        res.dview() == construction(),
{
    {
        let x: Vec<u8> =
            mk_vec_u8![0x63u8, 0x6fu8, 0x6eu8, 0x73u8, 0x74u8, 0x72u8, 0x75u8, 0x63u8, 0x74u8, 0x69u8, 0x6fu8, 0x6eu8, ];
        x
    }
}

pub closed spec fn identifier() -> Seq<u8> {
    seq![0x69u8, 0x64u8, 0x65u8, 0x6eu8, 0x74u8, 0x69u8, 0x66u8, 0x69u8, 0x65u8, 0x72u8, ]
}

pub exec fn owl_identifier() -> (res: Vec<u8>)
    ensures
        res.dview() == identifier(),
{
    {
        let x: Vec<u8> =
            mk_vec_u8![0x69u8, 0x64u8, 0x65u8, 0x6eu8, 0x74u8, 0x69u8, 0x66u8, 0x69u8, 0x65u8, 0x72u8, ];
        x
    }
}

pub closed spec fn mac1() -> Seq<u8> {
    seq![0x6du8, 0x61u8, 0x63u8, 0x31u8, 0x2du8, 0x2du8, 0x2du8, ]
}

pub exec fn owl_mac1() -> (res: Vec<u8>)
    ensures
        res.dview() == mac1(),
{
    {
        let x: Vec<u8> = mk_vec_u8![0x6du8, 0x61u8, 0x63u8, 0x31u8, 0x2du8, 0x2du8, 0x2du8, ];
        x
    }
}

pub closed spec fn msg1_tag_value() -> Seq<u8> {
    seq![0x01u8, 0x00u8, 0x00u8, 0x00u8, ]
}

pub exec fn owl_msg1_tag_value() -> (res: Vec<u8>)
    ensures
        res.dview() == msg1_tag_value(),
{
    {
        let x: Vec<u8> = mk_vec_u8![0x01u8, 0x00u8, 0x00u8, 0x00u8, ];
        x
    }
}

pub closed spec fn msg2_tag_value() -> Seq<u8> {
    seq![0x02u8, 0x00u8, 0x00u8, 0x00u8, ]
}

pub exec fn owl_msg2_tag_value() -> (res: Vec<u8>)
    ensures
        res.dview() == msg2_tag_value(),
{
    {
        let x: Vec<u8> = mk_vec_u8![0x02u8, 0x00u8, 0x00u8, 0x00u8, ];
        x
    }
}

pub closed spec fn transp_tag_value() -> Seq<u8> {
    seq![0x04u8, 0x00u8, 0x00u8, 0x00u8, ]
}

pub exec fn owl_transp_tag_value() -> (res: Vec<u8>)
    ensures
        res.dview() == transp_tag_value(),
{
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
fn main() { /* entrypoint() */ }


