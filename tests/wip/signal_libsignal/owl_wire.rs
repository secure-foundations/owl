// Wire formats for the Signal model extracted with `owl --no-vest`
// (tests/wip/signal_libsignal/{pqxdh,x3dh}): libsignal's protobuf messages.
//
// TRUSTED. The generated lib.rs calls these hooks from #[verifier::external_body]
// shims; Verus does not check them. Each type's hooks are deterministic, implement
// one fixed encoding, and parse inverts serialize.
//
// Only `signal_message` and `prekey_msg` are wire formats. The state and output
// structs of the model (alice_init_state, alice_state, bob_state_1, ...) are only
// passed around as Rust values; their hooks are unreachable.
//
// Encodings of the Owl fields:
//   - group elements are 32-byte X25519 keys; on the wire they are libsignal's
//     33-byte serialization (0x05 || key);
//   - counters are 8 bytes, a big-endian u64 that must fit in a u32;
//   - signal_message._sm_ctxt is the st_aead output: AES-CBC ciphertext || 8-byte
//     MAC; the MAC goes after the protobuf;
//   - signal_message._sm_addr is the `addresses` field (empty = absent);
//   - prekey_msg._pm_meta is registration id (4) || has one-time prekey (1) ||
//     one-time prekey id (4) || signed prekey id (4) || Kyber prekey id (4), all
//     big-endian (17 bytes).
//
// The parsers are strict: they accept only a message whose protobuf is exactly what
// the serializer produces (prost's encoding, fields in declaration order). The trusted
// st_aead (signal_message_aead.rs) computes libsignal's MAC over that same encoding, so for an
// accepted message it equals libsignal's MAC over the received bytes. Messages that
// libsignal would accept but that fail these checks (non-canonical encodings, SPQR
// payloads, unknown fields) are rejected here; the libsignal glue routes them to
// libsignal's own code before calling the verified code.
#![allow(unused_variables)]
use crate::*;
use prost::Message;

/// prost types for the two messages, as prost-build generates them from libsignal's
/// rust/protocol/src/proto/wire.proto (field order matters for the encoding).
pub mod proto {
    #[derive(Clone, PartialEq, ::prost::Message)]
    pub struct SignalMessage {
        #[prost(bytes = "vec", optional, tag = "1")]
        pub ratchet_key: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
        #[prost(uint32, optional, tag = "2")]
        pub counter: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "3")]
        pub previous_counter: ::core::option::Option<u32>,
        #[prost(bytes = "vec", optional, tag = "4")]
        pub ciphertext: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
        #[prost(bytes = "vec", optional, tag = "5")]
        pub pq_ratchet: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
        #[prost(bytes = "vec", optional, tag = "6")]
        pub addresses: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
    }
    #[derive(Clone, PartialEq, ::prost::Message)]
    pub struct PreKeySignalMessage {
        #[prost(uint32, optional, tag = "5")]
        pub registration_id: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "1")]
        pub pre_key_id: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "6")]
        pub signed_pre_key_id: ::core::option::Option<u32>,
        #[prost(uint32, optional, tag = "7")]
        pub kyber_pre_key_id: ::core::option::Option<u32>,
        #[prost(bytes = "vec", optional, tag = "8")]
        pub kyber_ciphertext: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
        #[prost(bytes = "vec", optional, tag = "2")]
        pub base_key: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
        #[prost(bytes = "vec", optional, tag = "3")]
        pub identity_key: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
        /// SignalMessage
        #[prost(bytes = "vec", optional, tag = "4")]
        pub message: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
    }
}

/// Version byte of a session-version-4 message: (4 << 4) | 4.
pub const VERSION_BYTE: u8 = 0x44;
/// Length of libsignal's truncated message MAC.
pub const MAC_LEN: usize = 8;
/// libsignal's key-type byte for Curve25519 public keys.
pub const DJB_TYPE: u8 = 0x05;
/// Length of `prekey_msg._pm_meta`.
pub const META_LEN: usize = 17;

/// 32-byte key -> libsignal's 33-byte serialization.
pub fn pk_to_wire(pk: &[u8]) -> Option<Vec<u8>> {
    if pk.len() != 32 {
        return None;
    }
    let mut v = Vec::with_capacity(33);
    v.push(DJB_TYPE);
    v.extend_from_slice(pk);
    Some(v)
}

/// libsignal's 33-byte serialization -> 32-byte key (strict: no trailing bytes).
pub fn pk_from_wire(pk: &[u8]) -> Option<&[u8]> {
    if pk.len() != 33 || pk[0] != DJB_TYPE {
        return None;
    }
    Some(&pk[1..])
}

pub fn counter_to_owl(c: u32) -> [u8; 8] {
    (c as u64).to_be_bytes()
}

pub fn counter_from_owl(b: &[u8]) -> Option<u32> {
    let b: [u8; 8] = b.try_into().ok()?;
    u32::try_from(u64::from_be_bytes(b)).ok()
}

/// The protobuf of a SignalMessage (without version byte and MAC).
pub fn signal_message_proto(
    rk: &[u8],
    counter: u32,
    previous_counter: u32,
    ct: &[u8],
    addresses: &[u8],
) -> Option<Vec<u8>> {
    let m = proto::SignalMessage {
        ratchet_key: Some(pk_to_wire(rk)?),
        counter: Some(counter),
        previous_counter: Some(previous_counter),
        ciphertext: Some(ct.to_vec()),
        pq_ratchet: None,
        addresses: if addresses.is_empty() { None } else { Some(addresses.to_vec()) },
    };
    Some(m.encode_to_vec())
}

// ---------- signal_message ----------

pub fn parse_owl_signal_message<'a>(arg: OwlBuf<'a>) -> Option<owl_signal_message<'a>> {
    let b = arg.as_slice();
    if b.len() < 1 + MAC_LEN || b[0] != VERSION_BYTE {
        return None;
    }
    let body = &b[1..b.len() - MAC_LEN];
    let mac = &b[b.len() - MAC_LEN..];
    let m = proto::SignalMessage::decode(body).ok()?;
    if m.pq_ratchet.is_some() || m.addresses.as_ref().is_some_and(|a| a.is_empty()) {
        return None;
    }
    let rk = pk_from_wire(m.ratchet_key.as_ref()?)?;
    let counter = m.counter?;
    let prev = m.previous_counter?;
    let ct = m.ciphertext.as_ref()?;
    let addr = m.addresses.clone().unwrap_or_default();
    // canonical encoding only
    if signal_message_proto(rk, counter, prev, ct, &addr)?.as_slice() != body {
        return None;
    }
    let mut ctxt = ct.clone();
    ctxt.extend_from_slice(mac);
    Some(owl_signal_message {
        owl__sm_rk: OwlBuf::from_vec(rk.to_vec()),
        owl__sm_ctr: OwlBuf::from_vec(counter_to_owl(counter).to_vec()),
        owl__sm_prev: OwlBuf::from_vec(counter_to_owl(prev).to_vec()),
        owl__sm_ctxt: OwlBuf::from_vec(ctxt),
        owl__sm_addr: OwlBuf::from_vec(addr),
    })
}

pub fn serialize_owl_signal_message_inner<'a>(arg: &owl_signal_message<'a>) -> Option<OwlBuf<'a>> {
    let ctxt = arg.owl__sm_ctxt.as_slice();
    if ctxt.len() < MAC_LEN {
        return None;
    }
    let (ct, mac) = ctxt.split_at(ctxt.len() - MAC_LEN);
    let body = signal_message_proto(
        arg.owl__sm_rk.as_slice(),
        counter_from_owl(arg.owl__sm_ctr.as_slice())?,
        counter_from_owl(arg.owl__sm_prev.as_slice())?,
        ct,
        arg.owl__sm_addr.as_slice(),
    )?;
    let mut out = Vec::with_capacity(1 + body.len() + MAC_LEN);
    out.push(VERSION_BYTE);
    out.extend_from_slice(&body);
    out.extend_from_slice(mac);
    Some(OwlBuf::from_vec(out))
}

// ---------- prekey_msg ----------

/// Encode `prekey_msg._pm_meta`.
pub fn encode_meta(
    registration_id: u32,
    pre_key_id: Option<u32>,
    signed_pre_key_id: u32,
    kyber_pre_key_id: u32,
) -> [u8; META_LEN] {
    let mut m = [0u8; META_LEN];
    m[0..4].copy_from_slice(&registration_id.to_be_bytes());
    m[4] = pre_key_id.is_some() as u8;
    m[5..9].copy_from_slice(&pre_key_id.unwrap_or(0).to_be_bytes());
    m[9..13].copy_from_slice(&signed_pre_key_id.to_be_bytes());
    m[13..17].copy_from_slice(&kyber_pre_key_id.to_be_bytes());
    m
}

/// Decode `prekey_msg._pm_meta` (strict: the one-time prekey id is 0 when absent).
pub fn decode_meta(m: &[u8]) -> Option<(u32, Option<u32>, u32, u32)> {
    if m.len() != META_LEN || m[4] > 1 {
        return None;
    }
    let u = |i: usize| u32::from_be_bytes(m[i..i + 4].try_into().unwrap());
    let pk = if m[4] == 1 { Some(u(5)) } else if u(5) == 0 { None } else { return None };
    Some((u(0), pk, u(9), u(13)))
}

fn prekey_msg_proto(arg: &owl_prekey_msg<'_>) -> Option<proto::PreKeySignalMessage> {
    let (reg, pk, spk, kyber) = decode_meta(arg.owl__pm_meta.as_slice())?;
    Some(proto::PreKeySignalMessage {
        registration_id: Some(reg),
        pre_key_id: pk,
        signed_pre_key_id: Some(spk),
        kyber_pre_key_id: Some(kyber),
        kyber_ciphertext: Some(arg.owl__pm_kct.as_slice().to_vec()),
        base_key: Some(pk_to_wire(arg.owl__pm_base.as_slice())?),
        identity_key: Some(pk_to_wire(arg.owl__pm_ik.as_slice())?),
        message: Some(arg.owl__pm_msg.as_slice().to_vec()),
    })
}

pub fn parse_owl_prekey_msg<'a>(arg: OwlBuf<'a>) -> Option<owl_prekey_msg<'a>> {
    let b = arg.as_slice();
    if b.is_empty() || b[0] != VERSION_BYTE {
        return None;
    }
    let body = &b[1..];
    let m = proto::PreKeySignalMessage::decode(body).ok()?;
    let meta = encode_meta(
        m.registration_id?,
        m.pre_key_id,
        m.signed_pre_key_id?,
        m.kyber_pre_key_id?,
    );
    let res = owl_prekey_msg {
        owl__pm_meta: OwlBuf::from_vec(meta.to_vec()),
        owl__pm_kct: OwlBuf::from_vec(m.kyber_ciphertext.clone()?),
        owl__pm_base: OwlBuf::from_vec(pk_from_wire(m.base_key.as_ref()?)?.to_vec()),
        owl__pm_ik: OwlBuf::from_vec(pk_from_wire(m.identity_key.as_ref()?)?.to_vec()),
        owl__pm_msg: OwlBuf::from_vec(m.message.clone()?),
    };
    // canonical encoding only
    if prekey_msg_proto(&res)?.encode_to_vec().as_slice() != body {
        return None;
    }
    Some(res)
}

pub fn serialize_owl_prekey_msg_inner<'a>(arg: &owl_prekey_msg<'a>) -> Option<OwlBuf<'a>> {
    let m = prekey_msg_proto(arg)?;
    let mut out = Vec::with_capacity(1 + m.encoded_len());
    out.push(VERSION_BYTE);
    m.encode(&mut out).ok()?;
    Some(OwlBuf::from_vec(out))
}

// ---------- model state structs: never parsed or serialized ----------

const NOT_WIRE: &str = "Signal model: state structs are not parsed or serialized";

pub fn parse_owl_alice_init_state<'a>(arg: OwlBuf<'a>) -> Option<owl_alice_init_state<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_alice_init_state_inner<'a>(arg: &owl_alice_init_state<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn parse_owl_secret_alice_init_state<'a>(arg: OwlBuf<'a>) -> Option<owl_secret_alice_init_state<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn secret_parse_owl_secret_alice_init_state<'a>(arg: SecretBuf<'a>) -> Option<owl_secret_alice_init_state<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_secret_alice_init_state_inner<'a>(arg: &owl_secret_alice_init_state<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }

pub fn parse_owl_alice_state<'a>(arg: OwlBuf<'a>) -> Option<owl_alice_state<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_alice_state_inner<'a>(arg: &owl_alice_state<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn parse_owl_secret_alice_state<'a>(arg: OwlBuf<'a>) -> Option<owl_secret_alice_state<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn secret_parse_owl_secret_alice_state<'a>(arg: SecretBuf<'a>) -> Option<owl_secret_alice_state<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_secret_alice_state_inner<'a>(arg: &owl_secret_alice_state<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }

pub fn parse_owl_alice_recv_out<'a>(arg: OwlBuf<'a>) -> Option<owl_alice_recv_out<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_alice_recv_out_inner<'a>(arg: &owl_alice_recv_out<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn parse_owl_secret_alice_recv_out<'a>(arg: OwlBuf<'a>) -> Option<owl_secret_alice_recv_out<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn secret_parse_owl_secret_alice_recv_out<'a>(arg: SecretBuf<'a>) -> Option<owl_secret_alice_recv_out<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_secret_alice_recv_out_inner<'a>(arg: &owl_secret_alice_recv_out<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }

pub fn parse_owl_bob_state_1<'a>(arg: OwlBuf<'a>) -> Option<owl_bob_state_1<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_bob_state_1_inner<'a>(arg: &owl_bob_state_1<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn parse_owl_secret_bob_state_1<'a>(arg: OwlBuf<'a>) -> Option<owl_secret_bob_state_1<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn secret_parse_owl_secret_bob_state_1<'a>(arg: SecretBuf<'a>) -> Option<owl_secret_bob_state_1<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_secret_bob_state_1_inner<'a>(arg: &owl_secret_bob_state_1<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }

pub fn parse_owl_bob_state<'a>(arg: OwlBuf<'a>) -> Option<owl_bob_state<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_bob_state_inner<'a>(arg: &owl_bob_state<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn parse_owl_secret_bob_state<'a>(arg: OwlBuf<'a>) -> Option<owl_secret_bob_state<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn secret_parse_owl_secret_bob_state<'a>(arg: SecretBuf<'a>) -> Option<owl_secret_bob_state<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_secret_bob_state_inner<'a>(arg: &owl_secret_bob_state<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }

pub fn parse_owl_bob_recv_out<'a>(arg: OwlBuf<'a>) -> Option<owl_bob_recv_out<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_bob_recv_out_inner<'a>(arg: &owl_bob_recv_out<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn parse_owl_secret_bob_recv_out<'a>(arg: OwlBuf<'a>) -> Option<owl_secret_bob_recv_out<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn secret_parse_owl_secret_bob_recv_out<'a>(arg: SecretBuf<'a>) -> Option<owl_secret_bob_recv_out<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_secret_bob_recv_out_inner<'a>(arg: &owl_secret_bob_recv_out<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }

pub fn parse_owl_bob_prekey_out<'a>(arg: OwlBuf<'a>) -> Option<owl_bob_prekey_out<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_bob_prekey_out_inner<'a>(arg: &owl_bob_prekey_out<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn parse_owl_secret_bob_prekey_out<'a>(arg: OwlBuf<'a>) -> Option<owl_secret_bob_prekey_out<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn secret_parse_owl_secret_bob_prekey_out<'a>(arg: SecretBuf<'a>) -> Option<owl_secret_bob_prekey_out<'a>> { unreachable!("{}", NOT_WIRE) }
pub fn serialize_owl_secret_bob_prekey_out_inner<'a>(arg: &owl_secret_bob_prekey_out<'a>) -> Option<SecretBuf<'a>> { unreachable!("{}", NOT_WIRE) }
