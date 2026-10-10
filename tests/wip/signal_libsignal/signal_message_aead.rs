//! Signal's message encryption as a nonce-based AEAD, for the libsignal integration
//! (tests/wip/signal_libsignal). TRUSTED: this is the st_aead primitive of that
//! model's cipher suite. It computes exactly what libsignal (v0.103, SPQR disabled)
//! computes for message n of a chain with chain key CK (ratchet/keys.rs,
//! triple_ratchet.rs, protocol.rs):
//!
//!   CK_n        = HMAC-SHA256^n(CK, 0x02)            (ChainKey::next_chain_key)
//!   seed        = HMAC-SHA256(CK_n, 0x01)             (ChainKey::message_keys)
//!   ck, mk, iv  = HKDF-SHA256(salt = none, seed, "WhisperMessageKeys"), 32/32/16 bytes
//!   ct          = AES-256-CBC-PKCS7(ck, iv, pt)
//!   mac         = HMAC-SHA256(mk, 0x05||IK_s || 0x05||IK_r || 0x44 ||
//!                             protobuf SignalMessage{rk, counter, prev, ct, addresses})[0..8]
//!   output      = ct || mac
//!
//! The key is CK (the chain key at index 0); the nonce is n (the first 8 bytes, little
//! endian, of the Owl counter). The AAD is Owl's encoding of the message header:
//! IK_s (32) || IK_r (32) || ratchet key (32) || counter (8, big-endian) ||
//! previous counter (8, big-endian) || addresses (0 or more bytes); the MAC covers it
//! in libsignal's encoding, with the ciphertext at its protobuf position. As an AEAD
//! keyed by CK with nonce n, this relies on HMAC-SHA256 being a PRF, HKDF, and
//! encrypt-then-MAC with AES-CBC.
//!
//! Loaded by extraction/src/owl_aead.rs as its submodule `signal_message_aead` when the
//! support library is built with the `libsignal-crypto` feature (only in the libsignal
//! fork). Uses the wire helpers of this model's owl_wire.rs.

use super::Error;
use hmac_libsignal::{Hmac, KeyInit as _, Mac as _};
use sha2_libsignal::Sha256;
use subtle::ConstantTimeEq;

const MAC_LEN: usize = crate::owl_wire::MAC_LEN;
const MAX_CHAIN_STEPS: u64 = 25_000; // libsignal's MAX_FORWARD_JUMPS

fn hmac_sha256(key: &[u8], data: &[&[u8]]) -> [u8; 32] {
    let mut m = Hmac::<Sha256>::new_from_slice(key).expect("HMAC takes any key length");
    for d in data {
        m.update(d);
    }
    m.finalize().into_bytes().into()
}

/// libsignal's message keys for message `n` of the chain with chain key `ck`.
fn message_keys(ck: &[u8], n: u64) -> Result<([u8; 32], [u8; 32], [u8; 16]), Error> {
    if ck.len() != 32 || n > MAX_CHAIN_STEPS {
        return Err(Error::InvalidInit);
    }
    let mut ck: [u8; 32] = ck.try_into().unwrap();
    for _ in 0..n {
        ck = hmac_sha256(&ck, &[&[0x02]]);
    }
    let seed = hmac_sha256(&ck, &[&[0x01]]);
    let mut okm = [0u8; 80];
    hkdf_libsignal::Hkdf::<Sha256>::new(None, &seed)
        .expand(b"WhisperMessageKeys", &mut okm)
        .map_err(|_| Error::InvalidInit)?;
    Ok((
        okm[0..32].try_into().unwrap(),
        okm[32..64].try_into().unwrap(),
        okm[64..80].try_into().unwrap(),
    ))
}

fn nonce_to_counter(iv: &[u8]) -> Result<u64, Error> {
    let b: [u8; 8] = iv.get(0..8).ok_or(Error::InvalidNonce)?.try_into().unwrap();
    if iv[8..].iter().any(|x| *x != 0) {
        return Err(Error::InvalidNonce);
    }
    Ok(u64::from_le_bytes(b))
}

/// libsignal's MAC input for a message with this header (Owl AAD) and ciphertext.
fn mac_input(aad: &[u8], ct: &[u8]) -> Result<Vec<u8>, Error> {
    use crate::owl_wire::{counter_from_owl, pk_to_wire, signal_message_proto, VERSION_BYTE};
    if aad.len() < 3 * 32 + 16 {
        return Err(Error::InvalidInit);
    }
    let (ik_s, rest) = aad.split_at(32);
    let (ik_r, rest) = rest.split_at(32);
    let (rk, rest) = rest.split_at(32);
    let (ctr, rest) = rest.split_at(8);
    let (prev, addresses) = rest.split_at(8);
    let body = signal_message_proto(
        rk,
        counter_from_owl(ctr).ok_or(Error::InvalidInit)?,
        counter_from_owl(prev).ok_or(Error::InvalidInit)?,
        ct,
        addresses,
    )
    .ok_or(Error::InvalidInit)?;
    let mut v = Vec::with_capacity(2 * 33 + 1 + body.len());
    v.extend_from_slice(&pk_to_wire(ik_s).unwrap());
    v.extend_from_slice(&pk_to_wire(ik_r).unwrap());
    v.push(VERSION_BYTE);
    v.extend_from_slice(&body);
    Ok(v)
}

pub fn seal(k: &[u8], pt: &[u8], iv: &[u8], aad: &[u8]) -> Result<Vec<u8>, Error> {
    let (ck, mk, civ) = message_keys(k, nonce_to_counter(iv)?)?;
    let mut ct =
        signal_crypto::aes_256_cbc_encrypt(pt, &ck, &civ).map_err(|_| Error::Encrypting)?;
    let mac = hmac_sha256(&mk, &[&mac_input(aad, &ct)?]);
    ct.extend_from_slice(&mac[..MAC_LEN]);
    Ok(ct)
}

pub fn open(k: &[u8], c: &[u8], iv: &[u8], aad: &[u8]) -> Result<Vec<u8>, Error> {
    if c.len() < MAC_LEN {
        return Err(Error::InvalidTagSize);
    }
    let (ct, their_mac) = c.split_at(c.len() - MAC_LEN);
    let (ck, mk, civ) = message_keys(k, nonce_to_counter(iv)?)?;
    let mac = hmac_sha256(&mk, &[&mac_input(aad, ct)?]);
    if !bool::from(mac[..MAC_LEN].ct_eq(their_mac)) {
        return Err(Error::Decrypting);
    }
    signal_crypto::aes_256_cbc_decrypt(ct, &ck, &civ).map_err(|_| Error::Decrypting)
}
