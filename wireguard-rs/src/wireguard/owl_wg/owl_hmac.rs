use crate::wireguard::owl_wg::owl_util::gen_rand_bytes;
use crypto::common::KeyInit;
use hmac::Mac;
use hmac::Hmac;
use sha1::Sha1;
use sha2::{Sha256, Sha384, Sha512};
use vstd::prelude::*;

verus! {

pub enum Mode {
    Sha1,
    Sha256,
    Sha384,
    Sha512,
}

#[inline]
pub const fn tag_size(mode: &Mode) -> usize {
    match mode {
        Mode::Sha1 => 20,
        Mode::Sha256 => 32,
        Mode::Sha384 => 48,
        Mode::Sha512 => 64,
    }
}

#[inline]
pub open const spec fn spec_key_size(mode: Mode) -> usize {
    64
}

/// Get the key size of the `Mode` in bytes.
#[inline]
pub const fn key_size(mode: Mode) -> (u:usize)
    ensures u == spec_key_size(mode)
{
    64
}

#[inline]
pub fn gen_rand_key(_mode: &Mode) -> Vec<u8> {
    gen_rand_bytes(64)
}

#[verifier(external_body)]
pub fn hmac(mode: Mode, key: &[u8], data: &[u8], tag_length: Option<usize>) -> Vec<u8> {
    let tag_length = match tag_length {
        Some(v) => v,
        None => tag_size(&mode),
    };

    #[verifier(external_body)]
    fn hmac_inner<H: Mac + KeyInit>(key: &[u8], data: &[u8]) -> Vec<u8> {
        let mut mac = <H as Mac>::new_from_slice(key).expect("HMAC got invalid length");
        mac.update(data);
        mac.finalize().into_bytes().to_vec()
    }

    let mut result = match mode {
        Mode::Sha1 => hmac_inner::<Hmac<Sha1>>(key, data),
        Mode::Sha256 => hmac_inner::<Hmac<Sha256>>(key, data),
        Mode::Sha384 => hmac_inner::<Hmac<Sha384>>(key, data),
        Mode::Sha512 => hmac_inner::<Hmac<Sha512>>(key, data),
    };

    result.truncate(tag_length);
    return result;
}

#[verifier(external_body)]
pub fn verify(
    mode: Mode,
    key: &[u8],
    data: &[u8],
    value: &[u8],
    tag_length: Option<usize>,
) -> bool {
    let mac = hmac(mode, key, data, tag_length);
    mac == value
}

} // verus!
