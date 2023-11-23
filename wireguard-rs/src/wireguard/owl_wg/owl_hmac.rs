use crate::wireguard::owl_wg::owl_util::gen_rand_bytes;
use crypto::common::KeyInit;
use hmac::Mac;
use hmac::NewMac;
use blake2::Blake2s;
use hmac::Hmac;
use sha1::Sha1;
use sha2::{Sha256, Sha384, Sha512};
use vstd::prelude::*;

type HMACBlake2s = Hmac<Blake2s>;

verus! {

pub enum Mode {
    Sha1,
    Sha256,
    Sha384,
    Sha512,
    Blake2s,
}

#[inline]
pub const fn tag_size(mode: &Mode) -> usize {
    match mode {
        Mode::Sha1 => 20,
        Mode::Sha256 => 32,
        Mode::Sha384 => 48,
        Mode::Sha512 => 64,
        Mode::Blake2s => 32,
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

    // #[verifier(external_body)]
    // fn hmac_inner<H: Mac + KeyInit>(key: &[u8], data: &[u8]) -> Vec<u8> {
    //     let mut mac = <H as Mac>::new_from_slice(key).expect("HMAC got invalid length");
    //     mac.update(data);
    //     mac.finalize().into_bytes().to_vec()
    // }

    let mut result = match mode {
        // Mode::Sha1 => hmac_inner::<Hmac<Sha1>>(key, data),
        // Mode::Sha256 => hmac_inner::<Hmac<Sha256>>(key, data),
        // Mode::Sha384 => hmac_inner::<Hmac<Sha384>>(key, data),
        // Mode::Sha512 => hmac_inner::<Hmac<Sha512>>(key, data),
        Mode::Blake2s => {
            let mut mac = HMACBlake2s::new_varkey(key).unwrap();
            mac.update(data);
            mac.finalize().into_bytes().to_vec()
        }
        _ => { panic!("unsupported hmac mode") }
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

#[verifier(external_body)]
pub fn blake2s(input: &[u8]) -> (res: Vec<u8>) {
    use blake2::Digest;
    let mut hsh = Blake2s::new();
    hsh.update(input);
    hsh.finalize().to_vec()
}

#[test]
fn test_owl_blake2s() {
    let input = b"Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s";
    let expected = [
        0x60, 0xe2, 0x6d, 0xae, 0xf3, 0x27, 0xef, 0xc0, 0x2e, 0xc3, 0x35, 0xe2, 0xa0, 0x25, 0xd2, 0xd0,
        0x16, 0xeb, 0x42, 0x06, 0xf8, 0x72, 0x77, 0xf5, 0x2d, 0x38, 0xd1, 0x98, 0x8b, 0x78, 0xcd, 0x36,
    ];
    dbg!(hex::encode(input));
    let actual = blake2s(input);
    assert_eq!(actual, expected);
}

} // verus!
