use vstd::{prelude::*, vec::*};
use crate::owl_util::gen_rand_bytes;
use aead::{Aead, Nonce, Payload};
use aes_gcm::{Aes128Gcm, Aes256Gcm, KeyInit};
use chacha20poly1305::ChaCha20Poly1305;

verus! {

// #[is_variant]
#[derive(Clone, Copy)]
pub enum Mode {
    Aes128Gcm,
    Aes256Gcm,
    Chacha20Poly1305,
}

#[inline]
pub open spec fn spec_key_size(mode: Mode) -> usize {
    match mode {
        Mode::Aes128Gcm => 16,
        Mode::Aes256Gcm => 32,
        Mode::Chacha20Poly1305 => 32,
    }
}

/// Get the key size of the `Mode` in bytes.
#[inline]
pub const fn key_size(mode: Mode) -> (u:usize)
    ensures u == spec_key_size(mode)
{
    match mode {
        Mode::Aes128Gcm => 16,
        Mode::Aes256Gcm => 32,
        Mode::Chacha20Poly1305 => 32,
    }
}

/// Generate a random key for cipher `mode`.
/// NB: uses the owl stdlib random number generator, not cryptographically secure!
#[inline]
pub fn gen_rand_key(mode: Mode) -> Vec<u8> {
    gen_rand_bytes(key_size(mode))
}

/// Get the tag size of the `Mode` in bytes.
#[inline]
pub open spec fn spec_tag_size(mode: Mode) -> usize {
    match mode {
        Mode::Aes128Gcm => 16,
        Mode::Aes256Gcm => 16,
        Mode::Chacha20Poly1305 => 16,
    }
}


/// Get the tag size of the `Mode` in bytes.
#[inline]
pub const fn tag_size(mode: Mode) -> (u:usize)
    ensures u == spec_tag_size(mode)
{
    match mode {
        Mode::Aes128Gcm => 16,
        Mode::Aes256Gcm => 16,
        Mode::Chacha20Poly1305 => 16,
    }
}

/// Generate a random tag for cipher `mode`.
/// NB: uses the owl stdlib random number generator, not cryptographically secure!
#[inline]
pub fn gen_rand_tag(mode: Mode) -> Vec<u8> {
    gen_rand_bytes(tag_size(mode))
}

/// Get the nonce size of the `Mode` in bytes.
#[inline]
pub open spec fn spec_nonce_size(mode: Mode) -> usize {
    match mode {
        Mode::Aes128Gcm => 12,
        Mode::Aes256Gcm => 12,
        Mode::Chacha20Poly1305 => 12,
    }
}

/// Get the nonce size of the `Mode` in bytes.
#[inline]
pub const fn nonce_size(mode: Mode) -> (u:usize)
    ensures u == spec_nonce_size(mode)
{
    match mode {
        Mode::Aes128Gcm => 12,
        Mode::Aes256Gcm => 12,
        Mode::Chacha20Poly1305 => 12,
    }
}

/// Generate a random nonce for cipher `mode`.
/// NB: uses the owl stdlib random number generator, not cryptographically secure!
#[inline]
pub fn gen_rand_nonce(mode: Mode) -> Vec<u8> {
    gen_rand_bytes(nonce_size(mode))
}

/// Generate a random (key | iv) byte string for cipher `mode`.
/// NB: uses the owl stdlib random number generator, not cryptographically secure!
#[inline]
pub fn gen_rand_key_iv(mode: Mode) -> Vec<u8> {
    gen_rand_bytes(key_size(mode) + nonce_size(mode))
}

#[derive(Clone)]
pub enum Error {
    InvalidInit,
    InvalidAlgorithm,
    InvalidCiphertext,
    InvalidNonce,
    UnsupportedConfig,
    Encrypting,
    Decrypting,
    InvalidKeySize,
    InvalidTagSize,
}

pub type Aad = [u8];
pub type Ciphertext = Vec<u8>;
pub type Tag = Vec<u8>;

#[verifier(external_body)]
pub fn encrypt_combined(
    alg: Mode,
    k: &[u8],
    msg: &[u8],
    iv: &[u8],
    //aad: &Aad,
) -> Result<Vec<u8>, Error> {
    // TODO handle AAD if needed
    let aad = &[];

    // check lengths
    if k.len() != key_size(alg) {
        return Err(Error::InvalidKeySize);
    }
    if iv.len() != nonce_size(alg) {
        return Err(Error::InvalidNonce);
    }

    #[verifier(external_body)]
    fn encrypt_inner<C: Aead + KeyInit>(
        k: &[u8],
        msg: &[u8],
        iv: &[u8],
        aad: &Aad,
    ) -> Result<Vec<u8>, Error> {
        let cipher = match C::new_from_slice(k) {
            std::result::Result::Ok(c) => c,
            std::result::Result::Err(_) => {
                return Err(Error::InvalidInit);
            }
        };

        let nonce = <Nonce<C>>::from_slice(iv);
        let plaintext = Payload { msg: msg, aad: aad };

        let ctxt = match cipher.encrypt(nonce, plaintext) {
            std::result::Result::Ok(v) => v,
            std::result::Result::Err(_) => {
                return Err(Error::Encrypting);
            }
        };
        return Ok(Vec{ vec: ctxt });
    }

    return match alg {
        Mode::Aes128Gcm => encrypt_inner::<Aes128Gcm>(k, msg, iv, aad),
        Mode::Aes256Gcm => encrypt_inner::<Aes256Gcm>(k, msg, iv, aad),
        Mode::Chacha20Poly1305 => encrypt_inner::<ChaCha20Poly1305>(k, msg, iv, aad),
    };
}

#[verifier(external_body)]
pub fn encrypt(
    alg: Mode,
    k: &[u8],
    msg: &[u8],
    iv: &[u8],
    // aad: &Aad,
) -> Result<(Ciphertext, Tag), Error> {
    let mut ctxt_tag = match encrypt_combined(alg, k, msg, iv) {
        Ok(c) => c,
        Err(e) => return Err(e),
    };

    if ctxt_tag.len() <= tag_size(alg) {
        return Err(Error::Encrypting);
    }

    let tag = Vec { vec: ctxt_tag.vec.split_off(ctxt_tag.len() - tag_size(alg)) };
    return Ok((ctxt_tag, tag));
}

#[verifier(external_body)]
pub fn decrypt(
    alg: Mode,
    k: &[u8],
    ctxt: &[u8],
    tag: &[u8],
    iv: &[u8],
    // aad: &Aad,
) -> Result<Vec<u8>, Error> {
    let aad = &[];

    // check lengths
    if k.len() != key_size(alg) {
        return Err(Error::InvalidKeySize);
    }
    if iv.len() != nonce_size(alg) {
        return Err(Error::InvalidNonce);
    }
    if tag.len() != tag_size(alg) {
        return Err(Error::InvalidTagSize);
    }

    #[verifier(external_body)]
    fn decrypt_inner<C: Aead + KeyInit>(
        k: &[u8],
        ctxt: &[u8],
        tag: &[u8],
        iv: &[u8],
        aad: &Aad,
    ) -> Result<Vec<u8>, Error> {
        let cipher = match C::new_from_slice(k) {
            std::result::Result::Ok(c) => c,
            std::result::Result::Err(_) => {
                return Err(Error::InvalidInit);
            }
        };

        let nonce = <Nonce<C>>::from_slice(iv);
        let ctxt_tag = &[ctxt, tag].concat();
        let ciphertext = Payload {
            msg: ctxt_tag,
            aad: aad,
        };

        let ctxt = match cipher.decrypt(nonce, ciphertext) {
            std::result::Result::Ok(v) => v,
            std::result::Result::Err(_) => {
                return Err(Error::Decrypting);
            }
        };
        return Ok(Vec { vec: ctxt });
    }

    return match alg {
        Mode::Aes128Gcm => decrypt_inner::<Aes128Gcm>(k, ctxt, tag, iv, aad),
        Mode::Aes256Gcm => decrypt_inner::<Aes256Gcm>(k, ctxt, tag, iv, aad),
        Mode::Chacha20Poly1305 => decrypt_inner::<ChaCha20Poly1305>(k, ctxt, tag, iv, aad),
    };
}

#[verifier(external_body)]
pub fn decrypt_combined(
    alg: Mode,
    k: &[u8],
    ctxt: &[u8],
    iv: &[u8],
    // aad: &Aad,
) -> Result<Vec<u8>, Error> {
    if ctxt.len() < tag_size(alg) {
        return Err(Error::InvalidTagSize);
    }
    let msg_len = ctxt.len() - tag_size(alg);
    let tag = &ctxt[msg_len..];
    let ctxt = &ctxt[..msg_len];
    return decrypt(alg, k, ctxt, tag, iv);
}
} // verus!