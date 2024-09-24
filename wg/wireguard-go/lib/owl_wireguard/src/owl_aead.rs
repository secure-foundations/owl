use crate::owl_util::gen_rand_bytes;
use aead::{Aead, AeadInPlace, NewAead, Nonce, Payload};
use aes_gcm::{Aes128Gcm, Aes256Gcm, KeyInit};
use chacha20poly1305::ChaCha20Poly1305;
use vstd::prelude::*;
use generic_array::*;

#[cfg(not(feature = "nonverif-crypto"))]
use libcrux::{aead::*, digest, drbg};

const USE_BORINGSSL: bool = true;


verus! {

#[derive(Clone, Copy)]
pub enum Mode {
    Aes128Gcm,
    Aes256Gcm,
    Chacha20Poly1305,
}

#[inline]
pub open const spec fn spec_key_size(mode: Mode) -> usize {
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
pub open const spec fn spec_tag_size(mode: Mode) -> usize {
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
pub open const spec fn spec_nonce_size(mode: Mode) -> usize {
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

#[derive(Clone, Copy, Debug)]
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

#[cfg(not(feature = "nonverif-crypto"))]
#[inline]
#[verifier(external)]
pub fn crux_alg_of_mode(alg : Mode) -> Algorithm {
    match alg {
        Mode::Aes128Gcm => Algorithm::Aes128Gcm,
        Mode::Aes256Gcm => Algorithm::Aes256Gcm,
        Mode::Chacha20Poly1305 => Algorithm::Chacha20Poly1305
    }
}

// #[verifier(external_body)]
// pub fn encrypt_inplace(
//     alg: Mode,
//     k: &[u8],
//     msg: &mut [u8],
//     iv: &[u8],
//     aad: &Aad,
// ) -> Result<(), Error> {
//     // dbg!(hex::encode(&k));
//     // dbg!(hex::encode(&iv));
//     // dbg!(hex::encode(&msg));
//     // dbg!(hex::encode(&aad));
//     if USE_BORINGSSL {
//         use ring::aead::{Aad, LessSafeKey, Nonce as RingAeadNonce, UnboundKey, CHACHA20_POLY1305};
//         use std::convert::TryInto;

//         let key = LessSafeKey::new(
//             UnboundKey::new(&CHACHA20_POLY1305, &k).unwrap(),
//         );
//         let nonce = RingAeadNonce::assume_unique_for_key(iv.try_into().unwrap());
//         let aad_ring = Aad::from(aad);

//         let tag_offset = msg.len() - 16;
//         let tag = key.seal_in_place_separate_tag(nonce, aad_ring, &mut msg[..tag_offset]).unwrap();
//         msg[tag_offset..].copy_from_slice(tag.as_ref());
//         // dbg!(hex::encode(&msg));
//         Ok(())
//     } else {
//         unimplemented!()
//         // match alg {
//         //     Mode::Chacha20Poly1305 => {
//         //         let r = ChaCha20Poly1305::new(GenericArray::from_slice(k))
//         //         .encrypt(iv.into(), Payload { msg: msg, aad: aad })
//         //         .map_err(|_| Error::Encrypting);
//         //         // dbg!(r.clone().map(|v| hex::encode(&v)));
//         //         r
//         //     }
//         //     _ => panic!("unsupported aead mode"),
//         // }    
//     }
// }

#[verifier(external_body)]
pub fn encrypt_combined_into(
    alg: Mode,
    k: &[u8],
    msg: &[u8],
    iv: &[u8],
    aad: &Aad,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<(), Error> {
    // dbg!(hex::encode(&k));
    // dbg!(hex::encode(&iv));
    // dbg!(hex::encode(&msg));
    // dbg!(hex::encode(&aad));
    data[pos..pos + msg.len()].copy_from_slice(msg);

    #[cfg(feature="nonverif-crypto")]
    {
        if USE_BORINGSSL {
            use ring::aead::{Aad, LessSafeKey, Nonce as RingAeadNonce, UnboundKey, CHACHA20_POLY1305};
            use std::convert::TryInto;

            let key = LessSafeKey::new(
                UnboundKey::new(&CHACHA20_POLY1305, &k).unwrap(),
            );
            let tmp = iv.try_into().unwrap();
            let nonce = RingAeadNonce::assume_unique_for_key(tmp);
            let aad_ring = Aad::from(aad);
            // let mut ctxt = Vec::with_capacity(msg.len() + tag_size(alg)); //msg.to_vec();
            // ctxt.extend_from_slice(msg);

            let tag = key.seal_in_place_separate_tag(nonce, aad_ring, &mut data[pos..pos + msg.len()]).unwrap();
            // println!("data: {}", hex::encode(data.as_slice()));
            data[pos + msg.len()..pos + msg.len() + tag.as_ref().len()].copy_from_slice(&tag.as_ref());
            Ok(())
        } else {
            {
                match alg {
                    Mode::Chacha20Poly1305 => {
                        let tag = ChaCha20Poly1305::new(GenericArray::from_slice(k))
                        .encrypt_in_place_detached(iv.into(), aad, &mut data[pos..pos + msg.len()])
                        .map_err(|_| Error::Encrypting)?;
                        // dbg!(r.clone().map(|v| hex::encode(&v)));
                        data[pos + msg.len()..pos + msg.len() + tag.len()].copy_from_slice(&tag[..]);
                        Ok(())
                    }
                    _ => panic!("unsupported aead mode"),
                }
            }
        }
    }

    #[cfg(not(feature="nonverif-crypto"))]
    {
        let crux_alg = crux_alg_of_mode(alg);
        let key = Key::from_slice(crux_alg, k).map_err(|_| Error::InvalidInit)?;
        let iv = Iv::new(iv).map_err(|_| Error::InvalidInit)?;
        let tag = libcrux::aead::encrypt(&key, &mut data[pos..pos + msg.len()], iv, &aad).map_err(|_| Error::Encrypting)?;
        data[pos + msg.len()..pos + msg.len() + tag.as_ref().len()].copy_from_slice(tag.as_ref());
        Ok(())  
    }
}

#[verifier(external_body)]
pub fn encrypt_combined(
    alg: Mode,
    k: &[u8],
    msg: &[u8],
    iv: &[u8],
    aad: &Aad,
) -> Result<Vec<u8>, Error> {
    // dbg!(hex::encode(&k));
    // dbg!(hex::encode(&iv));
    // dbg!(hex::encode(&msg));
    // dbg!(hex::encode(&aad));
    #[cfg(feature="nonverif-crypto")]
    {
        if USE_BORINGSSL {
            use ring::aead::{Aad, LessSafeKey, Nonce as RingAeadNonce, UnboundKey, CHACHA20_POLY1305};
            use std::convert::TryInto;

            let key = LessSafeKey::new(
                UnboundKey::new(&CHACHA20_POLY1305, &k).unwrap(),
            );
            let tmp = iv.try_into().unwrap();
            let nonce = RingAeadNonce::assume_unique_for_key(tmp);
            let aad_ring = Aad::from(aad);
            let mut ctxt = Vec::with_capacity(msg.len() + tag_size(alg)); //msg.to_vec();
            ctxt.extend_from_slice(msg);

            key.seal_in_place_append_tag(nonce, aad_ring, &mut ctxt).unwrap();
            Ok(ctxt)
        } else {
            match alg {
                Mode::Chacha20Poly1305 => {
                    let r = ChaCha20Poly1305::new(GenericArray::from_slice(k))
                    .encrypt(iv.into(), Payload { msg: msg, aad: aad })
                    .map_err(|_| Error::Encrypting);
                    // dbg!(r.clone().map(|v| hex::encode(&v)));
                    r
                }
                _ => panic!("unsupported aead mode"),
            }    
        }
    }
    #[cfg(not(feature = "nonverif-crypto"))]
    {
        let crux_alg = crux_alg_of_mode(alg);
        let key = Key::from_slice(crux_alg, k).map_err(|_| Error::InvalidInit)?;
        let iv = Iv::new(iv).map_err(|_| Error::InvalidInit)?;
        let (tag, mut ctxt) = libcrux::aead::encrypt_detached(&key, msg, iv, &aad).map_err(|_| Error::Encrypting)?;
        ctxt.extend(tag.as_ref());
        Ok(ctxt)
    }


    // check lengths
    // if k.len() != key_size(alg) {
    //     return Err(Error::InvalidKeySize);
    // }
    // if iv.len() != nonce_size(alg) {
    //     return Err(Error::InvalidNonce);
    // }

    // #[verifier(external_body)]
    // fn encrypt_inner<C: Aead + KeyInit>(
    //     k: &[u8],
    //     msg: &[u8],
    //     iv: &[u8],
    //     aad: &Aad,
    // ) -> Result<Vec<u8>, Error> {
    //     let cipher = match C::new_from_slice(k) {
    //         Ok(c) => c,
    //         Err(_) => {
    //             return Err(Error::InvalidInit);
    //         }
    //     };

    //     let nonce = <Nonce<C>>::from_slice(iv);
    //     let plaintext = Payload { msg: msg, aad: aad };

    //     let ctxt = match cipher.encrypt(nonce, plaintext) {
    //         Ok(v) => v,
    //         Err(_) => {
    //             return Err(Error::Encrypting);
    //         }
    //     };
    //     return Ok(ctxt);
    // }

    // return match alg {
    //     Mode::Aes128Gcm => encrypt_inner::<Aes128Gcm>(k, msg, iv, aad),
    //     Mode::Aes256Gcm => encrypt_inner::<Aes256Gcm>(k, msg, iv, aad),
    //     Mode::Chacha20Poly1305 => encrypt_inner::<ChaCha20Poly1305>(k, msg, iv, aad),
    // };
}

#[verifier(external_body)]
pub fn encrypt(
    alg: Mode,
    k: &[u8],
    msg: &[u8],
    iv: &[u8],
    aad: &Aad,
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let mut ctxt_tag = encrypt_combined(alg, k, msg, iv, aad)?;

    if ctxt_tag.len() <= tag_size(alg) {
        return Err(Error::Encrypting);
    }

    let tag = ctxt_tag.split_off(ctxt_tag.len() - tag_size(alg));
    return Ok((ctxt_tag, tag));
}

#[verifier(external_body)]
pub fn decrypt(
    alg: Mode,
    k: &[u8],
    ctxt: &[u8],
    tag: &[u8],
    iv: &[u8],
    aad: &Aad,
) -> Result<Vec<u8>, Error> {
    unimplemented!()
    // // check lengths
    // if k.len() != key_size(alg) {
    //     return Err(Error::InvalidKeySize);
    // }
    // if iv.len() != nonce_size(alg) {
    //     return Err(Error::InvalidNonce);
    // }
    // if tag.len() != tag_size(alg) {
    //     return Err(Error::InvalidTagSize);
    // }

    // #[verifier(external_body)]
    // fn decrypt_inner<C: Aead + KeyInit>(
    //     k: &[u8],
    //     ctxt: &[u8],
    //     tag: &[u8],
    //     iv: &[u8],
    //     aad: &Aad,
    // ) -> Result<Vec<u8>, Error> {
    //     let cipher = match C::new_from_slice(k) {
    //         Ok(c) => c,
    //         Err(_) => {
    //             return Err(Error::InvalidInit);
    //         }
    //     };

    //     let nonce = <Nonce<C>>::from_slice(iv);
    //     let ctxt_tag = &[ctxt, tag].concat();
    //     let ciphertext = Payload {
    //         msg: ctxt_tag,
    //         aad: aad,
    //     };

    //     let ctxt = match cipher.decrypt(nonce, ciphertext) {
    //         Ok(v) => v,
    //         Err(_) => {
    //             return Err(Error::Decrypting);
    //         }
    //     };
    //     return Ok(ctxt);
    // }

    // return match alg {
    //     Mode::Aes128Gcm => decrypt_inner::<Aes128Gcm>(k, ctxt, tag, iv, aad),
    //     Mode::Aes256Gcm => decrypt_inner::<Aes256Gcm>(k, ctxt, tag, iv, aad),
    //     Mode::Chacha20Poly1305 => decrypt_inner::<ChaCha20Poly1305>(k, ctxt, tag, iv, aad),
    // };
}

#[verifier(external_body)]
pub fn decrypt_combined(
    alg: Mode,
    k: &[u8],
    ctxt: &[u8],
    iv: &[u8],
    aad: &Aad,
) -> Result<Vec<u8>, Error> {
    // dbg!(hex::encode(&k));
    // dbg!(hex::encode(&iv));
    // dbg!(hex::encode(&ctxt));
    // dbg!(hex::encode(&aad));
    #[cfg(feature="nonverif-crypto")]
    {
        if USE_BORINGSSL {
            use ring::aead::{Aad, LessSafeKey, Nonce as RingAeadNonce, UnboundKey, CHACHA20_POLY1305};
            use std::convert::TryInto;

            let key = LessSafeKey::new(
                UnboundKey::new(&CHACHA20_POLY1305, &k).unwrap(),
            );
            let nonce = RingAeadNonce::assume_unique_for_key(iv.try_into().unwrap());
            let aad_ring = Aad::from(aad);
            let mut ptxt = ctxt.to_vec();

            let ptxt = key.open_in_place(nonce, aad_ring, &mut ptxt).unwrap();
            // dbg!(hex::encode(&ptxt));
            Ok(ptxt.to_vec())
        } else {
            match alg {
                Mode::Chacha20Poly1305 => {
                    let r = ChaCha20Poly1305::new(GenericArray::from_slice(k))
                    .decrypt(iv.into(), Payload { msg: ctxt, aad: aad })
                    .map_err(|e| { dbg!(e); Error::Decrypting });
                    // dbg!(r.clone().map(|v| hex::encode(&v)));
                    r
                },
                _ => panic!("unsupported aead mode"),
            }
        }
    }

    #[cfg(not(feature="nonverif-crypto"))]
    {
        let msg_len = ctxt.len() - tag_size(alg);
        let crux_alg = crux_alg_of_mode(alg);
        let key = Key::from_slice(crux_alg, k).map_err(|_| Error::InvalidInit)?;
        let iv = Iv::new(iv).map_err(|_| Error::InvalidInit)?;
        let tag = Tag::from_slice(&ctxt[msg_len..]).map_err(|_| Error::InvalidInit)?;
        let ptxt = libcrux::aead::decrypt_detached(&key, &ctxt[..msg_len], iv, &aad, &tag).map_err(|_| Error::Decrypting)?;
        Ok(ptxt)
    }
    // if ctxt.len() < tag_size(alg) {
    //     return Err(Error::InvalidTagSize);
    // }
    // let msg_len = ctxt.len() - tag_size(alg);
    // let tag = &ctxt[msg_len..];
    // let ctxt = &ctxt[..msg_len];
    // return decrypt(alg, k, ctxt, tag, iv, aad);
}

} // verus!
