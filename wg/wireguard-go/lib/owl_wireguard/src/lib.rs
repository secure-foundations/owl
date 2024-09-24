#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![feature(vec_into_raw_parts)]

mod speclib;
mod execlib; 
mod owl_aead;
mod owl_dhke;
mod owl_hkdf;
mod owl_hmac;
mod owl_pke;
mod owl_util;
mod owl_wireguard;

use vstd::prelude::*;
use std::slice;
// use std::{thread, time};

// #[no_mangle]
// pub extern "C" fn test(name: *const libc::c_char) {
//     let name_cstr = unsafe { CStr::from_ptr(name) };
//     let name = name_cstr.to_str().unwrap();
//     println!("Hello {}!", name);
//     let t = time::Duration::from_millis(100);
//     thread::sleep(t);
// }

#[no_mangle]
pub extern "C" fn wg_send(
    plaintext: *const u8,
    plaintext_len: usize,
    peer: u32,
    send_key: *const u8,
    send_key_len: usize,
    nonce: usize,
    obuf: *mut u8,
    obuf_len: usize,
) {
    let plaintext = unsafe { slice::from_raw_parts(plaintext, plaintext_len) };
    let send_key = unsafe { slice::from_raw_parts(send_key, send_key_len) };

    // obuf_len needs to be right!
    let mut obuf_vec = unsafe { Vec::from_raw_parts(obuf, obuf_len, obuf_len) };
    // let mut local_obuf = vec![3; obuf_len];

    // obuf_vec.clear();
    // println!("owl obuf start:\n\t{}", hex::encode(&obuf_vec));
    // println!("plaintext_len:\n\t{}", plaintext.len());

    let cfg = owl_wireguard::cfg_Initiator {
        owl_S_init: vec![],
        owl_E_init: vec![],
        pk_owl_S_resp: vec![],
        pk_owl_S_init: vec![],
        pk_owl_E_resp: vec![],
        pk_owl_E_init: vec![],
        salt: vec![],
    };
    let mut state = owl_wireguard::state_Initiator::init_state_Initiator();
    state.owl_N_init_send = nonce;

    cfg.owl_transp_send_init_wrapper(
        &mut state, 
        plaintext, 
        &mut obuf_vec, 
        peer.to_le_bytes().as_slice(), 
        [].as_slice(), 
        send_key, 
        [].as_slice()
    );
    // println!("owl output:\n\t{}", hex::encode(&local_obuf));

    let (ptr, _, _) = obuf_vec.into_raw_parts();

    // if !obuf.is_null() && obuf_len > 0 {
    //     let obuf_slice = unsafe { std::slice::from_raw_parts_mut(obuf, obuf_len) };
    //     obuf_slice.copy_from_slice(&local_obuf);
    // } else {
    //     panic!("bad obuf")
    // }
}

#[no_mangle]
pub extern "C" fn wg_recv(
    peer: u32,
    recv_key: *const u8,
    recv_key_len: usize,
    nonce: usize,
    buf: *mut u8,
    buf_len: usize,
) {
    let recv_key = unsafe { slice::from_raw_parts(recv_key, recv_key_len) };
    let mut buf = unsafe { slice::from_raw_parts_mut(buf, buf_len) };

    let cfg = owl_wireguard::cfg_Initiator {
        owl_S_init: vec![],
        owl_E_init: vec![],
        pk_owl_S_resp: vec![],
        pk_owl_S_init: vec![],
        pk_owl_E_resp: vec![],
        pk_owl_E_init: vec![],
        salt: vec![],
    };
    let mut state = owl_wireguard::state_Initiator::init_state_Initiator();
    state.owl_N_init_recv = nonce;

    // println!("buf: {}", hex::encode(&buf));

    let decrypt_opt = cfg.owl_transp_recv_init_wrapper(
        &mut state, 
        &mut buf, 
        [].as_slice(), 
        peer.to_le_bytes().as_slice(), 
        [].as_slice(),
        recv_key, 
    );

    match decrypt_opt {
        Some(plaintext) => {
            buf[16..(16+plaintext.as_slice().len())].copy_from_slice(&plaintext.as_slice());
        },
        None => {
            panic!("decryption failed");
        },
    };
}



verus! {

pub spec const SPEC_CIPHER: owl_aead::Mode = owl_aead::Mode::Chacha20Poly1305;

pub spec const SPEC_ENCKEY_SIZE: usize = owl_aead::spec_key_size(CIPHER);

pub spec const SPEC_TAG_SIZE: usize = owl_aead::spec_tag_size(CIPHER);

pub spec const SPEC_NONCE_SIZE: usize = 32;

pub spec const SPEC_HMAC_MODE: owl_hmac::Mode = owl_hmac::Mode::Sha512;

pub spec const SPEC_MACKEY_SIZE: usize = owl_hmac::spec_key_size(HMAC_MODE);

pub spec const SPEC_KDFKEY_SIZE: usize = owl_hkdf::spec_kdfkey_size();

#[verifier::when_used_as_spec(SPEC_CIPHER)]
pub exec const CIPHER: owl_aead::Mode
    ensures
        CIPHER == SPEC_CIPHER,
{
    owl_aead::Mode::Chacha20Poly1305
}

#[verifier::when_used_as_spec(SPEC_ENCKEY_SIZE)]
pub exec const ENCKEY_SIZE: usize
    ensures
        ENCKEY_SIZE == SPEC_ENCKEY_SIZE,
{
    owl_aead::key_size(CIPHER)
}

#[verifier::when_used_as_spec(SPEC_TAG_SIZE)]
pub exec const TAG_SIZE: usize
    ensures
        TAG_SIZE == SPEC_TAG_SIZE,
{
    owl_aead::tag_size(CIPHER)
}

#[verifier::when_used_as_spec(SPEC_NONCE_SIZE)]
pub exec const NONCE_SIZE: usize
    ensures
        NONCE_SIZE == SPEC_NONCE_SIZE,
{
    // owl_aead::nonce_size(CIPHER)
    32
}

#[verifier::when_used_as_spec(SPEC_HMAC_MODE)]
pub exec const HMAC_MODE: owl_hmac::Mode
    ensures
        HMAC_MODE == SPEC_HMAC_MODE,
{
    owl_hmac::Mode::Blake2s
}

#[verifier::when_used_as_spec(SPEC_MACKEY_SIZE)]
pub exec const MACKEY_SIZE: usize
    ensures
        MACKEY_SIZE == SPEC_MACKEY_SIZE,
{
    owl_hmac::key_size(HMAC_MODE)
}

#[verifier::when_used_as_spec(SPEC_KDFKEY_SIZE)]
pub exec const KDFKEY_SIZE: usize
    ensures
        KDFKEY_SIZE == SPEC_KDFKEY_SIZE,
{
    owl_hkdf::kdfkey_size()
}
    

#[derive(Debug)]
pub enum OwlError {
    IntegerOverflow,
}

}