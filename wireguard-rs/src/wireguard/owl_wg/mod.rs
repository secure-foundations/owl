#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

mod speclib;
pub mod execlib; // pub for testing
mod owl_aead;
mod owl_dhke;
mod owl_hkdf;
mod owl_hmac;
mod owl_pke;
mod owl_util;
mod deep_view;
mod parse_serialize;
pub mod owl_wireguard;


use vstd::prelude::*;

verus! {

pub open const spec fn CIPHER() -> owl_aead::Mode {
    owl_aead::Mode::Chacha20Poly1305
}

pub const fn cipher() -> (r: owl_aead::Mode)
    ensures
        r == CIPHER(),
{
    owl_aead::Mode::Chacha20Poly1305
}

pub open const spec fn KEY_SIZE() -> usize {
    owl_aead::spec_key_size(CIPHER())
}

pub const fn key_size() -> (r: usize)
    ensures
        r == KEY_SIZE(),
{
    owl_aead::key_size(cipher())
}

pub open const spec fn TAG_SIZE() -> usize {
    owl_aead::spec_tag_size(CIPHER())
}

pub const fn tag_size() -> (r: usize)
    ensures
        r == TAG_SIZE(),
{
    owl_aead::tag_size(cipher())
}

pub open const spec fn NONCE_SIZE() -> usize {
    owl_aead::spec_nonce_size(CIPHER())
}

pub const fn nonce_size() -> (r: usize)
    ensures
        r == NONCE_SIZE(),
{
    owl_aead::nonce_size(cipher())
}

pub open const spec fn HMAC_MODE() -> owl_hmac::Mode {
    owl_hmac::Mode::Blake2s
}

pub const fn hmac_mode() -> (r: owl_hmac::Mode)
    ensures
        r == HMAC_MODE(),
{
    owl_hmac::Mode::Blake2s
}

pub open const spec fn MACKEY_SIZE() -> usize {
    owl_hmac::spec_key_size(HMAC_MODE())
}

pub const fn mackey_size() -> (r: usize)
    ensures
        r == MACKEY_SIZE(),
{
    owl_hmac::key_size(hmac_mode())
}

#[derive(Debug)]
pub enum OwlError {
    IntegerOverflow,
}

}