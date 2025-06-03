#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#[cfg_attr(verus_keep_ghost, forbid(unsafe_code))]

pub use vstd::{modes::*, prelude::*, seq::*, view::*};
pub mod speclib;
pub use crate::speclib::{*, itree::*};
pub mod execlib;
pub use crate::execlib::{*};
pub mod owl_const_bytes;
pub use crate::owl_const_bytes::*;
pub mod owl_aead;
pub mod owl_dhke;
pub mod owl_hkdf;
pub mod owl_hmac;
pub mod owl_pke;
pub mod owl_util;
pub use vest::{
    properties::*,
    regular::*,
    regular::builder::*,
    regular::bytes::*,
    regular::repetition::*,
    regular::tag::*,
    regular::sequence::*,
    regular::variant::*,
    regular::uints::*,
    utils::*,
};

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
pub spec const SPEC_CIPHER: owl_aead::Mode = crate::owl_aead::Mode::Chacha20Poly1305;
pub spec const SPEC_ENCKEY_SIZE: usize = owl_aead::spec_key_size(CIPHER);
pub spec const SPEC_TAG_SIZE: usize = owl_aead::spec_tag_size(CIPHER);
pub spec const SPEC_NONCE_SIZE: usize = owl_aead::spec_nonce_size(CIPHER);
pub spec const SPEC_HMAC_MODE: owl_hmac::Mode = crate::owl_hmac::Mode::Sha512;
pub spec const SPEC_MACKEY_SIZE: usize = owl_hmac::spec_key_size(HMAC_MODE);
pub spec const SPEC_KDFKEY_SIZE: usize = owl_hkdf::spec_kdfkey_size();
pub spec const SPEC_COUNTER_SIZE: usize = 8usize;
pub spec const SPEC_SIGNATURE_SIZE: usize = 64usize;
pub spec const SPEC_MACLEN_SIZE: usize = 16usize;    

#[verifier::when_used_as_spec(SPEC_CIPHER)]
pub exec const CIPHER: owl_aead::Mode ensures CIPHER == SPEC_CIPHER { crate::owl_aead::Mode::Chacha20Poly1305 }

#[verifier::when_used_as_spec(SPEC_ENCKEY_SIZE)]
pub exec const ENCKEY_SIZE: usize ensures ENCKEY_SIZE == SPEC_ENCKEY_SIZE { owl_aead::key_size(CIPHER) }

#[verifier::when_used_as_spec(SPEC_TAG_SIZE)]
pub exec const TAG_SIZE: usize ensures TAG_SIZE == SPEC_TAG_SIZE { owl_aead::tag_size(CIPHER) }

#[verifier::when_used_as_spec(SPEC_NONCE_SIZE)]
pub exec const NONCE_SIZE: usize ensures NONCE_SIZE == SPEC_NONCE_SIZE { owl_aead::nonce_size(CIPHER) }

#[verifier::when_used_as_spec(SPEC_HMAC_MODE)]
pub exec const HMAC_MODE: owl_hmac::Mode ensures HMAC_MODE == SPEC_HMAC_MODE { crate::owl_hmac::Mode::Sha512 }

#[verifier::when_used_as_spec(SPEC_MACKEY_SIZE)]
pub exec const MACKEY_SIZE: usize ensures MACKEY_SIZE == SPEC_MACKEY_SIZE { owl_hmac::key_size(HMAC_MODE) }

#[verifier::when_used_as_spec(SPEC_KDFKEY_SIZE)]
pub exec const KDFKEY_SIZE: usize ensures KDFKEY_SIZE == SPEC_KDFKEY_SIZE { owl_hkdf::kdfkey_size() }

#[verifier::when_used_as_spec(SPEC_COUNTER_SIZE)]
pub exec const COUNTER_SIZE: usize ensures COUNTER_SIZE == SPEC_COUNTER_SIZE { 8usize }

#[verifier::when_used_as_spec(SPEC_SIGNATURE_SIZE)]
pub exec const SIGNATURE_SIZE: usize ensures SIGNATURE_SIZE == SPEC_SIGNATURE_SIZE { 64usize }

#[verifier::when_used_as_spec(SPEC_MACLEN_SIZE)]
pub exec const MACLEN_SIZE: usize ensures MACLEN_SIZE == SPEC_MACLEN_SIZE { 16usize }

pub trait OwlEffects {
    fn owl_output<A>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
        x: &[u8],
        dest_addr: Option<&str>,
        ret_addr: &str,
    )
        requires
            old(t).view().is_output(
                x.view(),
                option_map(view_option(dest_addr), |a| endpoint_of_addr(a)),
            ),
        ensures
            t.view() == old(t).view().give_output(),
    ;

    fn owl_input<A>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
    ) -> (ie: (Vec<u8>, String))
        requires
            old(t).view().is_input(),
        ensures
            t.view() == old(t).view().take_input(ie.0.view(), endpoint_of_addr(ie.1.view())),
    ;

    fn owl_sample<A, 'a>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
        n: usize,
    ) -> (res: SecretBuf<'a>)
        requires
            old(t).view().is_sample(n),
        ensures
            t.view() == old(t).view().get_sample(res.view()),
            res.len_valid(),
    ;

    fn owl_output_serialize_fused<A, I: VestPublicInput, C: View + Combinator<I, Vec<u8>>>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
        comb: C,
        val: C::Type,
        dest_addr: Option<&str>,
        ret_addr: &str,
    ) where <C as View>::V: SecureSpecCombinator<Type = <C::Type as View>::V>
        requires
            comb@.spec_serialize(val.view()) matches Ok(b) ==> old(t).view().is_output(
                b,
                option_map(view_option(dest_addr), |a| endpoint_of_addr(a)),
            ),
        ensures
            t.view() == old(t).view().give_output(),
    ;
}


// for debugging purposes, not used by the compiler
#[verifier(external_body)]
pub fn debug_print_bytes(x: &[u8]) {
    println!("debug_print_bytes: {:?}", x);
}

#[derive(Debug)]
pub struct msg {
    pub ret_addr: String,
    pub payload: Vec<u8>
}

#[verifier(external_body)]
pub fn serialize_msg(l: &msg) -> Vec<u8> {
    unimplemented!()
    // serde_json::to_vec(&l).expect("Can't serialize msg")
}

#[verifier(external_body)]
pub fn deserialize_msg<'a>(s: &'a [u8]) -> msg {
    unimplemented!()
    // serde_json::from_slice(s).expect("Can't deserialize msg")
}

#[derive(Debug)]
pub enum OwlError {
    IntegerOverflow,
}

} // verus!
