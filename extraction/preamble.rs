#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]

pub use vstd::{modes::*, prelude::*, seq::*, string::*};
pub mod speclib;
pub use crate::speclib::{*, itree::*};
pub mod execlib;
pub use crate::execlib::{*};
pub mod owl_aead;
pub mod owl_dhke;
pub mod owl_hkdf;
pub mod owl_hmac;
pub mod owl_pke;
pub mod owl_util;
pub use parsley::{
    *,
    properties::*,
    regular::*,
    regular::builder::*,
    regular::bytes::*,
    regular::bytes_const::*,
    regular::choice::*,
    regular::tail::*,
    regular::uints::*,
    utils::*,
};

pub use extraction_lib::*;
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

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct TcpListenerWrapper ( std::net::TcpListener );

#[verifier(external_type_specification)]
pub struct OwlErrorWrapper ( OwlError );


#[verifier(external_body)]
pub fn owl_output<A>(Tracked(t): Tracked<&mut ITreeToken<A,Endpoint>>, x: &[u8], dest_addr: &StrSlice, ret_addr: &StrSlice)
    requires old(t).view().is_output(x.view(), endpoint_of_addr(dest_addr.view()))
    ensures  t.view() == old(t).view().give_output()
{
    let msg = msg { ret_addr: std::string::String::from(ret_addr.into_rust_str()), payload: std::vec::Vec::from(x) };
    let serialized = serialize_msg(&msg);
    let mut stream = TcpStream::connect(dest_addr.into_rust_str()).unwrap();
    stream.write_all(&serialized).unwrap();
    stream.flush().unwrap();
}

#[verifier(external_body)]
pub fn owl_input<A>(Tracked(t): Tracked<&mut ITreeToken<A,Endpoint>>, listener: &TcpListener) -> (ie:(Vec<u8>, String))
    requires old(t).view().is_input()
    ensures  t.view() == old(t).view().take_input(ie.0.view(), endpoint_of_addr(ie.1.view()))
{
    let (mut stream, _addr) = listener.accept().unwrap();
    let mut reader = io::BufReader::new(&mut stream);
    let received: std::vec::Vec<u8> = reader.fill_buf().unwrap().to_vec();
    reader.consume(received.len());
    let msg : msg = deserialize_msg(&received);
    (msg.payload, String::from_rust_string(msg.ret_addr))
}

#[verifier(external_body)]
pub fn owl_sample<A>(Tracked(t): Tracked<&mut ITreeToken<A,Endpoint>>, n: usize) -> (res:Vec<u8>)
    requires old(t).view().is_sample(n)
    ensures  t.view() == old(t).view().get_sample(res.view())
{
    owl_util::gen_rand_bytes(n)
}

// for debugging purposes, not used by the compiler
#[verifier(external_body)]
pub fn debug_print_bytes(x: &[u8]) {
    println!("debug_print_bytes: {:?}", x);
}

} // verus!
