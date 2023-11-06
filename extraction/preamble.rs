#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]

pub use vstd::{modes::*, prelude::*, seq::*, slice::*, string::*, *};
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

pub use extraction_lib::*;
pub use std::collections::HashMap;
pub use std::env;
pub use std::fs;
pub use std::io::{self, BufRead, Write};
pub use std::net::{SocketAddr, TcpListener, TcpStream, ToSocketAddrs};
pub use std::rc::Rc;
pub use std::str;
pub use std::thread;
pub use std::time::Duration;
pub use std::time::Instant;

verus! {
pub open const spec fn CIPHER() -> owl_aead::Mode { crate::owl_aead::Mode::Chacha20Poly1305 }
pub const fn cipher() -> (r:owl_aead::Mode) ensures r == CIPHER() { crate::owl_aead::Mode::Chacha20Poly1305 }
pub open const spec fn KEY_SIZE() -> usize { owl_aead::spec_key_size(CIPHER()) }
pub const fn key_size() -> (r:usize) ensures r == KEY_SIZE() { owl_aead::key_size(cipher()) }
pub open const spec fn TAG_SIZE() -> usize { owl_aead::spec_tag_size(CIPHER()) }
pub const fn tag_size() -> (r:usize) ensures r == TAG_SIZE() { owl_aead::tag_size(cipher()) }
pub open const spec fn NONCE_SIZE() -> usize { owl_aead::spec_nonce_size(CIPHER()) }
pub const fn nonce_size() -> (r:usize) ensures r == NONCE_SIZE() { owl_aead::nonce_size(cipher()) }
pub open const spec fn HMAC_MODE() -> owl_hmac::Mode { crate::owl_hmac::Mode::Sha512 }
pub const fn hmac_mode() -> (r:owl_hmac::Mode) ensures r == HMAC_MODE() { crate::owl_hmac::Mode::Sha512 }
pub open const spec fn MACKEY_SIZE() -> usize { owl_hmac::spec_key_size(HMAC_MODE()) }
pub const fn mackey_size() -> (r:usize) ensures r == MACKEY_SIZE() { owl_hmac::key_size(hmac_mode()) }


#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct TcpListenerWrapper ( std::net::TcpListener );

#[verifier(external_type_specification)]
pub struct OwlErrorWrapper ( OwlError );


#[verifier(external_body)]
pub fn owl_output<A>(Tracked(t): Tracked<&mut ITreeToken<A,Endpoint>>, x: &[u8], dest_addr: &StrSlice, ret_addr: &StrSlice)
    requires old(t)@.is_output(x@, endpoint_of_addr(dest_addr.view()))
    ensures  t@ == old(t)@.give_output()
{
    let msg = msg { ret_addr: std::string::String::from(ret_addr.into_rust_str()), payload: std::vec::Vec::from(x) };
    let serialized = serialize_msg(&msg);
    let mut stream = TcpStream::connect(dest_addr.into_rust_str()).unwrap();
    stream.write_all(&serialized).unwrap();
    stream.flush().unwrap();
}

#[verifier(external_body)]
pub fn owl_input<A>(Tracked(t): Tracked<&mut ITreeToken<A,Endpoint>>, listener: &TcpListener) -> (ie:(Vec<u8>, String))
    requires old(t)@.is_input()
    ensures  t@ == old(t)@.take_input(ie.0@, endpoint_of_addr(ie.1.view()))
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
    requires old(t)@.is_sample(n)
    ensures  t@ == old(t)@.get_sample(res@)
{
    owl_util::gen_rand_bytes(n)
}

} // verus!
