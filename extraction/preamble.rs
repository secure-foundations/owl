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
pub mod deep_view;
pub use crate::deep_view::{*};
pub mod parse_serialize;

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
// pub use crate::parse_serialize::View as _;

verus! {
pub const CIPHER: owl_aead::Mode = crate::owl_aead::Mode::Chacha20Poly1305;
pub const ENCKEY_SIZE: usize = owl_aead::spec_key_size(CIPHER);
pub const TAG_SIZE: usize = owl_aead::spec_tag_size(CIPHER);
pub const NONCE_SIZE: usize = owl_aead::spec_nonce_size(CIPHER);
pub const HMAC_MODE: owl_hmac::Mode = crate::owl_hmac::Mode::Sha512;
pub const MACKEY_SIZE: usize = owl_hmac::spec_key_size(HMAC_MODE);
pub const KDFKEY_SIZE: usize = owl_hkdf::spec_kdfkey_size();

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct TcpListenerWrapper ( std::net::TcpListener );

#[verifier(external_type_specification)]
pub struct OwlErrorWrapper ( OwlError );


#[verifier(external_body)]
pub fn owl_output<A>(Tracked(t): Tracked<&mut ITreeToken<A,Endpoint>>, x: &[u8], dest_addr: &StrSlice, ret_addr: &StrSlice)
    requires old(t).view().is_output(x.dview(), endpoint_of_addr(dest_addr.view()))
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
    ensures  t.view() == old(t).view().take_input(ie.0.dview(), endpoint_of_addr(ie.1.view()))
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
    ensures  t.view() == old(t).view().get_sample(res.dview())
{
    owl_util::gen_rand_bytes(n)
}

// for debugging purposes, not used by the compiler
#[verifier(external_body)]
pub fn debug_print_bytes(x: &[u8]) {
    println!("debug_print_bytes: {:?}", x);
}

pub fn ghost_unit() -> (res: Ghost<()>)
    ensures res == Ghost(())
{
    Ghost(())
}

} // verus!
