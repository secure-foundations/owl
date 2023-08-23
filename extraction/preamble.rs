#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

pub use vstd::{modes::*, prelude::*, seq::*, slice::*, string::*, *};
pub mod speclib;
#[macro_use]
pub use crate::speclib::{*, itree::*};
pub mod execlib;
#[macro_use]
pub use crate::execlib::{*};
pub mod owl_aead;
pub mod owl_dhke;
pub mod owl_hkdf;
pub mod owl_hmac;
pub mod owl_pke;
pub mod owl_util;

pub use serde::{Deserialize, Serialize};
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
trait OwlOps {
    fn owl_enc(&self, key: &[u8]) -> Vec<u8>;
    fn owl_dec(&self, key: &[u8]) -> Option<Vec<u8>>;
    fn owl_length(&self) -> usize;
    fn owl_mac(&self, key: &[u8]) -> Vec<u8>;
    fn owl_mac_vrfy(&self, key: &[u8], value: &[u8]) -> Option<Vec<u8>>;
    fn owl_pkenc(&self, pubkey: &[u8]) -> Vec<u8>;
    fn owl_pkdec(&self, privkey: &[u8]) -> Vec<u8>;
    fn owl_sign(&self, privkey: &[u8]) -> Vec<u8>;
    fn owl_vrfy(&self, pubkey: &[u8], signature: &[u8]) -> Option<Vec<u8>>;
    fn owl_dh_combine(&self, others_pk: &[u8]) -> Vec<u8>;
    fn owl_dhpk(&self) -> Vec<u8>;
    fn owl_extract_expand_to_len(&self, salt: &[u8], len: usize) -> Vec<u8>;
    fn owl_xor(&self, other: &[u8]) -> Vec<u8>;
}
// impl OwlOps for &[u8] {
//     #[verifier(external_body)] fn owl_enc(&self, key: &[u8]) -> Vec<u8> {
//         match owl_aead::encrypt_combined(cipher(), &key[..key_size()], self, &key[key_size()..], &[]) {
//             Ok(c) => c,
//             Err(e) => {
//                 // dbg!(e);
//                 vec![]
//             }
//         }
//     }
//     #[verifier(external_body)] fn owl_dec(&self, key: &[u8]) -> Option<Vec<u8>> {
//         match owl_aead::decrypt_combined(cipher(), &key[..key_size()], self, &key[key_size()..], &[]) {
//             Ok(p) => Some(p),
//             Err(e) => {
//                 // dbg!(e);
//                 None
//             }
//         }
//     }
//     #[verifier(external_body)]
//     fn owl_length(&self) -> usize {
//         self.len()
//     }
//     fn owl_mac(&self, key: &[u8]) -> Vec<u8> {
//         owl_hmac::hmac(hmac_mode(), key, self, None)
//     }
//     #[verifier(external_body)]
//     fn owl_mac_vrfy(&self, key: &[u8], value: &[u8]) -> Option<Vec<u8>> {
//         if owl_hmac::verify(hmac_mode(), key, self, value, None) {
//             Some(self.to_vec())
//         } else {
//             None
//         }
//     }
//     fn owl_pkenc(&self, pubkey: &[u8]) -> Vec<u8> {
//         owl_pke::encrypt(&pubkey, self)
//     }
//     fn owl_pkdec(&self, privkey: &[u8]) -> Vec<u8> {
//         owl_pke::decrypt(&privkey, self)
//     }
//     fn owl_sign(&self, privkey: &[u8]) -> Vec<u8> {
//         owl_pke::sign(&privkey, self)
//     }
//     #[verifier(external_body)]
//     fn owl_vrfy(&self, pubkey: &[u8], signature: &[u8]) -> Option<Vec<u8>> {
//         if owl_pke::verify(&pubkey, &signature, self) {
//             Some(self.to_vec())
//         } else {
//             None
//         }
//     }
//     fn owl_dh_combine(&self, others_pk: &[u8]) -> Vec<u8> {
//         owl_dhke::ecdh_combine(self, &others_pk)
//     }
//     fn owl_dhpk(&self) -> Vec<u8> {
//         owl_dhke::ecdh_dhpk(self)
//     }
//     fn owl_extract_expand_to_len(&self, salt: &[u8], len: usize) -> Vec<u8> {
//         owl_hkdf::extract_expand_to_len(self, salt, len)
//     }
//     #[verifier(external_body)]
//     fn owl_xor(&self, other: &[u8]) -> Vec<u8> {
//         {
//             let c: Vec<u8> = self.iter().zip(other).map(|(x, y)| x ^ y).collect();
//             c
//         }
//     }
// }

// #[derive(Serialize, Deserialize, Debug)] // TODO incorporate real parsing/marshaling
// pub struct msg {
//     ret_addr: std::string::String,
//     payload: std::vec::Vec<u8>
// }

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct TcpListenerWrapper ( std::net::TcpListener );

#[verifier(external_body)]
pub fn owl_output<A>(t: &mut Tracked<ITreeToken<A,Endpoint>>, x: &[u8], dest_addr: &StrSlice, ret_addr: &StrSlice)
    requires old(t)@@.is_output(x@, endpoint_of_addr(dest_addr.view()))
    ensures  t@@ === old(t)@@.give_output()
{
    // let msg = msg { ret_addr: std::string::String::from(ret_addr.into_rust_str()), payload: std::vec::Vec::from(x) };
    // let serialized = serde_json::to_vec(&msg).unwrap();
    let serialized = x.to_vec();
    let mut stream = TcpStream::connect(dest_addr.into_rust_str()).unwrap();
    stream.write_all(&serialized).unwrap();
    stream.flush().unwrap();
    // todo!()
}

#[verifier(external_body)]
pub fn owl_input<A>(t: &mut Tracked<ITreeToken<A,Endpoint>>, listener: &TcpListener) -> (ie:(Vec<u8>, String))
    requires old(t)@@.is_input()
    ensures  t@@ === old(t)@@.take_input(ie.0@, endpoint_of_addr(ie.1.view()))
{
    let (mut stream, _addr) = listener.accept().unwrap();
    let mut reader = io::BufReader::new(&mut stream);
    let received: std::vec::Vec<u8> = reader.fill_buf().unwrap().to_vec();
    reader.consume(received.len());
    // let msg : msg = serde_json::from_slice(&received).expect("Couldn't parse input");
    // (Vec { vec: msg.payload }, String::from_rust_string(msg.ret_addr))
    // todo!()
    (received, String::from_str(new_strlit(""))) // TODO proper endpoint variable handling
}

#[verifier(external_body)]
pub fn owl_sample<A>(t: &mut Tracked<ITreeToken<A,Endpoint>>, n: usize) -> (res:Vec<u8>)
    requires old(t)@@.is_sample(n)
    ensures  t@@ === old(t)@@.get_sample(res@)
{
    owl_util::gen_rand_bytes(n)
}

// pub fn get_num_from_cmdline(loc_prompt: &str) -> usize {
//     let mut input_text = std::string::String::new();
//     println!("Enter number of {loc_prompt} to generate: ");
//     io::stdin()
//     .read_line(&mut input_text)
//     .expect("failed to read from stdin");
//     let n = input_text.trim().parse::<usize>().expect("not an int");
//     n
// }
} // verus!
