#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

pub use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct msg {
    pub ret_addr: String,
    pub payload: Vec<u8>
}

pub fn serialize_msg(l: &msg) -> Vec<u8> {
    serde_json::to_vec(&l).expect("Can't serialize msg")
}
pub fn deserialize_msg<'a>(s: &'a [u8]) -> msg {
    serde_json::from_slice(s).expect("Can't deserialize msg")
}

#[derive(Debug)]
pub enum OwlError {
    IntegerOverflow,
}
