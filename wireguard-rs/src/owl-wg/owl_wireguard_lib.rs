// Extracted rust library code from file tests/wip/wireguard-full.owl:
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




#[derive(Serialize, Deserialize)]
pub struct cfg_Initiator_config {pub owl_S_init: Vec<u8>,
pub owl_E_init: Vec<u8>,
pub pk_owl_S_resp: Vec<u8>,
pub pk_owl_S_init: Vec<u8>,
pub pk_owl_E_resp: Vec<u8>,
pub pk_owl_E_init: Vec<u8>,
pub salt: Vec<u8>}
pub fn serialize_cfg_Initiator_config(l: &cfg_Initiator_config) -> String{
serde_json::to_string(&l).expect("Can't serialize cfg_Initiator_config")
}
pub fn deserialize_cfg_Initiator_config<'a>(s: &'a str) -> cfg_Initiator_config{
serde_json::from_str(s).expect("Can't deserialize cfg_Initiator_config")
}

#[derive(Serialize, Deserialize)]
pub struct cfg_Responder_config {pub owl_S_resp: Vec<u8>,
pub owl_E_resp: Vec<u8>,
pub pk_owl_S_resp: Vec<u8>,
pub pk_owl_S_init: Vec<u8>,
pub pk_owl_E_resp: Vec<u8>,
pub pk_owl_E_init: Vec<u8>,
pub salt: Vec<u8>}
pub fn serialize_cfg_Responder_config(l: &cfg_Responder_config) -> String{
serde_json::to_string(&l).expect("Can't serialize cfg_Responder_config")
}
pub fn deserialize_cfg_Responder_config<'a>(s: &'a str) -> cfg_Responder_config{
serde_json::from_str(s).expect("Can't deserialize cfg_Responder_config")
}

#[derive(Serialize, Deserialize)]
pub struct cfg_dummy_config {pub pk_owl_S_resp: Vec<u8>,
pub pk_owl_S_init: Vec<u8>,
pub pk_owl_E_resp: Vec<u8>,
pub pk_owl_E_init: Vec<u8>,
pub salt: Vec<u8>}
pub fn serialize_cfg_dummy_config(l: &cfg_dummy_config) -> String{
serde_json::to_string(&l).expect("Can't serialize cfg_dummy_config")
}
pub fn deserialize_cfg_dummy_config<'a>(s: &'a str) -> cfg_dummy_config{
serde_json::from_str(s).expect("Can't deserialize cfg_dummy_config")
}