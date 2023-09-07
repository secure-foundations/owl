pub use serde::{Deserialize, Serialize};

// // owl_util.rs
// pub use rand;

// // owl_aead.rs
// pub use aead;
// pub use aes_gcm;
// pub use chacha20poly1305;

// // owl_pke.rs
// pub use digest;
// pub use rsa;

// // owl_dhke.rs
// pub use p256;

// // owl_hkdf.rs
// pub use hkdf;
// pub use sha2;

// // owl_hmac.rs
// pub use crypto;
// // pub use digest;
// pub use hmac;
// pub use sha1;
// // pub use sha2;

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