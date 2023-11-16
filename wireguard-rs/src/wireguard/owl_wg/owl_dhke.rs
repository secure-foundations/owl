// use p256::{
//     ecdh::diffie_hellman,
//     pkcs8::{DecodePublicKey, EncodePublicKey},
//     PublicKey, SecretKey,
// };
use x25519_dalek::{PublicKey, SharedSecret, StaticSecret};
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub fn gen_ecdh_key_pair() -> (_: (Vec<u8>, Vec<u8>)) {
    unimplemented!()
    // let mut rng = rand::thread_rng();
    // let secret = SecretKey::random(&mut rng);
    // let sk_bytes = secret.to_sec1_der().unwrap().to_vec();
    // let pk_bytes = secret
    //     .public_key()
    //     .to_public_key_der()
    //     .unwrap()
    //     .as_bytes()
    //     .to_vec();
    // (sk_bytes, pk_bytes)
}

#[verifier(external_body)]
pub fn ecdh_dhpk(sk: &[u8]) -> Vec<u8> {
    use std::convert::TryInto;
    let sk_length_checked: [u8; 32] = sk.try_into().unwrap();
    let sk_decoded = StaticSecret::from(sk_length_checked);
    let pk = PublicKey::from(&sk_decoded);
    pk.to_bytes().to_vec()
}

#[verifier(external_body)]
pub fn ecdh_combine(sk: &[u8], others_pk: &[u8]) -> Vec<u8> {
    use std::convert::TryInto;
    let sk_length_checked: [u8; 32] = sk.try_into().unwrap();
    let pk_length_checked: [u8; 32] = others_pk.try_into().unwrap();
    let sk_decoded = StaticSecret::from(sk_length_checked);
    let pk_decoded = PublicKey::from(pk_length_checked);
    let shared_secret = sk_decoded.diffie_hellman(&pk_decoded);
    shared_secret.as_bytes().to_vec()
}

} // verus!