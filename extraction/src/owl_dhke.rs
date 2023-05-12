use p256::{
    ecdh::diffie_hellman,
    pkcs8::{DecodePublicKey, EncodePublicKey},
    PublicKey, SecretKey,
};
use vstd::{prelude::*, vec::*};

verus! {

#[verifier(external_body)]
pub fn gen_ecdh_key_pair() -> (_: (Vec<u8>, Vec<u8>)) {
    let mut rng = rand::thread_rng();
    let secret = SecretKey::random(&mut rng);
    let sk_bytes = secret.to_sec1_der().unwrap().to_vec();
    let pk_bytes = secret
        .public_key()
        .to_public_key_der()
        .unwrap()
        .as_bytes()
        .to_vec();
    (Vec { vec: sk_bytes }, Vec { vec: pk_bytes })
}

#[verifier(external_body)]
pub fn ecdh_combine(sk: &[u8], others_pk: &[u8]) -> Vec<u8> {
    let sk_decoded = SecretKey::from_sec1_der(sk).unwrap();
    let pk_decoded = PublicKey::from_public_key_der(others_pk).unwrap();
    let shared_secret = diffie_hellman(sk_decoded.to_nonzero_scalar(), pk_decoded.as_affine());
    let v = shared_secret.raw_secret_bytes().to_vec();
    Vec { vec: v }
}

} // verus!
