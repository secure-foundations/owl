use p256::{
    ecdh::diffie_hellman,
    pkcs8::{DecodePublicKey, EncodePublicKey},
    PublicKey, SecretKey,
};

pub fn gen_ecdh_key_pair() -> (Vec<u8>, Vec<u8>) {
    let mut rng = rand::thread_rng();
    let secret = SecretKey::random(&mut rng);
    let sk_bytes = secret.to_sec1_der().unwrap().to_vec();
    let pk_bytes = secret
        .public_key()
        .to_public_key_der()
        .unwrap()
        .as_bytes()
        .to_vec();
    (sk_bytes, pk_bytes)
}

pub fn ecdh_combine(sk: &[u8], others_pk: &[u8]) -> Vec<u8> {
    let sk_decoded = SecretKey::from_sec1_der(sk).unwrap();
    let pk_decoded = PublicKey::from_public_key_der(others_pk).unwrap();
    let shared_secret = diffie_hellman(sk_decoded.to_nonzero_scalar(), pk_decoded.as_affine());
    shared_secret.raw_secret_bytes().to_vec()
}
