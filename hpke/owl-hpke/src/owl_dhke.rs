use x25519_dalek::{PublicKey, SharedSecret, StaticSecret};
use vstd::prelude::*;
use libcrux::ecdh::*;
use libcrux::drbg::*;

verus! {

#[verifier(external_body)]
pub fn gen_ecdh_key_pair() -> (Vec<u8>, Vec<u8>) {
    #[cfg(feature = "nonverif-crypto")]
    {
        let mut rng = rand::thread_rng();
        let secret = StaticSecret::random_from_rng(&mut rng);
        let public = PublicKey::from(&secret);
        let sk_bytes = secret.to_bytes().to_vec();
        let pk_bytes = public.to_bytes().to_vec();
        (sk_bytes, pk_bytes)
    }
    #[cfg(not(feature = "nonverif-crypto"))]
    {
        let mut rng = Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
        let (pk, sk) = x25519_key_gen(&mut rng).unwrap();
        let pk_bytes = pk.0.to_vec();
        let sk_bytes = sk.0.to_vec();
        (sk_bytes, pk_bytes)
    }
}

#[verifier(external_body)]
pub fn ecdh_dhpk(sk: &[u8]) -> Vec<u8> {
    #[cfg(feature = "nonverif-crypto")]
    {
        use std::convert::TryInto;
        let sk_length_checked: [u8; 32] = sk.try_into().unwrap();
        let sk_decoded = StaticSecret::from(sk_length_checked);
        let pk = PublicKey::from(&sk_decoded);
        pk.to_bytes().to_vec()
    }
    #[cfg(not(feature = "nonverif-crypto"))]
    {
        secret_to_public(Algorithm::X25519, sk).unwrap()
    }
}

#[verifier(external_body)]
pub fn ecdh_combine(sk: &[u8], others_pk: &[u8]) -> Vec<u8> {
    #[cfg(feature = "nonverif-crypto")]
    {
        use std::convert::TryInto;
        let sk_length_checked: [u8; 32] = sk.try_into().unwrap();
        let pk_length_checked: [u8; 32] = others_pk.try_into().unwrap();
        let sk_decoded = StaticSecret::from(sk_length_checked);
        let pk_decoded = PublicKey::from(pk_length_checked);
        let shared_secret = sk_decoded.diffie_hellman(&pk_decoded);
        shared_secret.as_bytes().to_vec()
    }
    #[cfg(not(feature = "nonverif-crypto"))]
    {
        derive(Algorithm::X25519, others_pk, sk).unwrap()
    } 
} 

} // verus!
