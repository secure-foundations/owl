use hkdf::Hkdf;
use sha2::Sha256;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub fn extract_expand_to_len(ikm: &[u8], salt: &[u8], len: usize) -> Vec<u8> {
    let h = Hkdf::<Sha256>::new(Some(salt), ikm);
    let mut okm = vec![0u8; len];
    h.expand(&[], &mut okm).expect("failed to expand");
    okm
}

} // verus!
