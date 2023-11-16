use hkdf::Hkdf;
use blake2::{Blake2s};
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub fn extract_expand_to_len(ikm: &[u8], salt: &[u8], len: usize) -> Vec<u8> {
    let h = Hkdf::<Blake2s>::new(Some(salt), ikm);
    let mut okm: Vec<u8> = vec![0u8; len];
    h.expand(&[], &mut okm).expect("failed to expand");
    okm
}

} // verus!
