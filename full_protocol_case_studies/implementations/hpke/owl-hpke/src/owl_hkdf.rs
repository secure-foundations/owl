use hkdf::Hkdf;
use sha2::Sha256;
use vstd::prelude::*;

use libcrux::hkdf::*;

verus! {

pub open spec fn spec_kdfkey_size() -> usize { 32 }
pub const fn kdfkey_size() -> (r:usize) ensures r == spec_kdfkey_size() { 32 }

#[verifier(external_body)]
pub fn gen_rand_kdf_key() -> Vec<u8> {
    crate::owl_util::gen_rand_bytes(kdfkey_size())
}

#[verifier(external_body)]
pub fn extract_expand_to_len(ikm: &[u8], salt: &[u8], info: &[u8], len: usize) -> Vec<u8> {
    #[cfg(feature = "nonverif-crypto")]
    {
        let h = Hkdf::<Sha256>::new(Some(salt), ikm);
        let mut okm = vec![0u8; len];
        h.expand(info, &mut okm).expect("failed to expand");
        okm
    }
    #[cfg(not(feature = "nonverif-crypto"))]
    {
        // support other algorithms here?
        libcrux::hkdf::hkdf(Algorithm::Sha256, salt, ikm, info, len).unwrap()
    }
}


} // verus!
