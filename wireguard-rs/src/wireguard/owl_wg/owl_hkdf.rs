use hkdf::Hkdf;
use blake2::Blake2s;
use vstd::prelude::*;

verus! {

pub open spec fn spec_kdfkey_size() -> usize { 32 }
pub const fn kdfkey_size() -> (r:usize) ensures r == spec_kdfkey_size() { 32 }

#[verifier(external_body)]
pub fn gen_rand_kdf_key() -> Vec<u8> {
    crate::wireguard::owl_wg::owl_util::gen_rand_bytes(kdfkey_size())
}

#[verifier(external_body)]
pub fn extract_expand_to_len(ikm: &[u8], salt: &[u8], info: &[u8], len: usize) -> Vec<u8> {
    let h = Hkdf::<Blake2s>::new(Some(salt), ikm);
    let mut okm = vec![0u8; len];
    h.expand(info, &mut okm).expect("failed to expand");
    okm
}

} // verus!
