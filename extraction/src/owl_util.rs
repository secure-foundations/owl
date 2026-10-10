use rand::{distributions::Uniform, Rng};
use vstd::prelude::*;
#[cfg(not(feature = "nonverif-crypto"))]
use libcrux::drbg::*;
#[cfg(not(feature = "nonverif-crypto"))]
use libcrux::digest::Algorithm;

verus! {

#[verifier(external_body)]
pub fn gen_rand_bytes(len: usize) -> Vec<u8> {
    #[cfg(feature = "nonverif-crypto")]
    {
        let mut v = vec![0u8; len];
        rand::thread_rng().fill(&mut v[..]);
        v
    }
    #[cfg(not(feature = "nonverif-crypto"))]
    {
        let mut rng = Drbg::new(Algorithm::Sha256).unwrap();
        rng.generate_vec(len).unwrap()
    }
}

} // verus!
