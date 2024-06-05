use rand::{distributions::Uniform, Rng};
use vstd::prelude::*;
use libcrux::drbg::*;
use libcrux::digest::Algorithm;

verus! {

#[verifier(external_body)]
pub fn gen_rand_bytes(len: usize) -> Vec<u8> {
    let mut rng = Drbg::new(Algorithm::Sha256).unwrap();
    rng.generate_vec(len).unwrap()
}

} // verus!
