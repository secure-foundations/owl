use rand::{distributions::Uniform, Rng};
use vstd::{prelude::*, vec::*};

verus! {

#[verifier(external_body)]
pub fn gen_rand_bytes(len: usize) -> Vec<u8> {
    let range = Uniform::from(0..u8::MAX);
    Vec { vec : rand::thread_rng().sample_iter(&range).take(len).collect() }
}

} // verus!
