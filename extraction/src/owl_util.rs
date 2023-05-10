use vstd::{prelude::*, vec::*, slice::*};
use rand::{distributions::Uniform, Rng};

verus! {

#[verifier(external_body)]
pub fn gen_rand_bytes(len: usize) -> Vec<u8> {
    let range = Uniform::from(0..u8::MAX);
    Vec { vec : rand::thread_rng().sample_iter(&range).take(len).collect() }
}

/// Clones a Vec<u8> (because currently Verus doesn't support this natively)
#[verifier(external_body)]
pub exec fn clone_vec_u8(v: &Vec<u8>) -> (res: Vec<u8>)
    ensures v@ == res@
{
    Vec { vec: v.vec.clone() }
}

#[verifier(external_body)]
pub exec fn extend_vec_u8(v: &mut Vec<u8>, s: &[u8])
    ensures v@ == old(v)@.add(s@)
{
    v.vec.extend(s);
}

} // verus!
