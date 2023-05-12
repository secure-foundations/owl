use std::rc::Rc;
use vstd::{prelude::*, seq::*, slice::*, vec::*, *};

verus! {

/// Clones a Vec<u8> (because currently Verus doesn't support this natively)
#[verifier(external_body)]
pub exec fn clone_vec_u8(v: &Vec<u8>) -> (res: Vec<u8>)
    ensures v@ == res@
{
    todo!() // Vec { vec: v.vec.clone() }
}

#[verifier(external_body)]
pub exec fn extend_vec_u8(v: &mut Vec<u8>, s: &[u8])
    ensures v@ == old(v)@.add(s@)
{
    v.vec.extend(s);
}

pub exec fn vec_u8_from_elem(e: u8, n: usize) -> (res: Vec<u8>)
    ensures res@ === Seq::new(n as nat, |i| e)
{
    let mut v = Vec::new();
    let mut i = 0;
    proof { assert_seqs_equal!(v@, Seq::new(0, |i| e)); }
    while i < n
        invariant
            i <= n,
            v@ === Seq::new(i as nat, |j| e)
    {
        v.push(e);
        i = i + 1;
        proof { assert_seqs_equal!(v@, Seq::new(i as nat, |j| e)); }
    }
    v
}

#[verifier(external_body)]
pub exec fn slice_len<T>(slice: &[T]) -> (res: usize)
    ensures slice@.len() == res
{
    slice.len()
}

#[verifier(external_body)]
pub exec fn rc_clone(rc: &Rc<Vec<u8>>) -> (res: Rc<Vec<u8>>)
    ensures (*rc)@ == (*res)@
{
    Rc::clone(&rc)
}

} // verus!
