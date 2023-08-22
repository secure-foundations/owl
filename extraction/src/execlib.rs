// use crate::owl_aead;
use crate::speclib;
use std::rc::Rc;
use vstd::{prelude::*, *};

verus! {

/// Clones a Vec<u8> (because currently Verus doesn't support this natively)
#[verifier(external_body)]
pub exec fn clone_vec_u8(v: &Vec<u8>) -> (res: Vec<u8>)
    ensures v@ === res@
{
    todo!() // Vec { vec: v.vec.clone() }
}

#[verifier(external_body)]
pub exec fn extend_vec_u8(v: &mut Vec<u8>, s: &[u8])
    ensures v@ === old(v)@.add(s@)
{
    v.extend(s);
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

// #[verifier(external_body)]
// pub exec fn slice_len<T>(slice: &[T]) -> (res: usize)
//     ensures slice@.len() == res
// {
//     slice.len()
// }

#[verifier(external_body)]
pub exec fn rc_clone(rc: &Rc<Vec<u8>>) -> (res: Rc<Vec<u8>>)
    ensures (*rc)@ === (*res)@
{
    Rc::clone(&rc)
}

#[verifier(external_body)]
pub exec fn rc_new(v: Vec<u8>) -> (res: Rc<Vec<u8>>)
    ensures v@ === (*res)@
{
    Rc::new(v)
}

#[verifier(external_body)]
pub exec fn owl_enc(k: &[u8], msg: &[u8], iv: &[u8]) -> (ctxt: Vec<u8>)
    ensures
        ctxt@ === speclib::enc(k@, msg@, iv@)
    //     ((k@.len() == crate::KEY_SIZE && msg@.len() == crate::TAG_SIZE) ==> ctxt@ === speclib::enc(k@, msg@, iv@)),
    //    !((k@.len() == crate::KEY_SIZE && msg@.len() == crate::TAG_SIZE) ==> ctxt@ === seq![]),
{
    // match owl_aead::encrypt_combined(cipher(), k, msg, iv) {
    //     Ok(c) => c,
    //     Err(e) => {
    //         // dbg!(e);
    //         vec![]
    //     }
    // }
    todo!()
}

#[verifier(external_body)]
pub exec fn owl_dec(k: &[u8], c: &[u8]) -> (x: Option<Vec<u8>>)
    ensures
        speclib::view_option(x) === speclib::dec(k@, c@)
        // (k@.len() == crate::KEY_SIZE && speclib::dec(k@, c@).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0()@ === speclib::dec(k@, c@).get_Some_0(),
        // speclib::dec(k@, c@).is_None() ==> x.is_None(),
        // k@.len() != crate::KEY_SIZE ==> x.is_None(),
{
    todo!()
    // match owl_aead::decrypt_combined(cipher(), slice_subrange(&k, 0, key_size()), self, slice_subrange(&key, key_size(), key.len())) {
    //     Ok(p) => Some(p),
    //     Err(e) => {
    //         // dbg!(e);
    //         None
    //     }
    // }
}

} // verus!
