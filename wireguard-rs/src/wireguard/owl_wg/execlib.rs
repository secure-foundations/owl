use vstd::prelude::*;
use crate::wireguard::owl_wg::{owl_aead, speclib, deep_view::*, *};
use std::rc::Rc;

verus! {

pub enum OwlBuf<'a> {
    Borrowed(&'a [u8]),
    Owned(Rc<Vec<u8>>, usize, usize), // buffer, start, len
} 

impl DView for OwlBuf<'_> {
    type V = Seq<u8>;

    open spec fn dview(&self) -> Self::V {
        match self {
            OwlBuf::Borrowed(s) => s.dview(),
            OwlBuf::Owned(v, start, len) => (*v).dview().subrange(*start as int, (*start + *len) as int),
        }
    }
}

impl<'x> OwlBuf<'x> {
    // Invariants
    #[verifier::opaque]
    pub open spec fn len_valid(&self) -> bool {
        match self {
            OwlBuf::Borrowed(s) => true,
            OwlBuf::Owned(v, start, len) => 
                (*start as int + *len as int <= (*v).dview().len()) 
                && (*v).dview().len() <= usize::MAX as int,
        }
    }

    // Constructors
    pub fn from_slice(s: &[u8]) -> (result: OwlBuf)
        ensures result.dview() == s.dview(),
                result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        OwlBuf::Borrowed(s)
    }

    pub fn from_vec(v: Vec<u8>) -> (result: OwlBuf<'x>)
        ensures result.dview() == v.dview(),
                result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        let len = vec_length(&v);
        proof { assert_seqs_equal!(v.dview(), v.dview().subrange(0int, len as int)); }
        OwlBuf::Owned(rc_new(v), 0, len)
    }
 
    pub fn from_vec_option(v: Option<Vec<u8>>) -> (result: Option<OwlBuf<'x>>)
        ensures dview_option(result) == dview_option(v),
                result.is_Some() ==> result.get_Some_0().len_valid(),
    {
        match v {
            Some(v) => Some(OwlBuf::from_vec(v)),
            None => None,
        }
    }

    // Member functions
    pub fn len(&self) -> (result: usize)
        requires self.len_valid()
        ensures result == self.dview().len()
    {
        match self {
            OwlBuf::Borrowed(s) => {
                proof { assert_seqs_equal!(s.dview(), self.dview()); }
                slice_len(s)
            },
            OwlBuf::Owned(v, start, len) => {
                reveal(OwlBuf::len_valid);
                *len
            },
        }
    }

    pub fn as_slice<'a>(&'a self) -> (result: &'a [u8])
        requires self.len_valid()
        ensures  result.dview() == self.dview()
    {
        match self {
            OwlBuf::Borrowed(s) => s,
            OwlBuf::Owned(v, start, len) => {
                reveal(OwlBuf::len_valid);
                slice_subrange(vec_as_slice(&*v), *start, *start + *len)
            },
        }
    }

    pub fn subrange(&self, start: usize, end: usize) -> (result: OwlBuf)
        requires self.len_valid(),
                    0 <= start <= end <= self.dview().len(),
        ensures  result.dview() == self.dview().subrange(start as int, end as int),
                    result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        match self {
            OwlBuf::Borrowed(s) => OwlBuf::Borrowed(slice_subrange(s, start, end)),
            OwlBuf::Owned(v, start0, _) => {
                let new_start = *start0 + start;
                let len = end - start;
                proof { 
                    assert_seqs_equal!(
                        self.dview().subrange(start as int, end as int), 
                        (*v).dview().subrange(new_start as int, new_start as int + len as int)
                    ); 
                }
                OwlBuf::Owned(rc_clone(v), new_start, len)
            },
        }
    }

    pub fn eq_contents(&self, other: &OwlBuf) -> (result: bool)
        requires self.len_valid(),
                    other.len_valid(),
        ensures  result == (self.dview() == other.dview())
    {
        reveal(OwlBuf::len_valid);
        let self_slice = self.as_slice();
        let other_slice = other.as_slice();
        slice_eq(self_slice, other_slice)
    }

    pub fn another_ref<'a>(&'a self) -> (result: OwlBuf<'x>)
        requires self.len_valid(),
        ensures  result.dview() == self.dview(),
                    result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        match self {
            OwlBuf::Borrowed(s) => OwlBuf::Borrowed(s),
            OwlBuf::Owned(v, start, len) => {
                OwlBuf::Owned(rc_clone(v), *start, *len)
            },
        }
    }
}

#[verifier(external_body)]
pub exec fn rc_new<T:DView>(t: T) -> (r: Rc<T>)
    ensures r.dview() == t.dview()
{ Rc::new(t) }

#[verifier(external_body)]
pub exec fn rc_clone<T:DView>(t: &Rc<T>) -> (r: Rc<T>)
    ensures r.dview() == t.dview()
{ Rc::clone(t) }


#[verifier(external_body)]
pub exec fn slice_eq(s1: &[u8], s2: &[u8]) -> (res: bool)
    ensures res == (s1.dview() == s2.dview())
{
    s1 == s2
}

#[verifier(external_body)]
pub exec fn slice_len<T: DView>(slice: &[T]) -> (length: usize)
    ensures 
        length >= 0,
        length == slice.dview().len()
{
    slice.len()
}

#[verifier(external_body)]
pub exec fn vec_eq(v1: &Vec<u8>, v2: &Vec<u8>) -> (res: bool)
    ensures res == (v1.dview() == v2.dview())
{
    v1 == v2
}

#[verifier(external_body)]
pub exec fn rc_vec_eq(v1: &Vec<u8>, v2: &Vec<u8>) -> (res: bool)
    ensures res == (v1.dview() == v2.dview())
{
    v1 == v2
}

#[verifier(external_body)]
pub exec fn clone_vec_u8(v: &Vec<u8>) -> (res: Vec<u8>)
    ensures res.dview() == v.dview()
{
    v.clone()
}

#[verifier(external_body)]
pub exec fn extend_vec_u8(v: &mut Vec<u8>, s: &[u8])
    ensures v.dview() == old(v).dview().add(s.dview())
{
    v.extend(s);
}

#[verifier::external_body]
pub exec fn vec_truncate(vec: &mut Vec<u8>, len: usize)
    ensures
        vec.dview() == seq_truncate(old(vec).dview(), len as nat)
{
    vec.truncate(len)
}

pub exec fn owl_concat(a: &[u8], b: &[u8]) -> (res: Vec<u8>)
    ensures res.dview() == concat(a.dview(), b.dview())
{
    let mut v = slice_to_vec(a);
    extend_vec_u8(&mut v, b);
    v
}


pub exec fn vec_u8_from_elem(e: u8, n: usize) -> (res: Vec<u8>)
    ensures res.dview() == Seq::new(n as nat, |i| e)
{
    let mut v = vec_new();
    let mut i = 0;
    proof { assert_seqs_equal!(v.dview(), Seq::new(0, |i| e)); }
    while i < n
        invariant
            i <= n,
            v.dview() == Seq::new(i as nat, |j| e)
    {
        vec_push(&mut v, e);
        i = i + 1;
        proof { assert_seqs_equal!(v.dview(), Seq::new(i as nat, |j| e)); }
    }
    v
}

pub exec fn vec_u8_of_len(n: usize) -> (res: Vec<u8>)
    ensures res.dview() == seq_u8_of_len(n as nat)
{
    vec_u8_from_elem(0u8, n)
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! mk_vec_u8 {
    ($($e:expr),* $(,)?) => {
        verus_exec_expr!{{
            #[allow(unused_mut)]
            let mut v = vec_new();
            $(
                vec_push(&mut v, $e);
            )*
            v
        }}
    };
}
pub(crate) use mk_vec_u8;

// By convention, we include the nonce at the start of the ciphertext. (TODO check wrt wire formats)

#[verifier(external_body)]
pub exec fn owl_enc(k: &[u8], msg: &[u8], iv: &[u8]) -> (ctxt: Vec<u8>)
    ensures
        ctxt.dview() == enc(k.dview(), msg.dview(), iv.dview())
    //     ((k.dview().len() == crate::KEY_SIZE && msg.dview().len() == crate::TAG_SIZE) ==> ctxt.dview() == enc(k.dview(), msg.dview(), iv.dview())),
    //    !((k.dview().len() == crate::KEY_SIZE && msg.dview().len() == crate::TAG_SIZE) ==> ctxt.dview() == seq![]),
{
    match owl_aead::encrypt_combined(cipher(), k, msg, iv, &[]) {
        Ok(mut c) => {
            let mut v = iv.to_owned();
            v.append(&mut c);
            v
        },
        Err(_e) => {
            // dbg!(e);
            vec![]
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_dec(k: &[u8], c: &[u8]) -> (x: Option<Vec<u8>>)
    ensures
        dview_option(x) == dec(k.dview(), c.dview())
        // (k.dview().len() == crate::KEY_SIZE && dec(k.dview(), c.dview()).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0().dview() == dec(k.dview(), c.dview()).get_Some_0(),
        // dec(k.dview(), c.dview()).is_None() ==> x.is_None(),
        // k.dview().len() != crate::KEY_SIZE ==> x.is_None(),
{
    match owl_aead::decrypt_combined(cipher(), k, &c[nonce_size()..], &c[..nonce_size()], &[]) {
        Ok(p) => Some(p),
        Err(_e) => {
            // dbg!(e);
            None
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_sign(privkey: &[u8], msg: &[u8]) -> (signature: Vec<u8>)
    ensures signature.dview() == sign(privkey.dview(), msg.dview())
{
    owl_pke::sign(privkey, msg)
}

#[verifier(external_body)]
pub exec fn owl_vrfy(pubkey: &[u8], msg: &[u8], signature: &[u8]) -> (x: Option<Vec<u8>>)
    ensures dview_option(x) == vrfy(pubkey.dview(), msg.dview(), signature.dview())
{
    if owl_pke::verify(pubkey, signature, msg) {
        Some(msg.to_vec())
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn owl_dhpk(privkey: &[u8]) -> (pubkey: Vec<u8>)
    ensures pubkey.dview() == dhpk(privkey.dview())
{
    owl_dhke::ecdh_dhpk(privkey)
}


#[verifier(external_body)]
pub exec fn owl_dh_combine(pubkey: &[u8], privkey: &[u8]) -> (ss: Vec<u8>)
    ensures
        ss.dview() == dh_combine(pubkey.dview(), privkey.dview())
{
    owl_dhke::ecdh_combine(privkey, pubkey)
}

#[verifier(external_body)]
pub exec fn owl_extract_expand_to_len(len: usize, salt: &[u8], ikm: &[u8], info: &[u8]) -> (h: Vec<u8>) 
    ensures h.dview() == kdf(len.dview(), salt.dview(), ikm.dview(), info.dview()),
            h.dview().len() == len
{
    owl_hkdf::extract_expand_to_len(ikm, salt, info, len)
}

#[verifier(external_body)]
pub exec fn owl_mac(mackey: &[u8], msg: &[u8]) -> (mac_val: Vec<u8>)
    ensures mac_val.dview() == mac(mackey.dview(), msg.dview())
{
    owl_hmac::hmac(hmac_mode(), mackey, msg, None)
}

#[verifier(external_body)]
pub exec fn owl_mac_vrfy(mackey: &[u8], msg: &[u8], mac: &[u8]) -> (x: Option<Vec<u8>>)
    ensures dview_option(x) == mac_vrfy(mackey.dview(), msg.dview(), mac.dview())
{
    if owl_hmac::verify(hmac_mode(), mackey, msg, mac, None) {
        Some(msg.to_vec())
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn owl_pkenc(pubkey: &[u8], msg: &[u8]) -> (ctxt: Vec<u8>)
    ensures ctxt.dview() == pkenc(pubkey.dview(), msg.dview())
{
    owl_pke::encrypt(pubkey, msg)
}

#[verifier(external_body)]
pub exec fn owl_pkdec(privkey: &[u8], ctxt: &[u8]) -> (msg: Vec<u8>)
    ensures msg.dview() == sign(privkey.dview(), ctxt.dview())
{
    owl_pke::decrypt(privkey, ctxt)
}


#[verifier(external_body)]
pub exec fn owl_enc_st_aead(k: &[u8], msg: &[u8], nonce: &mut usize, aad: &[u8]) -> (res: Result<Vec<u8>, OwlError>)
    ensures
        res.is_Ok() ==> (res.get_Ok_0().dview(), *nonce) == enc_st_aead(k.dview(), msg.dview(), *old(nonce), aad.dview()),
        // *nonce == *old(nonce) + 1,
{
    if *nonce > usize::MAX - 1 { return Err (OwlError::IntegerOverflow) }
    let mut iv = nonce.to_le_bytes().to_vec();
    iv.resize(nonce_size(), 0u8);
    let res = match owl_aead::encrypt_combined(cipher(), k, msg, &iv[..], aad) {
        Ok(mut c) => {
            let mut v = iv.to_owned();
            v.append(&mut c);
            v
        },
        Err(_e) => {
            // dbg!(e);
            vec![]
        }
    };
    *nonce += 1;
    Ok(res)
}

#[verifier(external_body)]
pub exec fn owl_enc_st_aead_into(dst: &mut [u8], start: usize, end: usize, k: &[u8], msg: &[u8], nonce: &mut usize, aad: &[u8]) -> (res: Result<Ghost<Seq<u8>>, OwlError>)
    ensures
        res.is_Ok() ==> (dst.dview().subrange(start as int, end as int), *nonce) == enc_st_aead(k.dview(), msg.dview(), *old(nonce), aad.dview()),
        res.is_Ok() ==> (res.get_Ok_0().view(), *nonce) == enc_st_aead(k.dview(), msg.dview(), *old(nonce), aad.dview()),
        res.is_Ok() ==> res.get_Ok_0().view() == dst.dview().subrange(start as int, end as int)
        // *nonce == *old(nonce) + 1,
{
    todo!()
    // if *nonce > usize::MAX - 1 { return Err (OwlError::IntegerOverflow) }
    // let mut iv = nonce.to_le_bytes().to_vec();
    // iv.resize(nonce_size(), 0u8);
    // let res = match owl_aead::encrypt_combined(cipher(), k, msg, &iv[..], aad) {
    //     Ok(mut c) => {
    //         let mut v = iv.to_owned();
    //         v.append(&mut c);
    //         v
    //     },
    //     Err(_e) => {
    //         // dbg!(e);
    //         vec![]
    //     }
    // };
    // *nonce += 1;
    // Ok(res)
}


#[verifier(external_body)]
pub exec fn owl_dec_st_aead(k: &[u8], c: &[u8], nonce: &[u8], aad: &[u8]) -> (x: Option<Vec<u8>>)
    ensures
        dview_option(x) == dec_st_aead(k.dview(), c.dview(), nonce.dview(), aad.dview())
        // (k.dview().len() == crate::KEY_SIZE && dec(k.dview(), c.dview()).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0().dview() == dec(k.dview(), c.dview()).get_Some_0(),
        // dec(k.dview(), c.dview()).is_None() ==> x.is_None(),
        // k.dview().len() != crate::KEY_SIZE ==> x.is_None(),
{
    match owl_aead::decrypt_combined(cipher(), k, &c[nonce_size()..], nonce, aad) {
        Ok(p) => Some(p),
        Err(_e) => {
            // dbg!(e);
            None
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_is_group_elem(x: &[u8]) -> (b: bool)
    ensures b == is_group_elem(x.dview())
{
    // todo!("implement is_group_elem")
    x.len() == 32 // TODO what should go here?
}

#[verifier(external_body)]
pub exec fn owl_crh(x: &[u8]) -> (res: Vec<u8>)
    ensures res.dview() == crh(x.dview())
{
    owl_hmac::blake2s(x)
}

#[verifier(external_body)]
pub exec fn owl_bytes_as_counter(x: &[u8]) -> (res: usize)
    ensures res == bytes_as_counter(x.dview())
{
    todo!("implement bytes_as_counter")
}

#[verifier(external_body)]
pub exec fn owl_counter_as_bytes(x: &usize) -> (res: Vec<u8>)
    ensures res.dview() == counter_as_bytes(x.dview())
{
    let mut v = x.to_le_bytes().to_vec();
    v.resize(nonce_size(), 0u8);
    v
}

} // verus!
