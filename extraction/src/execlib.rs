use std::rc::Rc;
pub use vstd::{modes::*, prelude::*, seq::*, string::*, slice::*};
use crate::{speclib, *};

verus! {

pub enum OwlBuf<'a> {
    Borrowed(&'a [u8]),
    Owned(Rc<Vec<u8>>, usize, usize), // buffer, start, len
} 

impl View for OwlBuf<'_> {
    type V = Seq<u8>;

    open spec fn view(&self) -> Self::V {
        match self {
            OwlBuf::Borrowed(s) => s.view(),
            OwlBuf::Owned(v, start, len) => (*v).view().subrange(*start as int, (*start + *len) as int),
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
                (*start as int + *len as int <= (*v).view().len()) 
                && (*v).view().len() <= usize::MAX as int,
        }
    }

    // Constructors
    pub fn from_slice(s: &[u8]) -> (result: OwlBuf)
        ensures result.view() == s.view(),
                result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        OwlBuf::Borrowed(s)
    }

    pub fn from_vec(v: Vec<u8>) -> (result: OwlBuf<'x>)
        ensures result.view() == v.view(),
                result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        broadcast use axiom_spec_len;
        let len = v.len();
        proof { assert_seqs_equal!(v.view(), v.view().subrange(0int, len as int)); }
        OwlBuf::Owned(Rc::new(v), 0, len)
    }
 
    pub fn from_vec_option(v: Option<Vec<u8>>) -> (result: Option<OwlBuf<'x>>)
        ensures view_option(result) == view_option(v),
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
        ensures result == self.view().len()
    {
        match self {
            OwlBuf::Borrowed(s) => {
                proof { assert_seqs_equal!(s.view(), self.view()); }
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
        ensures  result.view() == self.view()
    {
        match self {
            OwlBuf::Borrowed(s) => s,
            OwlBuf::Owned(v, start, len) => {
                reveal(OwlBuf::len_valid);
                slice_subrange((*v).as_slice(), *start, *start + *len)
            },
        }
    }

    pub fn subrange(&self, start: usize, end: usize) -> (result: OwlBuf)
        requires self.len_valid(),
                    0 <= start <= end <= self.view().len(),
        ensures  result.view() == self.view().subrange(start as int, end as int),
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
                        self.view().subrange(start as int, end as int), 
                        (*v).view().subrange(new_start as int, new_start as int + len as int)
                    ); 
                }
                OwlBuf::Owned(Rc::clone(v), new_start, len)
            },
        }
    }

    pub fn eq_contents(&self, other: &OwlBuf) -> (result: bool)
        requires self.len_valid(),
                    other.len_valid(),
        ensures  result == (self.view() == other.view())
    {
        reveal(OwlBuf::len_valid);
        let self_slice = self.as_slice();
        let other_slice = other.as_slice();
        slice_eq(self_slice, other_slice)
    }

    pub fn another_ref<'a>(&'a self) -> (result: OwlBuf<'x>)
        requires self.len_valid(),
        ensures  result.view() == self.view(),
                    result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        match self {
            OwlBuf::Borrowed(s) => OwlBuf::Borrowed(s),
            OwlBuf::Owned(v, start, len) => {
                OwlBuf::Owned(Rc::clone(v), *start, *len)
            },
        }
    }

    pub fn into_owned(self) -> (result: OwlBuf<'x>)
        requires self.len_valid(),
        ensures  result.view() == self.view(),
                    result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        match self {
            OwlBuf::Borrowed(s) => OwlBuf::from_vec(slice_to_vec(s)),
            OwlBuf::Owned(v, start, len) => OwlBuf::Owned(v, start, len),
        }
    }
}

pub fn owl_unit() -> (res: ())
{ () }

pub fn owl_ghost_unit() -> (res: Ghost<()>)
{ Ghost(()) }

#[verifier(external_body)]
pub exec fn slice_eq(s1: &[u8], s2: &[u8]) -> (res: bool)
    ensures res == (s1.view() == s2.view())
{
    s1 == s2
}

#[verifier(external_body)]
pub exec fn slice_len<T: View>(slice: &[T]) -> (length: usize)
    ensures 
        length >= 0,
        length == slice.view().len()
{
    slice.len()
}

#[verifier(external_body)]
pub exec fn vec_eq(v1: &Vec<u8>, v2: &Vec<u8>) -> (res: bool)
    ensures res == (v1.view() == v2.view())
{
    v1 == v2
}

#[verifier(external_body)]
pub exec fn rc_vec_eq(v1: &Vec<u8>, v2: &Vec<u8>) -> (res: bool)
    ensures res == (v1.view() == v2.view())
{
    v1 == v2
}

#[verifier(external_body)]
pub exec fn clone_vec_u8(v: &Vec<u8>) -> (res: Vec<u8>)
    ensures res.view() == v.view()
{
    v.clone()
}

#[verifier(external_body)]
pub exec fn extend_vec_u8(v: &mut Vec<u8>, s: &[u8])
    ensures v.view() == old(v).view().add(s.view())
{
    v.extend(s);
}

#[verifier::external_body]
pub exec fn vec_truncate(vec: &mut Vec<u8>, len: usize)
    ensures
        vec.view() == seq_truncate(old(vec).view(), len as nat)
{
    vec.truncate(len)
}

pub exec fn owl_concat(a: &[u8], b: &[u8]) -> (res: Vec<u8>)
    ensures res.view() == concat(a.view(), b.view())
{
    let mut v = slice_to_vec(a);
    extend_vec_u8(&mut v, b);
    v
}


#[verifier(external_body)]
pub exec fn vec_u8_from_elem(e: u8, n: usize) -> (res: Vec<u8>)
    ensures res.view() == Seq::new(n as nat, |i| e)
{
    // let mut v = vec_new();
    // let mut i = 0;
    // proof { assert_seqs_equal!(v.view(), Seq::new(0, |i| e)); }
    // while i < n
    //     invariant
    //         i <= n,
    //         v.view() == Seq::new(i as nat, |j| e)
    // {
    //     vec_push(&mut v, e);
    //     i = i + 1;
    //     proof { assert_seqs_equal!(v.view(), Seq::new(i as nat, |j| e)); }
    // }
    // v
    vec![e; n]
}

pub exec fn vec_u8_of_len(n: usize) -> (res: Vec<u8>)
    ensures res.view() == seq_u8_of_len(n as nat)
{
    vec_u8_from_elem(0u8, n)
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! mk_vec_u8 {
    ($($e:expr),* $(,)?) => {
        verus_exec_expr!{{
            #[allow(unused_mut)]
            let mut v = Vec::new();
            $(
                v.push($e);
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
        ctxt.view() == enc(k.view(), msg.view(), iv.view())
    //     ((k.view().len() == crate::KEY_SIZE && msg.view().len() == crate::TAG_SIZE) ==> ctxt.view() == enc(k.view(), msg.view(), iv.view())),
    //    !((k.view().len() == crate::KEY_SIZE && msg.view().len() == crate::TAG_SIZE) ==> ctxt.view() == seq![]),
{
    match owl_aead::encrypt_combined(CIPHER, k, msg, iv, &[]) {
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
        view_option(x) == dec(k.view(), c.view())
        // (k.view().len() == crate::KEY_SIZE && dec(k.view(), c.view()).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0().view() == dec(k.view(), c.view()).get_Some_0(),
        // dec(k.view(), c.view()).is_None() ==> x.is_None(),
        // k.view().len() != crate::KEY_SIZE ==> x.is_None(),
{
    match owl_aead::decrypt_combined(CIPHER, k, &c[NONCE_SIZE..], &c[..NONCE_SIZE], &[]) {
        Ok(p) => Some(p),
        Err(_e) => {
            // dbg!(e);
            None
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_sign(privkey: &[u8], msg: &[u8]) -> (signature: Vec<u8>)
    ensures signature.view() == sign(privkey.view(), msg.view())
{
    owl_pke::sign(privkey, msg)
}

#[verifier(external_body)]
pub exec fn owl_vrfy(pubkey: &[u8], msg: &[u8], signature: &[u8]) -> (x: Option<Vec<u8>>)
    ensures view_option(x) == vrfy(pubkey.view(), msg.view(), signature.view())
{
    if owl_pke::verify(pubkey, signature, msg) {
        Some(msg.to_vec())
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn owl_dhpk(privkey: &[u8]) -> (pubkey: Vec<u8>)
    ensures pubkey.view() == dhpk(privkey.view())
{
    owl_dhke::ecdh_dhpk(privkey)
}


#[verifier(external_body)]
pub exec fn owl_dh_combine(pubkey: &[u8], privkey: &[u8]) -> (ss: Vec<u8>)
    ensures
        ss.view() == dh_combine(pubkey.view(), privkey.view())
{
    owl_dhke::ecdh_combine(privkey, pubkey)
}

#[verifier(external_body)]
pub exec fn owl_extract_expand_to_len(len: usize, salt: &[u8], ikm: &[u8], info: &[u8]) -> (h: Vec<u8>) 
    ensures h.view() == kdf(len.view(), salt.view(), ikm.view(), info.view()),
            h.view().len() == len
{
    owl_hkdf::extract_expand_to_len(ikm, salt, info, len)
}

#[verifier(external_body)]
pub exec fn owl_mac(mackey: &[u8], msg: &[u8]) -> (mac_val: Vec<u8>)
    ensures mac_val.view() == mac(mackey.view(), msg.view())
{
    owl_hmac::hmac(HMAC_MODE, mackey, msg, None)
}

#[verifier(external_body)]
pub exec fn owl_mac_vrfy(mackey: &[u8], msg: &[u8], mac: &[u8]) -> (x: Option<Vec<u8>>)
    ensures view_option(x) == mac_vrfy(mackey.view(), msg.view(), mac.view())
{
    if owl_hmac::verify(HMAC_MODE, mackey, msg, mac, None) {
        Some(msg.to_vec())
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn owl_pkenc(pubkey: &[u8], msg: &[u8]) -> (ctxt: Vec<u8>)
    ensures ctxt.view() == pkenc(pubkey.view(), msg.view())
{
    owl_pke::encrypt(pubkey, msg)
}

#[verifier(external_body)]
pub exec fn owl_pkdec(privkey: &[u8], ctxt: &[u8]) -> (msg: Vec<u8>)
    ensures msg.view() == sign(privkey.view(), ctxt.view())
{
    owl_pke::decrypt(privkey, ctxt)
}


#[verifier(external_body)]
pub exec fn owl_enc_st_aead(k: &[u8], msg: &[u8], nonce: &mut usize, aad: &[u8]) -> (res: Result<Vec<u8>, OwlError>)
    ensures
        res.is_Ok() ==> (res.get_Ok_0().view(), *nonce) == enc_st_aead(k.view(), msg.view(), *old(nonce), aad.view()),
        // *nonce == *old(nonce) + 1,
{
    if *nonce > usize::MAX - 1 { return Err (OwlError::IntegerOverflow) }
    let mut iv = nonce.to_le_bytes().to_vec();
    iv.resize(NONCE_SIZE, 0u8);
    let res = match owl_aead::encrypt_combined(CIPHER, k, msg, &iv[..], aad) {
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
        res.is_Ok() ==> (dst.view().subrange(start as int, end as int), *nonce) == enc_st_aead(k.view(), msg.view(), *old(nonce), aad.view()),
        res.is_Ok() ==> (res.get_Ok_0().view(), *nonce) == enc_st_aead(k.view(), msg.view(), *old(nonce), aad.view()),
        res.is_Ok() ==> res.get_Ok_0().view() == dst.view().subrange(start as int, end as int)
        // *nonce == *old(nonce) + 1,
{
    todo!()
    // if *nonce > usize::MAX - 1 { return Err (OwlError::IntegerOverflow) }
    // let mut iv = nonce.to_le_bytes().to_vec();
    // iv.resize(NONCE_SIZE, 0u8);
    // let res = match owl_aead::encrypt_combined(CIPHER, k, msg, &iv[..], aad) {
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
        view_option(x) == dec_st_aead(k.view(), c.view(), nonce.view(), aad.view())
        // (k.view().len() == crate::KEY_SIZE && dec(k.view(), c.view()).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0().view() == dec(k.view(), c.view()).get_Some_0(),
        // dec(k.view(), c.view()).is_None() ==> x.is_None(),
        // k.view().len() != crate::KEY_SIZE ==> x.is_None(),
{
    match owl_aead::decrypt_combined(CIPHER, k, &c[NONCE_SIZE..], nonce, aad) {
        Ok(p) => Some(p),
        Err(_e) => {
            // dbg!(e);
            None
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_is_group_elem(x: &[u8]) -> (b: bool)
    ensures b == is_group_elem(x.view())
{
    // todo!("implement is_group_elem")
    x.len() == 32 // TODO what should go here?
}

#[verifier(external_body)]
pub exec fn owl_crh(x: &[u8]) -> (res: Vec<u8>)
    ensures res.view() == crh(x.view())
{
    owl_hmac::blake2s(x)
}

#[verifier(external_body)]
pub exec fn owl_bytes_as_counter(x: &[u8]) -> (res: usize)
    ensures res == bytes_as_counter(x.view())
{
    todo!("implement bytes_as_counter")
}

#[verifier(external_body)]
pub exec fn owl_counter_as_bytes<'a>(x: &usize) -> (res: [u8; 8])
    ensures res.view() == counter_as_bytes(x.view())
{
    let v = x.to_le_bytes();
    v
}

} // verus!
