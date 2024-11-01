use std::rc::Rc;
pub use vstd::{modes::*, prelude::*, seq::*, view::*, slice::*};
use crate::{*, speclib::*};
use vest::regular::builder::*;




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
                slice_subrange((**v).as_slice(), *start, *start + *len)
            },
        }
    }

    pub fn subrange(self, start: usize, end: usize) -> (result: OwlBuf<'x>)
        requires self.len_valid(),
                    0 <= start <= end <= self.view().len(),
        ensures  result.view() == self.view().subrange(start as int, end as int),
                    result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        match self {
            OwlBuf::Borrowed(s) => OwlBuf::Borrowed(slice_subrange(s, start, end)),
            OwlBuf::Owned(v, start0, _) => {
                let new_start = start0 + start;
                let len = end - start;
                proof { 
                    assert_seqs_equal!(
                        self.view().subrange(start as int, end as int), 
                        (*v).view().subrange(new_start as int, new_start as int + len as int)
                    ); 
                }
                OwlBuf::Owned(Rc::clone(&v), new_start, len)
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

    pub fn another_ref_option<'a>(x: &'a Option<Self>) -> (result: Option<OwlBuf<'x>>)
        requires x.is_Some() ==> x.get_Some_0().len_valid(),
        ensures view_option(result) == view_option(*x),
                result.is_Some() ==> result.get_Some_0().len_valid(),
    {
        match x {
            Some(x) => Some(OwlBuf::another_ref(x)),
            None => None,
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

    pub fn into_secret(self) -> (result: SecretBuf<'x>)
        requires self.len_valid(),
        ensures  result.view() == self.view(),
                    result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        SecretBuf::from_buf(self)
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
// pub(crate) use mk_vec_u8;


pub open spec fn view_first_byte_pair(x: (u8, SecretBuf<'_>)) -> Seq<u8>
{
    seq![x.0].add(x.1.view())
}

pub open spec fn view_first_byte_pair_opt(x: Option<(u8, SecretBuf<'_>)>) -> Seq<u8>
{
    match x {
        Some(y) => seq![y.0].add(y.1.view()),
        None => seq![]
    }
}

}


////////////////////////////////////////////////////////////////////////////////
///////////////////// Secret buffer abstraction ////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

pub mod secret {
    use crate::execlib::*;
    use vstd::*;
    
    verus! {
    
    pub struct SecretBuf<'a> {
        buf: OwlBuf<'a>
    }

    impl View for SecretBuf<'_> {
        type V = Seq<u8>;

        closed spec fn view(&self) -> Self::V {
            self.buf.view()
        }
    }

    impl<'x> SecretBuf<'x> {
        #[verifier::opaque]
        pub closed spec fn len_valid(&self) -> bool {
            self.buf.len_valid()
        }

        pub fn from_buf(buf: OwlBuf<'x>) -> (result: SecretBuf<'x>)
            requires buf.len_valid()
            ensures result.view() == buf.view(),
                    result.len_valid(),
        {
            reveal(SecretBuf::len_valid);
            reveal(OwlBuf::len_valid);
            SecretBuf { buf }
        }

        pub fn another_ref<'a>(&'a self) -> (result: SecretBuf<'x>)
            requires self.len_valid()
            ensures  result.view() == self.view(),
                     result.len_valid(),
        {
            reveal(SecretBuf::len_valid);
            SecretBuf { buf: self.buf.another_ref() }
        }

        ///////// Declassifying operations on SecretBufs

        #[verifier::external_body]
        pub fn declassify<'a>(&'a self, Tracked(t): Tracked<DeclassifyingOpToken>) -> (result: OwlBuf<'x>)
            requires self.len_valid(),
                     t.view() matches DeclassifyingOp::ControlFlow(b) && b == self.view()
            ensures result.len_valid(),
                    result.view() == self.view(),
                    // t.view() == old(t).view().do_declassify()
        {
            reveal(SecretBuf::len_valid);
            self.buf.another_ref()
        }

        #[verifier::external_body]
        pub fn declassify_first_byte<'a>(
            &'a self, 
            Tracked(t): Tracked<DeclassifyingOpToken>
        ) -> (result: Option<(u8, SecretBuf<'x>)>)
            requires self.len_valid(),
                     t.view() matches DeclassifyingOp::EnumParse(b) && b == self.view()
            ensures result matches Some(p) ==> p.1.len_valid(), // && p.1.len() == self.len() - 1,
                    result matches Some(p) ==> self.view() == view_first_byte_pair(p),
                    result is None ==> self.view().len() == 0,
                    // t.view() == old(t).view().do_declassify()
        {
            if self.buf.len() == 0 {
                None
            } else {
                let first_byte = self.buf.as_slice()[0];
                let rest = SecretBuf { buf: self.buf.another_ref().subrange(1, self.buf.len()) };
                Some((first_byte, rest))
            }
        }

        #[verifier::external_body]
        pub fn ct_eq(&self, other: &SecretBuf, Tracked(t): Tracked<DeclassifyingOpToken>) -> (result: bool)
            requires self.len_valid(),
                     other.len_valid(),
                     t.view() matches DeclassifyingOp::EqCheck(l,r) && 
                        ((self@ == l && other@ == r) || (self@ == r && other@ == l))
            ensures  result <==> self.view() == other.view()
        {
            // self.buf.eq_contents(&other.buf)
            todo!("implement ct_eq")
        }
        
        fn private_as_slice(&self) -> (result: &[u8])
            requires self.len_valid()
            ensures  result.view() == self.view()
        {
            reveal(SecretBuf::len_valid);
            self.buf.as_slice()
        }
    }

    }



    verus!{

    // By convention, we include the nonce at the start of the ciphertext. (TODO check wrt wire formats)

    #[verifier(external_body)]
    pub exec fn owl_enc(k: SecretBuf<'_>, msg: SecretBuf<'_>, iv: SecretBuf<'_>) -> (ctxt: Vec<u8>)
        ensures
            ctxt.view() == enc(k.view(), msg.view(), iv.view())
        //     ((k.view().len() == crate::KEY_SIZE && msg.view().len() == crate::TAG_SIZE) ==> ctxt.view() == enc(k.view(), msg.view(), iv.view())),
        //    !((k.view().len() == crate::KEY_SIZE && msg.view().len() == crate::TAG_SIZE) ==> ctxt.view() == seq![]),
    {
        let k = k.private_as_slice();
        let msg = msg.private_as_slice();
        let iv = iv.private_as_slice();
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
    pub exec fn owl_dec<'a>(k: SecretBuf<'_>, c: OwlBuf<'a>, Tracked(t): Tracked<DeclassifyingOpToken>) -> (x: Option<SecretBuf<'a>>)
        requires
            t.view() matches DeclassifyingOp::ADec(k_spec, c_spec) && k@ == k_spec && c@ == c_spec
        ensures
            view_option(x) == dec(k.view(), c.view()),
            x matches Some(b) ==> b.len_valid()
            // (k.view().len() == crate::KEY_SIZE && dec(k.view(), c.view()).is_Some()) ==>
            //     x.is_Some() && x.get_Some_0().view() == dec(k.view(), c.view()).get_Some_0(),
            // dec(k.view(), c.view()).is_None() ==> x.is_None(),
            // k.view().len() != crate::KEY_SIZE ==> x.is_None(),
    {
        let k = k.private_as_slice();
        let c = c.as_slice();
        match owl_aead::decrypt_combined(CIPHER, k, &c[NONCE_SIZE..], &c[..NONCE_SIZE], &[]) {
            Ok(p) => Some(OwlBuf::from_vec(p).into_secret()),
            Err(_e) => {
                // dbg!(e);
                None
            }
        }
    }

    #[verifier(external_body)]
    pub exec fn owl_sign(privkey: SecretBuf, msg: OwlBuf) -> (signature: Vec<u8>)
        // requires msg == 
        ensures signature.view() == sign(privkey.view(), msg.view())
    {
        let privkey = privkey.private_as_slice();
        let msg = msg.as_slice();
        owl_pke::sign(privkey, msg)
    }

    #[verifier(external_body)]
    pub exec fn owl_vrfy<'a>(pubkey: SecretBuf<'_>, msg: SecretBuf<'_>, signature: OwlBuf<'a>, Tracked(t): Tracked<DeclassifyingOpToken>) -> (x: Option<SecretBuf<'a>>)
        requires
            t.view() matches DeclassifyingOp::SigVrfy(pubkey_spec, msg_spec, signature_spec) 
            && pubkey@ == pubkey_spec && msg@ == msg_spec && signature@ == signature_spec
        ensures 
            view_option(x) == vrfy(pubkey.view(), msg.view(), signature.view())
    {
        let pubkey = pubkey.private_as_slice();
        let msg = msg.private_as_slice();
        let signature = signature.as_slice();
        if owl_pke::verify(pubkey, signature, msg) {
            Some(OwlBuf::from_slice(signature).into_secret())
        } else {
            None
        }
    }

    // #[verifier(external_body)]
    // pub exec fn owl_dhpk(privkey: SecretBuf) -> (pubkey: Vec<u8>)
    //     ensures pubkey.view() == dhpk(privkey.view())
    // {
    //     owl_dhke::ecdh_dhpk(privkey)
    // }


    // #[verifier(external_body)]
    // pub exec fn owl_dh_combine(pubkey: &[u8], privkey: &[u8]) -> (ss: Vec<u8>)
    //     ensures
    //         ss.view() == dh_combine(pubkey.view(), privkey.view())
    // {
    //     owl_dhke::ecdh_combine(privkey, pubkey)
    // }

    // #[verifier(external_body)]
    // pub exec fn owl_extract_expand_to_len(len: usize, salt: &[u8], ikm: &[u8], info: &[u8]) -> (h: Vec<u8>) 
    //     ensures h.view() == kdf(len.view(), salt.view(), ikm.view(), info.view()),
    //             h.view().len() == len
    // {
    //     owl_hkdf::extract_expand_to_len(ikm, salt, info, len)
    // }

    // #[verifier(external_body)]
    // pub exec fn owl_mac(mackey: &[u8], msg: &[u8]) -> (mac_val: Vec<u8>)
    //     ensures mac_val.view() == mac(mackey.view(), msg.view())
    // {
    //     owl_hmac::hmac(HMAC_MODE, mackey, msg, None)
    // }

    // #[verifier(external_body)]
    // pub exec fn owl_mac_vrfy(mackey: &[u8], msg: &[u8], mac: &[u8], Tracked(t): Tracked<DeclassifyingOpToken>) -> (x: Option<Vec<u8>>)
    //     requires
    //         t.view() matches DeclassifyingOp::MacVrfy(mackey_spec, msg_spec, mac_spec)
    //         && mackey@ == mackey_spec && msg@ == msg_spec && mac@ == mac_spec
    //     ensures 
    //         view_option(x) == mac_vrfy(mackey.view(), msg.view(), mac.view())
    // {
    //     if owl_hmac::verify(HMAC_MODE, mackey, msg, mac, None) {
    //         Some(msg.to_vec())
    //     } else {
    //         None
    //     }
    // }

    // #[verifier(external_body)]
    // pub exec fn owl_pkenc(pubkey: &[u8], msg: &[u8]) -> (ctxt: Vec<u8>)
    //     ensures ctxt.view() == pkenc(pubkey.view(), msg.view())
    // {
    //     owl_pke::encrypt(pubkey, msg)
    // }

    // #[verifier(external_body)]
    // pub exec fn owl_pkdec(privkey: &[u8], ctxt: &[u8], Tracked(t): Tracked<DeclassifyingOpToken>) -> (msg: Option<Vec<u8>>)
    //     requires
    //         t.view() matches DeclassifyingOp::PkDec(privkey_spec, ctxt_spec) 
    //         && privkey@ == privkey_spec && ctxt@ == ctxt_spec
    //     ensures 
    //         view_option(msg) == pkdec(privkey.view(), ctxt.view())
    // {
    //     owl_pke::decrypt(privkey, ctxt)
    // }


    // // Builder for stateful AEAD encryption
    // pub struct OwlStAEADBuilder<'a> {
    //     pub k: &'a [u8],
    //     pub msg: &'a [u8],
    //     pub iv: &'a [u8],
    //     pub aad: &'a [u8],
    // }

    // // Hack: due to https://github.com/verus-lang/verus/issues/1147, we cannot use `Builder::into_vec` directly,
    // // so we have to define our own version with a different name.
    // impl<'a> OwlStAEADBuilder<'a> {
    //     pub fn into_fresh_vec(&self) -> (res: Vec<u8>)
    //         ensures
    //             res@ == self.value(),
    //     {
    //         let mut res = vec_u8_of_len(self.length());
    //         self.into_mut_vec(&mut res, 0);
    //         assert(res@.subrange(0, 0).add(self.value()).add(
    //             res@.subrange(0 + self.value().len() as int, self.value().len() as int),
    //         ) == res@);
    //         assert(res@.subrange(0, 0).add(self.value()).add(
    //             res@.subrange(0 + self.value().len() as int, self.value().len() as int),
    //         ) == self.value());
    //         res
    //     }
    // }


    // impl<'a> Builder for OwlStAEADBuilder<'a> {
    //     open spec fn value(&self) -> Seq<u8> {
    //         enc_st_aead(self.k.view(), self.msg.view(), self.iv.view(), self.aad.view())
    //     }
        
    //     #[verifier::external_body]
    //     proof fn value_wf(&self);
        
    //     #[verifier::external_body]
    //     fn length(&self) -> usize {
    //         self.msg.len() + TAG_SIZE
    //     }

    //     #[verifier::external_body]
    //     fn into_mut_vec(&self, data: &mut Vec<u8>, pos: usize) {
    //         let mut iv_sized = self.iv.to_vec();
    //         iv_sized.resize(NONCE_SIZE, 0u8);
    //         match owl_aead::encrypt_combined_into(CIPHER, self.k, self.msg, &iv_sized[..], self.aad, data, pos) {
    //             Ok(()) => (),
    //             Err(_e) => {
    //                 // dbg!(e);
    //                 ()
    //             }
    //         };
    //     }
    // }

    // impl View for OwlStAEADBuilder<'_> {
    //     type V = Seq<u8>;

    //     open spec fn view(&self) -> Self::V {
    //         self.value()
    //     }
    // }

    // #[verifier(external_body)]
    // pub exec fn owl_enc_st_aead_builder<'a>(k: SecretBuf<'a>, msg: SecretBuf<'a>, iv: SecretBuf<'a>, aad: SecretBuf<'a>) -> (res: OwlStAEADBuilder<'a>)
    //     ensures  
    //         res.view() == enc_st_aead(k.view(), msg.view(), iv.view(), aad.view()),
    // {
    //     OwlStAEADBuilder { k, msg, iv, aad }
    // }


    // #[verifier(external_body)]
    // pub exec fn owl_enc_st_aead(k: SecretBuf<'_>, msg: SecretBuf<'_>, iv: SecretBuf<'_>, aad: SecretBuf<'_>) -> (res: Vec<u8>)
    //     ensures
    //         res.view() == enc_st_aead(k.view(), msg.view(), iv.view(), aad.view()),
    // {
    //     let mut iv_sized = iv.to_vec();
    //     iv_sized.resize(NONCE_SIZE, 0u8);
    //     let res = match owl_aead::encrypt_combined(CIPHER, k, msg, &iv_sized[..], aad) {
    //         Ok(c) => c,
    //         Err(_e) => {
    //             // dbg!(e);
    //             vec![]
    //         }
    //     };
    //     res
    // }

    // // #[verifier(external_body)]
    // // pub exec fn owl_enc_st_aead_into(dst: &mut [u8], start: usize, end: usize, k: &[u8], msg: &[u8], nonce: &mut usize, aad: &[u8]) -> (res: Result<Ghost<Seq<u8>>, OwlError>)
    // //     ensures
    // //         res.is_Ok() ==> (dst.view().subrange(start as int, end as int), *nonce) == enc_st_aead(k.view(), msg.view(), *old(nonce), aad.view()),
    // //         res.is_Ok() ==> (res.get_Ok_0().view(), *nonce) == enc_st_aead(k.view(), msg.view(), *old(nonce), aad.view()),
    // //         res.is_Ok() ==> res.get_Ok_0().view() == dst.view().subrange(start as int, end as int)
    // //         // *nonce == *old(nonce) + 1,
    // // {
    // //     todo!()
    // //     // if *nonce > usize::MAX - 1 { return Err (OwlError::IntegerOverflow) }
    // //     // let mut iv = nonce.to_le_bytes().to_vec();
    // //     // iv.resize(NONCE_SIZE, 0u8);
    // //     // let res = match owl_aead::encrypt_combined(CIPHER, k, msg, &iv[..], aad) {
    // //     //     Ok(mut c) => {
    // //     //         let mut v = iv.to_owned();
    // //     //         v.append(&mut c);
    // //     //         v
    // //     //     },
    // //     //     Err(_e) => {
    // //     //         // dbg!(e);
    // //     //         vec![]
    // //     //     }
    // //     // };
    // //     // *nonce += 1;
    // //     // Ok(res)
    // // }


    // #[verifier(external_body)]
    // pub exec fn owl_dec_st_aead(k: SecretBuf<'_>, c: OwlBuf<'_>, nonce: SecretBuf<'_>, aad: SecretBuf<'_>, Tracked(t): Tracked<DeclassifyingOpToken>) -> (x: Option<Vec<u8>>)
    //     requires
    //         t.view() matches DeclassifyingOp::StAeadDec(k_spec, c_spec, nonce_spec, aad_spec) 
    //         && k@ == k_spec && c@ == c_spec && nonce@ == nonce_spec && aad@ == aad_spec
    //     ensures
    //         view_option(x) == dec_st_aead(k.view(), c.view(), nonce.view(), aad.view())
    //         // (k.view().len() == crate::KEY_SIZE && dec(k.view(), c.view()).is_Some()) ==>
    //         //     x.is_Some() && x.get_Some_0().view() == dec(k.view(), c.view()).get_Some_0(),
    //         // dec(k.view(), c.view()).is_None() ==> x.is_None(),
    //         // k.view().len() != crate::KEY_SIZE ==> x.is_None(),
    // {
    //     match owl_aead::decrypt_combined(CIPHER, k, &c, nonce, aad) {
    //         Ok(p) => Some(p),
    //         Err(_e) => {
    //             // dbg!(e);
    //             None
    //         }
    //     }
    // }

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

    #[verifier(external_body)]
    pub exec fn owl_xor(a: &[u8], b: &[u8]) -> (res: Vec<u8>)
        ensures res.view() == xor(a.view(), b.view())
    {
        let mut res = vec_u8_of_len(a.len());
        for i in 0..a.len() {
            res.set(i, a[i] ^ b[i]);
        }
        res
    }

    } // verus!

} // mod secret

pub use crate::execlib::secret::*;
pub use crate::*;