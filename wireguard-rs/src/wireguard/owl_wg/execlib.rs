use vstd::prelude::*;
use crate::wireguard::owl_wg::{owl_aead, speclib, deep_view::*, *};
use std::sync::Arc;

verus! {

#[verifier(external_body)]
pub exec fn arc_new<T:DView>(t: T) -> (r: Arc<T>)
    ensures r.dview() == t.dview()
{ Arc::new(t) }

#[verifier(external_body)]
pub exec fn arc_clone<T:DView>(t: &Arc<T>) -> (r: Arc<T>)
    ensures r.dview() == t.dview()
{ Arc::clone(t) }

#[verifier(external_body)]
pub exec fn vec_eq(v1: &Vec<u8>, v2: &Vec<u8>) -> (res: bool)
    ensures res == (v1.dview() == v2.dview())
{
    v1 == v2
}

#[verifier(external_body)]
pub exec fn rc_vec_eq(v1: &Arc<Vec<u8>>, v2: &Arc<Vec<u8>>) -> (res: bool)
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
pub exec fn owl_enc(k: &[u8], msg: &[u8], iv: &[u8]) -> (ctxt: Arc<Vec<u8>>)
    ensures
        ctxt.dview() == enc(k.dview(), msg.dview(), iv.dview())
    //     ((k.dview().len() == crate::KEY_SIZE && msg.dview().len() == crate::TAG_SIZE) ==> ctxt.dview() == enc(k.dview(), msg.dview(), iv.dview())),
    //    !((k.dview().len() == crate::KEY_SIZE && msg.dview().len() == crate::TAG_SIZE) ==> ctxt.dview() == seq![]),
{
    match owl_aead::encrypt_combined(cipher(), k, msg, iv, &[]) {
        Ok(mut c) => {
            let mut v = iv.to_owned();
            v.append(&mut c);
            arc_new(v)
        },
        Err(_e) => {
            // dbg!(e);
            arc_new(vec![])
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_dec(k: &[u8], c: &[u8]) -> (x: Option<Arc<Vec<u8>>>)
    ensures
        dview_option(x) == dec(k.dview(), c.dview())
        // (k.dview().len() == crate::KEY_SIZE && dec(k.dview(), c.dview()).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0().dview() == dec(k.dview(), c.dview()).get_Some_0(),
        // dec(k.dview(), c.dview()).is_None() ==> x.is_None(),
        // k.dview().len() != crate::KEY_SIZE ==> x.is_None(),
{
    match owl_aead::decrypt_combined(cipher(), k, &c[nonce_size()..], &c[..nonce_size()], &[]) {
        Ok(p) => Some(arc_new(p)),
        Err(_e) => {
            // dbg!(e);
            None
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_sign(privkey: &[u8], msg: &[u8]) -> (signature: Arc<Vec<u8>>)
    ensures signature.dview() == sign(privkey.dview(), msg.dview())
{
    arc_new(owl_pke::sign(privkey, msg))
}

#[verifier(external_body)]
pub exec fn owl_vrfy(pubkey: &[u8], msg: &[u8], signature: &[u8]) -> (x: Option<Arc<Vec<u8>>>)
    ensures dview_option(x) == vrfy(pubkey.dview(), msg.dview(), signature.dview())
{
    if owl_pke::verify(pubkey, signature, msg) {
        Some(arc_new(msg.to_vec()))
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn owl_dhpk(privkey: &[u8]) -> (pubkey: Arc<Vec<u8>>)
    ensures pubkey.dview() == dhpk(privkey.dview())
{
    arc_new(owl_dhke::ecdh_dhpk(privkey))
}


#[verifier(external_body)]
pub exec fn owl_dh_combine(pubkey: &[u8], privkey: &[u8]) -> (ss: Arc<Vec<u8>>)
    ensures
        ss.dview() == dh_combine(pubkey.dview(), privkey.dview())
{
    arc_new(owl_dhke::ecdh_combine(privkey, pubkey))
}

#[verifier(external_body)]
pub exec fn owl_extract_expand_to_len(len: usize, salt: &[u8], ikm: &[u8]) -> (h: Arc<Vec<u8>>) 
    ensures h.dview() == kdf(len.dview(), salt.dview(), ikm.dview()),
            h.dview().len() == len
{
    arc_new(owl_hkdf::extract_expand_to_len(ikm, salt, len))
}

#[verifier(external_body)]
pub exec fn owl_mac(mackey: &[u8], msg: &[u8]) -> (mac_val: Arc<Vec<u8>>)
    ensures mac_val.dview() == mac(mackey.dview(), msg.dview())
{
    //arc_new(owl_hmac::hmac(hmac_mode(), mackey, msg, None))
    // TODO: this probably ought to be a new primitive
    arc_new(owl_hmac::mac(mackey, msg))
}

#[verifier(external_body)]
pub exec fn owl_mac_vrfy(mackey: &[u8], msg: &[u8], mac: &[u8]) -> (x: Option<Arc<Vec<u8>>>)
    ensures dview_option(x) == mac_vrfy(mackey.dview(), msg.dview(), mac.dview())
{
    if owl_hmac::verify(hmac_mode(), mackey, msg, mac, None) {
        Some(arc_new(msg.to_vec()))
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn owl_pkenc(pubkey: &[u8], msg: &[u8]) -> (ctxt: Arc<Vec<u8>>)
    ensures ctxt.dview() == pkenc(pubkey.dview(), msg.dview())
{
    arc_new(owl_pke::encrypt(pubkey, msg))
}

#[verifier(external_body)]
pub exec fn owl_pkdec(privkey: &[u8], ctxt: &[u8]) -> (msg: Arc<Vec<u8>>)
    ensures msg.dview() == sign(privkey.dview(), ctxt.dview())
{
    arc_new(owl_pke::decrypt(privkey, ctxt))
}


#[verifier(external_body)]
pub exec fn owl_enc_st_aead(k: &[u8], msg: &[u8], nonce: &mut usize, aad: &[u8]) -> (res: Result<Arc<Vec<u8>>, OwlError>)
    ensures
        res.is_Ok() ==> (res.get_Ok_0().dview(), *nonce) == enc_st_aead(k.dview(), msg.dview(), *old(nonce), aad.dview()),
        // *nonce == *old(nonce) + 1,
{
    if *nonce > usize::MAX - 1 { return Err (OwlError::IntegerOverflow) }
    let mut iv = nonce.to_le_bytes().to_vec();
    iv.resize(owl_aead::nonce_size(cipher()), 0u8);
    let res = match owl_aead::encrypt_combined(cipher(), k, msg, &iv[..], aad) {
        Ok(mut c) => {
            // let mut v = iv.to_owned();
            // v.append(&mut c);
            arc_new(c)
        },
        Err(_e) => {
            // dbg!(e);
            arc_new(vec![])
        }
    };
    *nonce += 1;
    Ok(res)
}

#[verifier(external_body)]
pub exec fn owl_dec_st_aead(k: &[u8], c: &[u8], nonce: &[u8], aad: &[u8]) -> (x: Option<Arc<Vec<u8>>>)
    ensures
        dview_option(x) == dec_st_aead(k.dview(), c.dview(), nonce.dview(), aad.dview())
        // (k.dview().len() == crate::KEY_SIZE && dec(k.dview(), c.dview()).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0().dview() == dec(k.dview(), c.dview()).get_Some_0(),
        // dec(k.dview(), c.dview()).is_None() ==> x.is_None(),
        // k.dview().len() != crate::KEY_SIZE ==> x.is_None(),
{
    // match owl_aead::decrypt_combined(cipher(), k, &c[nonce_size()..], nonce, aad) {
    let mut nonce_resized = nonce.to_vec();
    nonce_resized.resize(owl_aead::nonce_size(cipher()), 0u8);
    match owl_aead::decrypt_combined(cipher(), k, c, &nonce_resized[..], aad) {
        Ok(p) => Some(arc_new(p)),
        Err(e) => {
            dbg!(e);
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
pub exec fn owl_crh(x: &[u8]) -> (res: Arc<Vec<u8>>)
    ensures res.dview() == crh(x.dview())
{
    arc_new(owl_hmac::blake2s(x))
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
    v.resize(owl_aead::nonce_size(cipher()), 0u8);
    v
}

} // verus!
