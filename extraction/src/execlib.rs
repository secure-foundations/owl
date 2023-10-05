use crate::{owl_aead, speclib, *};
use std::rc::Rc;

verus! {

#[verifier(external_body)]
pub exec fn vec_eq(v1: &Vec<u8>, v2: &Vec<u8>) -> (res: bool)
    ensures res == (v1@ == v2@)
{
    v1 == v2
}

#[verifier(external_body)]
pub exec fn rc_vec_eq(v1: &Rc<Vec<u8>>, v2: &Rc<Vec<u8>>) -> (res: bool)
    ensures res == (v1@ == v2@)
{
    v1 == v2
}

#[verifier(external_body)]
pub exec fn extend_vec_u8(v: &mut Vec<u8>, s: &[u8])
    ensures v@ == old(v)@.add(s@)
{
    v.extend(s);
}

pub exec fn vec_u8_from_elem(e: u8, n: usize) -> (res: Vec<u8>)
    ensures res@ == Seq::new(n as nat, |i| e)
{
    let mut v = Vec::new();
    let mut i = 0;
    proof { assert_seqs_equal!(v@, Seq::new(0, |i| e)); }
    while i < n
        invariant
            i <= n,
            v@ == Seq::new(i as nat, |j| e)
    {
        v.push(e);
        i = i + 1;
        proof { assert_seqs_equal!(v@, Seq::new(i as nat, |j| e)); }
    }
    v
}

#[verifier(external_body)]
pub exec fn rc_clone(rc: &Rc<Vec<u8>>) -> (res: Rc<Vec<u8>>)
    ensures rc@ == res@
{
    Rc::clone(&rc)
}

#[verifier(external_body)]
pub exec fn rc_new(v: Vec<u8>) -> (res: Rc<Vec<u8>>)
    ensures v@ == (*res)@
{
    Rc::new(v)
}

// By convention, we include the nonce at the start of the ciphertext. (TODO check wrt wire formats)

#[verifier(external_body)]
pub exec fn owl_enc(k: &[u8], msg: &[u8], iv: &[u8]) -> (ctxt: Rc<Vec<u8>>)
    ensures
        ctxt@ == enc(k@, msg@, iv@)
    //     ((k@.len() == crate::KEY_SIZE && msg@.len() == crate::TAG_SIZE) ==> ctxt@ == enc(k@, msg@, iv@)),
    //    !((k@.len() == crate::KEY_SIZE && msg@.len() == crate::TAG_SIZE) ==> ctxt@ == seq![]),
{
    match owl_aead::encrypt_combined(cipher(), k, msg, iv, &[]) {
        Ok(mut c) => {
            let mut v = iv.to_owned();
            v.append(&mut c);
            rc_new(v)
        },
        Err(_e) => {
            // dbg!(e);
            rc_new(vec![])
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_dec(k: &[u8], c: &[u8]) -> (x: Option<Rc<Vec<u8>>>)
    ensures
        view_option(x) == dec(k@, c@)
        // (k@.len() == crate::KEY_SIZE && dec(k@, c@).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0()@ == dec(k@, c@).get_Some_0(),
        // dec(k@, c@).is_None() ==> x.is_None(),
        // k@.len() != crate::KEY_SIZE ==> x.is_None(),
{
    match owl_aead::decrypt_combined(cipher(), k, &c[nonce_size()..], &c[..nonce_size()], &[]) {
        Ok(p) => Some(rc_new(p)),
        Err(_e) => {
            // dbg!(e);
            None
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_sign(privkey: &[u8], msg: &[u8]) -> (signature: Rc<Vec<u8>>)
    ensures signature@ == sign(privkey@, msg@)
{
    rc_new(owl_pke::sign(privkey, msg))
}

#[verifier(external_body)]
pub exec fn owl_vrfy(pubkey: &[u8], msg: &[u8], signature: &[u8]) -> (x: Option<Rc<Vec<u8>>>)
    ensures view_option(x) == vrfy(pubkey@, msg@, signature@)
{
    if owl_pke::verify(pubkey, signature, msg) {
        Some(rc_new(msg.to_vec()))
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn owl_dhpk(privkey: &[u8]) -> (pubkey: Rc<Vec<u8>>)
    ensures pubkey@ == dhpk(privkey@)
{
    rc_new(owl_dhke::ecdh_dhpk(privkey))
}


#[verifier(external_body)]
pub exec fn owl_dh_combine(pubkey: &[u8], privkey: &[u8]) -> (ss: Rc<Vec<u8>>)
    ensures
        ss@ == dh_combine(pubkey@, privkey@)
{
    rc_new(owl_dhke::ecdh_combine(privkey, pubkey))
}

#[verifier(external_body)]
pub exec fn owl_extract_expand_to_len(salt: &[u8], len: usize, ikm: &[u8]) -> (h: Rc<Vec<u8>>) 
    ensures h@ == kdf(len@, ikm@),
            h@.len() == len
{
    rc_new(owl_hkdf::extract_expand_to_len(ikm, salt, len))
}

#[verifier(external_body)]
pub exec fn owl_mac(mackey: &[u8], msg: &[u8]) -> (mac_val: Rc<Vec<u8>>)
    ensures mac_val@ == mac(mackey@, msg@)
{
    rc_new(owl_hmac::hmac(hmac_mode(), mackey, msg, None))
}

#[verifier(external_body)]
pub exec fn owl_mac_vrfy(mackey: &[u8], msg: &[u8], mac: &[u8]) -> (x: Option<Rc<Vec<u8>>>)
    ensures view_option(x) == mac_vrfy(mackey@, msg@, mac@)
{
    if owl_hmac::verify(hmac_mode(), mackey, msg, mac, None) {
        Some(rc_new(msg.to_vec()))
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn owl_pkenc(pubkey: &[u8], msg: &[u8]) -> (ctxt: Rc<Vec<u8>>)
    ensures ctxt@ == pkenc(pubkey@, msg@)
{
    rc_new(owl_pke::encrypt(pubkey, msg))
}

#[verifier(external_body)]
pub exec fn owl_pkdec(privkey: &[u8], ctxt: &[u8]) -> (msg: Rc<Vec<u8>>)
    ensures msg@ == sign(privkey@, ctxt@)
{
    rc_new(owl_pke::decrypt(privkey, ctxt))
}


#[verifier(external_body)]
pub exec fn owl_enc_st_aead(k: &[u8], msg: &[u8], nonce: &mut usize, aad: &[u8]) -> (res: Result<Rc<Vec<u8>>, OwlError>)
    ensures
        res.is_Ok() ==> (res.get_Ok_0()@, *nonce) == enc_st_aead(k@, msg@, *old(nonce), aad@),
        // *nonce == *old(nonce) + 1,
{
    if *nonce > usize::MAX - 1 { return Err (OwlError::IntegerOverflow) }
    let mut iv = nonce.to_le_bytes().to_vec();
    iv.resize(nonce_size(), 0u8);
    let res = match owl_aead::encrypt_combined(cipher(), k, msg, &iv[..], aad) {
        Ok(mut c) => {
            let mut v = iv.to_owned();
            v.append(&mut c);
            rc_new(v)
        },
        Err(_e) => {
            // dbg!(e);
            rc_new(vec![])
        }
    };
    *nonce += 1;
    Ok(res)
}

#[verifier(external_body)]
pub exec fn owl_dec_st_aead(k: &[u8], c: &[u8], nonce: usize, aad: &[u8]) -> (x: Option<Rc<Vec<u8>>>)
    ensures
        view_option(x) == dec_st_aead(k@, c@, nonce, aad@)
        // (k@.len() == crate::KEY_SIZE && dec(k@, c@).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0()@ == dec(k@, c@).get_Some_0(),
        // dec(k@, c@).is_None() ==> x.is_None(),
        // k@.len() != crate::KEY_SIZE ==> x.is_None(),
{
    let mut iv = nonce.to_le_bytes().to_vec();
    iv.resize(nonce_size(), 0u8);
    match owl_aead::decrypt_combined(cipher(), k, &c[nonce_size()..], &iv, aad) {
        Ok(p) => Some(rc_new(p)),
        Err(_e) => {
            // dbg!(e);
            None
        }
    }
}



} // verus!
