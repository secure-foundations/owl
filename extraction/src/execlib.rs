use crate::{owl_aead, *};
use std::rc::Rc;

verus! {

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
pub exec fn owl_enc(k: &[u8], msg: &[u8], iv: &[u8]) -> (ctxt: Vec<u8>)
    ensures
        ctxt@ == speclib::enc(k@, msg@, iv@)
    //     ((k@.len() == crate::KEY_SIZE && msg@.len() == crate::TAG_SIZE) ==> ctxt@ == speclib::enc(k@, msg@, iv@)),
    //    !((k@.len() == crate::KEY_SIZE && msg@.len() == crate::TAG_SIZE) ==> ctxt@ == seq![]),
{
    match owl_aead::encrypt_combined(cipher(), k, msg, iv, &[]) {
        Ok(mut c) => {
            let mut v = iv.to_owned();
            v.append(&mut c);
            v
        },
        Err(e) => {
            // dbg!(e);
            vec![]
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_dec(k: &[u8], c: &[u8]) -> (x: Option<Vec<u8>>)
    ensures
        speclib::view_option(x) == speclib::dec(k@, c@)
        // (k@.len() == crate::KEY_SIZE && speclib::dec(k@, c@).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0()@ == speclib::dec(k@, c@).get_Some_0(),
        // speclib::dec(k@, c@).is_None() ==> x.is_None(),
        // k@.len() != crate::KEY_SIZE ==> x.is_None(),
{
    match owl_aead::decrypt_combined(cipher(), k, &c[nonce_size()..], &c[..nonce_size()], &[]) {
        Ok(p) => Some(p),
        Err(e) => {
            // dbg!(e);
            None
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_sign(privkey: &[u8], msg: &[u8]) -> (signature: Vec<u8>)
    ensures signature@ == speclib::sign(privkey@, msg@)
{
    owl_pke::sign(privkey, msg)
}

#[verifier(external_body)]
pub exec fn owl_vrfy(pubkey: &[u8], msg: &[u8], signature: &[u8]) -> (x: Option<Vec<u8>>)
    ensures speclib::view_option(x) == speclib::vrfy(pubkey@, msg@, signature@)
{
    if owl_pke::verify(pubkey, signature, msg) {
        Some(msg.to_vec())
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn owl_dhpk(privkey: &[u8]) -> (pubkey: Vec<u8>)
    ensures pubkey@ == speclib::dhpk(privkey@)
{
    owl_dhke::ecdh_dhpk(privkey)
}


#[verifier(external_body)]
pub exec fn owl_dh_combine(pubkey: &[u8], privkey: &[u8]) -> (ss: Vec<u8>)
    ensures
        ss@ == speclib::dh_combine(pubkey@, privkey@)
{
    owl_dhke::ecdh_combine(privkey, pubkey)
}

#[verifier(external_body)]
pub exec fn owl_extract_expand_to_len(salt: &[u8], len: usize, ikm: &[u8]) -> (h: Vec<u8>) 
    ensures h@ == kdf(ikm@)
{
    owl_hkdf::extract_expand_to_len(ikm, salt, len)
}

#[verifier(external_body)]
pub exec fn owl_mac(mackey: &[u8], msg: &[u8]) -> (mac: Vec<u8>)
    ensures mac@ == speclib::mac(mackey@, msg@)
{
    owl_hmac::hmac(hmac_mode(), mackey, msg, None)
}

#[verifier(external_body)]
pub exec fn owl_mac_vrfy(mackey: &[u8], msg: &[u8], mac: &[u8]) -> (x: Option<Vec<u8>>)
    ensures speclib::view_option(x) == speclib::mac_vrfy(mackey@, msg@, mac@)
{
    if owl_hmac::verify(hmac_mode(), mackey, msg, mac, None) {
        Some(msg.to_vec())
    } else {
        None
    }
}

#[verifier(external_body)]
pub exec fn owl_pkenc(pubkey: &[u8], msg: &[u8]) -> (ctxt: Vec<u8>)
    ensures ctxt@ == speclib::pkenc(pubkey@, msg@)
{
    owl_pke::encrypt(pubkey, msg)
}

#[verifier(external_body)]
pub exec fn owl_pkdec(privkey: &[u8], ctxt: &[u8]) -> (msg: Vec<u8>)
    ensures msg@ == speclib::sign(privkey@, ctxt@)
{
    owl_pke::decrypt(privkey, ctxt)
}


#[verifier(external_body)]
pub exec fn owl_enc_with_nonce(k: &[u8], msg: &[u8], nonce: usize) -> (ctxt: Vec<u8>)
    ensures
        ctxt@ == speclib::enc_with_nonce(k@, msg@, nonce)
{
    let mut iv = nonce.to_le_bytes().to_vec();
    iv.resize(nonce_size(), 0u8);
    match owl_aead::encrypt_combined(cipher(), k, msg, &iv[..], &[]) {
        Ok(mut c) => {
            let mut v = iv.to_owned();
            v.append(&mut c);
            v
        },
        Err(e) => {
            // dbg!(e);
            vec![]
        }
    }
}

#[verifier(external_body)]
pub exec fn owl_dec_with_nonce(k: &[u8], nonce: usize, c: &[u8]) -> (x: Option<Vec<u8>>)
    ensures
        speclib::view_option(x) == speclib::dec_with_nonce(k@, nonce, c@)
        // (k@.len() == crate::KEY_SIZE && speclib::dec(k@, c@).is_Some()) ==>
        //     x.is_Some() && x.get_Some_0()@ == speclib::dec(k@, c@).get_Some_0(),
        // speclib::dec(k@, c@).is_None() ==> x.is_None(),
        // k@.len() != crate::KEY_SIZE ==> x.is_None(),
{
    let mut iv = nonce.to_le_bytes().to_vec();
    iv.resize(nonce_size(), 0u8);
    match owl_aead::decrypt_combined(cipher(), k, &c[nonce_size()..], &iv, &[]) {
        Ok(p) => Some(p),
        Err(e) => {
            // dbg!(e);
            None
        }
    }
}



} // verus!
