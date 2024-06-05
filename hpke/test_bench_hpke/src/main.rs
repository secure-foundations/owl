#![feature(test)]
extern crate test;

use rand::{rngs::StdRng, SeedableRng};
use hpke::{*, aead::*, kdf::*, kem::*, setup_receiver, setup_sender};
use owl_hpke::{*};
use hex;

// Some code is copied from the client-server example in rust-hpke

type HPKE_Kem = X25519HkdfSha256;
type HPKE_Aead = ChaCha20Poly1305;
type HPKE_Kdf = HkdfSha256;

const ENCAPPED_KEY_SIZE: usize = 32;
const TAG_SIZE: usize = 16;

const INFO_STR: &[u8] = b"";

fn gen_keypair() -> (Vec<u8>, Vec<u8>) {
    let mut csprng = StdRng::from_entropy();
    let (privkey, pubkey) = HPKE_Kem::gen_keypair(&mut csprng);
    (privkey.to_bytes().to_vec(), pubkey.to_bytes().to_vec())
}

fn gen_psk() -> Vec<u8> {
    owl_hpke::owl_util::gen_rand_bytes(32)
}

fn owl_send(receiver_pk: &[u8], skS: &[u8], pk_skS: &[u8], psk: &[u8], msg: &[u8]) -> Vec<u8> {
    let (skE, pk_skE) = gen_keypair();

    let cfg = owl_hpke::cfg_sender {
        salt: vec![],
        owl_psk: psk.to_vec(),
        owl_skS: skS.to_vec(),
        owl_skE: skE,
        pk_owl_skS: pk_skS.to_vec(),
        pk_owl_skE: pk_skE,
        pk_owl_skR: vec![]
    };
    let mut state = owl_hpke::state_sender::init_state_sender();

    let mut obuf = vec![0u8; ENCAPPED_KEY_SIZE + msg.len() + TAG_SIZE];
    
    cfg.owl_SingleShotSeal_wrapper(&mut state, receiver_pk, msg, &mut obuf);

    obuf
}

fn owl_recv(receiver_sk: &[u8], pk_skS: &[u8], psk: &[u8], enc_msg: &[u8]) -> Vec<u8> {
    let cfg = owl_hpke::cfg_receiver {
        salt: vec![],
        owl_psk: psk.to_vec(),
        owl_skR: receiver_sk.to_vec(),
        pk_owl_skR: vec![],
        pk_owl_skE: vec![],
        pk_owl_skS: vec![],
    };
    let mut state = owl_hpke::state_receiver::init_state_receiver();

    let res = cfg.owl_SingleShotOpen_wrapper(&mut state, pk_skS, enc_msg);

    match res.unwrap().owl_or_pt {
        owl_OpenMsg::owl_NoMsg() => panic!("owl_recv failed"),
        owl_OpenMsg::owl_SomeMsg(pt) => pt.as_slice().to_vec(),
    }
}

fn rust_send(receiver_pk: &[u8], skS: &[u8], pk_skS: &[u8], psk: &[u8], msg: &[u8]) -> Vec<u8> {
    let mut csprng = StdRng::from_entropy();
    let associated_data = b"";

    let receiver_pk = <HPKE_Kem as Kem>::PublicKey::from_bytes(receiver_pk)
        .expect("could not deserialize receiver pubkey!");

    // Encapsulate a key and use the resulting shared secret to encrypt a message. The AEAD context
    // is what you use to encrypt.
    let opmode = OpModeS::AuthPsk((
        <HPKE_Kem as Kem>::PrivateKey::from_bytes(skS).unwrap(),
        <HPKE_Kem as Kem>::PublicKey::from_bytes(pk_skS).unwrap(),
    ), PskBundle { psk: psk, psk_id: b"" });
    let (encapped_key, mut sender_ctx) =
        hpke::setup_sender::<HPKE_Aead, HPKE_Kdf, HPKE_Kem, _>(&opmode, &receiver_pk, INFO_STR, &mut csprng)
            .expect("invalid server pubkey!");

    // On success, seal_in_place_detached() will encrypt the plaintext in place
    let mut msg_copy = msg.to_vec();
    let tag = sender_ctx
        .seal_in_place_detached(&mut msg_copy, associated_data)
        .expect("encryption failed!");

    // Rename for clarity
    let ciphertext = msg_copy;

    // "serialize"
    let mut output = vec![];
    output.extend_from_slice(encapped_key.to_bytes().as_ref());
    output.extend_from_slice(&ciphertext);
    output.extend_from_slice(tag.to_bytes().as_ref());
    output
}

fn rust_recv(receiver_sk: &[u8], pk_skS: &[u8], psk: &[u8], enc_msg: &[u8]) -> Vec<u8> {
    // "parse"
    let encapped_key = &enc_msg[0..ENCAPPED_KEY_SIZE];
    let ctxt = &enc_msg[ENCAPPED_KEY_SIZE..enc_msg.len()-TAG_SIZE];
    let tag = &enc_msg[enc_msg.len()-TAG_SIZE..enc_msg.len()];
    let associated_data = b"";

    // We have to derialize the secret key, AEAD tag, and encapsulated pubkey. These fail if the
    // bytestrings are the wrong length.
    let server_sk = <HPKE_Kem as Kem>::PrivateKey::from_bytes(receiver_sk)
        .expect("could not deserialize server privkey!");
    let tag = AeadTag::<HPKE_Aead>::from_bytes(tag).expect("could not deserialize AEAD tag!");
    let encapped_key = <HPKE_Kem as Kem>::EncappedKey::from_bytes(encapped_key)
        .expect("could not deserialize the encapsulated pubkey!");

    // Decapsulate and derive the shared secret. This creates a shared AEAD context.
    let opmode = OpModeR::AuthPsk(
        <HPKE_Kem as Kem>::PublicKey::from_bytes(pk_skS).unwrap(),
        PskBundle { psk: psk, psk_id: b"" },
    );
    let mut receiver_ctx =
        hpke::setup_receiver::<HPKE_Aead, HPKE_Kdf, HPKE_Kem>(&opmode, &server_sk, &encapped_key, INFO_STR)
            .expect("failed to set up receiver!");

    // On success, open_in_place_detached() will decrypt the ciphertext in place
    let mut ciphertext_copy = ctxt.to_vec();
    receiver_ctx
        .open_in_place_detached(&mut ciphertext_copy, associated_data, &tag)
        .map_err(|e| { dbg!(e); panic!("invalid ciphertext!") });

    // Rename for clarity. Cargo clippy thinks it's unnecessary, but I disagree
    #[allow(clippy::let_and_return)]
    let plaintext = ciphertext_copy;

    plaintext
}


fn basic_interop_test() {
    let (receiver_privkey, receiver_pubkey) = gen_keypair();
    let (skS, pk_skS) = gen_keypair();
    let psk = gen_psk();

    let plaintext: Vec<u8> = vec![0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef,];
    dbg!(hex::encode(&plaintext));

    let rust_ctxt = rust_send(&receiver_pubkey, &skS, &pk_skS, &psk, &plaintext);
    dbg!(hex::encode(&rust_ctxt));

    let owl_ctxt = owl_send(&receiver_pubkey, &skS, &pk_skS, &psk, &plaintext);
    dbg!(hex::encode(&owl_ctxt));

    let rust_plaintext = rust_recv(&receiver_privkey, &pk_skS, &psk, &rust_ctxt);
    dbg!(hex::encode(&rust_plaintext));

    let owl_plaintext = owl_recv(&receiver_privkey, &pk_skS, &psk, &owl_ctxt);
    dbg!(hex::encode(&owl_plaintext));

    let rust_decrypt_owl = rust_recv(&receiver_privkey, &pk_skS, &psk, &owl_ctxt);
    dbg!(hex::encode(&rust_decrypt_owl));

    let owl_decrypt_rust = owl_recv(&receiver_privkey, &pk_skS, &psk, &rust_ctxt);
    dbg!(hex::encode(&owl_decrypt_rust));

    assert_eq!(plaintext, rust_plaintext);
    assert_eq!(plaintext, owl_plaintext);
}

#[test]
fn test_interop() {
    basic_interop_test();
}

#[test]
fn test_rs_rs() {
    let (receiver_privkey, receiver_pubkey) = gen_keypair();
    let (skS, pk_skS) = gen_keypair();
    let psk = gen_psk();

    let plaintext: Vec<u8> = vec![0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef,];

    let rust_ctxt = rust_send(&receiver_pubkey, &skS, &pk_skS, &psk, &plaintext);
    let rust_plaintext = rust_recv(&receiver_privkey, &pk_skS, &psk, &rust_ctxt);

    assert_eq!(plaintext, rust_plaintext);
}

#[test]
fn test_owl_owl() {
    let (receiver_privkey, receiver_pubkey) = gen_keypair();
    let (skS, pk_skS) = gen_keypair();
    let psk = gen_psk();

    let plaintext: Vec<u8> = vec![0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef,];

    let owl_ctxt = owl_send(&receiver_pubkey, &skS, &pk_skS, &psk, &plaintext);
    let owl_plaintext = owl_recv(&receiver_privkey, &pk_skS, &psk, &owl_ctxt);

    assert_eq!(plaintext, owl_plaintext);
}

use test::Bencher;

const PAYLOAD_SIZE: usize = 0;

#[bench]
fn bench_rust(b: &mut Bencher) {
    let (receiver_privkey, receiver_pubkey) = gen_keypair();
    let (skS, pk_skS) = gen_keypair();
    let psk = gen_psk();

    let plaintext: Vec<u8> = owl_hpke::owl_util::gen_rand_bytes(PAYLOAD_SIZE);

    b.iter(|| {
        let rust_ctxt = rust_send(&receiver_pubkey, &skS, &pk_skS, &psk, &plaintext);
        let rust_plaintext = rust_recv(&receiver_privkey, &pk_skS, &psk, &rust_ctxt);
        test::black_box(rust_plaintext);
    });
}

#[bench]
fn bench_owl(b: &mut Bencher) {
    let (receiver_privkey, receiver_pubkey) = gen_keypair();
    let (skS, pk_skS) = gen_keypair();
    let psk = gen_psk();

    let plaintext: Vec<u8> = owl_hpke::owl_util::gen_rand_bytes(PAYLOAD_SIZE);

    b.iter(|| {
        let owl_ctxt = owl_send(&receiver_pubkey, &skS, &pk_skS, &psk, &plaintext);
        let owl_plaintext = owl_recv(&receiver_privkey, &pk_skS, &psk, &owl_ctxt);
        test::black_box(owl_plaintext);
    });
}


fn main() {
    basic_interop_test();
}
