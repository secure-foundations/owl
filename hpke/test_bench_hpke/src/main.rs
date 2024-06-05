use rand::{rngs::StdRng, SeedableRng};
use hpke::{*, aead::*, kdf::*, kem::*, setup_receiver, setup_sender};
use owl_hpke::{*};
use hex;


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

fn owl_send(receiver_pk: &[u8], msg: &[u8]) -> Vec<u8> {
    todo!()
}

fn owl_recv(receiver_sk: &[u8], ctxt: &[u8]) -> Vec<u8> {
    todo!()
}

fn rust_send(receiver_pk: &[u8], msg: &[u8]) -> Vec<u8> {
    let mut csprng = StdRng::from_entropy();
    let associated_data = b"";

    let receiver_pk = <HPKE_Kem as Kem>::PublicKey::from_bytes(receiver_pk)
        .expect("could not deserialize receiver pubkey!");

    // Encapsulate a key and use the resulting shared secret to encrypt a message. The AEAD context
    // is what you use to encrypt.
    let (encapped_key, mut sender_ctx) =
        hpke::setup_sender::<HPKE_Aead, HPKE_Kdf, HPKE_Kem, _>(&OpModeS::Base, &receiver_pk, INFO_STR, &mut csprng)
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

fn rust_recv(receiver_sk: &[u8], msg: &[u8]) -> Vec<u8> {
    // "parse"
    let encapped_key = &msg[0..ENCAPPED_KEY_SIZE];
    let ctxt = &msg[ENCAPPED_KEY_SIZE..msg.len()-TAG_SIZE];
    let tag = &msg[msg.len()-TAG_SIZE..msg.len()];
    let associated_data = b"";

    // We have to derialize the secret key, AEAD tag, and encapsulated pubkey. These fail if the
    // bytestrings are the wrong length.
    let server_sk = <HPKE_Kem as Kem>::PrivateKey::from_bytes(receiver_sk)
        .expect("could not deserialize server privkey!");
    let tag = AeadTag::<HPKE_Aead>::from_bytes(tag).expect("could not deserialize AEAD tag!");
    let encapped_key = <HPKE_Kem as Kem>::EncappedKey::from_bytes(encapped_key)
        .expect("could not deserialize the encapsulated pubkey!");

    // Decapsulate and derive the shared secret. This creates a shared AEAD context.
    let mut receiver_ctx =
        hpke::setup_receiver::<HPKE_Aead, HPKE_Kdf, HPKE_Kem>(&OpModeR::Base, &server_sk, &encapped_key, INFO_STR)
            .expect("failed to set up receiver!");

    // On success, open_in_place_detached() will decrypt the ciphertext in place
    let mut ciphertext_copy = ctxt.to_vec();
    receiver_ctx
        .open_in_place_detached(&mut ciphertext_copy, associated_data, &tag)
        .expect("invalid ciphertext!");

    // Rename for clarity. Cargo clippy thinks it's unnecessary, but I disagree
    #[allow(clippy::let_and_return)]
    let plaintext = ciphertext_copy;

    plaintext
}


fn basic_test() {
    let (receiver_privkey, receiver_pubkey) = gen_keypair();

    let plaintext: Vec<u8> = vec![0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef,];
    dbg!(hex::encode(&plaintext));

    let rust_ctxt = rust_send(&receiver_pubkey, &plaintext);
    dbg!(hex::encode(&rust_ctxt));

    let rust_plaintext = rust_recv(&receiver_privkey, &rust_ctxt);
    dbg!(hex::encode(&rust_plaintext));

    assert_eq!(plaintext, rust_plaintext);
}


fn main() {
    basic_test();
}
