use rand::{rngs::StdRng, SeedableRng};
use hpke::{*, aead::*, kdf::*, kem::*, setup_receiver, setup_sender};
use owl_hpke::{*};

type HPKE_Kem = X25519HkdfSha256;
type HPKE_Aead = ChaCha20Poly1305;
type HPKE_Kdf = HkdfSha256;



fn server_init() -> (Vec<u8>, Vec<u8>) {
    let mut csprng = StdRng::from_entropy();
    let (privkey, pubkey) = HPKE_Kem::gen_keypair(&mut csprng);
    (privkey.to_bytes().to_vec(), pubkey.to_bytes().to_vec())
}


fn basic_test() {
    let (privkey, pubkey) = server_init();
    println!("privkey: {:?}", privkey);
    println!("pubkey: {:?}", pubkey);
    
}


fn main() {
    basic_test();
}
