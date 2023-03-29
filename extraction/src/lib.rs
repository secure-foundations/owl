pub mod owl_aead;
pub mod owl_dhke;
pub mod owl_hkdf;
pub mod owl_hmac;
pub mod owl_pke;
pub mod owl_util;

#[cfg(test)]
mod tests {
    #[test]
    fn hmac_example() {
        use crate::owl_hmac::{hmac, Mode};
        let key = [
            0x85, 0xa7, 0xcb, 0xaa, 0xe8, 0x25, 0xbb, 0x82, 0xc9, 0xb6, 0xf6, 0xc5, 0xc2, 0xaf,
            0x5a, 0xc0, 0x3d, 0x1f, 0x6d, 0xaa, 0x63, 0xd2, 0xa9, 0x3c, 0x18, 0x99, 0x48, 0xec,
            0x41, 0xb9, 0xde, 0xd9,
        ];
        let data = [0xa5, 0x9b];
        let expected_tag = [
            0x0f, 0xe2, 0xf1, 0x3b, 0xba, 0x21, 0x98, 0xf6, 0xdd, 0xa1, 0xa0, 0x84, 0xbe, 0x92,
            0x8e, 0x30, 0x4e, 0x9c, 0xb1, 0x6a, 0x56, 0xbc, 0x0b, 0x7b, 0x93, 0x9a, 0x07, 0x32,
            0x80, 0x24, 0x43, 0x73,
        ];
        let len = 32;

        let tag = hmac(Mode::Sha256, &key, &data, Some(len));
        assert_eq!(expected_tag[..], tag[..]);
    }

    #[test]
    fn aead_example() {
        use crate::owl_aead::{decrypt, encrypt, Mode};
        let key = [
            0x5b, 0x96, 0x04, 0xfe, 0x14, 0xea, 0xdb, 0xa9, 0x31, 0xb0, 0xcc, 0xf3, 0x48, 0x43,
            0xda, 0xb9, 0x5b, 0x96, 0x04, 0xfe, 0x14, 0xea, 0xdb, 0xa9, 0x31, 0xb0, 0xcc, 0xf3,
            0x48, 0x43, 0xda, 0xb9,
        ];
        let iv = [
            0x02, 0x83, 0x18, 0xab, 0xc1, 0x82, 0x40, 0x29, 0x13, 0x81, 0x41, 0xa2,
        ];
        let msg = [
            0x00, 0x1d, 0x0c, 0x23, 0x12, 0x87, 0xc1, 0x18, 0x27, 0x84, 0x55, 0x4c, 0xa3, 0xa2,
            0x19, 0x08,
        ];
        let aad = [];

        let (ciphertext, tag) = match encrypt(Mode::Chacha20Poly1305, &key, &msg, &iv, &aad) {
            Ok(r) => r,
            Err(e) => panic!("Error encrypting.{:?}", e),
        };

        let msg_ = match decrypt(Mode::Chacha20Poly1305, &key, &ciphertext, &tag, &iv, &aad) {
            Ok(r) => r,
            Err(e) => panic!("Error decrypting.{:?}", e),
        };

        assert_eq!(&msg[..], &msg_[..]);
    }

    #[test]
    fn randomly_test_aead() {
        use crate::owl_aead::*;
        use crate::owl_util::gen_rand_bytes;
        fn check_aead(alg: Mode) {
            let key = gen_rand_key(alg);

            let iv = gen_rand_nonce(alg);

            let msg = gen_rand_bytes(1024);

            let aad = gen_rand_bytes(128);

            let (ciphertext, tag) = match encrypt(
                alg,
                &key[..key_size(alg)],
                &msg,
                &iv[..nonce_size(alg)],
                &aad,
            ) {
                Ok(r) => r,
                Err(e) => panic!("Error encrypting.{:?}", e),
            };

            let ctxt_tag = match encrypt_combined(
                alg,
                &key[..key_size(alg)],
                &msg,
                &iv[..nonce_size(alg)],
                &aad,
            ) {
                Ok(r) => r,
                Err(e) => panic!("Error in encrypt_combined.{:?}", e),
            };

            assert_eq!([&ciphertext[..], &tag[..]].concat(), ctxt_tag);

            let msg_ = match decrypt(
                alg,
                &key[..key_size(alg)],
                &ciphertext,
                &tag,
                &iv[..nonce_size(alg)],
                &aad,
            ) {
                Ok(r) => r,
                Err(e) => panic!("Error decrypting.{:?}", e),
            };

            let msg__ = match decrypt_combined(
                alg,
                &key[..key_size(alg)],
                &ctxt_tag,
                &iv[..nonce_size(alg)],
                &aad,
            ) {
                Ok(r) => r,
                Err(e) => panic!("Error in decrypt_combined.{:?}", e),
            };

            assert_eq!(&msg[..], &msg_[..]);
            assert_eq!(&msg[..], &msg__[..]);
        }

        for _ in 0..1000 {
            check_aead(Mode::Aes128Gcm);
            check_aead(Mode::Aes256Gcm);
            check_aead(Mode::Chacha20Poly1305);
        }
    }

    #[test]
    fn randomly_test_pke() {
        use crate::owl_pke::*;
        use crate::owl_util::*;

        fn check_pke() {
            let (privkey, pubkey) = gen_rand_keys();
            let msg = gen_rand_bytes(64);
            let ctxt = encrypt(&pubkey, &msg);
            let msg_ = decrypt(&privkey, &ctxt);
            assert_eq!(&msg[..], &msg_[..]);
        }

        for _ in 0..10 {
            check_pke();
        }
    }

    #[test]
    fn randomly_test_pke_sign() {
        use crate::owl_pke::*;
        use crate::owl_util::*;

        fn check_pke_sign() {
            let (privkey, pubkey) = gen_rand_keys();
            let msg = gen_rand_bytes(64);
            let sig = sign(&privkey, &msg);
            if !verify(&pubkey, &sig, &msg) {
                panic!("check_pke_sign failed");
            }
        }

        for _ in 0..10 {
            check_pke_sign();
        }
    }

    #[test]
    fn randomly_test_ecdh() {
        use crate::owl_dhke::*;

        fn check_ecdh() {
            let (alice_sk, alice_pk) = gen_ecdh_key_pair();
            let (bob_sk, bob_pk) = gen_ecdh_key_pair();
            let alice_ss = ecdh_combine(&alice_sk[..], &bob_pk[..]);
            let bob_ss = ecdh_combine(&bob_sk[..], &alice_pk[..]);
            assert_eq!(alice_ss, bob_ss);
        }

        for _ in 0..20 {
            check_ecdh();
        }
    }
}
