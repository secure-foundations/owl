// KEM for the Owl support library: Kyber1024 and ML-KEM-1024 from libcrux-ml-kem, the
// implementation (and version) that libsignal calls (rust/protocol/src/kem/{kyber1024,
// mlkem1024}.rs). Available in every feature configuration.
//
// Keys and ciphertexts are in libsignal's serialized forms: one key-type byte followed by
// the raw value.
//   - public key:  type || ek   (1 + 1568 bytes)
//   - secret key:  type || dk   (1 + 3168 bytes)
//   - ciphertext:  type || ct   (1 + 1568 bytes)
// with type 0x08 = Kyber1024 and 0x0A = ML-KEM-1024. The shared secret is 32 bytes.
//
// The Owl model's kem_pk is the raw encapsulation key of a Kyber1024 key: Bob signs
// Encode(PK) = 0x08 ++ kem_pk(pqbo), which is libsignal's serialized Kyber1024 public key,
// and the verified path only takes Kyber1024 prekeys. So the Owl-facing functions
// encapsulate_kyber1024_raw and kyber1024_raw_public_key_of take and return the raw
// public key; secret keys and ciphertexts stay serialized.
//
// The functions below are plain Rust; the trusted Verus wrappers (owl_kem_encaps,
// owl_kem_decaps, owl_kem_pk) are in execlib.rs, and the length constants (KEM_PK_SIZE,
// KEM_CIPHERLEN_SIZE, KEMKEY_SIZE, KEM_COINS_SIZE) are in execlib.rs as well.

use libcrux_ml_kem::mlkem1024::{MlKem1024Ciphertext, MlKem1024PrivateKey, MlKem1024PublicKey};
use libcrux_ml_kem::{kyber1024, mlkem1024};

/// Key type byte of Kyber1024 keys and ciphertexts (libsignal `KeyType::Kyber1024`)
pub const KEY_TYPE_KYBER1024: u8 = 0x08;
/// Key type byte of ML-KEM-1024 keys and ciphertexts (libsignal `KeyType::MLKEM1024`)
pub const KEY_TYPE_MLKEM1024: u8 = 0x0A;

pub const RAW_PK_LEN: usize = 1568;
pub const RAW_SK_LEN: usize = 3168;
pub const RAW_CT_LEN: usize = 1568;
pub const SERIALIZED_PK_LEN: usize = 1 + RAW_PK_LEN;
pub const SERIALIZED_SK_LEN: usize = 1 + RAW_SK_LEN;
pub const SERIALIZED_CT_LEN: usize = 1 + RAW_CT_LEN;
pub const SHARED_SECRET_LEN: usize = libcrux_ml_kem::SHARED_SECRET_SIZE;
/// The randomness of one encapsulation (libsignal passes `csprng.random()`)
pub const COINS_LEN: usize = 32;

// In a decapsulation key dk = dk_pke || ek || H(ek) || z (FIPS 203; the same layout for
// Kyber round 3), ek starts after dk_pke, which is 384 * k = 1536 bytes for k = 4
const EK_OFFSET_IN_DK: usize = 1536;

fn is_supported_key_type(t: u8) -> bool {
    t == KEY_TYPE_KYBER1024 || t == KEY_TYPE_MLKEM1024
}

/// Splits a serialized value into its key type and raw value, if it has a supported key
/// type and the right length
fn split_serialized(x: &[u8], raw_len: usize) -> Option<(u8, &[u8])> {
    if x.len() != 1 + raw_len || !is_supported_key_type(x[0]) {
        return None;
    }
    Some((x[0], &x[1..]))
}

fn serialize(key_type: u8, raw: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(1 + raw.len());
    v.push(key_type);
    v.extend_from_slice(raw);
    v
}

/// Encapsulation to a serialized public key with the given coins. Returns the shared
/// secret and the serialized ciphertext (with the key type of the public key), or None if
/// the public key does not have a supported key type and length, or the coins are not
/// COINS_LEN bytes. Deterministic in (pk, coins).
pub fn encapsulate(pk: &[u8], coins: &[u8]) -> Option<(Vec<u8>, Vec<u8>)> {
    let (key_type, raw_pk) = split_serialized(pk, RAW_PK_LEN)?;
    let coins: [u8; COINS_LEN] = coins.try_into().ok()?;
    let pk = MlKem1024PublicKey::try_from(raw_pk).ok()?;
    let (ct, ss) = match key_type {
        KEY_TYPE_KYBER1024 => kyber1024::encapsulate(&pk, coins),
        KEY_TYPE_MLKEM1024 => mlkem1024::encapsulate(&pk, coins),
        _ => return None,
    };
    Some((ss.as_ref().to_vec(), serialize(key_type, ct.as_ref())))
}

/// Decapsulation of a serialized ciphertext with a serialized secret key. Returns None if
/// either does not have a supported key type and length, or their key types differ (as
/// libsignal does). Otherwise it returns a shared secret: ML-KEM (and Kyber) use implicit
/// rejection, so an invalid ciphertext of the right length yields a pseudorandom value.
pub fn decapsulate(sk: &[u8], ct: &[u8]) -> Option<Vec<u8>> {
    let (sk_type, raw_sk) = split_serialized(sk, RAW_SK_LEN)?;
    let (ct_type, raw_ct) = split_serialized(ct, RAW_CT_LEN)?;
    if sk_type != ct_type {
        return None;
    }
    let sk = MlKem1024PrivateKey::try_from(raw_sk).ok()?;
    let ct = MlKem1024Ciphertext::try_from(raw_ct).ok()?;
    let ss = match sk_type {
        KEY_TYPE_KYBER1024 => kyber1024::decapsulate(&sk, &ct),
        KEY_TYPE_MLKEM1024 => mlkem1024::decapsulate(&sk, &ct),
        _ => return None,
    };
    Some(ss.as_ref().to_vec())
}

/// Encapsulation to a raw Kyber1024 public key (the model's kem_pk) with the given coins.
/// Returns the shared secret and the serialized ciphertext (0x08 || ct), or None if the
/// public key or the coins have the wrong length. Deterministic in (pk, coins).
pub fn encapsulate_kyber1024_raw(pk: &[u8], coins: &[u8]) -> Option<(Vec<u8>, Vec<u8>)> {
    if pk.len() != RAW_PK_LEN {
        return None;
    }
    encapsulate(&serialize(KEY_TYPE_KYBER1024, pk), coins)
}

/// The raw public key (the model's kem_pk) of a serialized Kyber1024 secret key, or None if
/// the secret key is malformed or of another key type
pub fn kyber1024_raw_public_key_of(sk: &[u8]) -> Option<Vec<u8>> {
    let (key_type, raw_sk) = split_serialized(sk, RAW_SK_LEN)?;
    if key_type != KEY_TYPE_KYBER1024 {
        return None;
    }
    Some(raw_sk[EK_OFFSET_IN_DK..EK_OFFSET_IN_DK + RAW_PK_LEN].to_vec())
}

/// The serialized public key of a serialized secret key (the decapsulation key contains
/// the encapsulation key), or None if the secret key is malformed
pub fn public_key_of(sk: &[u8]) -> Option<Vec<u8>> {
    let (key_type, raw_sk) = split_serialized(sk, RAW_SK_LEN)?;
    Some(serialize(key_type, &raw_sk[EK_OFFSET_IN_DK..EK_OFFSET_IN_DK + RAW_PK_LEN]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::RngCore;

    // A key pair in libsignal's serialized form, generated as libsignal does
    fn keypair(key_type: u8) -> (Vec<u8>, Vec<u8>) {
        let mut seed = [0u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
        rand::thread_rng().fill_bytes(&mut seed);
        let (sk, pk) = match key_type {
            KEY_TYPE_KYBER1024 => kyber1024::generate_key_pair(seed).into_parts(),
            KEY_TYPE_MLKEM1024 => mlkem1024::generate_key_pair(seed).into_parts(),
            _ => unreachable!(),
        };
        (serialize(key_type, sk.as_ref()), serialize(key_type, pk.as_ref()))
    }

    fn coins() -> [u8; COINS_LEN] {
        let mut c = [0u8; COINS_LEN];
        rand::thread_rng().fill_bytes(&mut c);
        c
    }

    #[test]
    fn lengths_match_constants() {
        assert_eq!(RAW_PK_LEN, crate::KEM_PK_SIZE);
        assert_eq!(SERIALIZED_CT_LEN, crate::KEM_CIPHERLEN_SIZE);
        assert_eq!(SERIALIZED_SK_LEN, crate::KEMKEY_SIZE);
        assert_eq!(COINS_LEN, crate::KEM_COINS_SIZE);
        assert_eq!(SHARED_SECRET_LEN, 32);
        assert_eq!(MlKem1024PublicKey::try_from(&[0u8; RAW_PK_LEN][..]).is_ok(), true);
        assert_eq!(MlKem1024PrivateKey::try_from(&[0u8; RAW_SK_LEN][..]).is_ok(), true);
        assert_eq!(MlKem1024Ciphertext::try_from(&[0u8; RAW_CT_LEN][..]).is_ok(), true);
    }

    #[test]
    fn round_trip_both_key_types() {
        for key_type in [KEY_TYPE_KYBER1024, KEY_TYPE_MLKEM1024] {
            let (sk, pk) = keypair(key_type);
            assert_eq!(pk.len(), SERIALIZED_PK_LEN);
            assert_eq!(sk.len(), crate::KEMKEY_SIZE);
            assert_eq!(public_key_of(&sk), Some(pk.clone()));
            let c = coins();
            let (ss, ct) = encapsulate(&pk, &c).unwrap();
            assert_eq!(ss.len(), SHARED_SECRET_LEN);
            assert_eq!(ct.len(), crate::KEM_CIPHERLEN_SIZE);
            assert_eq!(ct[0], key_type);
            // deterministic in (pk, coins)
            assert_eq!(encapsulate(&pk, &c), Some((ss.clone(), ct.clone())));
            assert_eq!(decapsulate(&sk, &ct), Some(ss.clone()));
            // implicit rejection: a modified ciphertext decapsulates to another secret
            let mut bad_ct = ct.clone();
            bad_ct[100] ^= 1;
            let bad_ss = decapsulate(&sk, &bad_ct).unwrap();
            assert_ne!(bad_ss, ss);
        }
    }

    #[test]
    fn raw_kyber1024_functions() {
        // The model's kem_pk: the raw Kyber1024 key, whose serialization 0x08 || pk is
        // what Bob signs
        let (sk, pk) = keypair(KEY_TYPE_KYBER1024);
        let raw_pk = kyber1024_raw_public_key_of(&sk).unwrap();
        assert_eq!(raw_pk.len(), crate::KEM_PK_SIZE);
        assert_eq!(serialize(KEY_TYPE_KYBER1024, &raw_pk), pk);
        let c = coins();
        assert_eq!(encapsulate_kyber1024_raw(&raw_pk, &c), encapsulate(&pk, &c));
        let (ss, ct) = encapsulate_kyber1024_raw(&raw_pk, &c).unwrap();
        assert_eq!(ct[0], KEY_TYPE_KYBER1024);
        assert_eq!(decapsulate(&sk, &ct), Some(ss));
        // wrong lengths; ML-KEM-1024 secret keys are not Kyber1024 keys
        assert_eq!(encapsulate_kyber1024_raw(&pk, &c), None);
        assert_eq!(encapsulate_kyber1024_raw(&raw_pk, &c[..31]), None);
        let (sk_m, _) = keypair(KEY_TYPE_MLKEM1024);
        assert_eq!(kyber1024_raw_public_key_of(&sk_m), None);
    }

    #[test]
    fn matches_libcrux_directly() {
        // The serialized functions agree with libcrux on the raw values
        let (sk, pk) = keypair(KEY_TYPE_MLKEM1024);
        let c = coins();
        let (ss, ct) = encapsulate(&pk, &c).unwrap();
        let raw_pk = MlKem1024PublicKey::try_from(&pk[1..]).unwrap();
        let (raw_ct, raw_ss) = mlkem1024::encapsulate(&raw_pk, c);
        assert_eq!(&ss[..], raw_ss.as_ref());
        assert_eq!(&ct[1..], raw_ct.as_ref());
        let raw_sk = MlKem1024PrivateKey::try_from(&sk[1..]).unwrap();
        assert_eq!(mlkem1024::decapsulate(&raw_sk, &raw_ct).as_ref(), &ss[..]);
    }

    #[test]
    fn rejects_malformed_inputs() {
        let (sk_k, pk_k) = keypair(KEY_TYPE_KYBER1024);
        let (sk_m, pk_m) = keypair(KEY_TYPE_MLKEM1024);
        let c = coins();
        // wrong or unknown key type, wrong lengths
        let mut pk_bad = pk_k.clone();
        pk_bad[0] = 0x07;
        assert_eq!(encapsulate(&pk_bad, &c), None);
        assert_eq!(encapsulate(&pk_k[..RAW_PK_LEN], &c), None);
        assert_eq!(encapsulate(&pk_k, &c[..31]), None);
        assert_eq!(public_key_of(&sk_k[1..]), None);
        // a ciphertext for one key type does not decapsulate with the other
        let (_, ct_k) = encapsulate(&pk_k, &c).unwrap();
        let (_, ct_m) = encapsulate(&pk_m, &c).unwrap();
        assert_eq!(decapsulate(&sk_m, &ct_k), None);
        assert_eq!(decapsulate(&sk_k, &ct_m), None);
        assert_eq!(decapsulate(&sk_k, &ct_k[..RAW_CT_LEN]), None);
        assert!(decapsulate(&sk_k, &ct_k).is_some());
        // Kyber1024 and ML-KEM-1024 are different KEMs on the same key material
        let mut pk_as_m = pk_k.clone();
        pk_as_m[0] = KEY_TYPE_MLKEM1024;
        assert_ne!(encapsulate(&pk_as_m, &c).unwrap().0, encapsulate(&pk_k, &c).unwrap().0);
    }
}
