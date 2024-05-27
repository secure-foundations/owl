use super::*;

use std::net::SocketAddr;
use std::thread;
use std::time::Duration;

use hex;

use rand::rngs::OsRng;
use rand_core::{CryptoRng, RngCore};

use x25519_dalek::PublicKey;
use x25519_dalek::StaticSecret;

use super::messages::{Initiation, Response};
use crate::wireguard::handshake::device::Device;

fn setup_devices<R: RngCore + CryptoRng, O: Default>(
    rng1: &mut R,
    rng2: &mut R,
    rng3: &mut R,
    dev1_is_owl: bool,
    dev2_is_owl: bool,
) -> (PublicKey, Device<O>, PublicKey, Device<O>) {
    // generate new key pairs

    let sk1 = StaticSecret::new(rng1);
    let pk1 = PublicKey::from(&sk1);

    let sk2 = StaticSecret::new(rng2);
    let pk2 = PublicKey::from(&sk2);

    // We always use psk of 0
    let psk = [0u8; 32];
    // rng3.fill_bytes(&mut psk[..]);

    // initialize devices on both ends

    let mut dev1 = if dev1_is_owl { Device::new_owl() } else { Device::new() };
    let mut dev2 = if dev2_is_owl { Device::new_owl() } else { Device::new() }; 

    dev1.set_sk(Some(sk1));
    dev2.set_sk(Some(sk2));

    dev1.add(pk2, O::default()).unwrap();
    dev2.add(pk1, O::default()).unwrap();

    dev1.set_psk(pk2, psk).unwrap();
    dev2.set_psk(pk1, psk).unwrap();

    (pk1, dev1, pk2, dev2)
}


// fn setup_initiators<R: RngCore + CryptoRng, O: Default>(
//     rng1: &mut R,
// ) -> (PublicKey, PublicKey, Device<O>, Device<O>) {
//     // generate new key pairs

//     let sk1 = StaticSecret::new(rng1);
//     let sk1_cloned = sk1.clone();
//     let pk1 = PublicKey::from(&sk1);

//     let sk2 = StaticSecret::new(&mut OsRng);
//     let pk2 = PublicKey::from(&sk2);

//     // We always use psk of 0
//     let psk = [0u8; 32];
//     // rng3.fill_bytes(&mut psk[..]);

//     // initialize devices on both ends

//     let mut dev1 = Device::new_owl_initiator();
//     let mut dev2 = Device::new(); 

//     dev1.set_sk(Some(sk1));
//     dev2.set_sk(Some(sk1_cloned));

//     dev1.add(pk2, O::default()).unwrap();
//     dev2.add(pk2, O::default()).unwrap();

//     dev1.set_psk(pk2, psk).unwrap();
//     dev2.set_psk(pk2, psk).unwrap();

//     (pk1, pk2, dev1, dev2)
// }


fn wait() {
    thread::sleep(Duration::from_millis(20));
}

/* Test longest possible handshake interaction (7 messages):
 *
 * 1. I -> R (initiation)
 * 2. I <- R (cookie reply)
 * 3. I -> R (initiation)
 * 4. I <- R (response)
 * 5. I -> R (cookie reply)
 * 6. I -> R (initiation)
 * 7. I <- R (response)
 */
#[test]
fn handshake_under_load() {
    let (_pk1, dev1, pk2, dev2): (_, Device<usize>, _, _) =
        setup_devices(&mut OsRng, &mut OsRng, &mut OsRng, false, false);

    let src1: SocketAddr = "172.16.0.1:8080".parse().unwrap();
    let src2: SocketAddr = "172.16.0.2:7070".parse().unwrap();

    // 1. device-1 : create first initiation
    let msg_init = dev1.begin(&mut OsRng, &pk2).unwrap();

    // 2. device-2 : responds with CookieReply
    let msg_cookie = match dev2.process(&mut OsRng, &msg_init, Some(src1)).unwrap() {
        (None, Some(msg), None) => msg,
        _ => panic!("unexpected response"),
    };

    // device-1 : processes CookieReply (no response)
    match dev1.process(&mut OsRng, &msg_cookie, Some(src2)).unwrap() {
        (None, None, None) => (),
        _ => panic!("unexpected response"),
    }

    // avoid initiation flood detection
    wait();

    // 3. device-1 : create second initiation
    let msg_init = dev1.begin(&mut OsRng, &pk2).unwrap();

    // 4. device-2 : responds with noise response
    let msg_response = match dev2.process(&mut OsRng, &msg_init, Some(src1)).unwrap() {
        (Some(_), Some(msg), Some(kp)) => {
            assert_eq!(kp.initiator, false);
            msg
        }
        _ => panic!("unexpected response"),
    };

    // 5. device-1 : responds with CookieReply
    let msg_cookie = match dev1.process(&mut OsRng, &msg_response, Some(src2)).unwrap() {
        (None, Some(msg), None) => msg,
        _ => panic!("unexpected response"),
    };

    // device-2 : processes CookieReply (no response)
    match dev2.process(&mut OsRng, &msg_cookie, Some(src1)).unwrap() {
        (None, None, None) => (),
        _ => panic!("unexpected response"),
    }

    // avoid initiation flood detection
    wait();

    // 6. device-1 : create third initiation
    let msg_init = dev1.begin(&mut OsRng, &pk2).unwrap();

    // 7. device-2 : responds with noise response
    let (msg_response, kp1) = match dev2.process(&mut OsRng, &msg_init, Some(src1)).unwrap() {
        (Some(_), Some(msg), Some(kp)) => {
            assert_eq!(kp.initiator, false);
            (msg, kp)
        }
        _ => panic!("unexpected response"),
    };

    // device-1 : process noise response
    let kp2 = match dev1.process(&mut OsRng, &msg_response, Some(src2)).unwrap() {
        (Some(_), None, Some(kp)) => {
            assert_eq!(kp.initiator, true);
            kp
        }
        _ => panic!("unexpected response"),
    };

    assert_eq!(kp1.send, kp2.recv);
    assert_eq!(kp1.recv, kp2.send);
}

#[cfg(test)]
fn test_handshake(dev1_is_owl: bool, dev2_is_owl: bool, num_tests: usize) {
    let (pk1, mut dev1, pk2, mut dev2): (_, Device<usize>, _, _) =
        setup_devices(&mut OsRng, &mut OsRng, &mut OsRng, dev1_is_owl, dev2_is_owl);

    // do a few handshakes (every handshake should succeed)

    for i in 0..num_tests {
        println!("handshake : {}", i);

        // create initiation

        let msg1 = dev1.begin(&mut OsRng, &pk2).unwrap();

        println!("msg1 = {} : {} bytes", hex::encode(&msg1[..]), msg1.len());
        println!(
            "msg1 = {:?}",
            Initiation::parse(&msg1[..]).expect("failed to parse initiation")
        );

        // process initiation and create response

        let (_, msg2, ks_r) = dev2
            .process(&mut OsRng, &msg1, None)
            .expect("failed to process initiation");

        let ks_r = ks_r.unwrap();
        let msg2 = msg2.unwrap();

        println!("msg2 = {} : {} bytes", hex::encode(&msg2[..]), msg2.len());
        println!(
            "msg2 = {:?}",
            Response::parse(&msg2[..]).expect("failed to parse response")
        );

        assert!(!ks_r.initiator, "Responders key-pair is confirmed");

        // process response and obtain confirmed key-pair

        let (_, msg3, ks_i) = dev1
            .process(&mut OsRng, &msg2, None)
            .expect("failed to process response");
        let ks_i = ks_i.unwrap();

        assert!(msg3.is_none(), "Returned message after response");
        assert!(ks_i.initiator, "Initiators key-pair is not confirmed");

        assert_eq!(ks_i.send, ks_r.recv, "KeyI.send != KeyR.recv");
        assert_eq!(ks_i.recv, ks_r.send, "KeyI.recv != KeyR.send");

        dev1.release(ks_i.local_id());
        dev2.release(ks_r.local_id());

        // avoid initiation flood detection if we are doing multiple handshakes
        if num_tests > 1 {
            wait();
        }
    }

    dev1.remove(&pk2).unwrap();
    dev2.remove(&pk1).unwrap();
}

#[test]
fn handshake_no_load() {
    test_handshake(false, false, 10);
}


#[test]
fn handshake_owl_initiator_rs_responder() {
    test_handshake(true, false, 10);
}

#[test]
fn handshake_rs_initiator_owl_responder() {
    test_handshake(false, true, 10);
}

#[test]
fn handshake_owl_initiator_owl_responder() {
    test_handshake(true, true, 10);
}

use test::Bencher;

#[bench]
fn bench_1_rs_handshake(b: &mut Bencher) {
    b.iter(|| {
        test_handshake(false, false, 1)
    });
}

#[bench]
fn bench_2_owl_init_rs_resp_handshake(b: &mut Bencher) {
    b.iter(|| {
        test_handshake(true, false, 1)
    });
}

#[bench]
fn bench_3_rs_init_owl_resp_handshake(b: &mut Bencher) {
    b.iter(|| {
        test_handshake(false, true, 1)
    });
}

#[bench]
fn bench_4_owl_handshake(b: &mut Bencher) {
    b.iter(|| {
        test_handshake(true, true, 1)
    });
}


#[bench]
fn bench_1_rs_handshake_init(b: &mut Bencher) {
    b.iter(|| {
        let (pk1, mut dev1, pk2, mut dev2): (_, Device<usize>, _, _) = 
            setup_devices(&mut OsRng, &mut OsRng, &mut OsRng, false, false);
    });
}

#[bench]
fn bench_2_owl_init_rs_resp_handshake_init(b: &mut Bencher) {
    b.iter(|| {
        let (pk1, mut dev1, pk2, mut dev2): (_, Device<usize>, _, _) = 
            setup_devices(&mut OsRng, &mut OsRng, &mut OsRng, true, false);
    });
}

#[bench]
fn bench_3_rs_init_owl_resp_handshake_init(b: &mut Bencher) {
    b.iter(|| {
        let (pk1, mut dev1, pk2, mut dev2): (_, Device<usize>, _, _) = 
            setup_devices(&mut OsRng, &mut OsRng, &mut OsRng, false, true);
    });
}

#[bench]
fn bench_4_owl_handshake_init(b: &mut Bencher) {
    b.iter(|| {
        let (pk1, mut dev1, pk2, mut dev2): (_, Device<usize>, _, _) = 
            setup_devices(&mut OsRng, &mut OsRng, &mut OsRng, true, true);
    });
}