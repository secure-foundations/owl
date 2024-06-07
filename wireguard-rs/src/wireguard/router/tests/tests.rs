use crate::platform::udp::Reader;

use std::net::IpAddr;
use std::ops::Deref;
use std::sync::mpsc::{channel, Receiver, RecvTimeoutError, Sender};
use std::sync::Arc;
use std::sync::Mutex;
use std::time::Duration;

use rand::Rng;

use super::*;
use super::super::super::types::RouterDeviceType;

#[cfg(feature = "unstable")]
extern crate test;

const SIZE_MSG: usize = 1024;
const SIZE_KEEPALIVE: usize = message_data_len(0);
const TIMEOUT: Duration = Duration::from_millis(1000);

struct EventTracker<E> {
    rx: Mutex<Receiver<E>>,
    tx: Mutex<Sender<E>>,
}

impl<E> EventTracker<E> {
    fn new() -> Self {
        let (tx, rx) = channel();
        EventTracker {
            rx: Mutex::new(rx),
            tx: Mutex::new(tx),
        }
    }

    fn log(&self, e: E) {
        self.tx.lock().unwrap().send(e).unwrap();
    }

    fn wait(&self, timeout: Duration) -> Option<E> {
        match self.rx.lock().unwrap().recv_timeout(timeout) {
            Ok(v) => Some(v),
            Err(RecvTimeoutError::Timeout) => None,
            Err(RecvTimeoutError::Disconnected) => panic!("Disconnect"),
        }
    }

    fn now(&self) -> Option<E> {
        self.wait(Duration::from_millis(0))
    }
}

// type for tracking events inside the router module
struct Inner {
    send: EventTracker<(usize, bool)>,
    recv: EventTracker<(usize, bool)>,
    need_key: EventTracker<()>,
    key_confirmed: EventTracker<()>,
}

#[derive(Clone)]
struct Opaque {
    inner: Arc<Inner>,
}

impl Deref for Opaque {
    type Target = Inner;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

struct TestCallbacks();

impl Opaque {
    fn new() -> Opaque {
        Opaque {
            inner: Arc::new(Inner {
                send: EventTracker::new(),
                recv: EventTracker::new(),
                need_key: EventTracker::new(),
                key_confirmed: EventTracker::new(),
            }),
        }
    }
}

macro_rules! no_events {
    ($opq:expr) => {
        assert_eq!($opq.send.now(), None, "unexpected send event");
        assert_eq!($opq.recv.now(), None, "unexpected recv event");
        assert_eq!($opq.need_key.now(), None, "unexpected need_key event");
        assert_eq!(
            $opq.key_confirmed.now(),
            None,
            "unexpected key_confirmed event"
        );
    };
}

impl Callbacks for TestCallbacks {
    type Opaque = Opaque;

    fn send(t: &Self::Opaque, size: usize, sent: bool, _keypair: &Arc<KeyPair>, _counter: u64) {
        t.send.log((size, sent))
    }

    fn recv(t: &Self::Opaque, size: usize, sent: bool, _keypair: &Arc<KeyPair>) {
        t.recv.log((size, sent))
    }

    fn need_key(t: &Self::Opaque) {
        t.need_key.log(());
    }

    fn key_confirmed(t: &Self::Opaque) {
        t.key_confirmed.log(());
    }
}

#[cfg(test)]
fn test_outbound(device_type: RouterDeviceType) {
    init();

    // create device
    let (_fake, _reader, tun_writer, _mtu) = dummy::TunTest::create(false);
    let router: Device<_, TestCallbacks, _, _> = Device::new(1, tun_writer, device_type);
    router.set_outbound_writer(dummy::VoidBind::new());

    let tests = vec![
        ("192.168.1.0", 24, "192.168.1.20", true),
        ("172.133.133.133", 32, "172.133.133.133", true),
        ("172.133.133.133", 32, "172.133.133.132", false),
        (
            "2001:db8::ff00:42:0000",
            112,
            "2001:db8::ff00:42:3242",
            true,
        ),
        (
            "2001:db8::ff00:42:8000",
            113,
            "2001:db8::ff00:42:0660",
            false,
        ),
        (
            "2001:db8::ff00:42:8000",
            113,
            "2001:db8::ff00:42:ffff",
            true,
        ),
    ];

    for (mask, len, dst, okay) in tests.iter() {
        let len = *len;
        let okay = *okay;

        println!(
            "Check: {} {} {}/{}",
            dst,
            if okay { "\\in" } else { "\\notin" },
            mask,
            len
        );

        for set_key in vec![true, false] {
            for confirm_with_staged_packet in vec![true, false] {
                let send_keepalive = (!confirm_with_staged_packet || !okay) && set_key;
                let send_payload = okay && set_key;
                let need_key = ((confirm_with_staged_packet && set_key) || !set_key) && okay;

                println!(
                    "  confirm_with_staged_packet = {}, send_keepalive = {}, set_key = {}",
                    confirm_with_staged_packet, send_keepalive, set_key
                );

                // add new peer
                let opaque = Opaque::new();
                let peer = router.new_peer(opaque.clone());
                let mask: IpAddr = mask.parse().unwrap();

                // confirm using keepalive
                if set_key && (!confirm_with_staged_packet) {
                    peer.add_keypair(dummy_keypair(true));
                }

                // map subnet to peer
                peer.add_allowed_ip(mask, len);

                // create "IP packet"
                let dst = dst.parse().unwrap();
                let src = match dst {
                    IpAddr::V4(_) => "127.0.0.1".parse().unwrap(),
                    IpAddr::V6(_) => "::1".parse().unwrap(),
                };
                let msg = make_packet(SIZE_MSG, src, dst, 0);

                // crypto-key route the IP packet
                let res = router.send(pad(&msg));
                assert_eq!(
                    res.is_ok(),
                    okay,
                    "crypto-routing / destination lookup failure"
                );

                // confirm using staged packet
                if set_key && confirm_with_staged_packet {
                    peer.add_keypair(dummy_keypair(true));
                }

                // check for key-material request
                if need_key {
                    assert_eq!(
                        opaque.need_key.wait(TIMEOUT),
                        Some(()),
                        "should have requested a new key, if no encryption state was set"
                    );
                }

                // check for keepalive
                if send_keepalive {
                    assert_eq!(
                        opaque.send.wait(TIMEOUT),
                        Some((SIZE_KEEPALIVE, false)),
                        "keepalive should be sent before transport message"
                    );
                }

                // check for encryption of payload
                if send_payload {
                    assert_eq!(
                        opaque.send.wait(TIMEOUT),
                        Some((SIZE_KEEPALIVE + msg.len(), false)),
                        "message buffer should be encrypted"
                    )
                }

                // check that we handled all events
                no_events!(opaque);
            }
        }
    }
}

#[test]
fn test_outbound_no_owl() {
    test_outbound(RouterDeviceType::NoOwl);
}

#[test]
fn test_outbound_owl_initiator() {
    test_outbound(RouterDeviceType::OwlInitiator);
}

#[test]
fn test_outbound_owl_responder() {
    test_outbound(RouterDeviceType::OwlResponder);
}


#[cfg(test)]
fn test_bidirectional(dev1_type: RouterDeviceType, dev2_type: RouterDeviceType) {
    init();

    const MAX_SIZE_BODY: usize = 1 << 15;

    let tests = [
        (
            ("192.168.1.0", 24, "192.168.1.20", true),
            ("172.133.133.133", 32, "172.133.133.133", true),
        ),
        (
            ("192.168.1.0", 24, "192.168.1.20", true),
            ("172.133.133.133", 32, "172.133.133.133", true),
        ),
        (
            (
                "2001:db8::ff00:42:8000",
                113,
                "2001:db8::ff00:42:ffff",
                true,
            ),
            (
                "2001:db8::ff40:42:8000",
                113,
                "2001:db8::ff40:42:ffff",
                true,
            ),
        ),
        (
            (
                "2001:db8::ff00:42:8000",
                113,
                "2001:db8::ff00:42:ffff",
                true,
            ),
            (
                "2001:db8::ff40:42:8000",
                113,
                "2001:db8::ff40:42:ffff",
                true,
            ),
        ),
    ];

    let mut rng = rand::thread_rng();

    for (p1, p2) in tests.iter() {
        for confirm_with_staged_packet in vec![true, false] {
            println!(
                "peer1 = {:?}, peer2 = {:?}, confirm_with_staged_packet = {}",
                p1, p2, confirm_with_staged_packet
            );

            let ((bind_reader1, bind_writer1), (bind_reader2, bind_writer2)) =
                dummy::PairBind::pair();

            let mut confirm_packet_size = SIZE_KEEPALIVE;

            // create matching device
            let (_fake, _, tun_writer1, _) = dummy::TunTest::create(false);
            let (_fake, _, tun_writer2, _) = dummy::TunTest::create(false);

            let router1: Device<_, TestCallbacks, _, _> = Device::new(1, tun_writer1, dev1_type);
            router1.set_outbound_writer(bind_writer1);

            let router2: Device<_, TestCallbacks, _, _> = Device::new(1, tun_writer2, dev2_type);
            router2.set_outbound_writer(bind_writer2);

            // prepare opaque values for tracing callbacks

            let opaque1 = Opaque::new();
            let opaque2 = Opaque::new();

            // create peers with matching keypairs and assign subnets

            let peer1 = router1.new_peer(opaque1.clone());
            let peer2 = router2.new_peer(opaque2.clone());

            {
                let (mask, len, _ip, _okay) = p1;
                let mask: IpAddr = mask.parse().unwrap();
                peer1.add_allowed_ip(mask, *len);
                peer1.add_keypair(dummy_keypair(false));
            }

            {
                let (mask, len, _ip, _okay) = p2;
                let mask: IpAddr = mask.parse().unwrap();
                peer2.add_allowed_ip(mask, *len);
                peer2.set_endpoint(dummy::UnitEndpoint::new());
            }

            if confirm_with_staged_packet {
                // create IP packet
                let (_mask, _len, ip1, _okay) = p1;
                let (_mask, _len, ip2, _okay) = p2;

                let msg = make_packet(
                    SIZE_MSG,
                    ip1.parse().unwrap(), // src
                    ip2.parse().unwrap(), // dst
                    0,
                );

                // calculate size of encapsulated IP packet
                confirm_packet_size = msg.len() + SIZE_KEEPALIVE;

                // stage packet for sending
                router2
                    .send(pad(&msg))
                    .expect("failed to sent staged packet");

                // a new key should have been requested from the handshake machine
                assert_eq!(
                    opaque2.need_key.wait(TIMEOUT),
                    Some(()),
                    "a new key should be requested since a packet was attempted transmitted"
                );

                // no other events should fire
                no_events!(opaque1);
                no_events!(opaque2);
            }

            // add a keypair
            assert_eq!(peer1.get_endpoint(), None, "no endpoint has yet been set");
            peer2.add_keypair(dummy_keypair(true));

            // this should cause a key-confirmation packet (keepalive or staged packet)
            assert_eq!(
                opaque2.send.wait(TIMEOUT),
                Some((confirm_packet_size, true)),
                "expected successful transmission of a confirmation packet"
            );

            // no other events should fire
            no_events!(opaque1);
            no_events!(opaque2);

            // read confirming message received by the other end ("across the internet")
            let mut buf = vec![0u8; SIZE_MSG * 2];
            let (len, from) = bind_reader1.read(&mut buf).unwrap();
            buf.truncate(len);

            assert_eq!(
                len, confirm_packet_size,
                "unexpected size of confirmation message"
            );

            // pass to the router for processing
            router1
                .recv(from, buf)
                .expect("failed to receive confirmation message");

            // check that a receive event is fired
            assert_eq!(
                opaque1.recv.wait(TIMEOUT),
                Some((confirm_packet_size, true)),
                "we expect processing to be successful"
            );

            // the key is confirmed
            assert_eq!(
                opaque1.key_confirmed.wait(TIMEOUT),
                Some(()),
                "confirmation message should confirm the key"
            );

            // peer1 learns the endpoint
            assert!(
                peer1.get_endpoint().is_some(),
                "peer1 should learn the endpoint of peer2 from the confirmation message (roaming)"
            );

            // no other events should fire
            no_events!(opaque1);
            no_events!(opaque2);

            // now that peer1 has an endpoint
            // route packets in the other direction: peer1 -> peer2
            let mut sizes = vec![0, 1, 1500, MAX_SIZE_BODY];
            for _ in 0..100 {
                let body_size: usize = rng.gen();
                let body_size = body_size % MAX_SIZE_BODY;
                sizes.push(body_size);
            }

            for (id, body_size) in sizes.iter().enumerate() {
                // println!("packet: id = {}, body_size = {}", id, body_size);

                // pass IP packet to router
                let (_mask, _len, ip1, _okay) = p1;
                let (_mask, _len, ip2, _okay) = p2;
                let msg = make_packet(
                    *body_size,
                    ip2.parse().unwrap(), // src
                    ip1.parse().unwrap(), // dst
                    id as u64,
                );

                // calculate encrypted size
                let encrypted_size = msg.len() + SIZE_KEEPALIVE;

                router1
                    .send(pad(&msg))
                    .expect("we expect routing to be successful");

                // encryption succeeds and the correct size is logged
                assert_eq!(
                    opaque1.send.wait(TIMEOUT),
                    Some((encrypted_size, true)),
                    "expected send event for peer1 -> peer2 payload"
                );

                // otherwise no events
                no_events!(opaque1);
                no_events!(opaque2);

                // receive ("across the internet") on the other end
                let mut buf = vec![0u8; MAX_SIZE_BODY + 512];
                let (len, from) = bind_reader2.read(&mut buf).unwrap();
                buf.truncate(len);
                router2.recv(from, buf).unwrap();

                // check that decryption succeeds
                assert_eq!(
                    opaque2.recv.wait(TIMEOUT),
                    Some((msg.len() + SIZE_KEEPALIVE, true)),
                    "decryption and routing should succeed"
                );

                // otherwise no events
                no_events!(opaque1);
                no_events!(opaque2);
            }
        }
    }
}

#[test]
fn test_bidirectional_rs_rs() {
    test_bidirectional(RouterDeviceType::NoOwl, RouterDeviceType::NoOwl);
}

#[test]
fn test_bidirectional_rs_owl_initiator() {
    test_bidirectional(RouterDeviceType::NoOwl, RouterDeviceType::OwlInitiator);
}

#[test]
fn test_bidirectional_rs_owl_responder() {
    test_bidirectional(RouterDeviceType::NoOwl, RouterDeviceType::OwlResponder);
}

#[test]
fn test_bidirectional_owl_initiator_rs() {
    test_bidirectional(RouterDeviceType::OwlInitiator, RouterDeviceType::NoOwl);
}

#[test]
fn test_bidirectional_owl_initiator_owl_initiator() {
    test_bidirectional(RouterDeviceType::OwlInitiator, RouterDeviceType::OwlInitiator);
}

#[test]
fn test_bidirectional_owl_initiator_owl_responder() {
    test_bidirectional(RouterDeviceType::OwlInitiator, RouterDeviceType::OwlResponder);
}

#[test]
fn test_bidirectional_owl_responder_rs() {
    test_bidirectional(RouterDeviceType::OwlResponder, RouterDeviceType::NoOwl);
}

#[test]
fn test_bidirectional_owl_responder_owl_initiator() {
    test_bidirectional(RouterDeviceType::OwlResponder, RouterDeviceType::OwlInitiator);
}

#[test]
fn test_bidirectional_owl_responder_owl_responder() {
    test_bidirectional(RouterDeviceType::OwlResponder, RouterDeviceType::OwlResponder);
}



#[cfg(test)]
fn bench_bidirectional(b: &mut Bencher, dev1_type: RouterDeviceType, dev2_type: RouterDeviceType, num_packets: usize) {
    const MAX_SIZE_BODY: usize = 1 << 15;

    let tests = [
        (
            ("192.168.1.0", 24, "192.168.1.20", true),
            ("172.133.133.133", 32, "172.133.133.133", true),
        ),
    ];

    let mut rng = rand::thread_rng();

    for (p1, p2) in tests.iter() {
        let ((bind_reader1, bind_writer1), (bind_reader2, bind_writer2)) =
            dummy::PairBind::pair();

        let mut confirm_packet_size = SIZE_KEEPALIVE;

        // create matching device
        let (_fake, _, tun_writer1, _) = dummy::TunTest::create(false);
        let (_fake, _, tun_writer2, _) = dummy::TunTest::create(false);

        let router1: Device<_, TestCallbacks, _, _> = Device::new(1, tun_writer1, dev1_type);
        router1.set_outbound_writer(bind_writer1);

        let router2: Device<_, TestCallbacks, _, _> = Device::new(1, tun_writer2, dev2_type);
        router2.set_outbound_writer(bind_writer2);

        // prepare opaque values for tracing callbacks

        let opaque1 = Opaque::new();
        let opaque2 = Opaque::new();

        // create peers with matching keypairs and assign subnets

        let peer1 = router1.new_peer(opaque1.clone());
        let peer2 = router2.new_peer(opaque2.clone());

        {
            let (mask, len, _ip, _okay) = p1;
            let mask: IpAddr = mask.parse().unwrap();
            peer1.add_allowed_ip(mask, *len);
            peer1.add_keypair(dummy_keypair(false));
        }

        {
            let (mask, len, _ip, _okay) = p2;
            let mask: IpAddr = mask.parse().unwrap();
            peer2.add_allowed_ip(mask, *len);
            peer2.set_endpoint(dummy::UnitEndpoint::new());
        }

        // add a keypair
        peer2.add_keypair(dummy_keypair(true));

        // read confirming message received by the other end ("across the internet")
        let mut buf = vec![0u8; SIZE_MSG * 2];
        let (len, from) = bind_reader1.read(&mut buf).unwrap();
        buf.truncate(len);

        assert_eq!(
            len, confirm_packet_size,
            "unexpected size of confirmation message"
        );

        // pass to the router for processing
        router1
            .recv(from, buf)
            .expect("failed to receive confirmation message");


        // now that peer1 has an endpoint
        // route packets in the other direction: peer1 -> peer2
        b.iter(|| {
            let mut sizes = vec![1440; num_packets];
            for (id, body_size) in sizes.iter().enumerate() {

                // pass IP packet to router
                let (_mask, _len, ip1, _okay) = p1;
                let (_mask, _len, ip2, _okay) = p2;
                let msg = make_packet(
                    *body_size,
                    ip2.parse().unwrap(), // src
                    ip1.parse().unwrap(), // dst
                    id as u64,
                );

                // calculate encrypted size
                // let encrypted_size = msg.len() + SIZE_KEEPALIVE;
                let mut msg = pad(&msg);
                msg.reserve(16);

                router1
                    .send(msg)
                    .expect("we expect routing to be successful");

                // receive ("across the internet") on the other end
                let mut buf = vec![0u8; MAX_SIZE_BODY + 512];
                let (len, from) = bind_reader2.read(&mut buf).unwrap();
                buf.truncate(len);
                // router2.recv(from, buf).unwrap();
            }
        });
    }
}


use test::Bencher;

#[bench]
fn bench_bidirectional_1_rs_rs(b: &mut Bencher) {
    bench_bidirectional(b, RouterDeviceType::NoOwl, RouterDeviceType::NoOwl, 1000)
}

// #[bench]
// fn bench_bidirectional_3_rs_owl_responder(b: &mut Bencher) {
//     b.iter(|| {
//         bench_bidirectional(RouterDeviceType::NoOwl, RouterDeviceType::OwlResponder, 1)
//     });
// }

// #[bench]
// fn bench_bidirectional_2_owl_initiator_rs(b: &mut Bencher) {
//     b.iter(|| {
//         bench_bidirectional(RouterDeviceType::OwlInitiator, RouterDeviceType::NoOwl, 1)
//     });
// }

#[bench]
fn bench_bidirectional_4_owl_initiator_owl_responder(b: &mut Bencher) {
    bench_bidirectional(b, RouterDeviceType::OwlInitiator, RouterDeviceType::OwlResponder, 1000)
}

// #[bench]
// fn bench_bidirectional_1_baseline(b: &mut Bencher) {
//     bench_bidirectional(b, RouterDeviceType::NoOwl, RouterDeviceType::NoOwl, 0)
// }

// #[bench]
// fn bench_bidirectional_4_baseline(b: &mut Bencher) {
//     bench_bidirectional(b, RouterDeviceType::OwlInitiator, RouterDeviceType::OwlResponder, 0)
// }





#[cfg(test)]
fn bench_send_recv(b: &mut Bencher, dev1_type: RouterDeviceType, dev2_type: RouterDeviceType, do_routines: bool) {
    use std::sync::atomic::AtomicBool;

    use crate::wireguard::router::{queue::ParallelJob, device::DecryptionState, anti_replay::AntiReplay};
    

    #[cfg(feature = "memory_profile")]
    let heap_profiler_guard = heappy::HeapProfilerGuard::new(1).unwrap();

    let confirm_packet_size = SIZE_KEEPALIVE;

    // create device
    let ((bind_reader1, bind_writer1), (bind_reader2, bind_writer2)) =
    dummy::PairBind::pair();

    // create matching device
    let (_fake, _, tun_writer1, _) = dummy::TunTest::create(false);
    let (_fake, _, tun_writer2, _) = dummy::TunTest::create(false);

    let router1: Device<_, TestCallbacks, _, _> = Device::new(1, tun_writer1, dev1_type);
    router1.set_outbound_writer(bind_writer1);

    let router2: Device<_, TestCallbacks, _, _> = Device::new(1, tun_writer2, dev2_type);
    router2.set_outbound_writer(bind_writer2);

    let p1 = ("192.168.1.0", 24, "192.168.1.20");
    let p2 = ("172.133.133.133", 32, "172.133.133.133");

    // prepare opaque values for tracing callbacks

    let opaque1 = Opaque::new();
    let opaque2 = Opaque::new();

    // create peers with matching keypairs and assign subnets

    let peer1 = router1.new_peer(opaque1.clone());
    let peer2 = router2.new_peer(opaque2.clone());

    {
        let (mask, len, _ip) = p1;
        let mask: IpAddr = mask.parse().unwrap();
        peer1.add_allowed_ip(mask, len);
        peer1.add_keypair(dummy_keypair(false));
    }

    {
        let (mask, len, _ip) = p2;
        let mask: IpAddr = mask.parse().unwrap();
        peer2.add_allowed_ip(mask, len);
        peer2.set_endpoint(dummy::UnitEndpoint::new());
    }

    // add a keypair
    assert_eq!(peer1.get_endpoint(), None, "no endpoint has yet been set");
    peer2.add_keypair(dummy_keypair(true));

    // this should cause a key-confirmation packet (keepalive or staged packet)
    assert_eq!(
        opaque2.send.wait(TIMEOUT),
        Some((confirm_packet_size, true)),
        "expected successful transmission of a confirmation packet"
    );

    // no other events should fire
    no_events!(opaque1);
    no_events!(opaque2);

    // read confirming message received by the other end ("across the internet")
    let mut buf = vec![0u8; SIZE_MSG * 2];
    let (len, from) = bind_reader1.read(&mut buf).unwrap();
    buf.truncate(len);

    assert_eq!(
        len, confirm_packet_size,
        "unexpected size of confirmation message"
    );

    // pass to the router for processing
    router1
        .recv(from, buf)
        .expect("failed to receive confirmation message");

    // create "IP packet"
    let (dst,_,_) = p1;
    let (src,_,_) = p2;
    let dst = dst.parse().unwrap();
    let src = match dst {
        IpAddr::V4(_) => "127.0.0.1".parse().unwrap(),
        IpAddr::V6(_) => "::1".parse().unwrap(),
    };
    let packet = make_packet(BYTES_PER_PACKET, src, dst, 0);

    // suffix with zero and reserve capacity for tag
    // (normally done to enable in-place transport message construction)
    let mut msg = pad(&packet);
    msg.reserve(16);

    let keypair = Arc::new(dummy_keypair(false));


    b.iter(|| {
        for i in 0..NUM_PACKETS {
            let mut counter: u64 = 0;

            let packet: Vec<u8> = make_packet(BYTES_PER_PACKET, src, dst, 0);
            let mut msg = pad(&packet);
            msg.reserve(16);
    
            // dbg!(hex::encode(&msg));
    
            let send_job = super::super::send::SendJob::new(
                msg,
                counter,
                Arc::clone(&keypair),
                peer1.peer.clone(),
                dev1_type
            );
            
            if do_routines { 
                send_job.parallel_work();
            } else {
                // let cfg: owl_wireguard::cfg_Initiator<u8> = owl_wireguard::cfg_Initiator {
                //     owl_S_init: Arc::new(vec![]),
                //     owl_E_init: Arc::new(vec![]),
                //     pk_owl_S_resp: Arc::new(vec![]),
                //     pk_owl_S_init: Arc::new(vec![]),
                //     pk_owl_E_resp: Arc::new(vec![]),
                //     pk_owl_E_init: Arc::new(vec![]),
                //     salt: Arc::new(vec![]),
                //     device: None
                // };
                // let mut state = owl_wireguard::state_Initiator::init_state_Initiator();
                // // state.owl_N_init_send = job.counter as usize;

                // let mut transp_keys = owl_wireguard::owl_transp_keys {
                //     owl__transp_keys_initiator: vec![],
                //     owl__transp_keys_responder: vec![],
                //     owl__transp_keys_T_init_send: vec![],
                //     owl__transp_keys_T_resp_send: vec![],
                // };
            }

            let new_msg = send_job.get_buffer();
    
            let decryption_state = DecryptionState {
                keypair: Arc::new(dummy_keypair(true)),
                confirmed: AtomicBool::new(true),
                protector: spin::Mutex::new(AntiReplay::new()),
                peer: peer2.peer.clone(),
            };
    
            let recv_job = super::super::receive::ReceiveJob::new(
                new_msg,
                Arc::new(decryption_state),
                dummy::UnitEndpoint {},
                dev2_type
            );
        
            if do_routines { 
                recv_job.parallel_work();
            }
        }
    });

    #[cfg(feature = "memory_profile")]
    {
        let report = heap_profiler_guard.report();

        let filename = "/tmp/mem.pb";
        println!("Writing to {}", filename);
        let mut file = std::fs::File::create(filename).unwrap();
        report.write_pprof(&mut file).unwrap();
    }
}

#[bench]
fn bench_send_recv_no_owl(b: &mut Bencher) {
    bench_send_recv(b, RouterDeviceType::NoOwl, RouterDeviceType::NoOwl, true)
}

#[bench]
fn bench_send_recv_owl(b: &mut Bencher) {
    bench_send_recv(b, RouterDeviceType::OwlInitiator, RouterDeviceType::OwlInitiator, true)
}


#[bench]
fn bench_send_recv_baseline(b: &mut Bencher) {
    bench_send_recv(b, RouterDeviceType::NoOwl, RouterDeviceType::NoOwl, false)
}


const NUM_PACKETS: usize = 1000;

const BYTES_PER_PACKET: usize = 200;
// Note: bench_send_recv.py will append the appropriate constant to this file, so the line above must be commented out
// when using that script

