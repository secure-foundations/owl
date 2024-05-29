use std::collections::hash_map;
use std::collections::HashMap;
use std::convert::TryInto;
use std::net::SocketAddr;
use std::sync::Mutex;
use std::sync::Arc;
use std::time::Instant;

use byteorder::{ByteOrder, LittleEndian};
use dashmap::mapref::entry::Entry;
use dashmap::DashMap;
use zerocopy::AsBytes;

use rand::Rng;
use rand::rngs::OsRng;
use rand_core::{CryptoRng, RngCore};

use clear_on_drop::clear::Clear;

use x25519_dalek::PublicKey;
use x25519_dalek::StaticSecret;

use super::macs;
use super::messages::{CookieReply, Initiation, Response};
use super::messages::{TYPE_COOKIE_REPLY, TYPE_INITIATION, TYPE_RESPONSE};
use super::noise;
use super::peer::Peer;
use super::ratelimiter::RateLimiter;
use super::types::*;

use crate::wireguard::owl_wg::owl_wireguard;
use crate::wireguard::KeyPair;
use crate::wireguard::types::Key;

const MAX_PEER_PER_DEVICE: usize = 1 << 20;

pub struct KeyState {
    pub(super) sk: StaticSecret, // static secret key
    pub(super) pk: PublicKey,    // static public key
    macs: macs::Validator,       // validator for the mac fields
}

/// The device is generic over an "opaque" type
/// which can be used to associate the public key with this value.
/// (the instance is a Peer object in the parent module)
pub struct DeviceInner<O> {
    keyst: Option<KeyState>,
    id_map: DashMap<u32, [u8; 32]>, // concurrent map
    pk_map: HashMap<[u8; 32], Peer<O>>,
    limiter: Mutex<RateLimiter>,
}

pub struct OwlDevice<O> {
    eph_sk: Vec<u8>,
    static_sk: Vec<u8>,
    inner: DeviceInner<O>,
}

pub enum Device<O> {
    NoOwl(DeviceInner<O>),
    Owl (OwlDevice<O>),
}

impl<O> Device<O> {
    #[inline]
    pub fn inner(&self) -> &DeviceInner<O> {
        match self {
            Device::NoOwl(inner) => inner,
            Device::Owl(od) => &od.inner,
        }
    }

    pub fn inner_mut(&mut self) -> &mut DeviceInner<O> {
        match self {
            Device::NoOwl(inner) => inner,
            Device::Owl(od) => &mut od.inner,
        }
    }

    pub fn new() -> Device<O> {
        Device::NoOwl(DeviceInner::new())
    }

    pub fn new_owl() -> Device<O> {
        let eph_sk = StaticSecret::new(&mut OsRng).to_bytes().to_vec();
        let static_sk = vec![];
        Device::Owl(OwlDevice { eph_sk, static_sk, inner: DeviceInner::new() })
    }

    // pub fn new_owl_initiator() -> Device<O> {
    //     let inner = DeviceInner::new();

    //     // We generate the ephemeral key here---the Owl structs effectively always use the same "ephemeral key"
    //     // This is a hack---can be made more robust later
    //     let eph_sk = StaticSecret::new(&mut OsRng);

    //     let cfg = owl_wireguard::cfg_Initiator {
    //         owl_S_init: vec![],
    //         owl_E_init: eph_sk.to_bytes().to_vec(),
    //         pk_owl_S_resp: vec![],
    //         pk_owl_S_init: vec![],
    //         pk_owl_E_resp: vec![],
    //         pk_owl_E_init: vec![],
    //         salt: vec![],
    //         device: Some(inner),
    //     };
    //     let state = owl_wireguard::state_Initiator::init_state_Initiator();
    //     Device::Initiator(OwlInitiator {
    //         cfg,
    //         state
    //     })
    // }

    // pub fn new_owl_responder() -> Device<O> {
    //     let inner = DeviceInner::new();

    //     // We generate the ephemeral key here---the Owl structs effectively always use the same "ephemeral key"
    //     // This is a hack---can be made more robust later
    //     let eph_sk = StaticSecret::new(&mut OsRng);

    //     let cfg = owl_wireguard::cfg_Responder {
    //         owl_S_resp: vec![],
    //         owl_E_resp: eph_sk.to_bytes().to_vec(),
    //         pk_owl_S_resp: vec![],
    //         pk_owl_S_init: vec![],
    //         pk_owl_E_resp: vec![],
    //         pk_owl_E_init: vec![],
    //         salt: vec![],
    //         device: Some(inner)
    //     };
    //     let state = owl_wireguard::state_Responder::init_state_Responder();
    //     Device::Responder(OwlResponder {
    //         cfg,
    //         state
    //     })
    // }

    /// Update the secret key of the device
    ///
    /// # Arguments
    ///
    /// * `sk` - x25519 scalar representing the local private key
    pub fn set_sk(&mut self, sk: Option<StaticSecret>) -> Option<PublicKey> {
        match self {
            Device::NoOwl(_) => {},
            Device::Owl(o) => {
                o.static_sk = sk.clone().unwrap().to_bytes().to_vec();
            },
        }
        
        // update secret and public key
        self.inner_mut().keyst = sk.map(|sk| {
            let pk = PublicKey::from(&sk);
            let macs = macs::Validator::new(pk);
            KeyState { pk, sk, macs }
        });

        // recalculate / erase the shared secrets for every peer
        let (ids, same) = self.inner_mut().update_ss();

        // release ids from aborted handshakes
        for id in ids {
            self.release(id)
        }

        // if we found a peer matching the device public key
        // remove it and return its value to the caller
        same.map(|pk| {
            self.inner_mut().pk_map.remove(pk.as_bytes());
            pk
        })
    }

    /// Return the secret key of the device
    ///
    /// # Returns
    ///
    /// A secret key (x25519 scalar)
    pub fn get_sk(&self) -> Option<&StaticSecret> {
        self.inner().keyst.as_ref().map(|key| &key.sk)
    }

    /// Add a new public key to the state machine
    /// To remove public keys, you must create a new machine instance
    ///
    /// # Arguments
    ///
    /// * `pk` - The public key to add
    /// * `identifier` - Associated identifier which can be used to distinguish the peers
    pub fn add(&mut self, pk: PublicKey, opaque: O) -> Result<(), ConfigError> {
        // ensure less than 2^20 peers
        if self.inner().pk_map.len() > MAX_PEER_PER_DEVICE {
            return Err(ConfigError::new("Too many peers for device"));
        }

        // error if public key matches device
        if let Some(key) = self.inner().keyst.as_ref() {
            if pk.as_bytes() == key.pk.as_bytes() {
                return Err(ConfigError::new("Public key of peer matches the device"));
            }
        }

        let mut inner = self.inner_mut();
        // pre-compute shared secret and add to pk_map
        inner.pk_map.insert(
            *pk.as_bytes(),
            Peer::new(
                pk,
                inner.keyst
                .as_ref()
                .map(|key| *key.sk.diffie_hellman(&pk).as_bytes())
                .unwrap_or([0u8; 32]),
                opaque,
            ),
        );

        Ok(())
    }

    /// Remove a peer by public key
    /// To remove public keys, you must create a new machine instance
    ///
    /// # Arguments
    ///
    /// * `pk` - The public key of the peer to remove
    ///
    /// # Returns
    ///
    /// The call might fail if the public key is not found
    pub fn remove(&mut self, pk: &PublicKey) -> Result<(), ConfigError> {
        // remove the peer
        self.inner_mut().pk_map
            .remove(pk.as_bytes())
            .ok_or_else(|| ConfigError::new("Public key not in device"))?;

        // remove every id entry for the peer in the public key map
        // O(n) operations, however it is rare: only when removing peers.
        self.inner_mut().id_map.retain(|_, v| v != pk.as_bytes());
        Ok(())
    }

    /// Add a psk to the peer
    ///
    /// # Arguments
    ///
    /// * `pk` - The public key of the peer
    /// * `psk` - The psk to set / unset
    ///
    /// # Returns
    ///
    /// The call might fail if the public key is not found
    pub fn set_psk(&mut self, pk: PublicKey, psk: Psk) -> Result<(), ConfigError> {
        // match self {
        //     Device::NoOwl(_) => {},
        //     Device::Initiator(i) => {
        //         assert!(psk.as_bytes() == &[0u8; 32], "Only psk 0 is supported for owl-wireguard initiator");
        //     },
        //     Device::Responder(r) => {
        //         assert!(psk.as_bytes() == &[0u8; 32], "Only psk 0 is supported for owl-wireguard responder");
        //     },
        // }

        match self.inner_mut().pk_map.get_mut(pk.as_bytes()) {
            Some(mut peer) => {
                peer.psk = psk;
                Ok(())
            }
            _ => Err(ConfigError::new("No such public key")),
        }
    }

    /// Return the psk for the peer
    ///
    /// # Arguments
    ///
    /// * `pk` - The public key of the peer
    ///
    /// # Returns
    ///
    /// A 32 byte array holding the PSK
    ///
    /// The call might fail if the public key is not found
    pub fn get_psk(&self, pk: &PublicKey) -> Result<Psk, ConfigError> {
        match self.inner().pk_map.get(pk.as_bytes()) {
            Some(peer) => Ok(peer.psk),
            _ => Err(ConfigError::new("No such public key")),
        }
    }

    /// Release an id back to the pool
    ///
    /// # Arguments
    ///
    /// * `id` - The (sender) id to release
    pub fn release(&self, id: u32) {
        let old = self.inner().id_map.remove(&id);
        assert!(old.is_some(), "released id not allocated");
    }
}

pub struct Iter<'a, O> {
    iter: hash_map::Iter<'a, [u8; 32], Peer<O>>,
}

impl<'a, O> Iterator for Iter<'a, O> {
    type Item = (PublicKey, &'a O);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|(pk, peer)| (PublicKey::from(*pk), &peer.opaque))
    }
}

/* These methods enable the Device to act as a map
 * from public keys to the set of contained opaque values.
 *
 * It also abstracts away the problem of PublicKey not being hashable.
 */
impl<O> DeviceInner<O> {
    pub fn clear(&mut self) {
        self.id_map.clear();
        self.pk_map.clear();
    }

    pub fn len(&self) -> usize {
        self.pk_map.len()
    }

    /// Enables enumeration of (public key, opaque) pairs
    /// without exposing internal peer type.
    pub fn iter(&self) -> Iter<O> {
        Iter {
            iter: self.pk_map.iter(),
        }
    }

    /// Enables lookup by public key without exposing internal peer type.
    pub fn get(&self, pk: &PublicKey) -> Option<&O> {
        self.pk_map.get(pk.as_bytes()).map(|peer| &peer.opaque)
    }

    pub fn contains_key(&self, pk: &PublicKey) -> bool {
        self.pk_map.contains_key(pk.as_bytes())
    }
}

/* A mutable reference to the device needs to be held during configuration.
 * Wrapping the device in a RwLock enables peer config after "configuration time"
 */
impl<O> DeviceInner<O> {
    /// Initialize a new handshake state machine
    pub fn new() -> DeviceInner<O> {
        DeviceInner {
            keyst: None,
            id_map: DashMap::new(),
            pk_map: HashMap::new(),
            limiter: Mutex::new(RateLimiter::new()),
        }
    }

    fn update_ss(&mut self) -> (Vec<u32>, Option<PublicKey>) {
        let mut same = None;
        let mut ids = Vec::with_capacity(self.pk_map.len());
        for (pk, peer) in self.pk_map.iter_mut() {
            if let Some(key) = self.keyst.as_ref() {
                if key.pk.as_bytes() == pk {
                    same = Some(PublicKey::from(*pk));
                    peer.ss.clear()
                } else {
                    let pk = PublicKey::from(*pk);
                    peer.ss = *key.sk.diffie_hellman(&pk).as_bytes();
                }
            } else {
                peer.ss.clear();
            }
            if let Some(id) = peer.reset_state() {
                ids.push(id)
            }
        }

        (ids, same)
    }

    // Internal function
    //
    // Return the peer associated with the public key
    pub(super) fn lookup_pk(&self, pk: &PublicKey) -> Result<&Peer<O>, HandshakeError> {
        self.pk_map
            .get(pk.as_bytes())
            .ok_or(HandshakeError::UnknownPublicKey)
    }

    pub fn get_ss(&self, pk: &[u8; 32]) -> Option<[u8; 32]> {
        self.pk_map
            .get(pk.as_bytes())
            .map(|peer| peer.ss)
    }

    // Internal function
    //
    // Return the peer currently associated with the receiver identifier
    pub(super) fn lookup_id(&self, id: u32) -> Result<(&Peer<O>, PublicKey), HandshakeError> {
        // obtain a read reference to entry in the id_map
        let pk = self
            .id_map
            .get(&id)
            .ok_or(HandshakeError::UnknownReceiverId)?;

        // lookup the public key from the pk map
        match self.pk_map.get(&*pk) {
            Some(peer) => Ok((peer, PublicKey::from(*pk))),
            _ => unreachable!(),
        }
    }

    // If there is only one id in the id_map, return it
    // Just for testing purposes
    pub fn get_singleton_id(&self) -> u32 {
        if self.id_map.len() == 1 {
            self.id_map.iter().next().unwrap().key().clone()
        } else {
            panic!("get_singleton_id called on device with more than one id");
        }
    }

    // Internal function
    //
    // Allocated a new receiver identifier for the peer.
    // Implemented via rejection sampling.
    fn allocate<R: RngCore + CryptoRng>(&self, rng: &mut R, pk: &PublicKey) -> u32 {
        loop {
            let id = rng.gen();

            // read lock the shard and do quick check
            if self.id_map.contains_key(&id) {
                continue;
            }

            // write lock the shard and insert
            if let Entry::Vacant(entry) = self.id_map.entry(id) {
                entry.insert(*pk.as_bytes());
                return id;
            };
        }
    }
}

impl<O> Device<O> {
       /// Begin a new handshake
    ///
    /// # Arguments
    ///
    /// * `pk` - Public key of peer to initiate handshake for
    pub fn begin<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        pk: &PublicKey,
    ) -> Result<Vec<u8>, HandshakeError> {
        match (self.inner().keyst.as_ref(), self.inner().pk_map.get(pk.as_bytes())) {
            (_, None) => Err(HandshakeError::UnknownPublicKey),
            (None, _) => Err(HandshakeError::UnknownPublicKey),
            (Some(keyst), Some(peer)) => {
                let local = self.inner().allocate(rng, pk);
                let mut msg = Initiation::default();

                // create noise part of initation
                match self {
                    Device::NoOwl(_) => {
                        // match self {
                        //     Device::NoOwl(_) => {},
                        //     _ => { println!("using no-owl handshake in begin"); }
                        // };
                        noise::create_initiation(rng, keyst, peer, pk, local, &mut msg.noise)?;
                        // add macs to initation
                        peer.macs
                            .lock()
                            .generate(msg.noise.as_bytes(), &mut msg.macs);
                    },
                    Device::Owl(owl_device) => {
                        let cfg: owl_wireguard::cfg_Initiator<O> = owl_wireguard::cfg_Initiator {
                            owl_S_init: owl_device.static_sk.clone(),
                            owl_E_init: owl_device.eph_sk.clone(),
                            pk_owl_S_resp: vec![],
                            pk_owl_S_init: vec![],
                            pk_owl_E_resp: vec![],
                            pk_owl_E_init: vec![],
                            salt: vec![],
                            device: Some(&owl_device.inner)
                        };

                        // println!("dhpk_S_init = {:?}", hex::encode(&*i.cfg.owl_S_init));
                        // println!("dhpk_E_init = {:?}", hex::encode(&*i.cfg.owl_E_init));

                        let mut dummy_state = owl_wireguard::state_Initiator::init_state_Initiator();
                        let static_static = peer.ss;
                        
                        let init_sent_state = cfg.owl_init_stage1_wrapper(
                            &mut dummy_state,
                            pk.as_bytes(),
                            keyst.pk.as_bytes(),
                            static_static.as_bytes(),
                            None, // TODO psk
                            &mut msg.as_bytes_mut()
                        );

                        let hs: [u8; 32] = init_sent_state.owl_ss_h4.as_slice().try_into().unwrap();
                        let ck: [u8; 32] = init_sent_state.owl_iss_c3.as_slice().try_into().unwrap();
                        let e_init_as_array: [u8; 32] = ((*owl_device.eph_sk)[..]).try_into().unwrap();

                        // let static_static = peer.ss;

                        // let initiator_msg1_val = cfg.owl_generate_msg1_wrapper(
                        //     &mut dummy_state, 
                        //     Arc::new(pk.as_bytes().to_vec()), 
                        //     Arc::new(keyst.pk.as_bytes().to_vec()),
                        //     Arc::new(static_static.as_bytes().to_vec()), 
                        //     &mut msg.as_bytes_mut()
                        // );
                        
                        // let hs: [u8; 32] = initiator_msg1_val.owl__initiator_msg1_H4.try_into().unwrap();
                        // let ck: [u8; 32] = initiator_msg1_val.owl__initiator_msg1_C3.try_into().unwrap();
                        // let e_init_as_array: [u8; 32] = ((*i.cfg.owl_E_init)[..]).try_into().unwrap();

                        // save state
                        *peer.state.lock() = crate::wireguard::handshake::peer::State::InitiationSent {
                            hs: hs.into(),
                            ck: ck.into(),
                            eph_sk: e_init_as_array.into(),
                            local,
                        };

                        // println!("msg1 = {} : {} bytes", hex::encode(&msg.as_bytes()[..]), msg.as_bytes().len());

                        // noise::create_initiation_precomputed_eph_key(rng, keyst, peer, pk, local, StaticSecret::from(e_init_as_array), &mut msg.noise)?;
                        // peer.macs
                        //     .lock()
                        //     .generate(msg.noise.as_bytes(), &mut msg.macs);
                    },

                }

                // dbg!(hex::encode(&msg.noise.as_bytes()));


                Ok(msg.as_bytes().to_owned())
            }
        }
    }

    /// Process a handshake message.
    ///
    /// # Arguments
    ///
    /// * `msg` - Byte slice containing the message (untrusted input)
    pub fn process<'a, R: RngCore + CryptoRng>(
        &'a self,
        rng: &mut R,             // rng instance to sample randomness from
        msg: &[u8],              // message buffer
        src: Option<SocketAddr>, // optional source endpoint, set when "under load"
    ) -> Result<Output<'a, O>, HandshakeError> {
        // ensure type read in-range
        if msg.len() < 4 {
            return Err(HandshakeError::InvalidMessageFormat);
        }

        // obtain reference to key state
        // if no key is configured return a noop.
        let keyst = match self.inner().keyst.as_ref() {
            Some(key) => key,
            None => {
                return Ok((None, None, None));
            }
        };

        // de-multiplex the message type field
        match LittleEndian::read_u32(msg) {
            TYPE_INITIATION => {
                match self {
                    // Device::NoOwl(_) => {
                    _ => {
                        // match self {
                        //     Device::NoOwl(_) => {},
                        //     _ => { println!("using no-owl handshake for TYPE_INITIATION"); }
                        // };
                        // parse message
                        let msg = Initiation::parse(msg)?;

                        // check mac1 field
                        keyst.macs.check_mac1(msg.noise.as_bytes(), &msg.macs)?;

                        // address validation & DoS mitigation
                        if let Some(src) = src {
                            // check mac2 field
                            if !keyst.macs.check_mac2(msg.noise.as_bytes(), &src, &msg.macs) {
                                let mut reply = Default::default();
                                keyst.macs.create_cookie_reply(
                                    rng,
                                    msg.noise.f_sender.get(),
                                    &src,
                                    &msg.macs,
                                    &mut reply,
                                );
                                return Ok((None, Some(reply.as_bytes().to_owned()), None));
                            }

                            // check ratelimiter
                            if !self.inner().limiter.lock().unwrap().allow(&src.ip()) {
                                return Err(HandshakeError::RateLimited);
                            }
                        }

                        // consume the initiation
                        let (peer, pk, st) = noise::consume_initiation(self, keyst, &msg.noise)?;

                        // allocate new index for response
                        let local = self.inner().allocate(rng, &pk);

                        // prepare memory for response, TODO: take slice for zero allocation
                        let mut resp = Response::default();

                        // create response (release id on error)
                        let keys = noise::create_response(rng, peer, &pk, local, st, &mut resp.noise)
                            .map_err(|e| {
                                self.release(local);
                                e
                            })?;

                        // add macs to response
                        peer.macs
                            .lock()
                            .generate(resp.noise.as_bytes(), &mut resp.macs);

                        // return unconfirmed keypair and the response as vector
                        Ok((
                            Some(&peer.opaque),
                            Some(resp.as_bytes().to_owned()),
                            Some(keys),
                        ))
                    },
                    // Device::Initiator(_) => {
                    //     panic!("Initiator cannot receive initiation")
                    // },
                    // Device::Responder(r) => {
                    //     let mut dummy_state = owl_wireguard::state_Responder::init_state_Responder();
                    //     let msg1_val = r.cfg.owl_receive_msg1_wrapper(
                    //         &mut dummy_state,
                    //         Arc::new(keyst.pk.as_bytes().to_vec()),
                    //         msg
                    //     );

                    //     let msg1_val = msg1_val.ok_or(HandshakeError::DecryptionFailure)?;

                    //     let pk: [u8; 32] = (&msg1_val.owl__responder_msg1_sender_pk[..]).try_into().unwrap();
                    //     let pk = PublicKey::from(pk);
                    //     let peer = self.inner().lookup_pk(&pk)?;

                    //     // allocate new index for response
                    //     let local = self.inner().allocate(rng, &pk);

                    //     // allocate buffer for response
                    //     let mut resp = Response::default();

                    //     let transp_keys = r.cfg.owl_generate_msg2_wrapper(&mut dummy_state, msg1_val, &mut resp.as_bytes_mut());

                    //     Ok((
                    //         Some(&peer.opaque),
                    //         Some(resp.as_bytes().to_owned()),
                    //         Some(KeyPair {
                    //             birth: Instant::now(),
                    //             initiator: false,
                    //             send: Key {
                    //                 id: u32::from_le_bytes(transp_keys.owl__transp_keys_initiator.try_into().unwrap()),
                    //                 key: transp_keys.owl__transp_keys_T_resp_send.try_into().unwrap(),
                    //             },
                    //             recv: Key {
                    //                 id: local,
                    //                 key: transp_keys.owl__transp_keys_T_init_send.try_into().unwrap(),
                    //             },
                    //         }),
                    //     ))


                    // },
                }
            }
            TYPE_RESPONSE => {
                match self {
                    // Device::NoOwl(_) => {
                    _ => {
                        // match self {
                        //     Device::NoOwl(_) => {},
                        //     _ => { println!("using no-owl handshake for TYPE_RESPONSE"); }
                        // };
                        let msg: zerocopy::LayoutVerified<&[u8], Response> = Response::parse(msg)?;

                        // check mac1 field
                        keyst.macs.check_mac1(msg.noise.as_bytes(), &msg.macs)?;
        
                        // address validation & DoS mitigation
                        if let Some(src) = src {
                            // check mac2 field
                            if !keyst.macs.check_mac2(msg.noise.as_bytes(), &src, &msg.macs) {
                                let mut reply = Default::default();
                                keyst.macs.create_cookie_reply(
                                    rng,
                                    msg.noise.f_sender.get(),
                                    &src,
                                    &msg.macs,
                                    &mut reply,
                                );
                                return Ok((None, Some(reply.as_bytes().to_owned()), None));
                            }
        
                            // check ratelimiter
                            if !self.inner().limiter.lock().unwrap().allow(&src.ip()) {
                                return Err(HandshakeError::RateLimited);
                            }
                        }

                        // consume inner playload
                        noise::consume_response(self, keyst, &msg.noise)
                    },
                    // Device::Initiator(i) => {
                    //     let (peer, pk) = self.inner().lookup_id(self.inner().get_singleton_id())?;
                    //     let (hs, ck, local) = match *peer.state.lock() {
                    //         crate::wireguard::handshake::peer::State::InitiationSent {
                    //             hs,
                    //             ck,
                    //             local,
                    //             eph_sk: _,
                    //         } => Ok((hs, ck, local)),
                    //         _ => Err(HandshakeError::InvalidState),
                    //     }?;

                    //     // dbg!(hex::encode(e_init_as_array));
                    //     let initiator_msg1_val = crate::wireguard::owl_wg::owl_wireguard::owl_initiator_msg1_val {
                    //         owl__initiator_msg1_H4: hs.to_vec(),
                    //         owl__initiator_msg1_C3: ck.to_vec(),
                    //     };
                    //     let mut dummy_state = owl_wireguard::state_Initiator::init_state_Initiator();
                    //     let transp_keys = i.cfg.owl_receive_msg2_wrapper(&mut dummy_state, Arc::new(pk.as_bytes().to_vec()), initiator_msg1_val, msg.as_bytes());


                    //     // let msg: zerocopy::LayoutVerified<&[u8], Response> = Response::parse(msg)?;
                    //     // noise::consume_response(self, keyst, &msg.noise)
                    //     assert!(transp_keys.is_some());

                    //     let transp_keys = transp_keys.ok_or(HandshakeError::DecryptionFailure)?;
                        
                    //     // return confirmed key-pair
                    //     let birth = Instant::now();
                    //     Ok((
                    //         Some(&peer.opaque),
                    //         None,
                    //         Some(KeyPair {
                    //             birth,
                    //             initiator: true,
                    //             send: Key {
                    //                 id: u32::from_le_bytes(transp_keys.owl__transp_keys_responder.try_into().unwrap()),
                    //                 key: transp_keys.owl__transp_keys_T_init_send.try_into().unwrap(),
                    //             },
                    //             recv: Key {
                    //                 id: local,
                    //                 key: transp_keys.owl__transp_keys_T_resp_send.try_into().unwrap(),
                    //             },
                    //         }),
                    //     ))

                    // },
                    // Device::Responder(_) => {
                    //     panic!("Responder cannot receive response");
                    // },
                }
            }
            TYPE_COOKIE_REPLY => {
                let msg = CookieReply::parse(msg)?;

                // lookup peer
                let (peer, _) = self.inner().lookup_id(msg.f_receiver.get())?;

                // validate cookie reply
                peer.macs.lock().process(&msg)?;

                // this prompts no new message and
                // DOES NOT cryptographically verify the peer
                Ok((None, None, None))
            }
            _ => Err(HandshakeError::InvalidMessageFormat),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use std::collections::HashSet;

    proptest! {
        #[test]
        fn unique_shared_secrets(sk_bs: [u8; 32], pk1_bs: [u8; 32], pk2_bs: [u8; 32]) {
            let sk = StaticSecret::from(sk_bs);
            let pk1 = PublicKey::from(pk1_bs);
            let pk2 = PublicKey::from(pk2_bs);

            assert_eq!(pk1.as_bytes(), &pk1_bs);
            assert_eq!(pk2.as_bytes(), &pk2_bs);

            let mut dev : Device<u32> = Device::new();
            dev.set_sk(Some(sk));

            dev.add(pk1, 1).unwrap();
            if dev.add(pk2, 0).is_err() {
                assert_eq!(pk1_bs, pk2_bs);
                assert_eq!(*dev.inner().get(&pk1).unwrap(), 1);
            }


            // every shared secret is unique
            let mut ss: HashSet<[u8; 32]> = HashSet::new();
            for peer in dev.inner().pk_map.values() {
                ss.insert(peer.ss);
            }
            assert_eq!(ss.len(), dev.inner().len());
        }
    }
}
