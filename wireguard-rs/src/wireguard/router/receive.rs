use super::device::DecryptionState;
use super::ip::inner_length;
use super::messages::TransportHeader;
use super::queue::{ParallelJob, Queue, SequentialJob};
use super::types::Callbacks;
use super::{REJECT_AFTER_MESSAGES, SIZE_TAG};

use super::super::{tun, udp, Endpoint, types::RouterDeviceType};

use alloc::sync::Arc;
use core::sync::atomic::{AtomicBool, Ordering};
use ring::aead::{Aad, LessSafeKey, Nonce, UnboundKey, CHACHA20_POLY1305};
use spin::Mutex;
use zerocopy::{AsBytes, LayoutVerified};

use crate::wireguard::owl_wg::owl_wireguard;
use std::convert::TryInto;

struct Inner<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> {
    ready: AtomicBool,                       // job status
    buffer: Mutex<(Option<E>, Vec<u8>)>,     // endpoint & ciphertext buffer
    state: Arc<DecryptionState<E, C, T, B>>, // decryption state (keys and replay protector)
    job_type: RouterDeviceType
}

pub struct ReceiveJob<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>>(
    Arc<Inner<E, C, T, B>>,
);

impl<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> Clone
    for ReceiveJob<E, C, T, B>
{
    fn clone(&self) -> ReceiveJob<E, C, T, B> {
        ReceiveJob(self.0.clone())
    }
}

#[cfg(test)]
impl<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> ReceiveJob<E, C, T, B> {
    pub fn get_buffer(&self) -> Vec<u8> {
        let job = &self.0;
        let msg = &job.buffer.lock().1;
        msg.clone()
    }
}


impl<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> ReceiveJob<E, C, T, B> {
    pub fn new(
        buffer: Vec<u8>,
        state: Arc<DecryptionState<E, C, T, B>>,
        endpoint: E,
        job_type: RouterDeviceType
    ) -> ReceiveJob<E, C, T, B> {
        ReceiveJob(Arc::new(Inner {
            ready: AtomicBool::new(false),
            buffer: Mutex::new((Some(endpoint), buffer)),
            state,
            job_type
        }))
    }
}

impl<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> ParallelJob
    for ReceiveJob<E, C, T, B>
{
    fn queue(&self) -> &Queue<Self> {
        &self.0.state.peer.inbound
    }

    /* The parallel section of an incoming job:
     *
     * - Decryption.
     * - Crypto-key routing lookup.
     *
     * Note: We truncate the message buffer to 0 bytes in case of authentication failure
     * or crypto-key routing failure (attempted impersonation).
     *
     * Note: We cannot do replay protection in the parallel job,
     * since this can cause dropping of packets (leaving the window) due to scheduling.
     */
    fn parallel_work(&self) {
        debug_assert_eq!(
            self.is_ready(),
            false,
            "doing parallel work on completed job"
        );
        log::trace!("processing parallel receive job");

        // decrypt
        {
            // closure for locking
            let job = &self.0;
            let peer = &job.state.peer;
            let mut msg = job.buffer.lock();

            // process buffer
            let ok = (|| {
                match self.0.job_type {
                    RouterDeviceType::NoOwl => {              
                        // cast to header followed by payload
                        let (header, packet): (LayoutVerified<&mut [u8], TransportHeader>, &mut [u8]) =
                        match LayoutVerified::new_from_prefix(&mut msg.1[..]) {
                            Some(v) => v,
                            None => return false,
                        };

                        // create nonce object
                        let mut nonce = [0u8; 12];
                        debug_assert_eq!(nonce.len(), CHACHA20_POLY1305.nonce_len());
                        nonce[4..].copy_from_slice(header.f_counter.as_bytes());
                        let nonce = Nonce::assume_unique_for_key(nonce);
                        // do the weird ring AEAD dance
                        let key = LessSafeKey::new(
                            UnboundKey::new(&CHACHA20_POLY1305, &job.state.keypair.recv.key[..]).unwrap(),
                        );

                        // attempt to open (and authenticate) the body
                        match key.open_in_place(nonce, Aad::empty(), packet) {
                            Ok(_) => (),
                            Err(_) => return false,
                        }

                        // check that counter not after reject
                        if header.f_counter.get() >= REJECT_AFTER_MESSAGES {
                            return false;
                        }

                        // check crypto-key router
                        packet.len() == SIZE_TAG || peer.device.table.check_route(&peer, &packet)
                    }
                    RouterDeviceType::OwlInitiator => {
                        let cfg: owl_wireguard::cfg_Initiator<u8> = owl_wireguard::cfg_Initiator {
                            owl_S_init: vec![],
                            owl_E_init: vec![],
                            pk_owl_S_resp: vec![],
                            pk_owl_S_init: vec![],
                            pk_owl_E_resp: vec![],
                            pk_owl_E_init: vec![],
                            salt: vec![],
                            device: None
                        };
                        let mut state = owl_wireguard::state_Initiator::init_state_Initiator();
                        if (msg.1.len() < 16) {
                            return false;
                        } 
        
                        let transp_keys = owl_wireguard::owl_transp_keys_init {
                            owl_tki_msg2_receiver: crate::wireguard::owl_wg::execlib::OwlBuf::from_vec(vec![]),
                            owl_tki_msg2_sender: crate::wireguard::owl_wg::execlib::OwlBuf::from_slice(&msg.1[4..8]),
                            owl_tki_k_init_send: crate::wireguard::owl_wg::execlib::OwlBuf::from_slice(&job.state.keypair.send.key[..]),
                            owl_tki_k_resp_send: crate::wireguard::owl_wg::execlib::OwlBuf::from_slice(&job.state.keypair.recv.key[..]),
                        };
        
                        // TODO: the solver optimization stuff should allow us to do this in-place and avoid this copy
                        let ctxt = msg.1.to_vec();
                        let res = cfg.owl_transp_recv_init_wrapper(&mut state, transp_keys, &ctxt[..]);
                        
                        match res {
                            Some(ptxt) => {
                                let msg_len = msg.1.len();
                                msg.1[16..(msg_len - SIZE_TAG)].copy_from_slice(&ptxt.as_slice());
                                
                                // check crypto-key router
                                msg.1[16..].len() == SIZE_TAG || peer.device.table.check_route(&peer, &msg.1[16..])
                            },
                            None => false 
                        }
                    },
                    RouterDeviceType::OwlResponder => {
                        let cfg: owl_wireguard::cfg_Responder<u8> = owl_wireguard::cfg_Responder {
                            owl_S_resp: vec![],
                            owl_E_resp: vec![],
                            pk_owl_S_resp: vec![],
                            pk_owl_S_init: vec![],
                            pk_owl_E_resp: vec![],
                            pk_owl_E_init: vec![],
                            salt: vec![],
                            device: None
                        };
                        let mut state = owl_wireguard::state_Responder::init_state_Responder();
                        if (msg.1.len() < 16) {
                            return false;
                        } 
        
                        let transp_keys = owl_wireguard::owl_transp_keys_resp {
                            owl_tkr_msg2_receiver: crate::wireguard::owl_wg::execlib::OwlBuf::from_vec(msg.1[4..8].to_vec()),
                            owl_tkr_msg2_sender: crate::wireguard::owl_wg::execlib::OwlBuf::from_vec(vec![]),
                            owl_tkr_recvd: true, // TODO: confirm, but I think wireguard-rs handshake automatically sends the extra message
                            owl_tkr_k_init_send: crate::wireguard::owl_wg::execlib::OwlBuf::from_slice(&job.state.keypair.recv.key[..]),
                            owl_tkr_k_resp_send: crate::wireguard::owl_wg::execlib::OwlBuf::from_slice(&job.state.keypair.send.key[..]),
                        };

                        // TODO: the solver optimization stuff should allow us to do this in-place and avoid this copy
                        let ctxt = msg.1.to_vec();
                        let res = cfg.owl_transp_recv_resp_wrapper(&mut state, transp_keys, &ctxt[..]);
                        
                        match res {
                            Some(ptxt) => {
                                let msg_len = msg.1.len();
                                msg.1[16..(msg_len - SIZE_TAG)].copy_from_slice(&ptxt.as_slice());
                                
                                // check crypto-key router
                                msg.1[16..].len() == SIZE_TAG || peer.device.table.check_route(&peer, &msg.1[16..])
                            },
                            None => false 
                        }
                    },
                }
            })();

            // remove message in case of failure:
            // to indicate failure and avoid later accidental use of unauthenticated data.
            if !ok {
                msg.1.truncate(0);
            }
        };

        // mark ready
        self.0.ready.store(true, Ordering::Release);
    }
}

impl<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> SequentialJob
    for ReceiveJob<E, C, T, B>
{
    fn is_ready(&self) -> bool {
        self.0.ready.load(Ordering::Acquire)
    }

    fn sequential_work(self) {
        debug_assert_eq!(
            self.is_ready(),
            true,
            "doing sequential work on an incomplete job"
        );
        log::trace!("processing sequential receive job");

        let job = &self.0;
        let peer = &job.state.peer;
        let mut msg = job.buffer.lock();
        let endpoint = msg.0.take();

        // cast transport header
        let (header, packet): (LayoutVerified<&[u8], TransportHeader>, &[u8]) =
            match LayoutVerified::new_from_prefix(&msg.1[..]) {
                Some(v) => v,
                None => {
                    // also covers authentication failure (will fail to parse header)
                    return;
                }
            };

        // check for replay
        if !job.state.protector.lock().update(header.f_counter.get()) {
            log::debug!("inbound worker: replay detected");
            return;
        }

        // check for confirms key
        if !job.state.confirmed.swap(true, Ordering::SeqCst) {
            log::debug!("inbound worker: message confirms key");
            peer.confirm_key(&job.state.keypair);
        }

        // update endpoint
        *peer.endpoint.lock() = endpoint;

        // check if should be written to TUN
        // (keep-alive and malformed packets will have no inner length)
        if let Some(inner) = inner_length(packet) {
            if inner + SIZE_TAG <= packet.len() {
                let _ = peer.device.inbound.write(&packet[..inner]).map_err(|e| {
                    log::debug!("failed to write inbound packet to TUN: {:?}", e);
                });
            }
        }

        // trigger callback
        C::recv(&peer.opaque, msg.1.len(), true, &job.state.keypair);
    }
}
