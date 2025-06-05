use super::messages::{TransportHeader, TYPE_TRANSPORT};
use super::peer::Peer;
use super::queue::{ParallelJob, Queue, SequentialJob};
use super::types::{Callbacks};
use super::KeyPair;
use super::{REJECT_AFTER_MESSAGES, SIZE_TAG};

use super::super::{tun, udp, Endpoint, types::RouterDeviceType};

use alloc::sync::Arc;
use core::sync::atomic::{AtomicBool, Ordering};

use ring::aead::{Aad, LessSafeKey, Nonce, UnboundKey, CHACHA20_POLY1305};
use spin::Mutex;
use zerocopy::{AsBytes, LayoutVerified};

use crate::wireguard::owl_wg::owl_wireguard;

struct Inner<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> {
    ready: AtomicBool,
    buffer: Mutex<Vec<u8>>,
    counter: u64,
    keypair: Arc<KeyPair>,
    peer: Peer<E, C, T, B>,
    job_type: RouterDeviceType,
}

pub struct SendJob<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>>(
    Arc<Inner<E, C, T, B>>,
);

impl<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> Clone for SendJob<E, C, T, B> {
    fn clone(&self) -> SendJob<E, C, T, B> {
        SendJob(self.0.clone())
    }
}

#[cfg(test)]
impl<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>>  SendJob<E, C, T, B> {
    pub fn get_buffer(&self) -> Vec<u8> {
        let job = &self.0;
        let msg = job.buffer.lock();
        msg.clone()
    }
}

impl<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> SendJob<E, C, T, B> {
    pub fn new(
        buffer: Vec<u8>,
        counter: u64,
        keypair: Arc<KeyPair>,
        peer: Peer<E, C, T, B>,
        job_type: RouterDeviceType
    ) -> SendJob<E, C, T, B> {
        SendJob(Arc::new(Inner {
            buffer: Mutex::new(buffer),
            counter,
            keypair,
            peer,
            ready: AtomicBool::new(false),
            job_type
        }))
    }
}

impl<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> ParallelJob
    for SendJob<E, C, T, B>
{
    fn queue(&self) -> &Queue<Self> {
        &self.0.peer.outbound
    }

    fn parallel_work(&self) {
        debug_assert_eq!(
            self.is_ready(),
            false,
            "doing parallel work on completed job"
        );
        log::trace!("processing parallel send job");

        let job = &*self.0;
        let mut msg = job.buffer.lock();

        // make space for the tag
        msg.extend([0u8; SIZE_TAG].iter());

        // encrypt body
        match self.0.job_type {
            RouterDeviceType::NoOwl => {  
                // cast to header (should never fail)
                let (mut header, packet): (LayoutVerified<&mut [u8], TransportHeader>, &mut [u8]) =
                    LayoutVerified::new_from_prefix(&mut msg[..])
                        .expect("earlier code should ensure that there is ample space");
    
                // set header fields
                debug_assert!(
                    job.counter < REJECT_AFTER_MESSAGES,
                    "should be checked when assigning counters"
                );
                header.f_type.set(TYPE_TRANSPORT);
                header.f_receiver.set(job.keypair.send.id);
                header.f_counter.set(job.counter);
    
                // create a nonce object
                let mut nonce = [0u8; 12];
                debug_assert_eq!(nonce.len(), CHACHA20_POLY1305.nonce_len());
                nonce[4..].copy_from_slice(header.f_counter.as_bytes());
                let nonce = Nonce::assume_unique_for_key(nonce);
    
                // encrypt contents of transport message in-place
                let tag_offset = packet.len() - SIZE_TAG;
                let key = LessSafeKey::new(
                    UnboundKey::new(&CHACHA20_POLY1305, &job.keypair.send.key[..]).unwrap(),
                );
                let tag = key
                    .seal_in_place_separate_tag(nonce, Aad::empty(), &mut packet[..tag_offset])
                    .unwrap();
    

                // append tag
                packet[tag_offset..].copy_from_slice(tag.as_ref());
            },
            RouterDeviceType::OwlInitiator => {
                let cfg: owl_wireguard::cfg_Initiator<u8> = owl_wireguard::cfg_Initiator::mk_cfg_Initiator(
                    vec![],
                    &[],
                    &[],
                    &[],
                    &[],
                    &[],
                    &[],
                    None
                );
                let mut state = owl_wireguard::state_Initiator::init_state_Initiator();
                state.owl_N_init_send = job.counter as usize;

                // unsafe {
                // TODO: the solver optimization stuff should allow us to do this in-place and avoid this copy
                let plaintext = msg[SIZE_TAG..(msg.len() - SIZE_TAG)].to_vec();

                // Convert the message array to a borrow, unsafely
                // let plaintext =
                //     &*(&msg[SIZE_TAG..(msg.len() - SIZE_TAG)] as *const [u8] as *mut [u8]);
                
                let msg2_receiver = job.keypair.send.id.to_le_bytes();

                let succeeded = cfg.owl_transp_send_init_wrapper(
                    &mut state, 
                    &plaintext, 
                    &mut msg,
                    msg2_receiver.as_slice(),
                    [].as_slice(),
                    &job.keypair.send.key[..],
                    &job.keypair.recv.key[..],
                );
                // }
                // let succeeded = cfg.owl_transp_send_init_inplace(&mut state, transp_keys, &mut msg);

                // assert!(succeeded.is_some());
            },
            RouterDeviceType::OwlResponder => {
                let cfg: owl_wireguard::cfg_Responder<u8> = owl_wireguard::cfg_Responder::mk_cfg_Responder(
                    vec![],
                    &[],
                    &[],
                    &[],
                    &[],
                    &[],
                    &[],
                    None
                );
                let mut state = owl_wireguard::state_Responder::init_state_Responder();
                state.owl_N_resp_send = job.counter as usize;

                let msg2_sender = job.keypair.send.id.to_le_bytes();

                // TODO: the solver optimization stuff should allow us to do this in-place and avoid this copy
                let plaintext = msg[SIZE_TAG..(msg.len() - SIZE_TAG)].to_vec();

                let succeeded = cfg.owl_transp_send_resp_wrapper(
                    &mut state, 
                    &plaintext, 
                    &mut msg,
                    [].as_slice(),
                    msg2_sender.as_slice(),
                    true, // TODO: confirm, but I think wireguard-rs handshake automatically sends the extra message
                    &job.keypair.recv.key[..],
                    &job.keypair.send.key[..]
                );

                // assert!(succeeded.is_some());
            },
        }
        // dbg!(hex::encode(msg.as_bytes()));
        // mark ready
        self.0.ready.store(true, Ordering::Release);
    }
}

impl<E: Endpoint, C: Callbacks, T: tun::Writer, B: udp::Writer<E>> SequentialJob
    for SendJob<E, C, T, B>
{
    fn is_ready(&self) -> bool {
        self.0.ready.load(Ordering::Acquire)
    }

    fn sequential_work(self) {
        debug_assert_eq!(
            self.is_ready(),
            true,
            "doing sequential work 
            on an incomplete job"
        );
        log::trace!("processing sequential send job");

        // send to peer
        let job = &self.0;
        let msg = job.buffer.lock();
        let xmit = job.peer.send_raw(&msg[..]).is_ok();

        // trigger callback (for timers)
        C::send(&job.peer.opaque, msg.len(), xmit, &job.keypair, job.counter);
    }
}
