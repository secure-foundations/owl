#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#[cfg_attr(verus_keep_ghost, forbid(unsafe_code))]

pub use vstd::{modes::*, prelude::*, seq::*, view::*};
pub mod speclib;
pub use crate::speclib::{*, itree::*};
pub mod execlib;
pub use crate::execlib::{*};
pub mod owl_const_bytes;
pub use crate::owl_const_bytes::*;
pub use vest_lib::{
    combinators::*,
    core::spec::*,
    core::exec::{
        InputBuf, InputSlice, OutputBuf, PResult, ParseError, Parser, Prepare, Serializer,
        SerializerExt,
    },
};

pub use std::collections::HashMap;
pub use std::env;
pub use std::fs;
pub use std::io::{self, BufRead, Write};
pub use std::net::{SocketAddr, TcpListener, TcpStream, ToSocketAddrs};
pub use std::sync::Arc;
pub use std::str;
pub use std::thread;
pub use std::time::Duration;
pub use std::time::Instant;

verus! {
pub trait OwlEffects {
    fn owl_output<A>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
        x: &[u8],
        dest_addr: Option<&str>,
        ret_addr: &str,
    )
        requires
            old(t).view().is_output(
                x.view(),
                option_map(view_option(dest_addr), |a| endpoint_of_addr(a)),
            ),
        ensures
            final(t).view() == old(t).view().give_output(),
    ;

    fn owl_input<A>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
    ) -> (ie: (Vec<u8>, String))
        requires
            old(t).view().is_input(),
        ensures
            final(t).view() == old(t).view().take_input(ie.0.view(), endpoint_of_addr(ie.1.view())),
    ;

    fn owl_sample<A, 'a>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
        n: usize,
    ) -> (res: SecretBuf<'a>)
        requires
            old(t).view().is_sample(n),
        ensures
            final(t).view() == old(t).view().get_sample(res.view()),
            res.len_valid(),
    ;

    fn owl_output_serialize_fused<A, T: DeepView, C: Serializer<Vec<u8>, T>>(
        &mut self,
        Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>,
        comb: C,
        val: T,
        dest_addr: Option<&str>,
        ret_addr: &str,
    )
        requires
            comb.exec_inv(),
            comb.consistent(val.deep_view()),
            old(t).view().is_output(
                comb.spec_serialize(val.deep_view()),
                option_map(view_option(dest_addr), |a| endpoint_of_addr(a)),
            ),
        ensures
            final(t).view() == old(t).view().give_output(),
    ;
}


// for debugging purposes, not used by the compiler
#[verifier(external_body)]
pub fn debug_print_bytes(x: &[u8]) {
    println!("debug_print_bytes: {:?}", x);
}

#[derive(Debug)]
pub enum OwlError {
    IntegerOverflow,
}

} // verus!
