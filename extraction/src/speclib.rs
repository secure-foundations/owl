#![allow(unused_imports)]
#![allow(non_camel_case_types)]
pub use vstd::{modes::*, prelude::*, seq::*, *};
pub use crate::DView;

////////////////////////////////////////////////////////////////////////////////
///////////////////// CRYPTO ETC LIBRARY ///////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
verus! {


pub open spec fn options_match(s: Option<Seq<u8>>, v: Option<Vec<u8>>) -> bool
{
    (v.is_None() && s.is_None()) ||
    (v.is_Some() && s.is_Some() && v.get_Some_0().dview() == s.get_Some_0())
}

pub open spec fn view_option<T: View>(v: Option<T>) -> Option<T::V>
{
    match v {
        Option::Some(x) => Option::Some(x.view()),
        Option::None    => Option::None
    }
}

pub open spec fn dview_option<T: DView>(v: Option<T>) -> Option<T::V>
{
    match v {
        Option::Some(x) => Option::Some(x.dview()),
        Option::None    => Option::None
    }
}

pub open spec fn option_as_seq<T: OwlSpecSerialize>(v: Option<T>) -> Option<Seq<u8>>
{
    match v {
        Option::Some(x) => Option::Some(x.as_seq()),
        Option::None    => Option::None
    }
}


pub trait OwlSpecSerialize {
    spec fn as_seq(self) -> Seq<u8> where Self: Sized;
}

impl OwlSpecSerialize for Seq<u8> {
    open spec fn as_seq(self) -> Seq<u8> {
        self
    }
}

pub trait OwlSpecAsCtr {
    spec fn as_ctr(self) -> usize where Self: Sized;
}

impl OwlSpecAsCtr for Seq<u8> {
    open spec fn as_ctr(self) -> usize {
        bytes_as_counter(self)
    }
}

/// A convenience macro to produce the triangle necessary to confirm that there are no overflows
/// that occur when adding up a bunch of different expressions together.
/// from Jay Bosamiya
#[allow(unused_macros)]
macro_rules! no_usize_overflows {
  ($e:expr,) => {
    true
  };
  ($($e:expr),*) => {
    no_usize_overflows!(@@internal 0, $($e),*)
  };
  (@@internal $total:expr,) => {
    true
  };
  (@@internal $total:expr, $a:expr) => {
    usize::MAX - $total >= $a
  };
  (@@internal $total:expr, $a:expr, $($rest:expr),*) => {
    usize::MAX - $total >= $a
      &&
    no_usize_overflows!(@@internal ($total + $a), $($rest),*)
  };
}
pub(crate) use no_usize_overflows;

#[verifier::inline]
pub open const spec fn usize_max_as_nat() -> nat {
    usize::MAX as nat    
}

/// A convenience macro to produce the triangle necessary to confirm that there are no overflows
/// that occur when adding up a bunch of different expressions together.
/// from Jay Bosamiya
#[allow(unused_macros)]
macro_rules! no_usize_overflows_spec {
  ($e:expr,) => { verus_proof_expr! {
    true
  }};
  ($($e:expr),*) => { verus_proof_expr! {
    no_usize_overflows_spec!(@@internal (0 as nat), $($e),*)
  }};
  (@@internal $total:expr,) => { verus_proof_expr! {
    true
  }};
  (@@internal $total:expr, $a:expr) => { verus_proof_expr! {
    usize_max_as_nat() - $total >= $a
  }};
  (@@internal $total:expr, $a:expr, $($rest:expr),*) => { verus_proof_expr! {
    usize_max_as_nat() - $total >= $a
      &&
    no_usize_overflows_spec!(@@internal ($total + $a), $($rest),*)
  }};
}
pub(crate) use no_usize_overflows_spec;


// Rust cannot infer that the type of seq![] is Seq<u8>, so we annotate explicitly
pub open spec fn empty_seq_u8() -> Seq<u8> {
    seq![]
}

pub open spec fn seq_u8_of_len(n: nat) -> Seq<u8> {
    Seq::new(n, |i| 0u8)
}

pub open spec fn seq_truncate(s: Seq<u8>, n: nat) -> Seq<u8> {
    if n <= s.len() {
        s.subrange(0, n as int)
    } else {
        s
    }
}

pub open spec fn concat(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    a.add(b)
}


#[verifier(external_body)]
pub closed spec(checked) fn evercrypt_spec_of_enc(k: Seq<u8>, x: Seq<u8>, coins: Seq<u8>) -> Seq<u8>
    recommends k.len() == crate::KEY_SIZE(),
               coins.len() == crate::TAG_SIZE()
{
    todo!()
}

pub open spec(checked) fn enc(k: Seq<u8>, x: Seq<u8>, coins: Seq<u8>) -> (c: Seq<u8>)
{
    // match (k, c) {
    //     (Some(k), Some(c)) =>
            if (k.len() == crate::KEY_SIZE() && coins.len() == crate::TAG_SIZE()) {
                evercrypt_spec_of_enc(k, x, coins)
            } else {
                seq![]
            }
    //     _ => None
    // }
}


#[verifier(external_body)]
pub closed spec(checked) fn evercrypt_spec_of_dec(k: Seq<u8>, c: Seq<u8>) -> Option<Seq<u8>>
    recommends k.len() == crate::KEY_SIZE(),
{
    todo!()
}

pub open spec(checked) fn dec(k: Seq<u8>, c: Seq<u8>) -> (x: Option<Seq<u8>>)
{
    // match (k, c) {
    //     (Some(k), Some(c)) =>
            if (k.len() == crate::KEY_SIZE()) {
                evercrypt_spec_of_dec(k, c)
            } else {
                None
            }
    //     _ => None
    // }
}

#[verifier(external_body)]
pub closed spec(checked) fn sign(privkey: Seq<u8>, msg: Seq<u8>) -> (signature: Seq<u8>)
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn vrfy(pubkey: Seq<u8>, msg: Seq<u8>, signature: Seq<u8>) -> (x: Option<Seq<u8>>)
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn dhpk(privkey: Seq<u8>) -> (pubkey: Seq<u8>)
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn dh_combine(pubkey: Seq<u8>, privkey: Seq<u8>) -> (ss: Seq<u8>)
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn kdf(len: usize, salt: Seq<u8>, ikm: Seq<u8>, info: Seq<u8>) -> (h: Seq<u8>)
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn pkenc(pubkey: Seq<u8>, msg: Seq<u8>) -> (ctxt: Seq<u8>)
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn pkdec(privkey: Seq<u8>, ctxt: Seq<u8>) -> (msg: Seq<u8>)
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn mac(mackey: Seq<u8>, msg: Seq<u8>) -> (mac: Seq<u8>)
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn mac_vrfy(mackey: Seq<u8>, msg: Seq<u8>, mac: Seq<u8>) -> (x: Option<Seq<u8>>)
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn enc_st_aead_inner(k: Seq<u8>, x: Seq<u8>, nonce: usize, aad: Seq<u8>) -> (c: Seq<u8>)
{ unimplemented!() }

pub open spec(checked) fn enc_st_aead(k: Seq<u8>, x: Seq<u8>, nonce: usize, aad: Seq<u8>) -> 
    (res: (Seq<u8>, usize))
{ 
    // We ignore the possibility of overflow here
    (enc_st_aead_inner(k,x,nonce, aad), #[verifier::truncate] ((nonce + 1usize) as usize))
}

#[verifier(external_body)]
pub closed spec(checked) fn dec_st_aead(k: Seq<u8>, c: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>) -> (x: Option<Seq<u8>>)
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn is_group_elem(x: Seq<u8>) -> bool
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn crh(x: Seq<u8>) -> Seq<u8>
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn bytes_as_counter(x: Seq<u8>) -> usize
{ unimplemented!() }

#[verifier(external_body)]
pub closed spec(checked) fn counter_as_bytes(x: usize) -> Seq<u8>
{ unimplemented!() }

pub open spec fn andb(x: bool, y: bool) -> bool
{
    x && y
}

pub open spec fn notb(x: bool) -> bool
{
    !x
}


pub open spec fn length(x: Seq<u8>) -> usize
    recommends x.len() < usize::MAX
{
    x.len() as usize
}

}

////////////////////////////////////////////////////////////////////////////////
///////////////////// ITREE DEFINITION /////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

pub mod itree {
    use crate::*;
    use vstd::{modes::*, prelude::*, seq::*, *};

    verus! {
    #[is_variant]
    pub enum ITree<A, #[verifier(maybe_negative)] Endpoint> {
        Input  (FnSpec(Seq<u8>, Endpoint) -> ITree<A, Endpoint>),
        Output (Seq<u8>, Endpoint, Box<ITree<A, Endpoint>>),
        Sample (usize, FnSpec(Seq<u8>) -> ITree<A, Endpoint>),
        Ret    (A),
    }

    impl<A, Endpoint> ITree<A, Endpoint> {
        pub open spec fn is_input(&self) -> bool {
            self.is_Input()
        }
        pub open spec(checked) fn take_input(&self, i: Seq<u8>, ev: Endpoint) -> ITree<A,Endpoint>
            recommends self.is_input()
        {
            (self.get_Input_0())(i, ev)
        }
        pub open spec fn is_output(&self, o: Seq<u8>, ev: Endpoint) -> bool {
            self.is_Output() && self.get_Output_0() == o && self.get_Output_1() == ev
        }
        pub open spec(checked) fn give_output(&self) -> ITree<A,Endpoint>
            recommends (exists |o, ev| self.is_output(o, ev))
        {
            *self.get_Output_2()
        }
        pub open spec fn is_sample(&self, n: usize) -> bool {
            self.is_Sample() && self.get_Sample_0() == n
        }
        pub open spec(checked) fn get_sample(&self, coins: Seq<u8>) -> ITree<A,Endpoint>
            recommends (exists |n| self.is_sample(n))
        {
            (self.get_Sample_1())(coins)
        }
        pub open spec(checked) fn results_in(&self, a: A) -> bool 
        {
            self.is_Ret() && self.get_Ret_0() == a
        }

        pub open spec fn bind<B>(&self, next: FnSpec(A) -> ITree<B, Endpoint>) -> ITree<B, Endpoint>
            decreases self
        {
            match self {
                ITree::Input(k) => {
                    ITree::Input(|x, e| (k(x, e)).bind(next))
                },
                ITree::Output(o, e, t) => {
                    ITree::Output(*o, *e, Box::new((*t).bind(next)))
                },
                ITree::Sample(n, k) => {
                    ITree::Sample(*n, |coins| k(coins).bind(next))
                }
                ITree::Ret(a) => {
                    next(*a)
                }
            }
        }
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_ret<A, B, Endpoint>(x: A, k : FnSpec(A) -> ITree<B, Endpoint>)
        ensures
            (#[trigger] ITree::Ret(x).bind(k)) == k(x)
    { }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_input<A, B, Endpoint>(f : FnSpec(Seq<u8>, Endpoint) -> ITree<A, Endpoint>, k: FnSpec(A) -> ITree<B, Endpoint>)
        ensures
            (#[trigger] ITree::Input(f).bind(k)) == ITree::Input(|x,e| f(x,e).bind(k))
    { }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_output<A, B, Endpoint>(x : Seq<u8>, e: Endpoint, f : Box<ITree<A, Endpoint>>, k : FnSpec(A) -> ITree<B, Endpoint>)
        ensures
            (#[trigger] ITree::Output(x, e, f).bind(k)) == ITree::Output(x, e, Box::new((*f).bind(k)))
    { }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_sample<A, B, Endpoint>(n : usize, f : FnSpec(Seq<u8>) -> ITree<A, Endpoint>, k : FnSpec(A) -> ITree<B, Endpoint>)
        ensures
            (#[trigger] ITree::Sample(n, f).bind(k)) == ITree::Sample(n, |coins| f(coins).bind(k))
    { }

    //////////////////////////////////////////////////////
    ///// Proof for axiom_bind_assoc (TODO update) ///////
    //////////////////////////////////////////////////////

    // // triggering hack
    // pub open spec fn trig<A>(x: A) -> bool { true }

    // pub open spec fn is_equal<A>(x : ITree<A, Endpoint>, y : ITree<A, Endpoint>) -> bool
    //     decreases x, y
    // {
    //     match (x, y) {
    //         (ITree::Ret(a), ITree::Ret(b)) => x == y,
    //         (ITree::Input(kx), ITree::Input(ky)) => forall|v| #[trigger] trig(v) ==> is_equal(kx(v), ky(v)),
    //         (ITree::Output(ox, ex, tx), ITree::Output(oy, ey, ty)) => ox == oy && ex == ey && is_equal(*tx, *ty),
    //         (_, _) => false,
    //     }
    // }

    // pub proof fn is_equal_eq<A>(x: ITree<A, Endpoint>, y: ITree<A, Endpoint>)
    //     requires is_equal(x, y)
    //     ensures  x =~~= y
    //     decreases x, y
    // {
    //     match (x, y) {
    //         (ITree::Input(ff), ITree::Input(gg)) => {
    //             assert forall|v| #[trigger] ff(v) =~= gg(v) by {
    //                 assert(trig(v));
    //                 is_equal_eq(ff(v), gg(v))
    //             }
    //             assert (ff =~~= gg);
    //         },
    //         (ITree::Output(ox, tx), ITree::Output(oy, ty)) => {
    //             is_equal_eq(*tx, *ty)
    //         }
    //         _ => {}
    //     }
    // }

    // #[verifier(external_body)]
    // #[verifier(broadcast_forall)]
    // pub proof fn axiom_is_equal_eq<A>(x: ITree<A, Endpoint>, y: ITree<A, Endpoint>)
    //     requires is_equal(x, y)
    //     ensures  x =~~= y
    // {}

    // pub proof fn eq_is_equal<A>(x: ITree<A, Endpoint>, y: ITree<A, Endpoint>)
    //     requires x =~~= y
    //     ensures  is_equal(x, y)
    //     decreases x, y
    // {
    //     match (x, y) {
    //         (ITree::Input(ff), ITree::Input(gg)) => {
    //             assert forall|v| #[trigger] trig(v) implies is_equal(ff(v), gg(v)) by {
    //                 eq_is_equal(ff(v), gg(v))
    //             }
    //         },
    //         (ITree::Output(ox, tx), ITree::Output(oy, ty)) => {
    //             eq_is_equal(*tx, *ty)
    //         }
    //         _ => {}
    //     }
    // }

    // #[verifier(external_body)]
    // #[verifier(broadcast_forall)]
    // pub proof fn axiom_eq_is_equal<A>(x: ITree<A, Endpoint>, y: ITree<A, Endpoint>)
    //     requires x =~~= y
    //     ensures  is_equal(x, y)
    // {}

    // pub proof fn bind_assoc<A,B,C>(f: ITree<A, Endpoint>, g: FnSpec(A) -> ITree<B, Endpoint>, h: FnSpec(B) -> ITree<C, Endpoint>)
    //     ensures f.bind(g).bind(h) =~~= f.bind(|x| g(x).bind(h))
    //     decreases f
    // {
    //     match f {
    //         ITree::Ret(b) => {},
    //         ITree::Input(ff) => {
    //             assert(f.bind(g).get_Input_0() =~~= (|x| ff(x).bind(g)));
    //             assert(ITree::Input(|x| ff(x).bind(g)).bind(h).get_Input_0() =~~= |y| ff(y).bind(g).bind(h));
    //             assert(f.bind(|x| g(x).bind(h)).get_Input_0() =~~= |y| ff(y).bind(|x| g(x).bind(h)));
    //             assert forall |y| #[trigger] trig(y) implies is_equal(ff(y).bind(g).bind(h), ff(y).bind(|x| g(x).bind(h))) by {
    //                 bind_assoc(ff(y), g, h)
    //             }
    //             assert(is_equal(ITree::Input(|y| ff(y).bind(g).bind(h)), ITree::Input(|y| ff(y).bind(|x| g(x).bind(h)))));
    //         },
    //         ITree::Output(o, t) => {
    //             bind_assoc(*t, g, h)
    //         }
    //     }
    // }


    #[verifier(external_body)]
    // #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_assoc<A,B,C, Endpoint>(f: ITree<A, Endpoint>, g: FnSpec(A) -> ITree<B, Endpoint>, h: FnSpec(B) -> ITree<C, Endpoint>)
        ensures (#[trigger] f.bind(g).bind(h)) =~~= f.bind(|x| g(x).bind(h))
    {}


    //////////////////////////////////////////////////////
    ///// Handling subroutine calls //////////////////////
    //////////////////////////////////////////////////////

    // Hack because I seem to be unable to return `FnSpec`s
    #[allow(dead_code)]
    type FnSpecAlias<A,B> = FnSpec(A) -> B;


    pub open spec fn itree_conts_match<A,B>(k: FnSpec(A) -> ITree<B, Endpoint>, kt: FnSpec(A) -> ITreeToken<B, Endpoint>) -> bool
    {
        forall |v: A| ((#[trigger] kt(v)).view() == k(v))
    }

    #[verifier(external_body)]
    pub proof fn split_bind<A,B>(tracked t: ITreeToken<A, Endpoint>, s: ITree<B, Endpoint>) -> (tracked st_kt: (Tracked<ITreeToken<B, Endpoint>>, Tracked<FnSpecAlias<B, ITreeToken<A, Endpoint>>>))
        requires exists |k| (t.view() == #[trigger] s.bind::<A>(k))
        ensures  forall |k| (t.view() == #[trigger] s.bind::<A>(k)) ==> ((st_kt.0).view().view() == s && itree_conts_match(k, (st_kt.1).view()))
    { unimplemented!() }

    #[verifier(external_body)]
    pub proof fn join_bind<A,B>(s: ITree<B, Endpoint>, tracked st: ITreeToken<B, Endpoint>, tracked kt: FnSpecAlias<B, ITreeToken<A, Endpoint>>, v: B) -> (tracked t: Tracked<ITreeToken<A, Endpoint>>)
        requires st.view().results_in(v),
        ensures  t.view() == kt(v)
    { unimplemented!() }

    #[allow(unused_macros)]
    #[macro_export]
    macro_rules! owl_call {
        [$($tail:tt)*] => {
            ::builtin_macros::verus_exec_macro_exprs!{
                owl_call_internal!(res, res.dview().as_seq(), $($tail)*)
            }
        };
    }

    #[allow(unused_macros)]
    #[macro_export]
    macro_rules! owl_call_ret_option {
        [$($tail:tt)*] => {
            ::builtin_macros::verus_exec_macro_exprs!{
                owl_call_internal!(res, option_as_seq(dview_option(res)), $($tail)*)
            }
        };
    }

    #[allow(unused_macros)]
    #[macro_export]
    macro_rules! owl_call_internal {
        // ($itree:ident, $mut_state:expr, $spec:ident ( $($specarg:expr),* ), $exec:ident ( $($execarg:expr),* ) ) => {
        //     ::builtin_macros::verus_exec_expr! {{
        //         let tracked (Tracked(call_token), Tracked(cont_token)) = split_bind($itree, $spec($($specarg),*));
        //         let (res, Tracked(call_token)) = $exec(Tracked(call_token), $($execarg),*);
        //         let tracked Tracked($itree) = join_bind($spec($($specarg),*), call_token, cont_token, (res.view(), $mut_state));
        //         (res, Tracked($itree))
        //     }}
        // };
        ($res: ident, $view_res:expr, $itree:ident, $mut_state:expr, $spec:ident ( $($specarg:expr),* ), $self:ident . $exec:ident ( $($execarg:expr),* ) ) => {
            ::builtin_macros::verus_exec_expr! {{
                reveal($spec);
                let tracked (Tracked(call_token), Tracked(cont_token)) = split_bind($itree, $spec($($specarg),*));
                let ($res, Tracked(call_token)) = match $self.$exec(Tracked(call_token), $($execarg),*) {
                    Err(e) => return Err(e),
                    Ok(r) => r,
                };
                let tracked Tracked($itree) = join_bind($spec($($specarg),*), call_token, cont_token, ($view_res, $mut_state));
                ($res, Tracked($itree))
            }}
        };
        ($($tt:tt)*) => {
            compile_error!(concat!($("`", stringify!($tt), "`, "),*))
        }
    }

    struct UnforgeableAux;

    #[allow(dead_code)]
    pub struct ITreeToken<T,Endpoint> {
        token: UnforgeableAux,
        inner: (T, Endpoint)
    }

    impl<T,Endpoint> ITreeToken<T,Endpoint> {
        pub closed spec fn view(self) -> ITree<T,Endpoint>;

        // Token constructor---this is only used to make the executable code typecheck.
        // Verified code can never call this function (since it requires false), so it
        // cannot forge tokens.
        // We only need to return a token of type (), since we will use the subroutine call
        // machinery to get the itree of the right type.
        #[verifier(external_body)]
        pub fn dummy_itree_token() -> ITreeToken<(), Endpoint>
            requires false
        { unimplemented!() }
    }



    //////////////////////////////////////////////////////
    ///// Parsing Owl code into an ITree /////////////////
    //////////////////////////////////////////////////////

    #[allow(unused_macros)]
    #[macro_export]
    macro_rules! owl_spec {
        ($mut_state:ident, $mut_type:ident, ($($tt:tt)*)) => { verus_proof_expr!{ owl_spec!($mut_state, $mut_type, $($tt)*) } };
        ($mut_state:ident, $mut_type:ident, {$($tt:tt)*}) => { verus_proof_expr!{ owl_spec!($mut_state, $mut_type, $($tt)*) } }; // NB: this one has curly braces {}, above has parens (), don't delete!
        ($mut_state:ident, $mut_type:ident, (input ($var:ident, $evar:ident)) in $($next:tt)*) => { verus_proof_expr!{
            (ITree::Input(|$var, $evar| {owl_spec!($mut_state, $mut_type, $($next)*)}))
        }};
        ($mut_state:ident, $mut_type:ident, (input ($var:ident, _)) in $($next:tt)*) => { verus_proof_expr!{
            (ITree::Input(|$var, _evar| {owl_spec!($mut_state, $mut_type, $($next)*)}))
        }};
        ($mut_state:ident, $mut_type:ident, (input (_, _)) in $($next:tt)*) => { verus_proof_expr!{
            (ITree::Input(|_var, _evar| {owl_spec!($mut_state, $mut_type, $($next)*)}))
        }};
        ($mut_state:ident, $mut_type:ident, (output ($($e:tt)*) to ($($endpoint:tt)*)) in $($next:tt)*) => { verus_proof_expr!{
            (ITree::Output(($($e)*), $($endpoint)*, Box::new(owl_spec!($mut_state, $mut_type, $($next)*))))
        }};
        // vvv check this
        ($mut_state:ident, $mut_type:ident, output ($($e:tt)*) to ($($endpoint:tt)*)) => { verus_proof_expr!{
            (ITree::Output(($($e)*), $($endpoint)*, Box::new(ITree::Ret(((), $mut_state)))))
        }};
        ($mut_state:ident, $mut_type:ident, sample($n:expr, $f:ident($($arg:expr),*))) => { verus_proof_expr!{
            (ITree::Sample($n, |coins| {owl_spec!($mut_state, $mut_type, (ret($f($($arg),*, coins))))}))
        }};
        ($mut_state:ident, $mut_type:ident, inc_counter($ctr:ident)) => { verus_exec_expr!{ // need `exec` so that + uses usize not nat
            ITree::Ret(((), $mut_type {$ctr: $mut_state.$ctr + 1usize, .. $mut_state}))
        }};
        // Special case handling of tail calls, which need an explicit `bind` to the identity function
        // in order to work with the spec of `split_bind`
        ($mut_state:ident, $mut_type:ident, call ($($e:tt)*)) => { verus_proof_expr!{
            ($($e)*)
                .bind( |tmp : (_, $mut_type)| ITree::Ret(tmp) )
        }};
        // special case handling of `enc_st_aead`, which needs to increment the nonce counter, and so is stateful
        ($mut_state:ident, $mut_type:ident, ret (enc_st_aead($k:expr, $x:expr, $nonce:ident, $aad:expr))) => { verus_proof_expr!{
            {
                let (c, new_nonce) = enc_st_aead($k, $x, $mut_state.$nonce, $aad);
                ITree::Ret((c, $mut_type {$nonce: new_nonce, .. $mut_state}))
            }
        }};
        ($mut_state:ident, $mut_type:ident, ret ($($e:tt)*)) => { verus_proof_expr!{
            ITree::Ret(($($e)*, $mut_state))
        }};
        ($mut_state:ident, $mut_type:ident, 
            parse ($parser:ident($a:ident)) as 
                ($structTy:ident { $($fieldName:ident : $varName:ident),* } ) 
            in { $($next:tt)* } otherwise ($($otw:tt)*)) => 
        {verus_proof_expr! {
            if let Some(parseval) = $parser($a) {
                let $structTy { $($fieldName),* } = parseval;
                $(let $varName = $fieldName.as_seq();)*
                owl_spec!($mut_state, $mut_type, $($next)*)
            } else {
                owl_spec!($mut_state, $mut_type, $($otw)*)
            }
        }};
        ($mut_state:ident, $mut_type:ident, 
            parse ($a:ident) as 
                ($structTy:ident { $($fieldName:ident : $varName:ident),* } ) 
            in { $($next:tt)* }) => 
        {verus_proof_expr! {{
            let $structTy { $($fieldName),* } = $a;
            $(let $varName = $fieldName.as_seq();)*
            owl_spec!($mut_state, $mut_type, $($next)*)
        }}};
        ($mut_state:ident, $mut_type:ident, 
            case ($parser:ident($a:ident)) { $(| $pattern:pat => { $($branch:tt)* },)* otherwise ($($otw:tt)*)}) => 
        { verus_proof_expr!{
            if let Some(parseval) = $parser($a.as_seq()) {
                match parseval {
                    $($pattern => { owl_spec!($mut_state, $mut_type, $($branch)*) })*
                }
            } else {
                owl_spec!($mut_state, $mut_type, $($otw)*)
            }
        }};
        ($mut_state:ident, $mut_type:ident, case ($e:expr) { $(| $pattern:pat => { $($branch:tt)* },)* }) => { verus_proof_expr!{
            match $e {
                $($pattern => { owl_spec!($mut_state, $mut_type, $($branch)*) })*
            }
        }};
        ($mut_state:ident, $mut_type:ident, if ($e:expr) then ( $($e1:tt)* ) else ( $($e2:tt)* )) => { verus_proof_expr!{
            if $e {
                owl_spec!($mut_state, $mut_type, $($e1)*)
            } else {
                owl_spec!($mut_state, $mut_type, $($e2)*)
            }
        }};
        // Special-case handling of `let _ = ...` pattern for RHS returning ()
        ($mut_state:ident, $mut_type:ident, let _ = (call($($e:tt)*)) in $($next:tt)*) => { verus_proof_expr!{
            ($($e)*)
                .bind( |tmp : ((), $mut_type)| { let (_, $mut_state) = tmp; owl_spec!($mut_state, $mut_type, $($next)*) })
        }};
        ($mut_state:ident, $mut_type:ident, let _ = ($($e:tt)*) in $($next:tt)*) => { verus_proof_expr!{
            owl_spec!($mut_state, $mut_type, $($e)* )
                .bind( |tmp : ((), $mut_type)| { let (_, $mut_state) = tmp; owl_spec!($mut_state, $mut_type, $($next)*) })
        }};
        ($mut_state:ident, $mut_type:ident, let $var:ident = (call($($e:tt)*)) in $($next:tt)*) => { verus_proof_expr!{
            ($($e)*)
                .bind( |tmp : (_, $mut_type)| { let ($var, $mut_state) = tmp; owl_spec!($mut_state, $mut_type, $($next)*) })
        }};
        ($mut_state:ident, $mut_type:ident, let $var:ident = ($($e:tt)*) in $($next:tt)*) => { verus_proof_expr!{
            owl_spec!($mut_state, $mut_type, $($e)* )
                .bind( |tmp : (_, $mut_type)| { let ($var, $mut_state) = tmp; owl_spec!($mut_state, $mut_type, $($next)*) })
        }};
        ($($tt:tt)*) => {
            compile_error!(concat!($("`", stringify!($tt), "`, "),*))
        }
    }
    pub(crate) use owl_spec;

    } // verus!
} // mod itree
