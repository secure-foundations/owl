#![allow(unused_imports)]
#![allow(non_camel_case_types)]
pub use vstd::{modes::*, prelude::*, seq::*, *};

////////////////////////////////////////////////////////////////////////////////
///////////////////// CRYPTO ETC LIBRARY ///////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
verus! {

// Macro version of the stdlib's Option::and
#[macro_export]
macro_rules! option_and {
    ($id:ident, $($tt:tt)*) => {
        match $id {
            Some($id) => { $($tt)* },
            None => None
        }
    }
}

pub open spec fn options_match(s: Option<Seq<u8>>, v: Option<Vec<u8>>) -> bool
{
    (v.is_None() && s.is_None()) ||
    (v.is_Some() && s.is_Some() && v.get_Some_0()@ === s.get_Some_0())
}

pub open spec fn view_option(v: Option<Vec<u8>>) -> Option<Seq<u8>>
{
    match v {
        Option::Some(x) => Option::Some(x@),
        Option::None    => Option::None
    }
}

// pub closed spec fn cipherlen(l : nat) -> nat {
//     l + crate::TAG_SIZE as nat
// }

#[verifier(external_body)]
pub closed spec(checked) fn evercrypt_spec_of_enc(k: Seq<u8>, x: Seq<u8>, coins: Seq<u8>) -> Seq<u8>
    recommends k.len() == crate::KEY_SIZE,
               coins.len() == crate::TAG_SIZE
{
    todo!()
}

pub open spec(checked) fn enc(k: Seq<u8>, x: Seq<u8>, coins: Seq<u8>) -> (c: Seq<u8>)
{
    // match (k, c) {
    //     (Some(k), Some(c)) =>
            if (k.len() == crate::KEY_SIZE && coins.len() == crate::TAG_SIZE) {
                evercrypt_spec_of_enc(k, x, coins)
            } else {
                seq![]
            }
    //     _ => None
    // }
}


#[verifier(external_body)]
pub closed spec(checked) fn evercrypt_spec_of_dec(k: Seq<u8>, c: Seq<u8>) -> Option<Seq<u8>>
    recommends k.len() == crate::KEY_SIZE,
{
    todo!()
}

pub open spec(checked) fn dec(k: Seq<u8>, c: Seq<u8>) -> (x: Option<Seq<u8>>)
{
    // match (k, c) {
    //     (Some(k), Some(c)) =>
            if (k.len() == crate::KEY_SIZE) {
                evercrypt_spec_of_dec(k, c)
            } else {
                None
            }
    //     _ => None
    // }
}

pub open spec fn eq(a: Seq<u8>, b: Seq<u8>) -> bool
{
    a == b
}

pub open spec fn UNIT()
{
    ()
}


pub open spec fn andb(x: bool, y: bool) -> bool
{
    x && y
}

pub open spec fn length(x: Seq<u8>) -> nat
{
    x.len()
}


}

////////////////////////////////////////////////////////////////////////////////
///////////////////// ITREE DEFINITION /////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

pub mod itree {
    use crate::*;
    use vstd::{modes::*, option::*, prelude::*, seq::*, vec::*, *};

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
            self.is_Output() && self.get_Output_0() === o && self.get_Output_1() === ev
        }
        pub open spec(checked) fn give_output(&self) -> ITree<A,Endpoint>
            recommends (exists |o, ev| self.is_output(o, ev))
        {
            *self.get_Output_2()
        }
        pub open spec fn is_sample(&self, n: usize) -> bool {
            self.is_Sample() && self.get_Sample_0() === n
        }
        pub open spec(checked) fn get_sample(&self, coins: Seq<u8>) -> ITree<A,Endpoint>
            recommends (exists |n| self.is_sample(n))
        {
            (self.get_Sample_1())(coins)
        }
        pub open spec(checked) fn results_in(&self, a: A) -> bool {
            self.is_Ret() && self.get_Ret_0() === a
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
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_assoc<A,B,C, Endpoint>(f: ITree<A, Endpoint>, g: FnSpec(A) -> ITree<B, Endpoint>, h: FnSpec(B) -> ITree<C, Endpoint>)
        ensures (#[trigger] f.bind(g).bind(h)) =~~= f.bind(|x| g(x).bind(h))
    {}


    //////////////////////////////////////////////////////
    ///// Handling subroutine calls //////////////////////
    //////////////////////////////////////////////////////

    // Hack because I seem to be unable to return `FnSpec`s
    type FnSpecAlias<A,B> = FnSpec(A) -> B;


    pub open spec fn itree_conts_match<A,B>(k: FnSpec(A) -> ITree<B, Endpoint>, kt: FnSpec(A) -> ITreeToken<B, Endpoint>) -> bool
    {
        forall |v: A| ((#[trigger] kt(v))@ == k(v))
    }

    #[verifier(external_body)]
    pub proof fn split_bind<A,B>(tracked t: ITreeToken<A, Endpoint>, s: ITree<B, Endpoint>) -> (tracked st_kt: (Tracked<ITreeToken<B, Endpoint>>, Tracked<FnSpecAlias<B, ITreeToken<A, Endpoint>>>))
        requires exists |k| (t@ == #[trigger] s.bind::<A>(k))
        ensures  forall |k| (t@ == #[trigger] s.bind::<A>(k)) ==> ((st_kt.0)@@ == s && itree_conts_match(k, (st_kt.1)@))
    { unimplemented!() }

    #[verifier(external_body)]
    pub proof fn join_bind<A,B>(s: ITree<B, Endpoint>, tracked st: ITreeToken<B, Endpoint>, tracked kt: FnSpecAlias<B, ITreeToken<A, Endpoint>>, v: B) -> (tracked t: Tracked<ITreeToken<A, Endpoint>>)
        requires st@.results_in(v),
        ensures  t@ == kt(v)
    { unimplemented!() }

    #[allow(unused_macros)]
    #[macro_export]
    macro_rules! owl_call {
        [$($tail:tt)*] => {
            ::builtin_macros::verus_exec_macro_exprs!{
                owl_call_internal!($($tail)*)
            }
        };
    }

    #[allow(unused_macros)]
    macro_rules! owl_call_internal {
        ($itree:ident, $spec:ident ( $($specarg:expr),* ), $exec:ident ( $($execarg:expr),* ) ) => {
            ::builtin_macros::verus_exec_expr! {{
                let tracked (Tracked(call_token), Tracked(cont_token)) = split_bind($itree, $spec($($specarg),*));
                let (res, Tracked(call_token)) = $exec(Tracked(call_token), $($execarg),*);
                let tracked Tracked($itree) = join_bind($spec($($specarg),*), call_token, cont_token, res@);
                (res, Tracked($itree))
            }}
        };
        ($($tt:tt)*) => {
            compile_error!(concat!($("`", stringify!($tt), "`, "),*))
        }
    }

    struct UnforgeableAux;

    pub struct ITreeToken<T,Endpoint> {
        token: UnforgeableAux,
        inner: (T, Endpoint)
    }

    impl<T,Endpoint> ITreeToken<T,Endpoint> {
        pub closed spec fn view(self) -> ITree<T,Endpoint>;
    }



    //////////////////////////////////////////////////////
    ///// Parsing Owl code into an ITree /////////////////
    //////////////////////////////////////////////////////

    #[macro_export]
    macro_rules! owl_spec {
        (($($tt:tt)*)) => { owl_spec!($($tt)*) };
        ({$($tt:tt)*}) => { owl_spec!($($tt)*) }; // NB: this one has curly braces {}, above has parens (), don't delete!
        ((input ($var:ident, $evar:ident)) in $($next:tt)*) => {
            (ITree::Input(closure_to_fn_spec(|$var, $evar| {owl_spec!($($next)*)})))
        };
        ((input ($var:ident, _)) in $($next:tt)*) => {
            (ITree::Input(closure_to_fn_spec(|$var, _evar| {owl_spec!($($next)*)})))
        };
        ((input (_, _)) in $($next:tt)*) => {
            (ITree::Input(closure_to_fn_spec(|_var, _evar| {owl_spec!($($next)*)})))
        };
        ((output ($($e:tt)*) to ($($endpoint:tt)*)) in $($next:tt)*) => {
            (ITree::Output($($e)*, $($endpoint)*, Box::new(owl_spec!($($next)*))))
        };
        // vvv check this
        (output ($($e:tt)*) to ($($endpoint:tt)*)) => {
            (ITree::Output($($e)*, $($endpoint)*, Box::new(ITree::Ret(()))))
        };
        (sample($n:expr, $f:ident($($arg:expr),*))) => {
            (ITree::Sample($n, closure_to_fn_spec(|coins| {owl_spec!((ret($f($($arg),*, coins))))})))
        };
        (ret ($($e:tt)*)) => {
            ITree::Ret($($e)*)
        };
        (case ($e:expr) { $( $pattern:pat => { $($branch:tt)* },)* }) => {
            match $e {
                $($pattern => { owl_spec!($($branch)*) })*
            }
        };
        (if ($e:expr) then ( $($e1:tt)* ) else ( $($e2:tt)* )) => {
            if $e {
                owl_spec!($($e1)*)
            } else {
                owl_spec!($($e2)*)
            }
        };
        (let _ = ($($e:tt)*) in $($next:tt)*) => {
            owl_spec!( $($e)* )
                .bind( closure_to_fn_spec(|_var| owl_spec!($($next)*) ))
        };
        (let $var:ident = ($($e:tt)*) in $($next:tt)*) => {
            // owl_spec!(@@internal merged_let $var = ($($e)*) in { $($next)+ })
            owl_spec!( $($e)* )
                .bind( closure_to_fn_spec(|$var| owl_spec!($($next)*) ))
        };
        // (($($e:tt)*) in $($next:tt)*) => {
        //     // owl_spec!(@@internal merged_let $var = ($($e)*) in { $($next)+ })
        //     owl_spec!( $($e)* )
        //         .bind( closure_to_fn_spec(|_var| owl_spec!($($next)*) ))
        // };
        // (let $var:ident = { ($($e:tt)*) in $($next:tt)* }) => {
        //     // Re-merge the trailing tt* into a single tt
        //     // Duplicated to descend under { } added by previous rules
        //     owl_spec!(@@internal merged_let $var = ($($e)*) in { $($next)* })
        // };
        // (@@internal merged_let $var:ident = (ret $($e:tt)*) in $next:tt) => {
        //     { let $var = $($e)*; owl_spec!($next) }
        // };
        // (@@internal pushed_let $var:ident = (ret ($e:expr)) in $next:tt) => {
        //     { let $var = $e; owl_spec!($next) }
        // };
        // (@@internal merged_let $var:ident = (input ($($e:tt)*)) in $next:tt) => {
        //     owl_spec!((input ($($e)*)) in let $var = $next)
        // };
        // (@@internal merged_let $var:ident = (output ($($e:tt)*) to ($($endpoint:tt)*)) in $next:tt) => {
        //     owl_spec!((output ($($e)*) to ($($endpoint)*)) in let $var = $next)
        // };
        // (@@internal merged_let $var:ident = (sample($n:expr, $f:ident($($arg:expr),*), $cvar:ident)) in $next:tt) => {
        //     owl_spec!((sample($n, $f($($arg),*), $cvar)) in let $var = $next)
        // };
        // (@@internal merged_let $var:ident = (case ($e:expr) { $( $pattern:pat => { $($branch:tt)* },)* }) in $next:tt) => {
        //     match $e {
        //         $($pattern => {
        //             owl_spec!(@@internal pushed_let $var = ($($branch)*) in $next)
        //         })*
        //     }
        // };
        // (@@internal merged_let $var:ident = (if ($e:expr) then ( $($e1:tt)* ) else ( $($e2:tt)* )) in $next:tt) => {
        //     if $e {
        //         owl_spec!(@@internal pushed_let $var = ($($e1)*) in $next)
        //     } else {
        //         owl_spec!(@@internal pushed_let $var = ($($e2)*) in $next)
        //     }
        // };
        // // (@@internal pushed_let $var:ident = ($e:expr) in $($next:tt)+) => {
        // //     {
        // //         owl_spec!(let $var = $($e)*); owl_spec!($($next)+)
        // //     }
        // // };
        // (@@internal pushed_let $var:ident = ($($e:tt)*) in $($next:tt)+) => {
        //     {
        //         owl_spec!(let $var = $($e)* in $($next)+)
        //     }
        // };
        ($($tt:tt)*) => {
            compile_error!(concat!($("`", stringify!($tt), "`, "),*))
        }
    }
    pub(crate) use owl_spec;

    } // verus!
} // mod itree

////////////////////////////////////////////////////////////////////////////////
///////////////////// FOR TESTING ONLY /////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

verus! {
use crate::itree::*;

// #[verifier(external_body)]
// pub exec fn input<A>(Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>) -> (i: Vec<u8>)
//     requires old(t)@.is_input()
//     ensures  t@ == old(t)@.take_input(i@)
// {
//     todo!()
// }

// #[verifier(external_body)]
// pub exec fn output<A>(o: &Vec<u8>, Tracked(t): Tracked<&mut ITreeToken<A, Endpoint>>)
//     requires old(t)@.is_output(o@)
//     ensures  t@ == old(t)@.give_output()
// {
//     todo!()
// }


// Clones a Vec<u8> (because currently Verus doesn't support this natively)
#[verifier(external_body)]
pub exec fn clone_vec_u8(v: &Vec<u8>) -> (res: Vec<u8>)
    ensures v@ == res@
{
    todo!() // Vec { vec: v.vec.clone() }
}


// pub closed spec fn foo(x: Seq<u8>) -> Seq<u8>;


// #[verifier(external_body)]
// pub exec fn enc_impl(k: &Vec<u8>, x: &Vec<u8>) -> (c: Vec<u8>)
//     ensures c@ == enc(k@, x@)
// { unimplemented!() }

// #[verifier(external_body)]
// pub exec fn dec_impl(k: &Vec<u8>, c: &Vec<u8>) -> (x: Option<Vec<u8>>)
//     ensures options_match(dec(k@, c@), x)
// { unimplemented!() }

// #[verifier(external_body)]
// pub exec fn foo_impl(x: &Vec<u8>) -> (y: Vec<u8>)
//     ensures y@ == foo(x@)
// { unimplemented!() }


// pub open spec fn test(k: Seq<u8>) -> ITree<Seq<u8>, Endpoint> {
//     /*
//         input x in
//         let y = enc(k, x) in
//         foo(x)
//      */

//     owl_spec! (
//         (input (i7, ev6)) in
//         let caseval78 = (ret (dec(((*loc.owl_Top_shared_key).view(), i7)))) in
//         (case (caseval78)
//         {Some (k8) => {let foo9 = (ret (Top_t( (*loc.owl_Top_x).view()
//         , (*loc.owl_Top_y).view() ))) in
//         let c10 = (ret (enc((k8, foo9)))) in
//         (output (c10) to (ev6))},
//         None => {(ret (Top_UNIT()))},})
//     )
// }

// pub exec fn alice_subroutine_impl(Tracked(itree): Tracked<ITreeToken<Seq<u8>, Endpoint>>, k: &Vec<u8>) -> (res: (Vec<u8>, Tracked<ITreeToken<Seq<u8>, Endpoint>>))
//     requires itree@ == alice_subroutine(k@)
//     ensures  (res.1)@@.results_in(res.0@)
// {
//     let tracked mut itree = itree;
//     let x = input::<Seq<u8>>(Tracked(&mut itree));
//     let y = enc_impl(&k, &x);
//     (foo_impl(&y), Tracked(itree))
// }


}
