#![allow(unused_imports)]
#![allow(non_camel_case_types)]
pub use vstd::{modes::*, option::*, prelude::*, seq::*, vec::*, *};

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
        crate::Option::Some(x) => crate::Option::Some(x@),
        crate::Option::None    => crate::Option::None
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

// pub open spec fn get(x: Seq<u8>) -> Seq<u8>
// {
//     x
// }

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

    // Macro to parse pretty-printed Owl code into an ITree
    #[macro_export]
    macro_rules! owl_spec {
        ($cont:ident, ($($tt:tt)*)) => { owl_spec!($cont, $($tt)*) };
        ($cont:ident, {$($tt:tt)*}) => { owl_spec!($cont, $($tt)*) }; // NB: this one has curly braces {}, above has parens (), don't delete!
        ($cont:ident, (input ($var:ident, $evar:ident)) in $($next:tt)*) => {
            (ITree::Input(closure_to_fn_spec(|$var, $evar| {owl_spec!($cont, $($next)*)})))
        };
        ($cont:ident, (input ($var:ident, _)) in $($next:tt)*) => {
            (ITree::Input(closure_to_fn_spec(|$var, _evar| {owl_spec!($cont, $($next)*)})))
        };
        ($cont:ident, (input (_, _)) in $($next:tt)*) => {
            (ITree::Input(closure_to_fn_spec(|_var, _evar| {owl_spec!($cont, $($next)*)})))
        };
        ($cont:ident, (output ($($e:tt)*) to ($($endpoint:tt)*)) in $($next:tt)*) => {
            (ITree::Output($($e)*, $($endpoint)*, Box::new(owl_spec!($cont, $($next)*))))
        };
        // vvv check this
        ($cont:ident, output ($($e:tt)*) to ($($endpoint:tt)*)) => {
            (ITree::Output($($e)*, $($endpoint)*, Box::new($cont(()))))
        };
        ($cont:ident, (sample($n:expr, $f:ident($($arg:expr),*), $var:ident)) in $($next:tt)*) => {
            (ITree::Sample($n, closure_to_fn_spec(|coins| {owl_spec!($cont, let $var = (ret($f($($arg),*, coins))) in $($next)*)})))
        };
        ($cont:ident, ret ($($e:tt)*)) => {
            $cont($($e)*)
        };
        ($cont:ident, case ($e:expr) { $( $pattern:pat => { $($branch:tt)* },)* }) => {
            match $e {
                $($pattern => { owl_spec!($cont, $($branch)*) })*
            }
        };
        ($cont:ident, if ($e:expr) then ( $($e1:tt)* ) else ( $($e2:tt)* )) => {
            if $e {
                owl_spec!($cont, $($e1)*)
            } else {
                owl_spec!($cont, $($e2)*)
            }
        };
        ($cont:ident, let _ = ($($e:tt)*) in $($next:tt)+) => {
            owl_spec!($cont, ($($e)*) in $($next)+)
        };
        ($cont:ident, let $var:ident = ($($e:tt)*) in $($next:tt)+) => {
            // Re-merge the trailing tt* into a single tt
            owl_spec!($cont, @@internal merged_let $var = ($($e)*) in { $($next)+ })
        };
        ($cont:ident, let $var:ident = { ($($e:tt)*) in $($next:tt)* }) => {
            // Re-merge the trailing tt* into a single tt
            // Duplicated to descend under { } added by previous rules
            owl_spec!($cont, @@internal merged_let $var = ($($e)*) in { $($next)* })
        };
        ($cont:ident, @@internal merged_let $var:ident = (ret $($e:tt)*) in $next:tt) => {
            { let $var = $($e)*; owl_spec!($cont, $next) }
        };
        ($cont:ident, @@internal pushed_let $var:ident = (ret ($e:expr)) in $next:tt) => {
            { let $var = $e; owl_spec!($cont, $next) }
        };
        ($cont:ident, @@internal merged_let $var:ident = (input ($($e:tt)*)) in $next:tt) => {
            owl_spec!($cont, (input ($($e)*)) in let $var = $next)
        };
        ($cont:ident, @@internal merged_let $var:ident = (output ($($e:tt)*) to ($($endpoint:tt)*)) in $next:tt) => {
            owl_spec!($cont, (output ($($e)*) to ($($endpoint)*)) in let $var = $next)
        };
        ($cont:ident, @@internal merged_let $var:ident = (sample($n:expr, $f:ident($($arg:expr),*), $cvar:ident)) in $next:tt) => {
            owl_spec!($cont, (sample($n, $f($($arg),*), $cvar)) in let $var = $next)
        };
        ($cont:ident, @@internal merged_let $var:ident = (case ($e:expr) { $( $pattern:pat => { $($branch:tt)* },)* }) in $next:tt) => {
            match $e {
                $($pattern => {
                    owl_spec!($cont, @@internal pushed_let $var = ($($branch)*) in $next)
                })*
            }
        };
        ($cont:ident, @@internal merged_let $var:ident = (if ($e:expr) then ( $($e1:tt)* ) else ( $($e2:tt)* )) in $next:tt) => {
            if $e {
                owl_spec!($cont, @@internal pushed_let $var = ($($e1)*) in $next)
            } else {
                owl_spec!($cont, @@internal pushed_let $var = ($($e2)*) in $next)
            }
        };
        // (@@internal pushed_let $var:ident = ($e:expr) in $($next:tt)+) => {
        //     {
        //         owl_spec!($cont, let $var = $($e)*); owl_spec!($cont, $($next)+)
        //     }
        // };
        ($cont:ident, @@internal pushed_let $var:ident = ($($e:tt)*) in $($next:tt)+) => {
            {
                owl_spec!($cont, let $var = $($e)* in $($next)+)
            }
        };
        ($cont:ident, $($tt:tt)*) => {
            compile_error!(concat!($("`", stringify!($tt), "`, "),*))
        }
    }
    pub(crate) use owl_spec;

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
    }


    struct UnforgeableAux;

    pub struct ITreeToken<T,Endpoint> {
        token: UnforgeableAux,
        inner: (T, Endpoint)
    }

    impl<T,Endpoint> ITreeToken<T,Endpoint> {
        pub closed spec fn view(self) -> ITree<T,Endpoint>;
    }

    } // verus!
} // mod itree

fn main() {}
