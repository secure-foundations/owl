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

// hack
#[verifier(external_body)]
pub closed spec fn spec_foo() -> Seq<u8>
{
    todo!()
}

#[is_variant]
#[derive(Copy, Clone)]
pub enum Endpoint {
    Loc_alice,
    Loc_bob,
}

#[is_variant]
pub enum Message {
    Input(Seq<u8>),
    Output(Seq<u8>, Endpoint),
}

pub type Trace = Seq<Message>;

// crypto
// pub const KEY_SIZE: usize = 32;
// pub const TAG_SIZE: usize = 12;
// pub const KEY_TAG_SIZE: usize = KEY_SIZE + TAG_SIZE;

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

pub open spec(checked) fn enc(k: Option<Seq<u8>>, x: Option<Seq<u8>>, coins: Seq<u8>) -> (c: Option<Seq<u8>>)
{
    match (k, x) {
        (Some(k), Some(x)) =>
            if (k.len() == crate::KEY_SIZE && coins.len() == crate::TAG_SIZE) {
                Some(evercrypt_spec_of_enc(k, x, coins))
            } else {
                Some(seq![])
            }
        _ => None
    }
}

// #[macro_export]
// macro_rules! enc {
//     ($($tt:tt)*) => {
//         enc($($tt)*)
//     }
// }

// 0
#[verifier(external_body)]
pub closed spec(checked) fn evercrypt_spec_of_dec(k: Seq<u8>, c: Seq<u8>) -> Option<Seq<u8>>
    recommends k.len() == crate::KEY_SIZE,
{
    todo!()
}

pub open spec(checked) fn dec(k: Option<Seq<u8>>, c: Option<Seq<u8>>) -> (x: Option<Option<Seq<u8>>>)
{
    match (k, c) {
        (Some(k), Some(c)) =>
            if (k.len() == crate::KEY_SIZE) {
                Some(evercrypt_spec_of_dec(k, c))
            } else {
                Some(None)
            }
        _ => None
    }
}

// #[macro_export]
// macro_rules! dec {
//     ($($tt:tt)*) => {
//         dec($($tt)*)
//     }
// }

// #[verifier(external_body)]
// pub exec fn dec_impl(k: &Vec<u8>, c: &Vec<u8>) -> (x: Option<Vec<u8>>)
//     ensures
//         (k.len() == crate::KEY_SIZE && dec(k@, c@).is_Some()) ==> x.is_Some() && x.get_Some_0()@ === dec(k@, c@).get_Some_0(),
//         dec(k@, c@).is_None() ==> x.is_None(),
//         k.len() != crate::KEY_SIZE ==> x.is_None(),
// {
//     todo!() // call evercrypt
// }

pub open spec fn eq(a: Seq<u8>, b: Seq<u8>) -> bool
{
    a == b
}

pub open spec fn get(x: Seq<u8>) -> Option<Seq<u8>>
{
    Some(x)
}

pub open spec fn UNIT() -> Option<()>
{
    Some(())
}


// #[macro_export]
// macro_rules! UNIT {
//     ($($tt:tt)*) => {
//         ($($tt)*)
//     }
// }

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
    pub enum ITree<A> {
        Input  (FnSpec(Option<Seq<u8>>, Endpoint) -> ITree<A>),
        Output (Option<Seq<u8>>, Endpoint, Box<ITree<A>>),
        Sample (usize, FnSpec(Seq<u8>) -> ITree<A>),
        Ret    (A),
    }

    // Macro to parse pretty-printed Owl code into an ITree
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
        // ((output ($($e:tt)*)) in $($next:tt)*) => {
        //     (ITree::Output($($e)*, Box::new(owl_spec!($($next)*))))
        // };
        ((output ($($e:tt)*) to ($($endpoint:tt)*)) in $($next:tt)*) => {
            (ITree::Output($($e)*, $($endpoint)*, Box::new(owl_spec!($($next)*))))
        };
        // vvv check this
        (output ($($e:tt)*) to ($($endpoint:tt)*)) => {
            (ITree::Output($($e)*, $($endpoint)*, Box::new(ITree::Ret(Some(())))))
        };
        ((sample($n:expr, $f:ident($($arg:expr),*), $var:ident)) in $($next:tt)*) => {
            (ITree::Sample($n, closure_to_fn_spec(|coins| {owl_spec!(let $var = (ret($f($($arg),*, coins))) in $($next)*)})))
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
        (let _ = ($($e:tt)*) in $($next:tt)+) => {
            owl_spec!(($($e)*) in $($next)+)
        };
        (let $var:ident = ($($e:tt)*) in $($next:tt)+) => {
            // Re-merge the trailing tt* into a single tt
            owl_spec!(@@internal merged_let $var = ($($e)*) in { $($next)+ })
        };
        (let $var:ident = { ($($e:tt)*) in $($next:tt)* }) => {
            // Re-merge the trailing tt* into a single tt
            // Duplicated to descend under { } added by previous rules
            owl_spec!(@@internal merged_let $var = ($($e)*) in { $($next)* })
        };
        (@@internal merged_let $var:ident = (ret $($e:tt)*) in $next:tt) => {
            { let $var = $($e)*; owl_spec!($next) }
        };
        (@@internal pushed_let $var:ident = (ret ($e:expr)) in $next:tt) => {
            { let $var = $e; owl_spec!($next) }
        };
        (@@internal merged_let $var:ident = (input ($($e:tt)*)) in $next:tt) => {
            owl_spec!((input ($($e)*)) in let $var = $next)
        };
        (@@internal merged_let $var:ident = (output ($($e:tt)*) to ($($endpoint:tt)*)) in $next:tt) => {
            owl_spec!((output ($($e)*) to ($($endpoint)*)) in let $var = $next)
        };
        (@@internal merged_let $var:ident = (sample($n:expr, $f:ident($($arg:expr),*), $cvar:ident)) in $next:tt) => {
            owl_spec!((sample($n, $f($($arg),*), $cvar)) in let $var = $next)
        };
        (@@internal merged_let $var:ident = (case ($e:expr) { $( $pattern:pat => { $($branch:tt)* },)* }) in $next:tt) => {
            match $e {
                $($pattern => {
                    owl_spec!(@@internal pushed_let $var = ($($branch)*) in $next)
                })*
            }
        };
        (@@internal merged_let $var:ident = (if ($e:expr) then ( $($e1:tt)* ) else ( $($e2:tt)* )) in $next:tt) => {
            if $e {
                owl_spec!(@@internal pushed_let $var = ($($e1)*) in $next)
            } else {
                owl_spec!(@@internal pushed_let $var = ($($e2)*) in $next)
            }
        };
        // (@@internal pushed_let $var:ident = ($e:expr) in $($next:tt)+) => {
        //     {
        //         owl_spec!(let $var = $($e)*); owl_spec!($($next)+)
        //     }
        // };
        (@@internal pushed_let $var:ident = ($($e:tt)*) in $($next:tt)+) => {
            {
                owl_spec!(let $var = $($e)* in $($next)+)
            }
        };
        ($($tt:tt)*) => {
            compile_error!(concat!($("`", stringify!($tt), "`, "),*))
        }
    }
    pub(crate) use owl_spec;

    impl<A> ITree<A> {
        pub open spec fn is_input(&self) -> bool {
            self.is_Input()
        }
        pub open spec(checked) fn take_input(&self, i: Seq<u8>, ev: Endpoint) -> ITree<A>
            recommends self.is_input()
        {
            (self.get_Input_0())(Some(i), ev)
        }
        pub open spec fn is_output(&self, o: Seq<u8>) -> bool {
            self.is_Output() && self.get_Output_0() === Some(o)
        }
        pub open spec(checked) fn give_output(&self) -> ITree<A>
            recommends (exists |o| self.is_output(o))
        {
            *self.get_Output_2()
        }
        pub open spec fn is_sample(&self, n: usize) -> bool {
            self.is_Sample() && self.get_Sample_0() === n
        }
        pub open spec(checked) fn get_sample(&self, coins: Seq<u8>) -> ITree<A>
            recommends (exists |n| self.is_sample(n))
        {
            (self.get_Sample_1())(coins)
        }
        pub open spec(checked) fn results_in(&self, a: A) -> bool {
            self.is_Ret() && self.get_Ret_0() === a
        }
    }


    struct UnforgeableAux;

    pub struct ITreeToken<T> {
        token: UnforgeableAux,
        inner: T // just to satisfy rustc
    }

    impl<T> ITreeToken<T> {
        pub closed spec fn view(self) -> ITree<T>;
    }

    } // verus!
} // mod itree

////////////////////////////////////////////////////////////////////////////////
///////////////////// IMPLS OF INPUT/OUTPUT/SAMPLE /////////////////////////////
////////////////////////////////////////////////////////////////////////////////

verus! {
use itree::*;

#[verifier(external_body)]
pub exec fn input<A>(t: &mut Tracked<ITreeToken<A>>) -> (ie: (Vec<u8>, Endpoint))
    requires old(t)@@.is_input()
    ensures  t@@ === old(t)@@.take_input(ie.0@, ie.1)
{
    todo!()
}

#[verifier(external_body)]
pub exec fn output<A>(o: &Vec<u8>, t: &mut Tracked<ITreeToken<A>>)
    requires old(t)@@.is_output(o@)
    ensures  t@@ === old(t)@@.give_output()
{
    todo!()
}

#[verifier(external_body)]
pub exec fn sample<A>(n: usize, t: &mut Tracked<ITreeToken<A>>) -> (res: Vec<u8>)
    requires old(t)@@.is_sample(n)
    ensures t@@ === old(t)@@.get_sample(res@)
{
    todo!()
}

} // verus!

fn main() {}
