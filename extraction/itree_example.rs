#![allow(unused_imports)]
#![allow(non_camel_case_types)]
pub use vstd::{modes::*, prelude::*, seq::*, *};

pub mod itree {
    use crate::*;
    use vstd::prelude::*;

    verus! {

    #[is_variant]
    #[verifier::ext_equal]
    pub enum ITree<A> {  
        Input  (FnSpec(Seq<u8>) -> ITree<A>),
        Output (Seq<u8>, Box<ITree<A>>),
        Ret    (A),
    }

    impl<A> ITree<A> {
        pub open spec fn bind<B>(&self, next: FnSpec(A) -> ITree<B>) -> ITree<B>
            decreases self
        {  
            match self {
                ITree::Input(k) => {
                    ITree::Input(|x| (k(x)).bind(next))
                },
                ITree::Output(o, t) => {
                    ITree::Output(*o, Box::new((*t).bind(next)))
                },
                ITree::Ret(a) => { 
                    next(*a) 
                }
            }            
        }

        pub open spec fn is_input(&self) -> bool {
            self.is_Input()
            // exists |k| is_equal(*self, ITree::Input(k))
        }
        pub open spec(checked) fn take_input(&self, i: Seq<u8>) -> ITree<A>
            recommends self.is_input()
        {
            (self.get_Input_0())(i)
        }
        pub open spec fn is_output(&self, o: Seq<u8>) -> bool {
            self.is_Output() && self.get_Output_0() == o
            // exists |t| *self =~~= ITree::Output(o, t)
        }
        pub open spec(checked) fn give_output(&self) -> ITree<A>
            recommends (exists |o| self.is_output(o))
        {
            *self.get_Output_1()
        }
        pub open spec(checked) fn results_in(&self, a: A) -> bool {
            self.is_Ret() && self.get_Ret_0() == a
        }
    }

    pub proof fn axiom_bind_ret_proof<A, B>(x: A, k : FnSpec(A) -> ITree<B>)
    ensures
        (#[trigger] ITree::Ret(x).bind(k)) == k(x)
    { }

    pub proof fn axiom_bind_input_proof<A, B>(f : FnSpec(Seq<u8>) -> ITree<A>, k: FnSpec(A) -> ITree<B>)
        ensures
            (#[trigger] ITree::Input(f).bind(k)) == ITree::Input(|x| f(x).bind(k))
    { }

    pub proof fn axiom_bind_output_proof<A, B>(x : Seq<u8>, f : Box<ITree<A>>, k : FnSpec(A) -> ITree<B>)
        ensures
            (#[trigger] ITree::Output(x, f).bind(k)) == ITree::Output(x, Box::new((*f).bind(k)))
    { }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_ret<A, B>(x: A, k : FnSpec(A) -> ITree<B>)
        ensures
            (#[trigger] ITree::Ret(x).bind(k)) == k(x)
    { }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_input<A, B>(f : FnSpec(Seq<u8>) -> ITree<A>, k: FnSpec(A) -> ITree<B>)
        ensures
            (#[trigger] ITree::Input(f).bind(k)) == ITree::Input(|x| f(x).bind(k))
    { }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_output<A, B>(x : Seq<u8>, f : Box<ITree<A>>, k : FnSpec(A) -> ITree<B>)
        ensures
            (#[trigger] ITree::Output(x, f).bind(k)) == ITree::Output(x, Box::new((*f).bind(k)))
    { }

    // triggering hack
    pub open spec fn trig<A>(x: A) -> bool { true }

    pub open spec fn is_equal<A>(x : ITree<A>, y : ITree<A>) -> bool 
        decreases x, y
    { 
        match (x, y) {
            (ITree::Ret(a), ITree::Ret(b)) => x == y,
            (ITree::Input(kx), ITree::Input(ky)) => forall|v| #[trigger] trig(v) ==> is_equal(kx(v), ky(v)),
            (ITree::Output(ox, tx), ITree::Output(oy, ty)) => ox == oy && is_equal(*tx, *ty),
            (_, _) => false,
        }
    }

    pub proof fn is_equal_eq<A>(x: ITree<A>, y: ITree<A>)
        requires is_equal(x, y)
        ensures  x =~~= y
        decreases x, y
    {
        match (x, y) {
            (ITree::Input(ff), ITree::Input(gg)) => {
                assert forall|v| #[trigger] ff(v) =~= gg(v) by {
                    assert(trig(v));
                    is_equal_eq(ff(v), gg(v))
                }
                assert (ff =~~= gg);
            },
            (ITree::Output(ox, tx), ITree::Output(oy, ty)) => {
                is_equal_eq(*tx, *ty)
            }
            _ => {}
        }
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_is_equal_eq<A>(x: ITree<A>, y: ITree<A>)
        requires is_equal(x, y)
        ensures  x =~~= y
    {}
    
    pub proof fn eq_is_equal<A>(x: ITree<A>, y: ITree<A>)
        requires x =~~= y
        ensures  is_equal(x, y)
        decreases x, y
    {
        match (x, y) {
            (ITree::Input(ff), ITree::Input(gg)) => {
                assert forall|v| #[trigger] trig(v) implies is_equal(ff(v), gg(v)) by {
                    eq_is_equal(ff(v), gg(v))
                }
            },
            (ITree::Output(ox, tx), ITree::Output(oy, ty)) => {
                eq_is_equal(*tx, *ty)
            }
            _ => {}
        }
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_eq_is_equal<A>(x: ITree<A>, y: ITree<A>)
        requires x =~~= y
        ensures  is_equal(x, y)
    {}

    pub proof fn bind_assoc<A,B,C>(f: ITree<A>, g: FnSpec(A) -> ITree<B>, h: FnSpec(B) -> ITree<C>)
        ensures f.bind(g).bind(h) =~~= f.bind(|x| g(x).bind(h))
        decreases f
    {
        match f {
            ITree::Ret(b) => {},
            ITree::Input(ff) => {
                assert(f.bind(g).get_Input_0() =~~= (|x| ff(x).bind(g)));
                assert(ITree::Input(|x| ff(x).bind(g)).bind(h).get_Input_0() =~~= |y| ff(y).bind(g).bind(h));
                assert(f.bind(|x| g(x).bind(h)).get_Input_0() =~~= |y| ff(y).bind(|x| g(x).bind(h)));
                assert forall |y| #[trigger] trig(y) implies is_equal(ff(y).bind(g).bind(h), ff(y).bind(|x| g(x).bind(h))) by {
                    bind_assoc(ff(y), g, h)
                }
                assert(is_equal(ITree::Input(|y| ff(y).bind(g).bind(h)), ITree::Input(|y| ff(y).bind(|x| g(x).bind(h)))));
            },
            ITree::Output(o, t) => {
                bind_assoc(*t, g, h)
            }
        }
    }


    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_assoc<A,B,C>(f: ITree<A>, g: FnSpec(A) -> ITree<B>, h: FnSpec(B) -> ITree<C>)
        ensures (#[trigger] f.bind(g).bind(h)) =~~= f.bind(|x| g(x).bind(h))
    {}

    struct UnforgeableAux;

    pub struct ITreeToken<T> {
        token: UnforgeableAux,
        inner: T
    }

    impl<T> ITreeToken<T> {
        pub closed spec fn view(self) -> ITree<T>;
    }

    } // verus!
} // mod itree



verus! {
use crate::itree::*;

#[verifier(external_body)]
pub exec fn input<A>(Tracked(t): Tracked<&mut ITreeToken<A>>) -> (i: Vec<u8>)
    requires old(t)@.is_input()
    ensures  t@ == old(t)@.take_input(i@)
{
    todo!()
}

#[verifier(external_body)]
pub exec fn output<A>(o: &Vec<u8>, Tracked(t): Tracked<&mut ITreeToken<A>>)
    requires old(t)@.is_output(o@)
    ensures  t@ == old(t)@.give_output()
{
    todo!()
}

pub open spec fn options_match(s: Option<Seq<u8>>, v: Option<Vec<u8>>) -> bool
{
    match (s, v) {
        (Some(ss), Some(vv)) => vv@ == ss,
        (None, None) => true,
        (_, _) => false
    }
}
pub open spec fn view_option(v: Option<Vec<u8>>) -> Option<Seq<u8>>
{
    match v {
        Some(x) => Some(x@),
        None    => None
    }
}
// Clones a Vec<u8> (because currently Verus doesn't support this natively)
#[verifier(external_body)]
pub exec fn clone_vec_u8(v: &Vec<u8>) -> (res: Vec<u8>)
    ensures v@ == res@
{
    todo!() // Vec { vec: v.vec.clone() }
}


// -- example --
pub closed spec fn enc(k: Seq<u8>, x: Seq<u8>) -> Seq<u8>;
pub closed spec fn dec(k: Seq<u8>, c: Seq<u8>) -> Option<Seq<u8>>;
pub closed spec fn foo(x: Seq<u8>) -> Seq<u8>;

#[verifier(external_body)]
pub exec fn enc_impl(k: &Vec<u8>, x: &Vec<u8>) -> (c: Vec<u8>) 
    ensures c@ == enc(k@, x@)
{ unimplemented!() }

#[verifier(external_body)]
pub exec fn dec_impl(k: &Vec<u8>, c: &Vec<u8>) -> (x: Option<Vec<u8>>) 
    ensures options_match(dec(k@, c@), x)
{ unimplemented!() }

#[verifier(external_body)]
pub exec fn foo_impl(x: &Vec<u8>) -> (y: Vec<u8>) 
    ensures y@ == foo(x@)
{ unimplemented!() }


pub open spec fn alice_main(owl_k_data: Seq<u8>, owl_shared_key: Seq<u8>) -> ITree<Option<Seq<u8>>> {   
    /*  
        let c = enc(owl_shared_key, owl_k_data) in
        output c in
        input i in
        let result = case dec(owl_k_data, i) 
            | Some(x) => 
                let y = alice_subroutine(x) in 
                Some(y)
            | None => None
        in
        result
     */ 
    
    ITree::Ret(enc(owl_shared_key, owl_k_data)).bind(|c|
    ITree::Output(c, Box::new(ITree::Ret(()))).bind(|u|
    ITree::Input(|ii| ITree::Ret(ii)).bind(|i|
    match dec(owl_k_data, i) {
        Some(x) => {
            alice_subroutine(x).bind(|y|
            ITree::Ret(Some(y))
            )
        },
        None => ITree::Ret(None),
    }).bind(|result| 
    ITree::Ret(result)
    )))

    // alice_subroutine(i).bind(|r| 
    // alice_subroutine(r).bind(|rr|
    // ITree::Output(rr, Box::new(ITree::Ret(()))).bind(|u|
    // alice_subroutine(rr).bind(|rrr| 
    // ITree::Ret(Some(rrr)))
    // ))))))
}

pub open spec fn alice_subroutine(k: Seq<u8>) -> ITree<Seq<u8>> {   
    /*  
        input x in
        let y = enc(k, x) in 
        foo(x)
     */ 
    
    ITree::Input(|ii| ITree::Ret(ii)).bind(|x|   
    ITree::Ret(enc(k, x)).bind(|y|
    ITree::Ret(foo(y))   
    ))
}

pub exec fn alice_subroutine_impl(Tracked(itree): Tracked<ITreeToken<Seq<u8>>>, k: &Vec<u8>) -> (res: (Vec<u8>, Tracked<ITreeToken<Seq<u8>>>)) 
    requires itree@ == alice_subroutine(k@)
    ensures  (res.1)@@.results_in(res.0@)
{
    let tracked mut itree = itree;
    let x = input::<Seq<u8>>(Tracked(&mut itree));
    let y = enc_impl(&k, &x);
    (foo_impl(&y), Tracked(itree))
}


// Hack because I seem to be unable to return `FnSpec`s
type FnSpecAlias<A,B> = FnSpec(A) -> B;

pub open spec fn itree_conts_match<A,B>(k: FnSpec(A) -> ITree<B>, kt: FnSpec(A) -> ITreeToken<B>) -> bool 
{
    forall |v: A| ((#[trigger] kt(v))@ == k(v))
}

#[verifier(external_body)]
pub proof fn split_bind<A,B>(tracked t: ITreeToken<A>, s: ITree<B>) -> (tracked st_kt: (Tracked<ITreeToken<B>>, Tracked<FnSpecAlias<B, ITreeToken<A>>>))
    requires exists |k| (t@ == #[trigger] s.bind::<A>(k))
    ensures  forall |k| (t@ == #[trigger] s.bind::<A>(k)) ==> ((st_kt.0)@@ == s && itree_conts_match(k, (st_kt.1)@))
{ unimplemented!() }

#[verifier(external_body)]
pub proof fn join_bind<A,B>(s: ITree<B>, tracked st: ITreeToken<B>, tracked kt: FnSpecAlias<B, ITreeToken<A>>, v: B) -> (tracked t: Tracked<ITreeToken<A>>)
    requires st@.results_in(v),
    ensures  t@ == kt(v)
{ unimplemented!() }


// TODO: Rust macros don't want to match the `@` character?
#[allow(unused_macros)]
macro_rules! owl_call {
    ($tok:expr, $spec:ident ( $($specarg:expr),* ), $exec:ident ( $($execarg:expr),* ) ) => {
        {
            #[verus::internal(proof)] let mut call_token;
            #[verus::internal(proof)] let mut cont_token;
            #[verifier::proof_block] {
                #[verus::internal(proof)] let (tmp_call_token, tmp_cont_token) = split_bind($tok, $spec($($specarg),*));
                call_token = tmp_call_token.get();
                cont_token = tmp_cont_token.get();
            }
            let (res, verus_tmp_call_token) =
                $exec(#[verifier::ghost_wrapper] ::builtin::tracked_exec(#[verifier::tracked_block_wrapped] call_token), $($execarg),*);
            
            #[verifier::proof_block] { call_token = verus_tmp_call_token.get(); };

            #[verus::internal(proof)] let mut tok;
            #[verifier::proof_block] {
                #[verus::internal(proof)] let tmp = join_bind($spec($($specarg),*), call_token, cont_token, res.view());
                tok = tmp.get();
            };
            (res, #[verifier::ghost_wrapper] ::builtin::tracked_exec(#[verifier::tracked_block_wrapped] tok))

            // let tracked (Tracked(call_token), Tracked(cont_token)) = split_bind($itree, $spec($($specarg),*));
            // let (res, Tracked(call_token)) = $exec(Tracked(call_token), $($execarg),*);
            // let tracked Tracked($itree) = join_bind($spec($($specarg),*), call_token, cont_token, res@);
            // (res, Tracked($itree))
        }
    };
    ($($tt:tt)*) => {
        compile_error!(concat!($("`", stringify!($tt), "`, "),*))
    }
}

pub exec fn alice_main_impl(Tracked(itree): Tracked<ITreeToken<Option<Seq<u8>>>>, owl_k_data: Vec<u8>, owl_shared_key: Vec<u8>) -> (res: (Option<Vec<u8>>, Tracked<ITreeToken<Option<Seq<u8>>>>))
    requires itree@ == alice_main(owl_k_data@, owl_shared_key@)
    ensures  (res.1)@@.results_in(view_option(res.0))
{
    let tracked mut itree = itree;
    let c = enc_impl(&owl_shared_key, &owl_k_data);
    output::<Option<Seq<u8>>>(&c, Tracked(&mut itree));
    let i = input::<Option<Seq<u8>>>(Tracked(&mut itree));

    let (res, Tracked(itree)): (Option<Vec<u8>>, Tracked<ITreeToken<Option<Seq<u8>>>>) = match dec_impl(&owl_k_data, &i) {
        Some(x) => {
            let (y, Tracked(itree)) : (Vec<u8>, Tracked<ITreeToken<Option<Seq<u8>>>>) = // owl_call!(itree, alice_subroutine(x.view()), alice_subroutine_impl(&x));
            {
                let tracked (Tracked(call_token), Tracked(cont_token)) = split_bind(itree, alice_subroutine(x@));
                let (res, Tracked(call_token)) = alice_subroutine_impl(Tracked(call_token), &x);
                let tracked Tracked(res_token) = join_bind(alice_subroutine(x@), call_token, cont_token, res@);
                (res, Tracked(res_token))
            };

            (Some(y), Tracked(itree))
        },
        None => (None, Tracked(itree))
    };
    (res, Tracked(itree))

    // let tracked (Tracked(call_token), Tracked(cont_token)) = split_bind(itree, alice_subroutine(r@));  
    // let (rr, Tracked(call_token)) = alice_subroutine_impl(Tracked(call_token), &r);
    // let tracked Tracked(itree) = join_bind(alice_subroutine(r@), call_token, cont_token, rr@);

    // output::<Option<Seq<u8>>>(&rr, Tracked(&mut itree));

    // let tracked (Tracked(call_token), Tracked(cont_token)) = split_bind(itree, alice_subroutine(rr@));  
    // let (rrr, Tracked(call_token)) = alice_subroutine_impl(Tracked(call_token), &rr);
    // let tracked Tracked(itree) = join_bind(alice_subroutine(rr@), call_token, cont_token, rrr@);

    // let y = Some(rrr);
    // (y, Tracked(itree))
}

    // let result = match dec_impl(&owl_k_data, &i) {
    //     Some(x) => {
    //         // proof { bind_reassoc::<Seq<u8>, Seq<u8>, Option<Seq<u8>>>(alice_subroutine(x@)); }
    //         assert(exists |cont| itree@@ =~~= bind::<Seq<u8>, Option<Seq<u8>>>(alice_subroutine(x@), cont)) by {
    //             bind_reassoc::<Seq<u8>, Seq<u8>, Option<Seq<u8>>>(alice_subroutine(x@));
    //         };
    //         // assert(itree@@ =~~= bind::<Seq<u8>, Option<Seq<u8>>>(alice_subroutine(x@), elim_bind(itree, alice_subroutine(x@)))) by {
    //         //     bind_reassoc::<Seq<u8>, Seq<u8>, Option<Seq<u8>>>(alice_subroutine(x@));
    //         // };
    //         // let Tracked(cont) = choose |k| itree@@ =~~= bind(alice_subroutine(x@), k);
    //         // let tracked mut subroutine_call_itree;
    //         // proof {
    //         //     subroutine_call_itree = mk_token(Ghost(alice_subroutine(x@)));
    //         // }
    //         let y = alice_subroutine_impl_call(itree, &x);
    //         // *itree = mk_token(cont(y@));
    //         // Some(y)

    //         assume(false); None
    //     },
    //     None => None
    // };
    //result



// pub exec fn alice_subroutine_impl_call<A>(itree: &mut Tracked<ITreeToken<A>>, k: &Vec<u8>) -> (res: Vec<u8>) 
//     requires exists |cont| (old(itree)@@ == #[trigger] alice_subroutine(k@).bind::<A>(cont))
//     ensures  forall |cont| (old(itree)@@ == #[trigger] alice_subroutine(k@).bind::<A>(cont) ==> itree@@ == cont(res@))
// {
//     let (call_token, cont_token) = split_bind(itree, alice_subroutine(k@));

//     // let ghost cont = choose |c| old(itree)@@ == #[trigger] alice_subroutine(k@).bind::<A>(c);
//     // assert forall |c| (old(itree)@@ == #[trigger] alice_subroutine(k@).bind::<A>(c)) implies (c =~~= cont) by {
//     //     invert_bind_equality(alice_subroutine(k@), c, alice_subroutine(k@).bind(c), cont, alice_subroutine(k@).bind(cont))
//     //     // assert forall |v| #[trigger] c(v) =~~= #[trigger] cont(v) by {
//     //     //     assert(alice_subroutine(k@).bind::<A>(c) =~~= alice_subroutine(k@).bind::<A>(cont));
//     //     //     assume(false);
//     //     // }
//     // };

//     let mut token: Tracked<ITreeToken<Seq<u8>>> = blank_token();
//     proof {
//         assume(token@@ == alice_subroutine(k@));
//     }

//     let r = alice_subroutine_impl(&mut token, k);

//     assert(token@@.results_in(r@));
//     proof {
//         assume(itree@@ == cont(r@));
//     }

//     assert forall |c| (old(itree)@@ == #[trigger] alice_subroutine(k@).bind::<A>(c)) implies (itree@@ == c(r@)) by {

//     };

//     r    
// }

} // verus!


fn main() { }