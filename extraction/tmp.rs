#![allow(unused_imports)]
#![allow(non_camel_case_types)]
pub use vstd::{modes::*, option::*, prelude::*, seq::*, vec::*, *};

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
        pub open spec fn is_input(&self) -> bool {
            self.is_Input()
        }
        pub open spec(checked) fn take_input(&self, i: Seq<u8>) -> ITree<A>
            recommends self.is_input()
        {
            (self.get_Input_0())(i)
        }
        pub open spec fn is_output(&self, o: Seq<u8>) -> bool {
            self.is_Output() && self.get_Output_0() == o
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

    #[verifier(external_body)]
    pub closed spec fn Bind<A, B>(f : ITree<A>, k : FnSpec(A) -> ITree<B>) -> ITree<B> { todo!() }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_ret<A, B>(x: A, k : FnSpec(A) -> ITree<B>)
        ensures
            (#[trigger] Bind(ITree::Ret(x), k)) == k(x)
    { }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_inp<A, B>(f : FnSpec(Seq<u8>) -> ITree<A>, k: FnSpec(A) -> ITree<B>)
        ensures
            (#[trigger] Bind(ITree::Input(f), k)) == ITree::Input(|x| Bind(f(x), k))
    { }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_bind_out<A, B>(x : Seq<u8>, f : Box<ITree<A>>, k : FnSpec(A) -> ITree<B>)
        ensures
            (#[trigger] Bind(ITree::Output(x, f), k)) == ITree::Output(x, Box::new(Bind(*f, k)))
    { }

    // // TODO: In general, do we need this?
    // #[verifier(external_body)]
    // #[verifier(broadcast_forall)]
    // pub proof fn axiom_bind_bind<A, B, C>(f: ITree<A>, g : FnSpec(A) -> ITree<B>, h : FnSpec(B) -> ITree<C>) 
    //     ensures (#[trigger] Bind(Bind(f, g), h)) == Bind(f, |x| Bind(g(x), h)) 
    // { }

    // #[verifier(external_body)]
    // #[verifier(broadcast_forall)]
    // pub proof fn input_ext<A>(f: FnSpec(Seq<u8>) -> ITree<A>, g : FnSpec(Seq<u8>) -> ITree<A>)
    //     requires f =~~= g
    //     ensures #[trigger] (ITree::Input(f) =~~= ITree::Input(g))
    // {  }

    // #[verifier(external_body)]
    // #[verifier(broadcast_forall)]
    // pub proof fn output_ext<A>(x : Seq<u8>, y : Seq<u8>, f: Box<ITree<A>>, g : Box<ITree<A>>)
    //     requires x =~~= y, 
    //             *f =~~= *g
    //     ensures #[trigger] (ITree::Output(x, f) =~~= ITree::Output(y, g))
    // {  }

    // pub proof fn tstlemma()
    // {
    //     // These assertions only go through with the above `input_ext` and `output_ext` axioms.
    //     {
    //         assert (ITree::Output(seq![], Box::new(ITree::Input(|y| Bind(ITree::Ret(y), |z| ITree::Ret(z)))))
    //                 =~~=
    //                 ITree::Output(seq![], Box::new(ITree::Input(|y| ITree::Ret(y)))));
    //     }

    //     {
    //         assert (ITree::Input(|y| Bind(ITree::Ret(y), |z| ITree::Output(z, Box::new(ITree::Ret(z)))))
    //                 =~~=
    //                 ITree::Input(|y| ITree::Output(y, Box::new(ITree::Ret(y)))));
    //     }
    //     // assert(false); // sanity check--this fails
    // }

    struct UnforgeableAux;

    pub struct ITreeToken<T> {
        token: UnforgeableAux,
        inner: (T,)
    }

    impl<T> ITreeToken<T> {
        pub closed spec fn view(self) -> ITree<T>;
    }

    } // verus!
} // mod itree

verus! {
use crate::itree::*;

#[verifier(external_body)]
pub exec fn input<A>(t: &mut Tracked<ITreeToken<A>>) -> (i: Vec<u8>)
    requires old(t)@@.is_input()
    ensures  t@@ === old(t)@@.take_input(i@)
{
    todo!()
}

#[verifier(external_body)]
pub exec fn output<A>(o: &Vec<u8>, t: &mut Tracked<ITreeToken<A>>)
    requires old(t)@@.is_output(o@)
    ensures  t@@ == old(t)@@.give_output()
{
    todo!()
}

pub open spec fn options_match(s: Option<Seq<u8>>, v: Option<Vec<u8>>) -> bool
{
    (v.is_None() && s.is_None()) ||
    (v.is_Some() && s.is_Some() && v.get_Some_0()@ == s.get_Some_0())
}
pub open spec fn view_option(v: Option<Vec<u8>>) -> Option<Seq<u8>>
{
    match v {
        crate::Option::Some(x) => crate::Option::Some(x@),
        crate::Option::None    => crate::Option::None
    }
}


// -- example --
pub closed spec fn enc(k: Seq<u8>, x: Seq<u8>) -> Seq<u8>;
pub closed spec fn dec(k: Seq<u8>, c: Seq<u8>) -> Option<Seq<u8>>;
pub closed spec fn foo(x: Seq<u8>) -> Seq<u8>;


pub open spec fn alice_main(owl_k_data: Seq<u8>, owl_shared_key: Seq<u8>) -> ITree<Option<Seq<u8>>> {   
    /*  
        let c = enc(owl_shared_key, owl_k_data) in
        output c in
        input i in
        let result = case dec(owl_k_data, i) 
            | Some(x) => let y = foo(x) in Some(y)
            | None => None
        in
        result
     */ 
    
    Bind(ITree::Ret(enc(owl_shared_key, owl_k_data)), |c|
    Bind(ITree::Output(c, Box::new(ITree::Ret(()))), |u|
    Bind(ITree::Input(|ii| ITree::Ret(ii)), |i|
    Bind(            
        match dec(owl_k_data, i) {
            Some(x) => {
                Bind(ITree::Ret(foo(x)), |y| ITree::Ret(Some(y)))
            },
            None => ITree::Ret(None)
        }, |result|
    ITree::Ret(result)
    ))))
}

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


pub exec fn alice_main_impl( itree: &mut Tracked<ITreeToken<Option<Seq<u8>>>>, owl_k_data: Vec<u8>, owl_shared_key: Vec<u8>) -> (res:Option<Vec<u8>>)
    requires old(itree)@@ == alice_main(owl_k_data@, owl_shared_key@)
    ensures  itree@@.results_in(view_option(res))
{
    let c = enc_impl(&owl_shared_key, &owl_k_data);
    output(&c, itree);
    // output(&c, itree); // uncomment this to see verification failure
    let i = input(itree);
    let result = match dec_impl(&owl_k_data, &i) {
        Some(x) => Some(foo_impl(&x)),
        None => None
    };
    result
}


}



fn main() { }