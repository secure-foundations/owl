extern crate alloc;
use vstd::prelude::*;

verus! {

    /// deep view of an exec type
    pub trait DView {
        type V;
        spec fn dview(&self) -> Self::V;
    }

    impl<A: DView> DView for &A {
        type V = A::V;
        #[verifier::inline]
        open spec fn dview(&self) -> A::V {
            (**self).dview()
        }
    }

    impl<A: DView> DView for alloc::boxed::Box<A> {
        type V = A::V;
        #[verifier::inline]
        open spec fn dview(&self) -> A::V {
            (**self).dview()
        }
    }

    impl<A: DView> DView for alloc::rc::Rc<A> {
        type V = A::V;
        #[verifier::inline]
        open spec fn dview(&self) -> A::V {
            (**self).dview()
        }
    }

    impl<A: DView> DView for alloc::sync::Arc<A> {
        type V = A::V;
        #[verifier::inline]
        open spec fn dview(&self) -> A::V {
            (**self).dview()
        }
    }

    macro_rules! declare_identity_view {
        ($t:ty) => {
            #[cfg_attr(verus_keep_ghost, verifier::verify)]
            impl DView for $t {
                type V = $t;
                #[cfg(verus_keep_ghost)]
                #[verus::internal(spec)]
                #[verus::internal(open)]
                #[verifier::inline]
                fn dview(&self) -> $t {
                    *self
                }
            }
        }
    }

    declare_identity_view!(());
    declare_identity_view!(bool);
    declare_identity_view!(u8);
    declare_identity_view!(u16);
    declare_identity_view!(u32);
    declare_identity_view!(u64);
    declare_identity_view!(u128);
    declare_identity_view!(usize);
    declare_identity_view!(i8);
    declare_identity_view!(i16);
    declare_identity_view!(i32);
    declare_identity_view!(i64);
    declare_identity_view!(i128);
    declare_identity_view!(isize);

    macro_rules! declare_tuple_view {
        ([$($n:tt)*], [$($a:ident)*]) => {
            #[cfg_attr(verus_keep_ghost, verifier::verify)]
            impl<$($a: DView, )*> DView for ($($a, )*) {
                type V = ($($a::V, )*);
                #[cfg(verus_keep_ghost)]
                #[verus::internal(spec)]
                #[verus::internal(open)]
                fn dview(&self) -> ($($a::V, )*) {
                    ($(self.$n.dview(), )*)
                }
            }
        }
    }

    declare_tuple_view!([0], [A0]);
    declare_tuple_view!([0 1], [A0 A1]);
    declare_tuple_view!([0 1 2], [A0 A1 A2]);
    declare_tuple_view!([0 1 2 3], [A0 A1 A2 A3]);

    /// deep view of a Vec
    impl<T: DView> DView for Vec<T> {
        type V = Seq<T::V>;
        open spec fn dview(&self) -> Self::V;
        // {
        //     self@.map_values(|x: T| x.dview())
        // }
    }

    #[verifier::external]
    pub trait VecAdditionalExecFns<T> {
        fn set(&mut self, i: usize, value: T);
        fn set_and_swap(&mut self, i: usize, value: &mut T);
        fn length(&self) -> usize;
    }

    impl<T: DView> VecAdditionalExecFns<T> for Vec<T> {
        /// Replacement for `self[i] = value;` (which Verus does not support for technical reasons)

        #[verifier::external_body]
        fn set(&mut self, i: usize, value: T)
            requires
                i < old(self).dview().len(),
            ensures
                self.dview() == old(self).dview().update(i as int, value.dview()),
        {
            self[i] = value;
        }

        /// Replacement for `swap(&mut self[i], &mut value)` (which Verus does not support for technical reasons)

        #[verifier::external_body]
        fn set_and_swap(&mut self, i: usize, value: &mut T)
            requires
                i < old(self).dview().len(),
            ensures
                value.dview() == old(self).dview().index(i as int)
        {
            core::mem::swap(&mut self[i], value);
        }

        #[verifier::external_body]
        fn length(&self) -> (res: usize)
            ensures
                res == spec_vec_len(self)
        {
            self.len()
        }
    }

    #[verifier::external_body]
    pub fn vec_length<T: DView>(vec: &Vec<T>) -> (res: usize)
        ensures
            res == spec_vec_len(vec),
            res == vec.dview().len() as usize,
            res <= usize::MAX as int
    {
        vec.len()
    }

    #[verifier::external_body]
    pub fn vec_index<T: DView>(vec: &Vec<T>, i: usize) -> (element: &T)
        requires i < vec.dview().len(),
        ensures element.dview() == vec.dview().index(i as int)
    {
        &vec[i]
    }

    #[verifier::external_body]
    pub fn vec_as_slice<T: DView>(vec: &Vec<T>) -> (slice: &[T])
        ensures slice.dview() == vec.dview()
    {
        vec.as_slice()
    }

    #[verifier::external_body]
    pub fn vec_push<T: DView>(vec: &mut Vec<T>, value: T)
        ensures vec.dview() == old(vec).dview().push(value.dview())
    {
        vec.push(value);
    }

    #[verifier::external_body]
    pub fn vec_new<T: DView>() -> (v: Vec<T>)
        ensures
            v.dview() == Seq::<T::V>::empty(),
    {
        Vec::<T>::new()
    }

    #[verifier::external_body]
    pub fn vec_append<T: DView>(vec: &mut Vec<T>, other: &mut Vec<T>)
        ensures
            vec.dview() == old(vec).dview() + old(other).dview(),
    {
        vec.append(other)
    }

    pub open spec fn spec_vec_len<T: DView>(v: &Vec<T>) -> usize;

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_spec_len<T: DView>(v: &Vec<T>)
        ensures
            #[trigger] spec_vec_len(v) == v.dview().len()
    {}


    impl<T: DView> DView for [T] {
        type V = Seq<T::V>;
        open spec fn dview(&self) -> Self::V;
    }

    #[verifier(external_body)]
    pub exec fn slice_index_get<T: DView>(slice: &[T], i: usize) -> (out: &T)
        requires 0 <= i < slice.dview().len(),
        ensures out.dview() == slice.dview().index(i as int),
    {
        &slice[i]
    }

    #[verifier(external_body)]
    pub exec fn slice_to_vec<T: Copy + DView>(slice: &[T]) -> (out: Vec<T>)
        ensures out.dview() == slice.dview()
    {
        slice.to_vec()
    }

    #[verifier(external_body)]
    pub exec fn slice_subrange<T: DView, 'a>(slice: &'a [T], i: usize, j: usize) -> (out: &'a [T])
        requires 0 <= i <= j <= slice.dview().len()
        ensures out.dview() == slice.dview().subrange(i as int, j as int)
    {
        &slice[i .. j]
    }

    #[verifier(external_body)]
    pub exec fn swap_with_slice<T: DView>(left: &mut [T], right: &mut [T])
        requires
            old(left).dview().len() == old(right).dview().len(),
        ensures
            left.dview() == old(right).dview(),
            right.dview() == old(left).dview(),
    {
        left.swap_with_slice(right)
    }

    impl<T: DView> DView for &[T] {
        type V = Seq<T::V>;
        #[verifier::inline]
        open spec fn dview(&self) -> Self::V {
            (*self).dview()
        }
    }

    #[verifier::external]
    pub trait SliceAdditionalExecFns<T> {
        fn set(&mut self, i: usize, value: T);
        fn length(&self) -> usize;
    }

    impl<T: DView> SliceAdditionalExecFns<T> for [T] {

        /// Replacement for `self[i] = value;` (which Verus does not support for technical reasons)
        #[verifier::external_body]
        fn set(&mut self, i: usize, value: T)
            requires
                i < old(self).dview().len(),
            ensures
                self.dview() == old(self).dview().update(i as int, value.dview()),
        {
            self[i] = value;
        }

        #[verifier::external_body]
        fn length(&self) -> (length: usize)
            ensures
                length >= 0,
                length == self.dview().len()
        {
            self.len()
        }

    }
}
