use vstd::prelude::*;
use vstd::seq_lib::*;
extern crate alloc;
use alloc::vec::Vec;
use crate::deep_view::{VecAdditionalExecFns, *};

verus! {
    pub struct Stream {
        pub data: Vec<u8>,
        pub start: usize,
    }

    pub struct SpecStream {
        pub data: Seq<u8>,
        pub start: int, // the index, in range [0, data.len())
    }

    impl DView for Stream {
        type V = SpecStream;
        open spec fn dview(&self) -> SpecStream {
            SpecStream {
                data: self.data.dview(),
                start: self.start as int,
            }
        }
    }

    #[derive(PartialEq, Eq)]
    pub enum ParseError {
        Eof,
        NotEnoughData,
        NegativeIndex,
        IntegerOverflow,
        ConstMismatch,
    }

    #[derive(PartialEq, Eq)]
    pub enum SerializeError {
        NotEnoughSpace,
        NegativeIndex,
        IntegerOverflow,
        RepeatNMismatch, // for spec_serialize_repeat_n
        TailLengthMismatch, // for spec_serialize_tail
        ConstMismatch, // for const serializers
    }

    pub type ParseResult<Output> = Result<(Stream, usize, Output), ParseError>;
    pub type SpecParseResult<Output> = Result<(SpecStream, nat, Output), ParseError>;

    pub type SerializeResult = Result<(Stream, usize), SerializeError>;
    pub type SpecSerializeResult = Result<(SpecStream, nat), SerializeError>;

    impl std::fmt::Debug for Stream {
        #[verifier(external)]
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "Stream {{ data: {:?}, start: {} }}", self.data, self.start)
        }
    }

    impl std::clone::Clone for Stream {
        #[verifier(external_body)]
        fn clone(&self) -> (res: Self)
            ensures
                self.data == res.data,
                self.start == res.start
        {
            Self {
                data: self.data.clone(),
                start: self.start,
            }
        }
    }

    impl std::fmt::Debug for ParseError {
        #[verifier(external)]
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Eof => write!(f, "Eof"),
                Self::NotEnoughData => write!(f, "NotEnoughData"),
                Self::NegativeIndex => write!(f, "Other"),
                Self::IntegerOverflow => write!(f, "IntegerOverflow"),
                Self::ConstMismatch => write!(f, "ConstMismatch"),
            }
        }
    }

    impl std::fmt::Debug for SerializeError {
        #[verifier(external)]
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::NotEnoughSpace => write!(f, "NotEnoughSpace"),
                Self::NegativeIndex => write!(f, "NegativeIndex"),
                Self::RepeatNMismatch => write!(f, "RepeatNMismatch"),
                Self::IntegerOverflow => write!(f, "IntegerOverflow"),
                Self::TailLengthMismatch => write!(f, "TailLengthMismatch"),
                Self::ConstMismatch => write!(f, "ConstMismatch"),
            }
        }
    }

    pub enum Either<A, B> {
        Left(A),
        Right(B),
    }

    impl<A, B> DView for Either<A, B>
        where
            A: DView,
            B: DView,
    {
        type V = Either<A::V, B::V>;
        open spec fn dview(&self) -> Either<A::V, B::V> {
            match self {
                Self::Left(a) => Either::Left(a.dview()),
                Self::Right(b) => Either::Right(b.dview()),
            }
        }
    }

    impl<A,B> std::fmt::Debug for Either<A, B>
        where
            A: std::fmt::Debug,
            B: std::fmt::Debug,
    {
        #[verifier(external)]
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Left(a) => write!(f, "Left({:?})", a),
                Self::Right(b) => write!(f, "Right({:?})", b),
            }
        }
    }

    /// A *well-behaved parser* should
    /// 1. keep the input data unchanged
    /// 2. the new start position should be the addition of the old start position and the number of consumed bytes
    /// 3. the old and new start positions should be in range
    pub open spec fn prop_parse_well_behaved_on<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        s: SpecStream) -> bool
    {
        match parser(s) {
            Ok((sout, n, _)) => {
                &&& sout.data == s.data
                &&& s.start + n == sout.start
                &&& 0 <= s.start <= sout.start <= s.data.len()
            }
            Err(_) => true, // vacuously true
        }
    }

    /// A *well-behaved serializer* should
    /// 1. keep the length of the input data unchanged
    /// 2. keep the input data prior to the start position unchanged
    /// 3. keep the input data following serialized data unchanged
    /// 4. the new start position should be the addition of the old start position and the number of serialized bytes
    /// 5. the old and new start positions should be in range
    pub open spec fn prop_serialize_well_behaved_on<R>(
        serializer: FnSpec(SpecStream, R) -> SpecSerializeResult,
        s: SpecStream, v: R) -> bool
    {
        if let Ok((sout, n)) = serializer(s, v) {
            &&& sout.data.len() == s.data.len()
            &&& sout.data.subrange(0, s.start) == s.data.subrange(0, s.start)
            &&& sout.data.subrange(s.start + n, s.data.len() as int) == s.data.subrange(s.start + n, s.data.len() as int)
            &&& s.start + n == sout.start
            &&& 0 <= s.start <= sout.start <= s.data.len()
        } else {
            true // vacuously true
        }
    }

    pub open spec fn prop_serialize_deterministic_on<R>(
        serializer: FnSpec(SpecStream, R) -> SpecSerializeResult,
        s1: SpecStream, s2: SpecStream, v: R) -> bool
    {
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (serializer(s1, v), serializer(s2, v)) {
            n1 == n2 && sout1.data.subrange(s1.start, s1.start + n1) == sout2.data.subrange(s2.start, s2.start + n2)
        } else {
            true // vacuously true
        }
    }

    pub open spec fn prop_parse_strong_prefix_on<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        s1: SpecStream,
        s2: SpecStream) -> bool
    {
        if let Ok((sout1, n, x1)) = parser(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = parser(s2) {
                    n == m && x1 == x2
                } else {
                    false
                }
            } else {
                true // vacuously true
            }
        } else {
            true // vacuously true
        }
    }

    pub open spec fn prop_parse_correct_on<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        serializer: FnSpec(SpecStream, R) -> SpecSerializeResult,
        s: SpecStream, v: R) -> bool
    {
        if let Ok((sout, n)) = serializer(s, v) {
            if let Ok((_, m, res)) = parser(SpecStream {start: s.start, ..sout}) {
                n == m && v == res
            } else {
                false
            }
        } else {
            true // vacuously true
        }
    }

    pub open spec fn prop_parse_serialize_inverse_on<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        serializer: FnSpec(SpecStream, R) -> SpecSerializeResult,
        s: SpecStream) -> bool
    {
        if let Ok((ss, m, res)) = parser(s) {
            if let Ok((sout, n)) = serializer(s, res) {
                m == n && sout.data == s.data
            } else {
                false
            }
        } else {
            true // vacuously true
        }
    }

    pub open spec fn prop_parse_nonmalleable_on<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        s1: SpecStream,
        s2: SpecStream) -> bool
    {
        if let (Ok((sout1, n, x1)), Ok((sout2, m, x2))) = (parser(s1), parser(s2)) {
            x1 == x2 ==> n == m && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + m)
        } else {
            true // vacuously true
        }
    }

    /// An `exec` parser is equivalent to a `spec` parser if
    ///
    /// 1. on the same input stream, they both success and produce the same result,
    /// including the output stream, the number of consumed bytes and the result value
    /// 2. or they both fail and throw the same error.
    pub open spec fn prop_parse_exec_spec_equiv_on<T: DView>(
        s: Stream,
        res: ParseResult<T>,
        spec_parser: FnSpec(SpecStream) -> SpecParseResult<T::V>) -> bool
    {
        match spec_parser(s.dview()) {
            Ok((sout, sn, sx)) => {
                if let Ok((s, n, x)) = res {
                    &&& s.dview() == sout
                    &&& n == sn
                    &&& x.dview() == sx
                } else {
                    false
                }
            }
            Err(e) => {
                if let Err(e2) = res {
                    e == e2
                } else {
                    false
                }
            }
        }
    }

    /// An `exec` serializer is equivalent to a `spec` serializer if
    ///
    /// 1. on the same input stream and value, they both success and produce the same result,
    /// including the output stream and the number of serialized bytes
    /// 2. or they both fail and throw the same error.
    pub open spec fn prop_serialize_exec_spec_equiv_on<T: DView>(
        s: Stream,
        v: T,
        res: SerializeResult,
        spec_serializer: FnSpec(SpecStream, T::V) -> SpecSerializeResult) -> bool
        where T: std::fmt::Debug + DView
    {
        match spec_serializer(s.dview(), v.dview()) {
            Ok((sout, sn)) => {
                &&& res.is_ok()
                &&& res.unwrap().0.dview() == sout
                &&& res.unwrap().1 == sn
            }
            Err(e) => res.is_err() && res.unwrap_err() == e
        }
    }

    // prevent the body from seen
    #[verifier(opaque)]
    pub open spec fn prop_parse_well_behaved<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>) -> bool
    {
        forall |s: SpecStream| prop_parse_well_behaved_on(parser, s)
    }

    #[verifier(opaque)]
    pub open spec fn prop_serialize_well_behaved<T>(serializer: FnSpec(SpecStream, T) -> SpecSerializeResult) -> bool
    {
        forall |s: SpecStream, v: T| prop_serialize_well_behaved_on(serializer, s, v)
    }

    #[verifier(opaque)]
    pub open spec fn prop_serialize_deterministic<R>(serializer: FnSpec(SpecStream, R) -> SpecSerializeResult) -> bool
    {
        forall |s1: SpecStream, s2: SpecStream, v: R| prop_serialize_deterministic_on(serializer, s1, s2, v)
    }

    #[verifier(opaque)]
    pub open spec fn prop_parse_strong_prefix<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>) -> bool
    {
        forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(parser, s1, s2)
    }

    #[verifier(opaque)]
    pub open spec fn prop_parse_correct<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>, serializer: FnSpec(SpecStream, T) -> SpecSerializeResult) -> bool
    {
        forall |s: SpecStream, v: T| prop_parse_correct_on(parser, serializer, s, v)
    }

    #[verifier(opaque)]
    pub open spec fn prop_parse_serialize_inverse<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>, serializer: FnSpec(SpecStream, T) -> SpecSerializeResult) -> bool
    {
        forall |s: SpecStream| prop_parse_serialize_inverse_on(parser, serializer, s)
    }

    #[verifier(opaque)]
    /// this property can actually be derived from the parse_serialize_inverse property (with deterministic serializers)
    /// ∀ s. serialize(parse(s)) == s
    /// ==>
    /// ∀ s1 s2.
    /// &&& serialize(parse(s1)) == s1 && serialize(parse(s2)) == s2
    /// &&& (parse(s1) == parse(s2) <==> serialize(parse(s1)) == serialize(parse(s2)) ==> s1 == s2)
    pub open spec fn prop_parse_nonmalleable<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>) -> bool
    {
        forall |s1: SpecStream, s2: SpecStream| prop_parse_nonmalleable_on(parser, s1, s2)
    }

    pub proof fn lemma_parse_serialize_inverse_implies_nonmalleable<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>, serializer: FnSpec(SpecStream, T) -> SpecSerializeResult)
        requires
            prop_parse_serialize_inverse(parser, serializer),
            prop_serialize_deterministic(serializer)
        ensures
            prop_parse_nonmalleable(parser)
    {
        reveal(prop_parse_serialize_inverse);
        reveal(prop_parse_nonmalleable);
        reveal(prop_serialize_deterministic);
        assert forall |s1: SpecStream, s2: SpecStream| prop_parse_nonmalleable_on(parser, s1, s2) by {
            lemma_parse_serialize_inverse_on(parser, serializer, s1);
            lemma_parse_serialize_inverse_on(parser, serializer, s2);
            if let (Ok((sout1, n1, x1)), Ok((sout2, n2, x2))) = (parser(s1), parser(s2)) {
                if x1 == x2 {
                    lemma_serialize_deterministic_on(serializer, s1, s2, x1);
                    assert(n1 == n2);
                    assert(s1.data.subrange(s1.start, s1.start + n1) =~= s2.data.subrange(s2.start, s2.start + n2));
                }
            }
        }
    }

    #[verifier(opaque)]
    pub open spec fn prop_parse_exec_spec_equiv<T, P>(
        exec_parser: P,
        spec_parser: FnSpec(SpecStream) -> SpecParseResult<T::V>) -> bool
        where
            P: FnOnce(Stream) -> ParseResult<T>,
            T: DView,
    {
        &&& forall |s| #[trigger] exec_parser.requires((s,))
        &&& forall |s, res| #[trigger] exec_parser.ensures((s,), res) ==> prop_parse_exec_spec_equiv_on(s, res, spec_parser)
    }

    #[verifier(opaque)]
    pub open spec fn prop_serialize_exec_spec_equiv<T, P>(
        exec_serializer: P,
        spec_serializer: FnSpec(SpecStream, T::V) -> SpecSerializeResult) -> bool
        where
            P: FnOnce(Stream, T) -> SerializeResult,
            T: std::fmt::Debug + DView,
    {
        &&& forall |s, v| #[trigger] exec_serializer.requires((s, v))
        &&& forall |s, v, res| #[trigger] exec_serializer.ensures((s, v), res) ==> prop_serialize_exec_spec_equiv_on(s, v, res, spec_serializer)
    }

    // for performance boost
    pub proof fn lemma_parse_well_behaved_on<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>, s: SpecStream)
        requires
            prop_parse_well_behaved(parser)
        ensures
            prop_parse_well_behaved_on(parser, s)
    {
        reveal(prop_parse_well_behaved);
    }

    pub proof fn lemma_serialize_well_behaved_on<T>(serializer: FnSpec(SpecStream, T) -> SpecSerializeResult, s: SpecStream, v: T)
        requires
            prop_serialize_well_behaved(serializer)
        ensures
            prop_serialize_well_behaved_on(serializer, s, v)
    {
        reveal(prop_serialize_well_behaved);
    }

    pub proof fn lemma_serialize_deterministic_on<T>(serializer: FnSpec(SpecStream, T) -> SpecSerializeResult, s1: SpecStream, s2: SpecStream, v: T)
        requires
            prop_serialize_deterministic(serializer)
        ensures
            prop_serialize_deterministic_on(serializer, s1, s2, v)
    {
        reveal(prop_serialize_deterministic);
    }

    pub proof fn lemma_parse_strong_prefix_on<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>, s1: SpecStream, s2: SpecStream)
        requires
            prop_parse_strong_prefix(parser)
        ensures
            prop_parse_strong_prefix_on(parser, s1, s2)
    {
        reveal(prop_parse_strong_prefix);
    }

    pub proof fn lemma_parse_correct_on<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>, serializer: FnSpec(SpecStream, T) -> SpecSerializeResult, s: SpecStream, v: T)
        requires
            prop_parse_correct(parser, serializer)
        ensures
            prop_parse_correct_on(parser, serializer, s, v)
    {
        reveal(prop_parse_correct);
    }

    pub proof fn lemma_parse_serialize_inverse_on<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>, serializer: FnSpec(SpecStream, T) -> SpecSerializeResult, s: SpecStream)
        requires
            prop_parse_serialize_inverse(parser, serializer)
        ensures
            prop_parse_serialize_inverse_on(parser, serializer, s)
    {
        reveal(prop_parse_serialize_inverse);
    }

    pub proof fn lemma_parse_nonmalleable_on<T>(parser: FnSpec(SpecStream) -> SpecParseResult<T>, serializer: FnSpec(SpecStream, T) -> SpecSerializeResult, s1: SpecStream, s2: SpecStream)
        requires
            prop_parse_nonmalleable(parser)
        ensures
            prop_parse_nonmalleable_on(parser, s1, s2)
    {
        reveal(prop_parse_nonmalleable);
    }

    pub proof fn lemma_parse_exec_spec_equiv_on<T, P>(
        exec_parser: P,
        spec_parser: FnSpec(SpecStream) -> SpecParseResult<T::V>,
        s: Stream, res: ParseResult<T>)
        where
            P: FnOnce(Stream) -> ParseResult<T>,
            T: DView,
        requires
            prop_parse_exec_spec_equiv(exec_parser, spec_parser),
            exec_parser.ensures((s,), res)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, spec_parser)
    {
        reveal(prop_parse_exec_spec_equiv);
    }

    pub proof fn lemma_serialize_exec_spec_equiv_on<T, P>(
        exec_serializer: P,
        spec_serializer: FnSpec(SpecStream, T::V) -> SpecSerializeResult,
        s: Stream, v: T, res: SerializeResult)
        where
            P: FnOnce(Stream, T) -> SerializeResult,
            T: std::fmt::Debug + DView,
        requires
            prop_serialize_exec_spec_equiv(exec_serializer, spec_serializer),
            exec_serializer.ensures((s, v), res)
        ensures
            prop_serialize_exec_spec_equiv_on(s, v, res, spec_serializer)
    {
        reveal(prop_serialize_exec_spec_equiv);
    }

// Conversion between u16 and little-endian byte sequences

pub closed spec fn spec_u16_to_le_bytes(x: u16) -> Seq<u8>
{
  seq![
    (x & 0xff) as u8,
    ((x >> 8) & 0xff) as u8
  ]
}

pub closed spec fn spec_u16_from_le_bytes(s: Seq<u8>) -> u16
  recommends s.len() == 2
{
  (s[0] as u16) |
  (s[1] as u16) << 8
}

pub proof fn lemma_auto_spec_u16_to_from_le_bytes()
  ensures
    forall |x: u16|
    {
      &&& #[trigger] spec_u16_to_le_bytes(x).len() == 2
      &&& spec_u16_from_le_bytes(spec_u16_to_le_bytes(x)) == x
    },
    forall |s: Seq<u8>|
      s.len() == 2 ==> #[trigger] spec_u16_to_le_bytes(spec_u16_from_le_bytes(s)) == s,
{
  assert forall |x: u16|  {
    &&& #[trigger] spec_u16_to_le_bytes(x).len() == 2
    &&& spec_u16_from_le_bytes(spec_u16_to_le_bytes(x)) == x
  } by {
    let s = spec_u16_to_le_bytes(x);
    assert({
      &&& x & 0xff < 256
      &&& (x >> 8) & 0xff < 256
    }) by (bit_vector);

    assert(x == (
      (x & 0xff) |
      ((x >> 8) & 0xff) << 8)) by (bit_vector);
  };

  assert forall |s: Seq<u8>| s.len() == 2 implies #[trigger] spec_u16_to_le_bytes(spec_u16_from_le_bytes(s)) == s by {
    let x = spec_u16_from_le_bytes(s);
    let s0 = s[0] as u16;
    let s1 = s[1] as u16;

    assert(
      (
        (x == s0 | s1 << 8) &&
        (s0 < 256) &&
        (s1 < 256)
      ) ==>
      s0 == (x & 0xff) && s1 == ((x >> 8) & 0xff)
    ) by (bit_vector);

    assert_seqs_equal!(spec_u16_to_le_bytes(spec_u16_from_le_bytes(s)) == s);
  }
}

#[verifier(external_body)]
pub exec fn u16_from_le_bytes(s: &[u8]) -> (x:u16)
  requires s.dview().len() == 2,
  ensures x == spec_u16_from_le_bytes(s.dview()),
{
  use core::convert::TryInto;
  u16::from_le_bytes(s.try_into().unwrap())
}


#[verifier(external_body)]
pub exec fn u16_to_le_bytes(x: u16) -> (s: alloc::vec::Vec<u8>)
  ensures
    s.dview() == spec_u16_to_le_bytes(x),
    s.dview().len() == 2,
{
  x.to_le_bytes().to_vec()
}

// Conversion between u32 and little-endian byte sequences

pub closed spec fn spec_u32_to_le_bytes(x: u32) -> Seq<u8>
{
  seq![
    (x & 0xff) as u8,
    ((x >> 8) & 0xff) as u8,
    ((x >> 16) & 0xff) as u8,
    ((x >> 24) & 0xff) as u8,
  ]
}

pub closed spec fn spec_u32_from_le_bytes(s: Seq<u8>) -> u32
  recommends s.len() == 4
{
  (s[0] as u32) |
  (s[1] as u32) << 8 |
  (s[2] as u32) << 16 |
  (s[3] as u32) << 24
}

pub proof fn lemma_auto_spec_u32_to_from_le_bytes()
  ensures
    forall |x: u32|
    {
      &&& #[trigger] spec_u32_to_le_bytes(x).len() == 4
      &&& spec_u32_from_le_bytes(spec_u32_to_le_bytes(x)) == x
    },
    forall |s: Seq<u8>|
      s.len() == 4 ==> #[trigger] spec_u32_to_le_bytes(spec_u32_from_le_bytes(s)) == s,
{
  assert forall |x: u32|  {
    &&& #[trigger] spec_u32_to_le_bytes(x).len() == 4
    &&& spec_u32_from_le_bytes(spec_u32_to_le_bytes(x)) == x
  } by {
    let s = spec_u32_to_le_bytes(x);
    assert({
      &&& x & 0xff < 256
      &&& (x >> 8) & 0xff < 256
      &&& (x >> 16) & 0xff < 256
      &&& (x >> 24) & 0xff < 256
    }) by (bit_vector);

    assert(x == (
      (x & 0xff) |
      ((x >> 8) & 0xff) << 8 |
      ((x >> 16) & 0xff) << 16 |
      ((x >> 24) & 0xff) << 24)) by (bit_vector);
  };

  assert forall |s: Seq<u8>| s.len() == 4 implies #[trigger] spec_u32_to_le_bytes(spec_u32_from_le_bytes(s)) == s by {
    let x = spec_u32_from_le_bytes(s);
    let s0 = s[0] as u32;
    let s1 = s[1] as u32;
    let s2 = s[2] as u32;
    let s3 = s[3] as u32;

    assert(
      (
        (x == s0 | s1 << 8 | s2 << 16 | s3 << 24) &&
        (s0 < 256) &&
        (s1 < 256) &&
        (s2 < 256) &&
        (s3 < 256)
      ) ==>
      s0 == (x & 0xff) && s1 == ((x >> 8) & 0xff) && s2 == ((x >> 16) & 0xff) && s3 == ((x >> 24) & 0xff)
    ) by (bit_vector);

    assert_seqs_equal!(spec_u32_to_le_bytes(spec_u32_from_le_bytes(s)) == s);
  }
}

#[verifier(external_body)]
pub exec fn u32_from_le_bytes(s: &[u8]) -> (x:u32)
  requires s.dview().len() == 4,
  ensures x == spec_u32_from_le_bytes(s.dview()),
{
  use core::convert::TryInto;
  u32::from_le_bytes(s.try_into().unwrap())
}


#[verifier(external_body)]
pub exec fn u32_to_le_bytes(x: u32) -> (s: alloc::vec::Vec<u8>)
  ensures
    s.dview() == spec_u32_to_le_bytes(x),
    s.dview().len() == 4,
{
  x.to_le_bytes().to_vec()
}

// Conversion between u64 and little-endian byte sequences

pub closed spec fn spec_u64_to_le_bytes(x: u64) -> Seq<u8>
{
  seq![
    (x & 0xff) as u8,
    ((x >> 8) & 0xff) as u8,
    ((x >> 16) & 0xff) as u8,
    ((x >> 24) & 0xff) as u8,
    ((x >> 32) & 0xff) as u8,
    ((x >> 40) & 0xff) as u8,
    ((x >> 48) & 0xff) as u8,
    ((x >> 56) & 0xff) as u8,
  ]
}

pub closed spec fn spec_u64_from_le_bytes(s: Seq<u8>) -> u64
  recommends s.len() == 8
{
  (s[0] as u64) |
  (s[1] as u64) << 8 |
  (s[2] as u64) << 16 |
  (s[3] as u64) << 24 |
  (s[4] as u64) << 32 |
  (s[5] as u64) << 40 |
  (s[6] as u64) << 48 |
  (s[7] as u64) << 56
}

#[verifier::spinoff_prover]
pub proof fn lemma_auto_spec_u64_to_from_le_bytes()
  ensures
    forall |x: u64|
      #![trigger spec_u64_to_le_bytes(x)]
    {
      &&& spec_u64_to_le_bytes(x).len() == 8
      &&& spec_u64_from_le_bytes(spec_u64_to_le_bytes(x)) == x
    },
    forall |s: Seq<u8>|
      #![trigger spec_u64_to_le_bytes(spec_u64_from_le_bytes(s))]
      s.len() == 8 ==> spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s,
{
  assert forall |x: u64|  {
    &&& #[trigger] spec_u64_to_le_bytes(x).len() == 8
    &&& spec_u64_from_le_bytes(spec_u64_to_le_bytes(x)) == x
  } by {
    let s = spec_u64_to_le_bytes(x);
    assert({
      &&& x & 0xff < 256
      &&& (x >> 8) & 0xff < 256
      &&& (x >> 16) & 0xff < 256
      &&& (x >> 24) & 0xff < 256
      &&& (x >> 32) & 0xff < 256
      &&& (x >> 40) & 0xff < 256
      &&& (x >> 48) & 0xff < 256
      &&& (x >> 56) & 0xff < 256
    }) by (bit_vector);

    assert(x == (
      (x & 0xff) |
      ((x >> 8) & 0xff) << 8 |
      ((x >> 16) & 0xff) << 16 |
      ((x >> 24) & 0xff) << 24 |
      ((x >> 32) & 0xff) << 32 |
      ((x >> 40) & 0xff) << 40 |
      ((x >> 48) & 0xff) << 48 |
      ((x >> 56) & 0xff) << 56)) by (bit_vector);
  };

  assert forall |s: Seq<u8>| s.len() == 8 implies #[trigger] spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s by {
    let x = spec_u64_from_le_bytes(s);
    let s0 = s[0] as u64;
    let s1 = s[1] as u64;
    let s2 = s[2] as u64;
    let s3 = s[3] as u64;
    let s4 = s[4] as u64;
    let s5 = s[5] as u64;
    let s6 = s[6] as u64;
    let s7 = s[7] as u64;

    assert(
      (
        (x == s0 | s1 << 8 | s2 << 16 | s3 << 24 | s4 << 32 | s5 << 40 | s6 << 48 | s7 << 56) &&
        (s0 < 256) &&
        (s1 < 256) &&
        (s2 < 256) &&
        (s3 < 256) &&
        (s4 < 256) &&
        (s5 < 256) &&
        (s6 < 256) &&
        (s7 < 256)
      ) ==>
      s0 == (x & 0xff) && s1 == ((x >> 8) & 0xff) && s2 == ((x >> 16) & 0xff) && s3 == ((x >> 24) & 0xff) && s4 == ((x >> 32) & 0xff) && s5 == ((x >> 40) & 0xff) && s6 == ((x >> 48) & 0xff) && s7 == ((x >> 56) & 0xff)
    ) by (bit_vector);

    assert_seqs_equal!(spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s);
  }
}

#[verifier(external_body)]
pub exec fn u64_from_le_bytes(s: &[u8]) -> (x:u64)
  requires s.dview().len() == 8,
  ensures x == spec_u64_from_le_bytes(s.dview()),
{
  use core::convert::TryInto;
  u64::from_le_bytes(s.try_into().unwrap())
}


#[verifier(external_body)]
pub exec fn u64_to_le_bytes(x: u64) -> (s: alloc::vec::Vec<u8>)
  ensures
    s.dview() == spec_u64_to_le_bytes(x),
    s.dview().len() == 8,
{
  x.to_le_bytes().to_vec()
}

// Conversion between u128 and little-endian byte sequences

pub closed spec fn spec_u128_to_le_bytes(x: u128) -> Seq<u8>
{
  seq![
    (x & 0xff) as u8,
    ((x >> 8) & 0xff) as u8,
    ((x >> 16) & 0xff) as u8,
    ((x >> 24) & 0xff) as u8,
    ((x >> 32) & 0xff) as u8,
    ((x >> 40) & 0xff) as u8,
    ((x >> 48) & 0xff) as u8,
    ((x >> 56) & 0xff) as u8,
    ((x >> 64) & 0xff) as u8,
    ((x >> 72) & 0xff) as u8,
    ((x >> 80) & 0xff) as u8,
    ((x >> 88) & 0xff) as u8,
    ((x >> 96) & 0xff) as u8,
    ((x >> 104) & 0xff) as u8,
    ((x >> 112) & 0xff) as u8,
    ((x >> 120) & 0xff) as u8,
  ]
}

pub closed spec fn spec_u128_from_le_bytes(s: Seq<u8>) -> u128
  recommends s.len() == 16
{
  (s[0] as u128) |
  (s[1] as u128) << 8 |
  (s[2] as u128) << 16 |
  (s[3] as u128) << 24 |
  (s[4] as u128) << 32 |
  (s[5] as u128) << 40 |
  (s[6] as u128) << 48 |
  (s[7] as u128) << 56 |
  (s[8] as u128) << 64 |
  (s[9] as u128) << 72 |
  (s[10] as u128) << 80 |
  (s[11] as u128) << 88 |
  (s[12] as u128) << 96 |
  (s[13] as u128) << 104 |
  (s[14] as u128) << 112 |
  (s[15] as u128) << 120
}

#[verifier::spinoff_prover]
pub proof fn lemma_auto_spec_u128_to_from_le_bytes()
  ensures
    forall |x: u128|
    {
      &&& #[trigger] spec_u128_to_le_bytes(x).len() == 16
      &&& spec_u128_from_le_bytes(spec_u128_to_le_bytes(x)) == x
    },
    forall |s: Seq<u8>|
      s.len() == 16 ==> #[trigger] spec_u128_to_le_bytes(spec_u128_from_le_bytes(s)) == s,
{
  assert forall |x: u128|  {
    &&& #[trigger] spec_u128_to_le_bytes(x).len() == 16
    &&& spec_u128_from_le_bytes(spec_u128_to_le_bytes(x)) == x
  } by {
    let s = spec_u128_to_le_bytes(x);
    assert({
      &&& x & 0xff < 256
      &&& (x >> 8) & 0xff < 256
      &&& (x >> 16) & 0xff < 256
      &&& (x >> 24) & 0xff < 256
      &&& (x >> 32) & 0xff < 256
      &&& (x >> 40) & 0xff < 256
      &&& (x >> 48) & 0xff < 256
      &&& (x >> 56) & 0xff < 256
      &&& (x >> 64) & 0xff < 256
      &&& (x >> 72) & 0xff < 256
      &&& (x >> 80) & 0xff < 256
      &&& (x >> 88) & 0xff < 256
      &&& (x >> 96) & 0xff < 256
      &&& (x >> 104) & 0xff < 256
      &&& (x >> 112) & 0xff < 256
      &&& (x >> 120) & 0xff < 256
    }) by (bit_vector);

    assert(x == (
      (x & 0xff) |
      ((x >> 8) & 0xff) << 8 |
      ((x >> 16) & 0xff) << 16 |
      ((x >> 24) & 0xff) << 24 |
      ((x >> 32) & 0xff) << 32 |
      ((x >> 40) & 0xff) << 40 |
      ((x >> 48) & 0xff) << 48 |
      ((x >> 56) & 0xff) << 56 |
      ((x >> 64) & 0xff) << 64 |
      ((x >> 72) & 0xff) << 72 |
      ((x >> 80) & 0xff) << 80 |
      ((x >> 88) & 0xff) << 88 |
      ((x >> 96) & 0xff) << 96 |
      ((x >> 104) & 0xff) << 104 |
      ((x >> 112) & 0xff) << 112 |
      ((x >> 120) & 0xff) << 120)) by (bit_vector);
  };

  assert forall |s: Seq<u8>| s.len() == 16 implies #[trigger] spec_u128_to_le_bytes(spec_u128_from_le_bytes(s)) == s by {
    let x = spec_u128_from_le_bytes(s);
    let s0 = s[0] as u128;
    let s1 = s[1] as u128;
    let s2 = s[2] as u128;
    let s3 = s[3] as u128;
    let s4 = s[4] as u128;
    let s5 = s[5] as u128;
    let s6 = s[6] as u128;
    let s7 = s[7] as u128;
    let s8 = s[8] as u128;
    let s9 = s[9] as u128;
    let s10 = s[10] as u128;
    let s11 = s[11] as u128;
    let s12 = s[12] as u128;
    let s13 = s[13] as u128;
    let s14 = s[14] as u128;
    let s15 = s[15] as u128;

    assert(
      (
        (x == s0 | s1 << 8 | s2 << 16 | s3 << 24 | s4 << 32 | s5 << 40 | s6 << 48 | s7 << 56 | s8 << 64
                 | s9 << 72 | s10 << 80 | s11 << 88 | s12 << 96 | s13 << 104 | s14 << 112 | s15 << 120) &&
        (s0 < 256) &&
        (s1 < 256) &&
        (s2 < 256) &&
        (s3 < 256) &&
        (s4 < 256) &&
        (s5 < 256) &&
        (s6 < 256) &&
        (s7 < 256) &&
        (s8 < 256) &&
        (s9 < 256) &&
        (s10 < 256) &&
        (s11 < 256) &&
        (s12 < 256) &&
        (s13 < 256) &&
        (s14 < 256) &&
        (s15 < 256)
      ) ==>
      s0 == (x & 0xff) && s1 == ((x >> 8) & 0xff) && s2 == ((x >> 16) & 0xff) && s3 == ((x >> 24) & 0xff) && s4 == ((x >> 32) & 0xff) && s5 == ((x >> 40) & 0xff) && s6 == ((x >> 48) & 0xff) && s7 == ((x >> 56) & 0xff) && s8 == ((x >> 64) & 0xff) && s9 == ((x >> 72) & 0xff) && s10 == ((x >> 80) & 0xff) && s11 == ((x >> 88) & 0xff) && s12 == ((x >> 96) & 0xff) && s13 == ((x >> 104) & 0xff) && s14 == ((x >> 112) & 0xff) && s15 == ((x >> 120) & 0xff)
    ) by (bit_vector);

    assert_seqs_equal!(spec_u128_to_le_bytes(spec_u128_from_le_bytes(s)) == s);
  }
}

#[verifier(external_body)]
pub exec fn u128_from_le_bytes(s: &[u8]) -> (x:u128)
  requires s.dview().len() == 16,
  ensures x == spec_u128_from_le_bytes(s.dview()),
{
  use core::convert::TryInto;
  u128::from_le_bytes(s.try_into().unwrap())
}


#[verifier(external_body)]
pub exec fn u128_to_le_bytes(x: u128) -> (s: alloc::vec::Vec<u8>)
  ensures
    s.dview() == spec_u128_to_le_bytes(x),
    s.dview().len() == 16,
{
  x.to_le_bytes().to_vec()
}
}

use vstd::calc_macro::*;

verus! {

    pub open spec fn spec_parse_u8_le(s: SpecStream) -> (res: SpecParseResult<u8>)
        recommends
            0 <= s.start < s.data.len(),
            s.data.len() >= 1
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 1 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 1,
                    ..s
                },
                1,
                s.data[s.start],
            ))
        }
    }

    pub open spec fn spec_parse_u16_le(s: SpecStream) -> (res: SpecParseResult<u16>)
        recommends
            0 <= s.start < s.data.len() - 1,
            s.data.len() >= 2
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 2 || s.start >= s.data.len() - 1 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 2,
                    ..s
                },
                2,
                spec_u16_from_le_bytes(
                    s.data.subrange(s.start, s.start + 2)
                )
            ))
        }
    }

    pub open spec fn spec_parse_u32_le(s: SpecStream) -> (res: SpecParseResult<u32>)
        recommends
            0 <= s.start < s.data.len() - 3,
            s.data.len() >= 4
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 4 || s.start >= s.data.len() - 3 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 4,
                    ..s
                },
                4,
                spec_u32_from_le_bytes(
                    s.data.subrange(s.start, s.start + 4)
                )
            ))
        }
    }

    pub open spec fn spec_parse_u64_le(s: SpecStream) -> (res: SpecParseResult<u64>)
        recommends
            0 <= s.start < s.data.len() - 7,
            s.data.len() >= 8
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 8 || s.start >= s.data.len() - 7 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 8,
                    ..s
                },
                8,
                spec_u64_from_le_bytes(
                    s.data.subrange(s.start, s.start + 8)
                )
            ))
        }
    }

    pub open spec fn spec_serialize_u8_le(s: SpecStream, v: u8) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len(),
            s.data.len() >= 1
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 1 || s.start >= s.data.len() {
            Err(SerializeError::NotEnoughSpace)
        } else {
            Ok((
                SpecStream {
                    data: s.data.update(s.start, v),
                    start: s.start + 1,
                },
                1
            ))
        }
    }

    pub open spec fn spec_serialize_u16_le(s: SpecStream, v: u16) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len() - 1,
            s.data.len() >= 2
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 2 || s.start >= s.data.len() - 1 {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let data = spec_u16_to_le_bytes(v);
            Ok((
                SpecStream {
                    data: s.data.update(s.start, data[0])
                                .update(s.start + 1, data[1]),
                    start: s.start + 2,
                },
                2
            ))
        }
    }

    pub open spec fn spec_serialize_u32_le(s: SpecStream, v: u32) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len() - 3,
            s.data.len() >= 4
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 4 || s.start >= s.data.len() - 3 {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let data = spec_u32_to_le_bytes(v);
            Ok((
                SpecStream {
                    data: s.data.update(s.start, data[0])
                                .update(s.start + 1, data[1])
                                .update(s.start + 2, data[2])
                                .update(s.start + 3, data[3]),
                    start: s.start + 4,
                },
                4
            ))
        }
    }

    pub open spec fn spec_serialize_u64_le(s: SpecStream, v: u64) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len() - 7,
            s.data.len() >= 8
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 8 || s.start >= s.data.len() - 7 {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let data = spec_u64_to_le_bytes(v);
            Ok((
                SpecStream {
                    data: s.data.update(s.start, data[0])
                                .update(s.start + 1, data[1])
                                .update(s.start + 2, data[2])
                                .update(s.start + 3, data[3])
                                .update(s.start + 4, data[4])
                                .update(s.start + 5, data[5])
                                .update(s.start + 6, data[6])
                                .update(s.start + 7, data[7]),
                    start: s.start + 8,
                },
                8
            ))
        }
    }


    pub exec fn parse_u8_le(s: Stream) -> (res: ParseResult<u8>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 1 {
            Err(ParseError::NotEnoughData)
        } else {
            let v = *vec_index(&s.data, s.start); // s.data[s.start];
            Ok((
                Stream {
                    start: s.start + 1,
                    ..s
                },
                1,
                v
            ))
        }
    }

    pub exec fn parse_u16_le(s: Stream) -> (res: ParseResult<u16>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u16_le(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 2 || s.start >= s.data.length() - 1 {
            Err(ParseError::NotEnoughData)
        } else {
            let data = slice_subrange(vec_as_slice(&s.data), s.start, s.start + 2); // &s.data[s.start..s.start + 2];
            let v = u16_from_le_bytes(data);
            Ok((
                Stream {
                    start: s.start + 2,
                    ..s
                },
                2,
                v
            ))
        }
    }

    pub exec fn parse_u32_le(s: Stream) -> (res: ParseResult<u32>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u32_le(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 4 || s.start >= s.data.length() - 3 {
            Err(ParseError::NotEnoughData)
        } else {
            let data = slice_subrange(vec_as_slice(&s.data), s.start, s.start + 4); // &s.data[s.start..s.start + 4];
            let v = u32_from_le_bytes(data);
            Ok((
                Stream {
                    start: s.start + 4,
                    ..s
                },
                4,
                v
            ))
        }
    }

    pub exec fn parse_u64_le(s: Stream) -> (res: ParseResult<u64>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u64_le(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 8 || s.start >= s.data.length() - 7 {
            Err(ParseError::NotEnoughData)
        } else {
            let data = slice_subrange(vec_as_slice(&s.data), s.start, s.start + 8); // &s.data[s.start..s.start + 8];
            let v = u64_from_le_bytes(data);
            Ok((
                Stream {
                    start: s.start + 8,
                    ..s
                },
                8,
                v
            ))
        }
    }

    pub exec fn serialize_u8_le(s: Stream, v: u8) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v))
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.length() < 1 || s.start >= s.data.length() {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let mut s = s;
            s.data.set(s.start, v);
            s.start = s.start + 1;
            // assert(sres.is_ok());
            // assert(sres.unwrap().1 == 1);
            // assert(sres.unwrap().0 =~= s@);
            Ok((
                s,
                1
            ))
        }
    }

    pub exec fn serialize_u16_le(s: Stream, v: u16) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u16_le(s, v))
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.length() < 2 || s.start >= s.data.length() - 1  {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let mut s = s;
            let data = u16_to_le_bytes(v);
            s.data.set(s.start, *vec_index(&data, 0)); // s.data[s.start] = data[0];
            s.data.set(s.start + 1, *vec_index(&data, 1)); // s.data[s.start + 1] = data[1];
            s.start = s.start + 2;
            Ok((
                s,
                2
            ))
        }
    }

    pub exec fn serialize_u32_le(s: Stream, v: u32) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u32_le(s, v))
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.length() < 4 || s.start >= s.data.length() - 3  {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let mut s = s;
            let data = u32_to_le_bytes(v);
            s.data.set(s.start, *vec_index(&data, 0)); // s.data[s.start] = data[0];
            s.data.set(s.start + 1, *vec_index(&data, 1)); // s.data[s.start + 1] = data[1];
            s.data.set(s.start + 2, *vec_index(&data, 2)); // s.data[s.start + 2] = data[2];
            s.data.set(s.start + 3, *vec_index(&data, 3)); // s.data[s.start + 3] = data[3];
            s.start = s.start + 4;
            Ok((
                s,
                4
            ))
        }
    }

    pub exec fn serialize_u64_le(s: Stream, v: u64) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u64_le(s, v))
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.length() < 8 || s.start >= s.data.length() - 7  {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let mut s = s;
            let data = u64_to_le_bytes(v);
            s.data.set(s.start, *vec_index(&data, 0)); // s.data[s.start] = data[0];
            s.data.set(s.start + 1, *vec_index(&data, 1)); // s.data[s.start + 1] = data[1];
            s.data.set(s.start + 2, *vec_index(&data, 2)); // s.data[s.start + 2] = data[2];
            s.data.set(s.start + 3, *vec_index(&data, 3)); // s.data[s.start + 3] = data[3];
            s.data.set(s.start + 4, *vec_index(&data, 4)); // s.data[s.start + 4] = data[4];
            s.data.set(s.start + 5, *vec_index(&data, 5)); // s.data[s.start + 5] = data[5];
            s.data.set(s.start + 6, *vec_index(&data, 6)); // s.data[s.start + 6] = data[6];
            s.data.set(s.start + 7, *vec_index(&data, 7)); // s.data[s.start + 7] = data[7];
            s.start = s.start + 8;
            Ok((
                s,
                8
            ))
        }
    }

    pub proof fn lemma_parse_u8_le_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u8_le(s))
    {
        reveal(prop_parse_well_behaved::<u8>);
        let spec_parse_u8_le = |s| spec_parse_u8_le(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u8_le, s) by {
            lemma_parse_u8_le_well_behaved_on(s)
        }
    }

    pub proof fn lemma_parse_u16_le_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u16_le(s))
    {
        reveal(prop_parse_well_behaved::<u16>);
        let spec_parse_u16_le = |s| spec_parse_u16_le(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u16_le, s) by {
            lemma_parse_u16_le_well_behaved_on(s)
        }
    }

    pub proof fn lemma_parse_u32_le_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u32_le(s))
    {
        reveal(prop_parse_well_behaved::<u32>);
        let spec_parse_u32_le = |s| spec_parse_u32_le(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u32_le, s) by {
            lemma_parse_u32_le_well_behaved_on(s)
        }
    }

    pub proof fn lemma_parse_u64_le_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u64_le(s))
    {
        reveal(prop_parse_well_behaved::<u64>);
        let spec_parse_u64_le = |s| spec_parse_u64_le(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u64_le, s) by {
            lemma_parse_u64_le_well_behaved_on(s)
        }
    }

    pub proof fn lemma_serialize_u8_le_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u8_le(s, v))
    {
        reveal(prop_serialize_well_behaved::<u8>);
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u8_le, s, v) by {
            lemma_serialize_u8_le_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_u16_le_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u16_le(s, v))
    {
        reveal(prop_serialize_well_behaved::<u16>);
        let spec_serialize_u16_le = |s, v| spec_serialize_u16_le(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u16_le, s, v) by {
            lemma_serialize_u16_le_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_u32_le_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u32_le(s, v))
    {
        reveal(prop_serialize_well_behaved::<u32>);
        let spec_serialize_u32_le = |s, v| spec_serialize_u32_le(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u32_le, s, v) by {
            lemma_serialize_u32_le_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_u64_le_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u64_le(s, v))
    {
        reveal(prop_serialize_well_behaved::<u64>);
        let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u64_le, s, v) by {
            lemma_serialize_u64_le_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_u8_le_deterministic()
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_u8_le(s, v))
    {
        reveal(prop_serialize_deterministic::<u8>);
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u8_le, s1, s2, v) by {
            lemma_serialize_u8_le_deterministic_on(s1, s2, v)
        }
    }

    pub proof fn lemma_serialize_u16_le_deterministic()
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_u16_le(s, v))
    {
        reveal(prop_serialize_deterministic::<u16>);
        let spec_serialize_u16_le = |s, v| spec_serialize_u16_le(s, v);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u16_le, s1, s2, v) by {
            lemma_serialize_u16_le_deterministic_on(s1, s2, v)
        }
    }

    pub proof fn lemma_serialize_u32_le_deterministic()
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_u32_le(s, v))
    {
        reveal(prop_serialize_deterministic::<u32>);
        let spec_serialize_u32_le = |s, v| spec_serialize_u32_le(s, v);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u32_le, s1, s2, v) by {
            lemma_serialize_u32_le_deterministic_on(s1, s2, v)
        }
    }

    pub proof fn lemma_serialize_u64_le_deterministic()
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_u64_le(s, v))
    {
        reveal(prop_serialize_deterministic::<u64>);
        let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_u64_le, s1, s2, v) by {
            lemma_serialize_u64_le_deterministic_on(s1, s2, v)
        }
    }

    pub proof fn lemma_parse_u8_le_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u8_le(s))
    {
        reveal(prop_parse_strong_prefix::<u8>);
        let spec_parse_u8_le = |s| spec_parse_u8_le(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u8_le, s1, s2) by {
            lemma_parse_u8_le_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u16_le_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u16_le(s))
    {
        reveal(prop_parse_strong_prefix::<u16>);
        let spec_parse_u16_le = |s| spec_parse_u16_le(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u16_le, s1, s2) by {
            lemma_parse_u16_le_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u32_le_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u32_le(s))
    {
        reveal(prop_parse_strong_prefix::<u32>);
        let spec_parse_u32_le = |s| spec_parse_u32_le(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u32_le, s1, s2) by {
            lemma_parse_u32_le_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u64_le_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u64_le(s))
    {
        reveal(prop_parse_strong_prefix::<u64>);
        let spec_parse_u64_le = |s| spec_parse_u64_le(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u64_le, s1, s2) by {
            lemma_parse_u64_le_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u8_le_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u8_le(s), |s, v| spec_serialize_u8_le(s, v))
    {
        reveal(prop_parse_correct::<u8>);
        let spec_parse_u8_le = |s| spec_parse_u8_le(s);
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u8_le, spec_serialize_u8_le, s, v) by {
            lemma_parse_u8_le_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u16_le_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u16_le(s), |s, v| spec_serialize_u16_le(s, v))
    {
        reveal(prop_parse_correct::<u16>);
        let spec_parse_u16_le = |s| spec_parse_u16_le(s);
        let spec_serialize_u16_le = |s, v| spec_serialize_u16_le(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u16_le, spec_serialize_u16_le, s, v) by {
            lemma_parse_u16_le_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u32_le_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u32_le(s), |s, v| spec_serialize_u32_le(s, v))
    {
        reveal(prop_parse_correct::<u32>);
        let spec_parse_u32_le = |s| spec_parse_u32_le(s);
        let spec_serialize_u32_le = |s, v| spec_serialize_u32_le(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u32_le, spec_serialize_u32_le, s, v) by {
            lemma_parse_u32_le_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u64_le_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u64_le(s), |s, v| spec_serialize_u64_le(s, v))
    {
        reveal(prop_parse_correct::<u64>);
        let spec_parse_u64_le = |s| spec_parse_u64_le(s);
        let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u64_le, spec_serialize_u64_le, s, v) by {
            lemma_parse_u64_le_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u8_le_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_u8_le(s), |s, v| spec_serialize_u8_le(s, v))
    {
        reveal(prop_parse_serialize_inverse::<u8>);
        let spec_parse_u8_le = |s| spec_parse_u8_le(s);
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, s) by {
            lemma_parse_u8_le_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_u16_le_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_u16_le(s), |s, v| spec_serialize_u16_le(s, v))
    {
        reveal(prop_parse_serialize_inverse::<u16>);
        let spec_parse_u16_le = |s| spec_parse_u16_le(s);
        let spec_serialize_u16_le = |s, v| spec_serialize_u16_le(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u16_le, spec_serialize_u16_le, s) by {
            lemma_parse_u16_le_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_u32_le_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_u32_le(s), |s, v| spec_serialize_u32_le(s, v))
    {
        reveal(prop_parse_serialize_inverse::<u32>);
        let spec_parse_u32_le = |s| spec_parse_u32_le(s);
        let spec_serialize_u32_le = |s, v| spec_serialize_u32_le(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u32_le, spec_serialize_u32_le, s) by {
            lemma_parse_u32_le_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_u64_le_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_u64_le(s), |s, v| spec_serialize_u64_le(s, v))
    {
        reveal(prop_parse_serialize_inverse::<u64>);
        let spec_parse_u64_le = |s| spec_parse_u64_le(s);
        let spec_serialize_u64_le = |s, v| spec_serialize_u64_le(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u64_le, spec_serialize_u64_le, s) by {
            lemma_parse_u64_le_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_u8_le_nonmalleable()
        ensures
            prop_parse_nonmalleable(|s| spec_parse_u8_le(s))
    {
        lemma_parse_u8_le_serialize_inverse();
        lemma_serialize_u8_le_deterministic();
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u8_le(s), |s, v| spec_serialize_u8_le(s, v));
    }

    pub proof fn lemma_parse_u16_le_nonmalleable()
        ensures
            prop_parse_nonmalleable(|s| spec_parse_u16_le(s))
    {
        lemma_parse_u16_le_serialize_inverse();
        lemma_serialize_u16_le_deterministic();
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u16_le(s), |s, v| spec_serialize_u16_le(s, v));
    }

    pub proof fn lemma_parse_u32_le_nonmalleable()
        ensures
            prop_parse_nonmalleable(|s| spec_parse_u32_le(s))
    {
        lemma_parse_u32_le_serialize_inverse();
        lemma_serialize_u32_le_deterministic();
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u32_le(s), |s, v| spec_serialize_u32_le(s, v));
    }

    pub proof fn lemma_parse_u64_le_nonmalleable()
        ensures
            prop_parse_nonmalleable(|s| spec_parse_u64_le(s))
    {
        lemma_parse_u64_le_serialize_inverse();
        lemma_serialize_u64_le_deterministic();
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_u64_le(s), |s, v| spec_serialize_u64_le(s, v));
    }

    proof fn lemma_parse_u8_le_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u8_le(s), s)
    {}

    proof fn lemma_parse_u16_le_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u16_le(s), s)
    {}

    proof fn lemma_parse_u32_le_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u32_le(s), s)
    {}

    proof fn lemma_parse_u64_le_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u64_le(s), s)
    {}

    proof fn lemma_parse_u8_le_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u8_le(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u8_le(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u8_le(s2) {
                    assert(n == 1);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            s1.data[s1.start]; {}
                            s1.data.subrange(s1.start, s1.start + 1)[0]; {}
                            s2.data.subrange(s2.start, s2.start + 1)[0]; {}
                            s2.data[s2.start]; {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_parse_u16_le_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u16_le(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u16_le(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u16_le(s2) {
                    assert(n == 2);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            spec_u16_from_le_bytes(s1.data.subrange(s1.start, s1.start + 2)); {}
                            spec_u16_from_le_bytes(s2.data.subrange(s2.start, s2.start + 2)); {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_parse_u32_le_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u32_le(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u32_le(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u32_le(s2) {
                    assert(n == 4);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            spec_u32_from_le_bytes(s1.data.subrange(s1.start, s1.start + 4)); {}
                            spec_u32_from_le_bytes(s2.data.subrange(s2.start, s2.start + 4)); {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_parse_u64_le_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u64_le(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u64_le(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u64_le(s2) {
                    assert(n == 8);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            spec_u64_from_le_bytes(s1.data.subrange(s1.start, s1.start + 8)); {}
                            spec_u64_from_le_bytes(s2.data.subrange(s2.start, s2.start + 8)); {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_serialize_u8_le_well_behaved_on(s: SpecStream, v: u8)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u8_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u8_le(s, v) {
            assert(n == 1 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 1, s.data.len() as int) =~= s.data.subrange(s.start + 1, s.data.len() as int));
        }
    }

    proof fn lemma_serialize_u16_le_well_behaved_on(s: SpecStream, v: u16)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u16_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u16_le(s, v) {
            lemma_auto_spec_u16_to_from_le_bytes();
            assert(n == 2 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 2, s.data.len() as int) =~= s.data.subrange(s.start + 2, s.data.len() as int));
        }
    }

    proof fn lemma_serialize_u32_le_well_behaved_on(s: SpecStream, v: u32)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u32_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u32_le(s, v) {
            lemma_auto_spec_u32_to_from_le_bytes();
            assert(n == 4 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 4, s.data.len() as int) =~= s.data.subrange(s.start + 4, s.data.len() as int));
        }
    }

    proof fn lemma_serialize_u64_le_well_behaved_on(s: SpecStream, v: u64)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u64_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u64_le(s, v) {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(n == 8 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 8, s.data.len() as int) =~= s.data.subrange(s.start + 8, s.data.len() as int));
        }
    }

    proof fn lemma_serialize_u8_le_deterministic_on(s1: SpecStream, s2: SpecStream, v: u8)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_u8_le(s, v), s1, s2, v)
    {
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_u8_le(s1, v), spec_serialize_u8_le(s2, v)) {
            assert(n1 == 1 && n2 == 1);
            assert(sout1.data.subrange(s1.start, s1.start + 1) =~= sout2.data.subrange(s2.start, s2.start + 1));
        }
    }

    proof fn lemma_serialize_u16_le_deterministic_on(s1: SpecStream, s2: SpecStream, v: u16)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_u16_le(s, v), s1, s2, v)
    {
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_u16_le(s1, v), spec_serialize_u16_le(s2, v)) {
            lemma_auto_spec_u16_to_from_le_bytes();
            assert(n1 == 2 && n2 == 2);
            assert(sout1.data.subrange(s1.start, s1.start + 2) =~= sout2.data.subrange(s2.start, s2.start + 2));
        }
    }

    proof fn lemma_serialize_u32_le_deterministic_on(s1: SpecStream, s2: SpecStream, v: u32)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_u32_le(s, v), s1, s2, v)
    {
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_u32_le(s1, v), spec_serialize_u32_le(s2, v)) {
            lemma_auto_spec_u32_to_from_le_bytes();
            assert(n1 == 4 && n2 == 4);
            assert(sout1.data.subrange(s1.start, s1.start + 4) =~= sout2.data.subrange(s2.start, s2.start + 4));
        }
    }

    proof fn lemma_serialize_u64_le_deterministic_on(s1: SpecStream, s2: SpecStream, v: u64)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_u64_le(s, v), s1, s2, v)
    {
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_u64_le(s1, v), spec_serialize_u64_le(s2, v)) {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(n1 == 8 && n2 == 8);
            assert(sout1.data.subrange(s1.start, s1.start + 8) =~= sout2.data.subrange(s2.start, s2.start + 8));
        }
    }

    proof fn lemma_parse_u8_le_correct_on(s: SpecStream, v: u8)
        ensures
            prop_parse_correct_on(|s| spec_parse_u8_le(s), |s, v| spec_serialize_u8_le(s, v), s, v)
    {}

    proof fn lemma_parse_u16_le_correct_on(s: SpecStream, v: u16)
        ensures
            prop_parse_correct_on(|s| spec_parse_u16_le(s), |s, v| spec_serialize_u16_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u16_le(s, v) {
            assert(sout.data.len() == s.data.len()) by { lemma_serialize_u16_le_well_behaved_on(s, v)}
            if let Ok((_, m, res)) = spec_parse_u16_le(SpecStream {start: s.start, ..sout}) {
                lemma_auto_spec_u16_to_from_le_bytes();
                assert(n == m);
                assert(res == spec_u16_from_le_bytes(sout.data.subrange(s.start, s.start + 2)));
                assert(sout.data.subrange(s.start, s.start + 2) =~= spec_u16_to_le_bytes(v));
                assert(v =~= res);
            }
        }
    }

    proof fn lemma_parse_u32_le_correct_on(s: SpecStream, v: u32)
        ensures
            prop_parse_correct_on(|s| spec_parse_u32_le(s), |s, v| spec_serialize_u32_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u32_le(s, v) {
            assert(sout.data.len() == s.data.len()) by { lemma_serialize_u32_le_well_behaved_on(s, v)}
            if let Ok((_, m, res)) = spec_parse_u32_le(SpecStream {start: s.start, ..sout}) {
                lemma_auto_spec_u32_to_from_le_bytes();
                assert(n == m);
                assert(res == spec_u32_from_le_bytes(sout.data.subrange(s.start, s.start + 4)));
                assert(sout.data.subrange(s.start, s.start + 4) =~= spec_u32_to_le_bytes(v));
                assert(v =~= res);
            }
        }
    }

    proof fn lemma_parse_u64_le_correct_on(s: SpecStream, v: u64)
        ensures
            prop_parse_correct_on(|s| spec_parse_u64_le(s), |s, v| spec_serialize_u64_le(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u64_le(s, v) {
            assert(sout.data.len() == s.data.len()) by { lemma_serialize_u64_le_well_behaved_on(s, v)}
            if let Ok((_, m, res)) = spec_parse_u64_le(SpecStream {start: s.start, ..sout}) {
                lemma_auto_spec_u64_to_from_le_bytes();
                assert(n == m);
                assert(res == spec_u64_from_le_bytes(sout.data.subrange(s.start, s.start + 8)));
                assert(sout.data.subrange(s.start, s.start + 8) =~= spec_u64_to_le_bytes(v));
                assert(v =~= res);
            }
        }
    }

    proof fn lemma_parse_u8_le_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_u8_le(s), |s, v| spec_serialize_u8_le(s, v), s)
    {
        if let Ok((ss, m, res)) = spec_parse_u8_le(s) {
            if let Ok((sout, n)) = spec_serialize_u8_le(s, res) {
                assert(n == m && sout.data =~= s.data);
            }
        }
    }

    proof fn lemma_parse_u16_le_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_u16_le(s), |s, v| spec_serialize_u16_le(s, v), s)
    {
        if let Ok((ss, m, res)) = spec_parse_u16_le(s) {
            if let Ok((sout, n)) = spec_serialize_u16_le(s, res) {
                assert(n == m && sout.data =~= s.data) by {
                    lemma_auto_spec_u16_to_from_le_bytes();
                }
            }
        }
    }

    proof fn lemma_parse_u32_le_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_u32_le(s), |s, v| spec_serialize_u32_le(s, v), s)
    {
        if let Ok((ss, m, res)) = spec_parse_u32_le(s) {
            if let Ok((sout, n)) = spec_serialize_u32_le(s, res) {
                assert(n == m && sout.data =~= s.data) by {
                    lemma_auto_spec_u32_to_from_le_bytes();
                }
            }
        }
    }

    proof fn lemma_parse_u64_le_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_u64_le(s), |s, v| spec_serialize_u64_le(s, v), s)
    {
        if let Ok((ss, m, res)) = spec_parse_u64_le(s) {
            if let Ok((sout, n)) = spec_serialize_u64_le(s, res) {
                assert(n == m && sout.data =~= s.data) by {
                    lemma_auto_spec_u64_to_from_le_bytes();
                }
            }
        }
    }

    pub open spec fn spec_parse_u8_be(s: SpecStream) -> (res: SpecParseResult<u8>)
        recommends
            0 <= s.start < s.data.len(),
            s.data.len() >= 1
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 1 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 1,
                    ..s
                },
                1,
                s.data[s.start],
            ))
        }
    }

    pub open spec fn spec_parse_u16_be(s: SpecStream) -> (res: SpecParseResult<u16>)
        recommends
            0 <= s.start < s.data.len() - 1,
            s.data.len() >= 2
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 2 || s.start >= s.data.len() - 1 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 2,
                    ..s
                },
                2,
                (s.data[s.start] * 256 + s.data[s.start + 1]) as u16,
            ))
        }
    }

    pub open spec fn spec_parse_u32_be(s: SpecStream) -> (res: SpecParseResult<u32>)
        recommends
            0 <= s.start < s.data.len() - 3,
            s.data.len() >= 4
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.len() {
            Err(ParseError::Eof)
        } else if s.data.len() < 4 || s.start >= s.data.len() - 3 {
            Err(ParseError::NotEnoughData)
        } else {
            Ok((
                SpecStream {
                    start: s.start + 4,
                    ..s
                },
                4,
                (s.data[s.start] * 256 * 256 * 256
                    + s.data[s.start + 1] * 256 * 256
                    + s.data[s.start + 2] * 256
                    + s.data[s.start + 3]) as u32,
            ))
        }
    }

    pub open spec fn spec_serialize_u8_be(s: SpecStream, v: u8) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len(),
            s.data.len() >= 1
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 1 || s.start >= s.data.len() {
            Err(SerializeError::NotEnoughSpace)
        } else {
            Ok((
                SpecStream {
                    data: s.data.update(s.start, v),
                    start: s.start + 1,
                },
                1
            ))
        }
    }

    pub open spec fn spec_serialize_u16_be(s: SpecStream, v: u16) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len() - 1,
            s.data.len() >= 2
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 2 || s.start >= s.data.len() - 1 {
            Err(SerializeError::NotEnoughSpace)
        } else {
            Ok((
                SpecStream {
                    data: s.data.update(s.start, (v / 256) as u8)
                                .update(s.start + 1, (v % 256) as u8),
                    start: s.start + 2,
                },
                2
            ))
        }
    }

    pub open spec fn spec_serialize_u32_be(s: SpecStream, v: u32) -> SpecSerializeResult
        recommends
            0 <= s.start < s.data.len() - 3,
            s.data.len() >= 4
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.len() < 4 || s.start >= s.data.len() - 3 {
            Err(SerializeError::NotEnoughSpace)
        } else {
            Ok((
                SpecStream {
                    data: s.data.update(s.start, (v / 256 / 256 / 256) as u8)
                                .update(s.start + 1, ((v / 256 / 256) % 256) as u8)
                                .update(s.start + 2, ((v / 256) % 256) as u8)
                                .update(s.start + 3, (v % 256) as u8),
                    start: s.start + 4,
                },
                4
            ))
        }
    }

    pub exec fn parse_u8_be(s: Stream) -> (res: ParseResult<u8>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_be(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 1 {
            Err(ParseError::NotEnoughData)
        } else {
            let v = *vec_index(&s.data, s.start);
            Ok((
                Stream {
                    start: s.start + 1,
                    ..s
                },
                1,
                v
            ))
        }
    }

    pub exec fn parse_u16_be(s: Stream) -> (res: ParseResult<u16>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u16_be(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 2 || s.start >= s.data.length() - 1 {
            Err(ParseError::NotEnoughData)
        } else {
            let v = (*vec_index(&s.data, s.start) as u16 * 256 + *vec_index(&s.data, s.start + 1) as u16);
            Ok((
                Stream {
                    start: s.start + 2,
                    ..s
                },
                2,
                v
            ))
        }
    }

    pub exec fn parse_u32_be(s: Stream) -> (res: ParseResult<u32>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u32_be(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start >= s.data.length() {
            Err(ParseError::Eof)
        } else if s.data.length() < 4 || s.start >= s.data.length() - 3 {
            Err(ParseError::NotEnoughData)
        } else {
            let v = (*vec_index(&s.data, s.start) as u32 * 256 * 256 * 256
                + *vec_index(&s.data, s.start + 1) as u32 * 256 * 256
                + *vec_index(&s.data, s.start + 2) as u32 * 256
                + *vec_index(&s.data, s.start + 3) as u32);
            Ok((
                Stream {
                    start: s.start + 4,
                    ..s
                },
                4,
                v
            ))
        }
    }

    pub exec fn serialize_u8_be(s: Stream, v: u8) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_be(s, v))
    {
        // let ghost sres = spec_serialize_u8_be(s@, v);
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.length() < 1 || s.start >= s.data.length() {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let mut s = s;
            s.data.set(s.start, v);
            s.start = s.start + 1;
            // assert(sres.is_ok());
            // assert(sres.unwrap().1 == 1);
            // assert(sres.unwrap().0 =~= s@);
            Ok((
                s,
                1
            ))
        }
    }

    pub exec fn serialize_u16_be(s: Stream, v: u16) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u16_be(s, v))
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.length() < 2 || s.start >= s.data.length() - 1  {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let mut s = s;
            s.data.set(s.start, (v / 256) as u8);
            s.data.set(s.start + 1, (v % 256) as u8);
            s.start = s.start + 2;
            Ok((
                s,
                2
            ))
        }
    }

    pub exec fn serialize_u32_be(s: Stream, v: u32) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u32_be(s, v))
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.data.length() < 4 || s.start >= s.data.length() - 3  {
            Err(SerializeError::NotEnoughSpace)
        } else {
            let mut s = s;
            s.data.set(s.start, (v / 256 / 256 / 256) as u8);
            s.data.set(s.start + 1, (v / 256 / 256 % 256) as u8);
            s.data.set(s.start + 2, (v / 256 % 256) as u8);
            s.data.set(s.start + 3, (v % 256) as u8);
            s.start = s.start + 4;
            Ok((
                s,
                4
            ))
        }
    }

    pub proof fn lemma_parse_u8_be_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u8_be(s))
    {
        reveal(prop_parse_well_behaved::<u8>);
        let spec_parse_u8_be = |s| spec_parse_u8_be(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u8_be, s) by {
            lemma_parse_u8_be_well_behaved_on(s)
        }
    }

    pub proof fn lemma_parse_u16_be_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u16_be(s))
    {
        reveal(prop_parse_well_behaved::<u16>);
        let spec_parse_u16_be = |s| spec_parse_u16_be(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u16_be, s) by {
            lemma_parse_u16_be_well_behaved_on(s)
        }
    }

    pub proof fn lemma_parse_u32_be_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_u32_be(s))
    {
        reveal(prop_parse_well_behaved::<u32>);
        let spec_parse_u32_be = |s| spec_parse_u32_be(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_u32_be, s) by {
            lemma_parse_u32_be_well_behaved_on(s)
        }
    }

    pub proof fn lemma_serialize_u8_be_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u8_be(s, v))
    {
        reveal(prop_serialize_well_behaved::<u8>);
        let spec_serialize_u8_be = |s, v| spec_serialize_u8_be(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u8_be, s, v) by {
            lemma_serialize_u8_be_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_u16_be_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u16_be(s, v))
    {
        reveal(prop_serialize_well_behaved::<u16>);
        let spec_serialize_u16_be = |s, v| spec_serialize_u16_be(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u16_be, s, v) by {
            lemma_serialize_u16_be_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_u32_be_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_u32_be(s, v))
    {
        reveal(prop_serialize_well_behaved::<u32>);
        let spec_serialize_u32_be = |s, v| spec_serialize_u32_be(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_u32_be, s, v) by {
            lemma_serialize_u32_be_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_parse_u8_be_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u8_be(s))
    {
        reveal(prop_parse_strong_prefix::<u8>);
        let spec_parse_u8_be = |s| spec_parse_u8_be(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u8_be, s1, s2) by {
            lemma_parse_u8_be_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u16_be_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u16_be(s))
    {
        reveal(prop_parse_strong_prefix::<u16>);
        let spec_parse_u16_be = |s| spec_parse_u16_be(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u16_be, s1, s2) by {
            lemma_parse_u16_be_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u32_be_strong_prefix()
        ensures
            prop_parse_strong_prefix(|s| spec_parse_u32_be(s))
    {
        reveal(prop_parse_strong_prefix::<u32>);
        let spec_parse_u32_be = |s| spec_parse_u32_be(s);
        assert forall |s1, s2| #[trigger] prop_parse_strong_prefix_on(spec_parse_u32_be, s1, s2) by {
            lemma_parse_u32_be_strong_prefix_on(s1, s2)
        }
    }

    pub proof fn lemma_parse_u8_be_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u8_be(s), |s, v| spec_serialize_u8_be(s, v))
    {
        reveal(prop_parse_correct::<u8>);
        let spec_parse_u8_be = |s| spec_parse_u8_be(s);
        let spec_serialize_u8_be = |s, v| spec_serialize_u8_be(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u8_be, spec_serialize_u8_be, s, v) by {
            lemma_parse_u8_be_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u16_be_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u16_be(s), |s, v| spec_serialize_u16_be(s, v))
    {
        reveal(prop_parse_correct::<u16>);
        let spec_parse_u16_be = |s| spec_parse_u16_be(s);
        let spec_serialize_u16_be = |s, v| spec_serialize_u16_be(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u16_be, spec_serialize_u16_be, s, v) by {
            lemma_parse_u16_be_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u32_be_correct()
        ensures
            prop_parse_correct(|s| spec_parse_u32_be(s), |s, v| spec_serialize_u32_be(s, v))
    {
        reveal(prop_parse_correct::<u32>);
        let spec_parse_u32_be = |s| spec_parse_u32_be(s);
        let spec_serialize_u32_be = |s, v| spec_serialize_u32_be(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_u32_be, spec_serialize_u32_be, s, v) by {
            lemma_parse_u32_be_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_u8_be_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_u8_be(s), |s, v| spec_serialize_u8_be(s, v))
    {
        reveal(prop_parse_serialize_inverse::<u8>);
        let spec_parse_u8_be = |s| spec_parse_u8_be(s);
        let spec_serialize_u8_be = |s, v| spec_serialize_u8_be(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u8_be, spec_serialize_u8_be, s) by {
            lemma_parse_u8_be_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_u16_be_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_u16_be(s), |s, v| spec_serialize_u16_be(s, v))
    {
        reveal(prop_parse_serialize_inverse::<u16>);
        let spec_parse_u16_be = |s| spec_parse_u16_be(s);
        let spec_serialize_u16_be = |s, v| spec_serialize_u16_be(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u16_be, spec_serialize_u16_be, s) by {
            lemma_parse_u16_be_serialize_inverse_on(s)
        }
    }

    // pub proof fn lemma_parse_u32_be_serialize_inverse()
    //     ensures
    //         prop_parse_serialize_inverse(|s| spec_parse_u32_be(s), |s, v| spec_serialize_u32_be(s, v))
    // {
    //     reveal(prop_parse_serialize_inverse::<u32>);
    //     let spec_parse_u32_be = |s| spec_parse_u32_be(s);
    //     let spec_serialize_u32_be = |s, v| spec_serialize_u32_be(s, v);
    //     assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_u32_be, spec_serialize_u32_be, s) by {
    //         lemma_parse_u32_be_serialize_inverse_on(s)
    //     }
    // }

    proof fn lemma_parse_u8_be_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u8_be(s), s)
    {}

    proof fn lemma_parse_u16_be_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u16_be(s), s)
    {
        if let Ok((sout, _, _)) = spec_parse_u16_be(s) {
            assert(s.data == sout.data);
        }
    }

    proof fn lemma_parse_u32_be_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_u32_be(s), s)
    {
        if let Ok((sout, _, _)) = spec_parse_u32_be(s) {
            assert(s.data == sout.data);
        }
    }

    proof fn lemma_parse_u8_be_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u8_be(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u8_be(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u8_be(s2) {
                    assert(n == 1);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            s1.data[s1.start]; {}
                            s1.data.subrange(s1.start, s1.start + 1)[0]; {}
                            s2.data.subrange(s2.start, s2.start + 1)[0]; {}
                            s2.data[s2.start]; {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_parse_u16_be_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u16_be(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u16_be(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u16_be(s2) {
                    assert(n == 2);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            (s1.data[s1.start] * 256 + s1.data[s1.start + 1]) as u16; {}
                            (s1.data.subrange(s1.start, s1.start + 2)[0] * 256 + s1.data.subrange(s1.start, s1.start + 2)[1]) as u16; {}
                            (s2.data.subrange(s2.start, s2.start + 2)[0] * 256 + s2.data.subrange(s2.start, s2.start + 2)[1]) as u16; {}
                            (s2.data[s2.start] * 256 + s2.data[s2.start + 1]) as u16; {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_parse_u32_be_strong_prefix_on(s1: SpecStream, s2: SpecStream)
        ensures
            prop_parse_strong_prefix_on(|s| spec_parse_u32_be(s), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_u32_be(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                if let Ok((sout2, m, x2)) = spec_parse_u32_be(s2) {
                    assert(n == 4);
                    assert(n == m);
                    assert(x1 == x2) by {
                        calc!{ (==)
                            x1; {}
                            (s1.data[s1.start] * 256 * 256 * 256 + s1.data[s1.start + 1] * 256 * 256 + s1.data[s1.start + 2] * 256 + s1.data[s1.start + 3]) as u32; {}
                            (s1.data.subrange(s1.start, s1.start + 4)[0] * 256 * 256 * 256 + s1.data.subrange(s1.start, s1.start + 4)[1] * 256 * 256 + s1.data.subrange(s1.start, s1.start + 4)[2] * 256 + s1.data.subrange(s1.start, s1.start + 4)[3]) as u32; {}
                            (s2.data.subrange(s2.start, s2.start + 4)[0] * 256 * 256 * 256 + s2.data.subrange(s2.start, s2.start + 4)[1] * 256 * 256 + s2.data.subrange(s2.start, s2.start + 4)[2] * 256 + s2.data.subrange(s2.start, s2.start + 4)[3]) as u32; {}
                            (s2.data[s2.start] * 256 * 256 * 256 + s2.data[s2.start + 1] * 256 * 256 + s2.data[s2.start + 2] * 256 + s2.data[s2.start + 3]) as u32; {}
                            x2;
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_serialize_u8_be_well_behaved_on(s: SpecStream, v: u8)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u8_be(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u8_be(s, v) {
            assert(n == 1 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 1, s.data.len() as int) =~= s.data.subrange(s.start + 1, s.data.len() as int));
        }
    }

    proof fn lemma_serialize_u16_be_well_behaved_on(s: SpecStream, v: u16)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u16_be(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u16_be(s, v) {
            assert(n == 2 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 2, s.data.len() as int) =~= s.data.subrange(s.start + 2, s.data.len() as int));
        }
    }

    proof fn lemma_serialize_u32_be_well_behaved_on(s: SpecStream, v: u32)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_u32_be(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_u32_be(s, v) {
            assert(n == 4 && sout.data.len() == s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + 4, s.data.len() as int) =~= s.data.subrange(s.start + 4, s.data.len() as int));
        }
    }

    proof fn lemma_parse_u8_be_correct_on(s: SpecStream, v: u8)
        ensures
            prop_parse_correct_on(|s| spec_parse_u8_be(s), |s, v| spec_serialize_u8_be(s, v), s, v)
    {}

    proof fn lemma_parse_u16_be_correct_on(s: SpecStream, v: u16)
        ensures
            prop_parse_correct_on(|s| spec_parse_u16_be(s), |s, v| spec_serialize_u16_be(s, v), s, v)
    {}

    proof fn lemma_parse_u32_be_correct_on(s: SpecStream, v: u32)
        ensures
            prop_parse_correct_on(|s| spec_parse_u32_be(s), |s, v| spec_serialize_u32_be(s, v), s, v)
    {}

    proof fn lemma_parse_u8_be_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_u8_be(s), |s, v| spec_serialize_u8_be(s, v), s)
    {
        assert(
        if let Ok((ss, m, res)) = spec_parse_u8_be(s) {
            if let Ok((sout, n)) = spec_serialize_u8_be(s, res) {
                n == m && sout.data =~= s.data
            } else {
                false
            }
        } else {
            true
        }
        );
    }

    proof fn lemma_parse_u16_be_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_u16_be(s), |s, v| spec_serialize_u16_be(s, v), s)
    {
        if let Ok((ss, m, res)) = spec_parse_u16_be(s) {
            if let Ok((sout, n)) = spec_serialize_u16_be(s, res) {
                assert(n == m && sout.data =~= s.data);
            }
        }
    }

    // proof fn lemma_parse_u32_be_serialize_inverse_on(s: SpecStream)
    //     ensures
    //         prop_parse_serialize_inverse_on(|s| spec_parse_u32_be(s), |s, v| spec_serialize_u32_be(s, v), s)
    // {
    //     assert(
    //         if let Ok((ss, m, res)) = spec_parse_u32_be(s) {
    //             if let Ok((sout, n)) = spec_serialize_u32_be(s, res) {
    //                 n == m && sout.data =~= s.data
    //             } else {
    //                 false
    //             }
    //         } else {
    //             true
    //         }
    //     );
    // }

}

verus! {

    pub open spec fn spec_parse_pair<R1, R2>(
        parser1: FnSpec(SpecStream) -> SpecParseResult<R1>,
        parser2: FnSpec(SpecStream) -> SpecParseResult<R2>) ->
        FnSpec(SpecStream) -> SpecParseResult<(R1,R2)>
    {
        move |s| match parser1(s) {
            Ok((s, n, r1)) => match parser2(s) {
                Ok((s, m, r2)) => {
                    if n + m > usize::MAX {
                        Err(ParseError::IntegerOverflow)
                    } else {
                        Ok((s, n + m, (r1, r2)))
                    }
                }
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        }
    }

    pub open spec fn spec_serialize_pair<T1, T2>(
        serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
        serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult) ->
        FnSpec(SpecStream, (T1, T2)) -> SpecSerializeResult
    {
        move |s, v: (T1, T2)| match serializer1(s, v.0) {
            Ok((s, n)) => match serializer2(s, v.1) {
                Ok((s, m)) => {
                    if n + m > usize::MAX {
                        Err(SerializeError::IntegerOverflow)
                    } else {
                        Ok((s, n + m))
                    }
                }
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        }
    }

    pub exec fn parse_pair<P1, P2, R1, R2>(
        exec_parser1: P1,
        exec_parser2: P2,
        Ghost(spec_parser1): Ghost<FnSpec(SpecStream) -> SpecParseResult<R1::V>>,
        Ghost(spec_parser2): Ghost<FnSpec(SpecStream) -> SpecParseResult<R2::V>>,
        s: Stream) -> (res: ParseResult<(R1,R2)>)
        where
            R1: DView,
            R2: DView,
            P1: FnOnce(Stream) -> ParseResult<R1>,
            P2: FnOnce(Stream) -> ParseResult<R2>,
        requires
            prop_parse_exec_spec_equiv(exec_parser1, spec_parser1),
            prop_parse_exec_spec_equiv(exec_parser2, spec_parser2),
        ensures
            prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parser1, spec_parser2))
        // prop_parse_exec_spec_equiv(parse_pair(exec_parser1, exec_parser2, spec_parser1, spec_parser2), spec_parse_pair(spec_parser1, spec_parser2))
    {
        // let ghost sres = spec_parse_pair(spec_parser1, spec_parser2)(s@);
        // let ghost sres1 = spec_parser1(s@);
        // let ghost sres2 = match sres1 {
        //     Ok((s1, n1, r1)) => spec_parser2(s1),
        //     Err(e) => Err(e),
        // };
        proof { reveal(prop_parse_exec_spec_equiv); }
        let res1 = exec_parser1(s);
        proof { lemma_parse_exec_spec_equiv_on(exec_parser1, spec_parser1, s, res1); }
        match res1 {
            Ok((s1, n1, r1)) => {
                let res2 = exec_parser2(s1);
                proof { lemma_parse_exec_spec_equiv_on(exec_parser2, spec_parser2, s1, res2); }
                match res2 {
                    Ok((s2, n2, r2)) => {
                        if n1 > usize::MAX - n2 {
                            Err(ParseError::IntegerOverflow)
                        } else {
                            Ok((s2, n1 + n2, (r1, r2)))
                        }
                    }
                    Err(e) => Err(e),
                }
            }
            Err(e) => Err(e),
        }
    }

    pub exec fn serialize_pair<S1, S2, T1, T2>(
        exec_serializer1: S1,
        exec_serializer2: S2,
        Ghost(spec_serializer1): Ghost<FnSpec(SpecStream, T1::V) -> SpecSerializeResult>,
        Ghost(spec_serializer2): Ghost<FnSpec(SpecStream, T2::V) -> SpecSerializeResult>,
        s: Stream, v: (T1, T2)) -> (res: SerializeResult)
        where
            S1: FnOnce(Stream, T1) -> SerializeResult,
            S2: FnOnce(Stream, T2) -> SerializeResult,
            T1: std::fmt::Debug + DView,
            T2: std::fmt::Debug + DView,
        requires
            prop_serialize_exec_spec_equiv(exec_serializer1, spec_serializer1),
            prop_serialize_exec_spec_equiv(exec_serializer2, spec_serializer2),
        ensures
            prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serializer1, spec_serializer2))
    {
        proof { reveal(prop_serialize_exec_spec_equiv); }
        let res1 = exec_serializer1(s, v.0);
        proof { lemma_serialize_exec_spec_equiv_on(exec_serializer1, spec_serializer1, s, v.0, res1); }
        match res1 {
            Ok((s, n)) => {
                let res2 = exec_serializer2(s, v.1);
                proof { lemma_serialize_exec_spec_equiv_on(exec_serializer2, spec_serializer2, s, v.1, res2); }
                match res2 {
                    Ok((s, m)) => {
                        if n > usize::MAX - m {
                            Err(SerializeError::IntegerOverflow)
                        } else {
                            Ok((s, n + m))
                        }
                    }
                    Err(e) => Err(e),
                }
            }
            Err(e) => Err(e),
        }
    }

    pub proof fn lemma_parse_pair_correct<T1, T2>(
        parser1: FnSpec(SpecStream) -> SpecParseResult<T1>,
        parser2: FnSpec(SpecStream) -> SpecParseResult<T2>,
        serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
        serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult)
        requires
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2),
            prop_parse_well_behaved(parser1),
            prop_parse_strong_prefix(parser1),
            prop_parse_correct(parser1, serializer1),
            prop_parse_correct(parser2, serializer2)
        ensures
            prop_parse_correct(spec_parse_pair(parser1, parser2),
                                spec_serialize_pair(serializer1, serializer2))
    {
        reveal(prop_parse_correct);
        assert forall |s, v| prop_parse_correct_on(spec_parse_pair(parser1, parser2),
        spec_serialize_pair(serializer1, serializer2), s, v) by {
            lemma_parse_pair_correct_on(parser1, parser2, serializer1, serializer2, s, v);
        }
    }

    pub proof fn lemma_parse_pair_serialize_inverse<T1, T2>(
        parser1: FnSpec(SpecStream) -> SpecParseResult<T1>,
        parser2: FnSpec(SpecStream) -> SpecParseResult<T2>,
        serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
        serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2),
            prop_serialize_well_behaved(serializer1),
            prop_parse_serialize_inverse(parser1, serializer1),
            prop_parse_serialize_inverse(parser2, serializer2)
        ensures
            prop_parse_serialize_inverse(spec_parse_pair(parser1, parser2),
                                    spec_serialize_pair(serializer1, serializer2))
    {
        reveal(prop_parse_serialize_inverse);
        assert forall |s: SpecStream| prop_parse_serialize_inverse_on(spec_parse_pair(parser1, parser2),
        spec_serialize_pair(serializer1, serializer2), s) by {
            lemma_parse_pair_serialize_inverse_on(parser1, parser2, serializer1, serializer2, s);
        }
    }

    pub proof fn lemma_parse_pair_well_behaved<R1, R2>(
        parser1: FnSpec(SpecStream) -> SpecParseResult<R1>,
        parser2: FnSpec(SpecStream) -> SpecParseResult<R2>)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2)
        ensures
            prop_parse_well_behaved(spec_parse_pair(parser1, parser2))
    {
        reveal(prop_parse_well_behaved);
        assert forall |s: SpecStream| prop_parse_well_behaved_on(spec_parse_pair(parser1, parser2), s) by {
            lemma_parse_pair_well_behaved_on(parser1, parser2, s);
        }
    }

    pub proof fn lemma_serialize_pair_well_behaved<T1, T2>(
        serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
        serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult)
        requires
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2)
        ensures
            prop_serialize_well_behaved(spec_serialize_pair(serializer1, serializer2))
    {
        reveal(prop_serialize_well_behaved);
        assert forall |s: SpecStream, v: (T1, T2)| prop_serialize_well_behaved_on(spec_serialize_pair(serializer1, serializer2), s, v) by {
            lemma_serialize_pair_well_behaved_on(serializer1, serializer2, s, v);
        }
    }

    pub proof fn lemma_serialize_pair_deterministic<T1, T2>(
        serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
        serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult)
        requires
            prop_serialize_deterministic(serializer1),
            prop_serialize_deterministic(serializer2),
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2)
        ensures
            prop_serialize_deterministic(spec_serialize_pair(serializer1, serializer2))
    {
        reveal(prop_serialize_deterministic);
        assert forall |s1, s2, v| prop_serialize_deterministic_on(spec_serialize_pair(serializer1, serializer2), s1, s2, v) by {
            lemma_serialize_pair_deterministic_on(serializer1, serializer2, s1, s2, v);
        }
    }

    pub proof fn lemma_parse_pair_strong_prefix<R1, R2>(
        parser1: FnSpec(SpecStream) -> SpecParseResult<R1>,
        parser2: FnSpec(SpecStream) -> SpecParseResult<R2>)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2),
            prop_parse_strong_prefix(parser1),
            prop_parse_strong_prefix(parser2),
        ensures
            prop_parse_strong_prefix(spec_parse_pair(parser1, parser2))
    {
        reveal(prop_parse_strong_prefix);
        assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_pair(parser1, parser2), s1, s2) by {
            lemma_parse_pair_strong_prefix_on(parser1, parser2, s1, s2);
        }
    }

    pub proof fn lemma_parse_pair_well_behaved_on<R1, R2>(
        parser1: FnSpec(SpecStream) -> SpecParseResult<R1>,
        parser2: FnSpec(SpecStream) -> SpecParseResult<R2>,
        s: SpecStream)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2)
        ensures
            prop_parse_well_behaved_on(spec_parse_pair(parser1, parser2), s)
    {
        if let Ok((s1, n1, _)) = parser1(s) {
            assert(
                s1.data == s.data &&
                s1.start == s.start + n1 &&
                0 <= s.start <= s1.start <= s.data.len()) by {
                    lemma_parse_well_behaved_on(parser1, s);
                }
            if let Ok((s2, n2, _)) = parser2(s1) {
                assert(
                    s2.data == s1.data &&
                    s2.start == s1.start + n2 &&
                    0 <= s1.start <= s2.start <= s1.data.len()) by {
                        lemma_parse_well_behaved_on(parser2, s1);
                    }
                if let Ok((sout, n, _)) = spec_parse_pair(parser1, parser2)(s) {
                    assert(n == n1 + n2);
                }
            }
        }
    }

    pub proof fn lemma_serialize_pair_well_behaved_on<T1, T2>(
        serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
        serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult,
        s: SpecStream, v: (T1, T2))
        requires
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2)
        ensures
            prop_serialize_well_behaved_on(spec_serialize_pair(serializer1, serializer2), s, v)
    {
        lemma_serialize_well_behaved_on(serializer1, s, v.0);
        if let Ok((s1, n1)) = serializer1(s, v.0) {
            assert(
                s1.data.len() == s.data.len()
                && 0 <= s.start <= s1.start <= s.data.len()
                && s1.start == s.start + n1
                && s1.data.subrange(0, s.start) == s.data.subrange(0, s.start)
                && s1.data.subrange(s.start + n1, s.data.len() as int) == s.data.subrange(s.start + n1, s.data.len() as int));
            lemma_serialize_well_behaved_on(serializer2, s1, v.1);
            if let Ok((s2, n2)) = serializer2(s1, v.1) {
                assert(
                    s2.data.len() == s1.data.len()
                    && 0 <= s1.start <= s2.start <= s1.data.len()
                    && s2.start == s1.start + n2
                    && s2.data.subrange(0, s1.start) == s1.data.subrange(0, s1.start)
                    && s2.data.subrange(s1.start + n2, s1.data.len() as int) == s1.data.subrange(s1.start + n2, s1.data.len() as int));
                if let Ok((sout, n)) = spec_serialize_pair(serializer1, serializer2)(s, v) {
                    // assert(n == n1 + n2);
                    // assert(s2 == sout);
                    assert(sout.data.len() == s.data.len());
                    assert(0 <= s.start <= sout.start <= s.data.len());
                    assert(sout.start == s.start + n);
                    assert(sout.data.subrange(0, s.start) == s.data.subrange(0, s.start)) by {
                        assert(s2.data.subrange(0, s1.start).subrange(0, s.start) =~= s2.data.subrange(0, s.start));
                        assert(s1.data.subrange(0, s1.start).subrange(0, s.start) =~= s1.data.subrange(0, s.start));
                    }
                    assert(sout.data.subrange(s.start + n, s.data.len() as int) == s.data.subrange(s.start + n, s.data.len() as int)) by {
                        assert(s1.data.subrange(s.start + n1, s.data.len() as int).subrange(n2 as int, s.data.len() - s.start - n1) =~= s1.data.subrange(s.start + n, s.data.len() as int));
                        assert(s.data.subrange(s.start + n1, s.data.len() as int).subrange(n2 as int, s.data.len() - s.start - n1) =~= s.data.subrange(s.start + n, s.data.len() as int));
                    }
                }
            }
        }
    }

    pub proof fn lemma_serialize_pair_deterministic_on<T1, T2>(
        serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
        serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult,
        s1: SpecStream, s2: SpecStream, v: (T1, T2))
        requires
            prop_serialize_deterministic(serializer1),
            prop_serialize_deterministic(serializer2),
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2)
        ensures
            prop_serialize_deterministic_on(spec_serialize_pair(serializer1, serializer2), s1, s2, v)
    {
        lemma_serialize_deterministic_on(serializer1, s1, s2, v.0);
        lemma_serialize_well_behaved_on(serializer1, s1, v.0);
        lemma_serialize_well_behaved_on(serializer1, s2, v.0);
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (serializer1(s1, v.0), serializer1(s2, v.0)) {
            lemma_serialize_deterministic_on(serializer2, sout1, sout2, v.1);
            lemma_serialize_well_behaved_on(serializer2, sout1, v.1);
            lemma_serialize_well_behaved_on(serializer2, sout2, v.1);
            if let (Ok((sout3, n3)), Ok((sout4, n4))) = (serializer2(sout1, v.1), serializer2(sout2, v.1)) {
                assert(n1 + n3 == n2 + n4);
                assert(sout3.data.subrange(s1.start, s1.start + n1 + n3) =~= sout4.data.subrange(s2.start, s2.start + n2 + n4)) by {
                    assert(sout1.data.subrange(0, s1.start + n1).subrange(s1.start, s1.start + n1) =~= sout1.data.subrange(s1.start, s1.start + n1));
                    assert(sout2.data.subrange(0, s2.start + n2).subrange(s2.start, s2.start + n2) =~= sout2.data.subrange(s2.start, s2.start + n2));
                    assert(sout3.data.subrange(0, s1.start + n1).subrange(s1.start, s1.start + n1) =~= sout3.data.subrange(s1.start, s1.start + n1));
                    assert(sout4.data.subrange(0, s2.start + n2).subrange(s2.start, s2.start + n2) =~= sout4.data.subrange(s2.start, s2.start + n2));

                    assert(sout3.data.subrange(s1.start, s1.start + n1) =~= sout4.data.subrange(s2.start, s2.start + n2));
                    assert(sout3.data.subrange(s1.start + n1, s1.start + n1 + n3) == sout4.data.subrange(s2.start + n2, s2.start + n2 + n4));

                    assert(sout3.data.subrange(s1.start, s1.start + n1 + n3) =~= sout3.data.subrange(s1.start, s1.start + n1) + sout3.data.subrange(s1.start + n1, s1.start + n1 + n3));
                    assert(sout4.data.subrange(s2.start, s2.start + n2 + n4) =~= sout4.data.subrange(s2.start, s2.start + n2) + sout4.data.subrange(s2.start + n2, s2.start + n2 + n4));
                }
            }
        }
    }

    pub proof fn lemma_parse_pair_strong_prefix_on<R1, R2>(
        parser1: FnSpec(SpecStream) -> SpecParseResult<R1>,
        parser2: FnSpec(SpecStream) -> SpecParseResult<R2>,
        s1: SpecStream, s2: SpecStream)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2),
            prop_parse_strong_prefix(parser1),
            prop_parse_strong_prefix(parser2),
        ensures
            prop_parse_strong_prefix_on(spec_parse_pair(parser1, parser2), s1, s2)
    {
        if let Ok((sout1, n, x1)) = spec_parse_pair(parser1, parser2)(s1) {
            if 0 <= s1.start <= s1.start + n <= s1.data.len()
            && 0 <= s2.start <= s2.start + n <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n) == s2.data.subrange(s2.start, s2.start + n) {
                // assert(parser1(s1).is_ok());
                if let Ok((p1s1, n1, p1x1)) = parser1(s1) {
                    // assert(parser2(p1s1).is_ok());
                    if let Ok((p2s1, n2, p2x1)) = parser2(p1s1) {
                        assert(s1.data.subrange(s1.start, s1.start + n1) == s2.data.subrange(s2.start, s2.start + n1)) by {
                            assert(s1.data.subrange(s1.start, s1.start + n).subrange(0, n1 as int) =~= s1.data.subrange(s1.start, s1.start + n1));
                            assert(s2.data.subrange(s2.start, s2.start + n).subrange(0, n1 as int) =~= s2.data.subrange(s2.start, s2.start + n1));
                        }
                        lemma_parse_strong_prefix_on(parser1, s1, s2);
                        // assert(parser1(s2).is_ok());
                        if let Ok((p1s2, m1, p1x2)) = parser1(s2) {
                            lemma_parse_well_behaved_on(parser1, s1);
                            lemma_parse_well_behaved_on(parser1, s2);
                            // assert(p1s1.data == s1.data);
                            // assert(p1s2.data == s2.data);
                            // assert(p1s1.start == s1.start + n1);
                            // assert(p1s2.start == s2.start + n1);
                            // assert(n == n1 + n2);
                            assert(s1.data.subrange(s1.start + n1, s1.start + n1 + n2) == s2.data.subrange(s2.start + n1, s2.start + n1 + n2)) by {
                                assert(s1.data.subrange(s1.start, s1.start + n).subrange(n1 as int, n as int) =~= s1.data.subrange(s1.start + n1, s1.start + n1 + n2));
                                assert(s2.data.subrange(s2.start, s2.start + n).subrange(n1 as int, n as int) =~= s2.data.subrange(s2.start + n1, s2.start + n1 + n2));
                            }
                            assert(p1s1.data.subrange(p1s1.start, p1s1.start + n2) == p1s2.data.subrange(p1s2.start, p1s2.start + n2));
                            lemma_parse_strong_prefix_on(parser2, p1s1, p1s2);
                            // assert(parser2(p1s2).is_ok());
                            if let Ok((p2s2, m2, p2x2)) = parser2(p1s2) {
                                if let Ok((sout2, m, x2)) = spec_parse_pair(parser1, parser2)(s2) {
                                    assert(m == n && x2 == x1);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    pub proof fn lemma_parse_pair_correct_on<T1, T2>(
        parser1: FnSpec(SpecStream) -> SpecParseResult<T1>,
        parser2: FnSpec(SpecStream) -> SpecParseResult<T2>,
        serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
        serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult,
        s: SpecStream, v: (T1, T2))
        requires
            prop_serialize_well_behaved(serializer1),
            prop_serialize_well_behaved(serializer2),
            prop_parse_well_behaved(parser1),
            prop_parse_strong_prefix(parser1),
            prop_parse_correct(parser1, serializer1),
            prop_parse_correct(parser2, serializer2)
        ensures
            prop_parse_correct_on(spec_parse_pair(parser1, parser2),
                                spec_serialize_pair(serializer1, serializer2), s, v)
    {
        if let Ok((s1, n1)) = serializer1(s, v.0) {
            if let Ok((s2, n2)) = serializer2(s1, v.1) {
                lemma_serialize_well_behaved_on(serializer1, s, v.0);
                lemma_serialize_well_behaved_on(serializer2, s1, v.1);
                lemma_parse_correct_on(parser1, serializer1, s, v.0);
                if let Ok((s_c1, n_c1, r_c1)) = parser1(SpecStream {start: s.start, ..s1}) {
                    assert(n1 == n_c1 && r_c1 == v.0);
                    assert(s1.data.subrange(s.start, s.start + n_c1) == s2.data.subrange(s.start, s.start + n_c1)) by {
                        assert(s1.data.subrange(0, s.start + n1).subrange(s.start, s.start + n1) =~= s1.data.subrange(s.start, s.start + n1));
                        assert(s2.data.subrange(0, s.start + n1).subrange(s.start, s.start + n1) =~= s2.data.subrange(s.start, s.start + n1));
                    }
                    lemma_parse_strong_prefix_on(parser1, SpecStream {start: s.start, ..s1}, SpecStream {start: s.start, ..s2});
                    if let Ok((s3, m1, res1)) = parser1(SpecStream {start: s.start, ..s2}) {
                        assert(m1 == n_c1 && res1 == r_c1);
                        assert(m1 == n1 && res1 == v.0); // crucial fact 1
                        lemma_parse_well_behaved_on(parser1, SpecStream {start: s.start, ..s2});
                        assert(s3.data == s2.data && s3.start == s.start + m1); // crucial fact 2 (s3 == SpecStream {start: s1.start, ..s2})
                        lemma_parse_correct_on(parser2, serializer2, s1, v.1);
                        // if let Ok((s_c2, n_c2, r_c2)) = parser2(SpecStream {start: s1.start, ..s2}) {
                            // assert(n2 == n_c2 && r_c2 == v.1);
                            if let Ok((s4, m2, res2)) = parser2(s3) {
                                // assert(m2 == n_c2 && res2 == r_c2);
                                assert(m1 + m2 == n1 + n2);
                                assert(res1 == v.0 && res2 == v.1);
                            }
                        // }
                    }
                }
            }
        }
    }

    pub proof fn lemma_parse_pair_serialize_inverse_on<T1, T2>(
        parser1: FnSpec(SpecStream) -> SpecParseResult<T1>,
        parser2: FnSpec(SpecStream) -> SpecParseResult<T2>,
        serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
        serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult,
        s: SpecStream)
        requires
            prop_parse_well_behaved(parser1),
            prop_parse_well_behaved(parser2),
            prop_serialize_well_behaved(serializer1),
            prop_parse_serialize_inverse(parser1, serializer1),
            prop_parse_serialize_inverse(parser2, serializer2)
        ensures
            prop_parse_serialize_inverse_on(spec_parse_pair(parser1, parser2),
                                    spec_serialize_pair(serializer1, serializer2), s)
    {
        if let Ok((s1, n1, x1)) = parser1(s) {
            if let Ok((s2, n2, x2)) = parser2(s1) {
                lemma_parse_well_behaved_on(parser1, s);
                lemma_parse_well_behaved_on(parser2, s1);
                lemma_parse_serialize_inverse_on(parser1, serializer1, s);
                lemma_serialize_well_behaved_on(serializer1, s, x1);
                if let Ok((s3, m1)) = serializer1(s, x1) {
                    assert(m1 == n1 && s3.data == s.data);
                    lemma_parse_serialize_inverse_on(parser2, serializer2, s1);
                    if let Ok((s4, m2)) = serializer2(s3, x2) {
                        assert(m1 + m2 == n1 + n2);
                        assert(s4.data == s.data);
                    }
                }
            }
        }
    }
}

verus! {

    pub open spec fn spec_parse_repeat_n_rec<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        n: nat,
        s: SpecStream) -> SpecParseResult<Seq<R>>
        decreases n
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start > s.data.len() {
            Err(ParseError::Eof)
        } else if n == 0 {
            Ok((s, 0, seq![]))
        } else {
            match spec_parse_repeat_n_rec(parser, (n - 1) as nat, s) {
                Ok((s, k, rs)) => match parser(s) {
                    Ok((s, m, r)) => {
                        if m + k > usize::MAX {
                            Err(ParseError::IntegerOverflow)
                        } else {
                            Ok((s, m + k, rs.push(r))) // repeat_n(n) = repeat_n(n - 1).push(parse()) = repeat_n(n - 2).push(parse()).push(parse()) = ... = repeat_n(0).push(parse()).push(parse()).push(parse()) = seq![parse(), parse(), ..., parse()]
                        }
                    }
                    Err(e) => Err(e),
                },
                Err(e) => Err(e),
            }
        }
    }

    pub open spec fn spec_parse_repeat_n<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        n: nat) ->
        FnSpec(SpecStream) -> SpecParseResult<Seq<R>>
    {
        move |s| spec_parse_repeat_n_rec(parser, n, s)
    }

    pub open spec fn spec_serialize_repeat_n_rec<T>(
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat,
        s: SpecStream,
        vs: Seq<T>) -> SpecSerializeResult
        recommends
            vs.len() == n // otherwise cannot prove correctness
        decreases n
    {
        if vs.len() != n {
            Err(SerializeError::RepeatNMismatch)
        } else if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.start > s.data.len() {
            Err(SerializeError::NotEnoughSpace)
        } else if n == 0 {
            Ok((s, 0))
        } else {
            match spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1)) {
                Ok((s, k)) => match serializer(s, vs[vs.len() as int - 1]) {
                    Ok((s, m)) => {
                        if m + k > usize::MAX {
                            Err(SerializeError::IntegerOverflow)
                        } else {
                            Ok((s, m + k))
                        }
                    }
                    Err(e) => Err(e),
                },
                Err(e) => Err(e),
            }
        }
    }

    pub open spec fn spec_serialize_repeat_n<T>(
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat) ->
        FnSpec(SpecStream, Seq<T>) -> SpecSerializeResult
    {
        move |s, vs| spec_serialize_repeat_n_rec(serializer, n, s, vs)
    }

    pub exec fn parse_repeat_n<P, R>(
        exec_parser: P,
        Ghost(spec_parser): Ghost<FnSpec(SpecStream) -> SpecParseResult<R::V>>,
        n: usize, s: Stream) -> (res: ParseResult<Vec<R>>)
        where
            P: Fn(Stream) -> ParseResult<R>,
            R: DView,
        requires
            prop_parse_exec_spec_equiv(exec_parser, spec_parser),
        ensures
            prop_parse_exec_spec_equiv_on(s, res, spec_parse_repeat_n(spec_parser, n as nat))
    {
        proof { reveal(prop_parse_exec_spec_equiv); }

        if s.start < 0 {
            return Err(ParseError::NegativeIndex);
        } else if s.start > s.data.length() {
            return Err(ParseError::Eof);
        }

        let (mut xs, mut mut_s, mut i, mut m): (Vec<R>, Stream, usize, usize) = (vec_new(), s, 0, 0);
        let ghost res = Ok((mut_s, 0, xs));

        while i < n
            invariant
                0 <= i <= n,
                0 <= m <= usize::MAX,
                forall |s| #![auto] exec_parser.requires((s,)),
                res == Ok::<(Stream, usize, Vec<R>), ParseError>((mut_s, m, xs)),
                prop_parse_exec_spec_equiv(exec_parser, spec_parser),
                prop_parse_exec_spec_equiv_on(s, res, spec_parse_repeat_n(spec_parser, i as nat)),
        {
            i = i + 1;
            let res1 = exec_parser(mut_s);
            proof { lemma_parse_exec_spec_equiv_on(exec_parser, spec_parser, mut_s, res1); }
            match res1 {
                Ok((s1, m1, r1)) => {
                    if m > usize::MAX - m1 {
                        proof { res = Err(ParseError::IntegerOverflow); }
                        proof { lemma_parse_repeat_n_rec_error_unrecoverable_on(spec_parser, i as nat, n as nat, s.dview()); }
                        assert(prop_parse_exec_spec_equiv_on(s, res, spec_parse_repeat_n(spec_parser, n as nat)));
                        return Err(ParseError::IntegerOverflow);
                    } else {
                        vec_push(&mut xs, r1);
                        mut_s = s1;
                        m = m + m1;
                        proof { res = Ok((mut_s, m, xs)); }
                        assert(prop_parse_exec_spec_equiv_on(s, res, spec_parse_repeat_n(spec_parser, i as nat)));
                    }
                }
                Err(e) => {
                    proof { res = Err(e); }
                    proof { lemma_parse_repeat_n_rec_error_unrecoverable_on(spec_parser, i as nat, n as nat, s.dview()); }
                    assert(prop_parse_exec_spec_equiv_on(s, res, spec_parse_repeat_n(spec_parser, n as nat)));
                    return Err(e);
                }
            }
        }

        Ok((mut_s, m, xs))
    }

    pub exec fn serialize_repeat_n<S, T>(
        exec_serializer: S,
        Ghost(spec_serializer): Ghost<FnSpec(SpecStream, T::V) -> SpecSerializeResult>,
        n: usize, s: Stream, vs: Vec<T>) -> (res: SerializeResult)
        where
            S: Fn(Stream, T) -> SerializeResult,
            T: std::fmt::Debug + DView + std::marker::Copy,
        requires
            prop_serialize_exec_spec_equiv(exec_serializer, spec_serializer),
        ensures
            prop_serialize_exec_spec_equiv_on(s, vs, res, spec_serialize_repeat_n(spec_serializer, n as nat)),
    {
        proof { reveal(prop_serialize_exec_spec_equiv); }

        if vs.length() != n {
            return Err(SerializeError::RepeatNMismatch);
        } else if s.start < 0 {
            return Err(SerializeError::NegativeIndex);
        } else if s.start > s.data.length() {
            return Err(SerializeError::NotEnoughSpace);
        }

        let (mut mut_s, mut i, mut m): (Stream, usize, usize) = (s, 0, 0);
        let ghost res = Ok((mut_s, 0));
        let ghost vi = seq![];
        assert(vi =~= vs.dview().subrange(0, i as int));

        while i < n
            invariant
                0 <= i <= n,
                0 <= m <= usize::MAX,
                vs.dview().len() == n,
                res == Ok::<(Stream, usize), SerializeError>((mut_s, m)),
                vi == vs.dview().subrange(0, i as int),
                forall |s, v| #![auto] exec_serializer.requires((s, v)),
                prop_serialize_exec_spec_equiv(exec_serializer, spec_serializer),
                prop_serialize_repeat_n_exec_spec_equiv_on(s.dview(), vi, res, spec_serialize_repeat_n(spec_serializer, i as nat)),
        {
            i = i + 1;
            let ghost old_vi = vi;
            let v = *vec_index(&vs, i - 1);
            proof {
                vi = vi.push(v.dview());
                assert(old_vi =~= vi.subrange(0, vi.len() as int - 1)); // to show it matches the spec version
                assert(vi =~= vs.dview().subrange(0, i as int));
            }
            let res1 = exec_serializer(mut_s, v);
            proof { lemma_serialize_exec_spec_equiv_on(exec_serializer, spec_serializer, mut_s, v, res1); }
            match res1 {
                Ok((s1, m1)) => {
                    if m > usize::MAX - m1 {
                        proof { res = Err(SerializeError::IntegerOverflow); }
                        proof { lemma_serialize_repeat_n_rec_error_unrecoverable_on(spec_serializer, i as nat, n as nat, s.dview(), vi, vs.dview()); }
                        assert(prop_serialize_exec_spec_equiv_on(s, vs, res, spec_serialize_repeat_n(spec_serializer, n as nat)));
                        return Err(SerializeError::IntegerOverflow);
                    } else {
                        mut_s = s1;
                        m = m + m1;
                        proof { res = Ok((mut_s, m)); }
                        assert(prop_serialize_repeat_n_exec_spec_equiv_on(s.dview(), vi, res, spec_serialize_repeat_n(spec_serializer, i as nat)));
                    }
                }
                Err(e) => {
                    proof { res = Err(e); }
                    proof { lemma_serialize_repeat_n_rec_error_unrecoverable_on(spec_serializer, i as nat, n as nat, s.dview(), vi, vs.dview()); }
                    assert(prop_serialize_exec_spec_equiv_on(s, vs, res, spec_serialize_repeat_n(spec_serializer, n as nat)));
                    return Err(e);
                }
            }
        }

        assert(vi =~= vs.dview());

        Ok((mut_s, m))
    }

    pub open spec fn prop_serialize_repeat_n_exec_spec_equiv_on<T>(
        s: SpecStream,
        vs: Seq<T>,
        res: SerializeResult,
        spec_serializer: FnSpec(SpecStream, Seq<T>) -> SpecSerializeResult) -> bool
    {
        match spec_serializer(s, vs) {
            Ok((sout, sn)) => {
                &&& res.is_ok()
                &&& res.unwrap().0.dview() == sout
                &&& res.unwrap().1 == sn
            }
            Err(e) => res.is_err() && res.unwrap_err() == e
        }
    }


    proof fn lemma_parse_repeat_n_rec_error_unrecoverable_on<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        n1: nat, n2: nat, s: SpecStream)
        ensures
        n2 >= n1 ==> {
            if let Err(e1) = spec_parse_repeat_n_rec(parser, n1, s) {
                if let Err(e2) = spec_parse_repeat_n_rec(parser, n2, s) {
                    e1 == e2
                } else {
                    false
                }
            } else {
                true
            }
        }
        decreases n2
    {
        if n2 == n1 {}
        else if n2 > n1 {
            lemma_parse_repeat_n_rec_error_unrecoverable_on(parser, n1, (n2 - 1) as nat, s);
        }
    }

    proof fn lemma_serialize_repeat_n_rec_error_unrecoverable_on<T>(
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n1: nat, n2: nat, s: SpecStream, vs1: Seq<T>, vs2: Seq<T>)
        requires
            n2 >= n1,
            vs1.len() == n1,
            vs2.len() == n2,
            vs1 == vs2.subrange(0, n1 as int),
        ensures
            if let Err(e1) = spec_serialize_repeat_n_rec(serializer, n1, s, vs1) {
                if let Err(e2) = spec_serialize_repeat_n_rec(serializer, n2, s, vs2) {
                    e1 == e2
                } else {
                    false
                }
            } else {
                true
            }
        decreases n2, vs2.len()
    {
        if n2 == n1 {
            assert(vs1 =~= vs2);
        }
        else if n2 > n1 {
            assert(vs1 =~= vs2.subrange(0, vs2.len() as int - 1).subrange(0, n1 as int));
            lemma_serialize_repeat_n_rec_error_unrecoverable_on(serializer, n1, (n2 - 1) as nat, s, vs1, vs2.subrange(0, vs2.len() as int - 1));
        }
    }

    pub proof fn spec_parse_repeat_n_rec_step<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        n: nat, s: SpecStream)
        ensures
            s.start < 0 ==> spec_parse_repeat_n_rec(parser, n, s) == Err::<(SpecStream, nat, Seq<R>), ParseError>(ParseError::NegativeIndex),
            s.start > s.data.len() ==> spec_parse_repeat_n_rec(parser, n, s) == Err::<(SpecStream, nat, Seq<R>), ParseError>(ParseError::Eof),
            0 <= s.start <= s.data.len() ==> {
                &&& n == 0 ==> spec_parse_repeat_n_rec(parser, n, s) == Ok::<(SpecStream, nat, Seq<R>), ParseError>((s, 0, seq![]))
                &&& n > 0 ==> match spec_parse_repeat_n_rec(parser, (n - 1) as nat, s) {
                    Err(e) => spec_parse_repeat_n_rec(parser, n, s) == Err::<(SpecStream, nat, Seq<R>), ParseError>(e),
                    Ok((s0, m, rs)) => match parser(s0) {
                        Err(e) => spec_parse_repeat_n_rec(parser, n, s) == Err::<(SpecStream, nat, Seq<R>), ParseError>(e),
                        Ok((s1, k, r)) => {
                            if m + k > usize::MAX {
                                spec_parse_repeat_n_rec(parser, n, s) == Err::<(SpecStream, nat, Seq<R>), ParseError>(ParseError::IntegerOverflow)
                            } else {
                                spec_parse_repeat_n_rec(parser, n, s) == Ok::<(SpecStream, nat, Seq<R>), ParseError>((s1, m + k, rs.push(r)))
                            }
                        }
                    }
                }
            }
    {}

    pub proof fn lemma_parse_repeat_n_correct<T>(
        parser: FnSpec(SpecStream) -> SpecParseResult<T>,
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat)
        requires
            prop_parse_well_behaved(parser),
            prop_serialize_well_behaved(serializer),
            prop_parse_strong_prefix(parser),
            prop_parse_correct(parser, serializer)
        ensures
            prop_parse_correct(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n))
    {
        reveal(prop_parse_correct);
        assert forall |s: SpecStream, vs: Seq<T>| prop_parse_correct_on(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n), s, vs) by {
            lemma_parse_repeat_n_correct_on(parser, serializer, n, s, vs);
        }
    }

    pub proof fn lemma_parse_repeat_n_serialize_inverse<T>(
        parser: FnSpec(SpecStream) -> SpecParseResult<T>,
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat)
        requires
            prop_parse_well_behaved(parser),
            prop_serialize_well_behaved(serializer),
            prop_parse_serialize_inverse(parser, serializer)
        ensures
            prop_parse_serialize_inverse(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n))
    {
        reveal(prop_parse_serialize_inverse);
        assert forall |s: SpecStream| prop_parse_serialize_inverse_on(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n), s) by {
            lemma_parse_repeat_n_serialize_inverse_on(parser, serializer, n, s);
        }
    }

    pub proof fn lemma_parse_repeat_n_well_behaved<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        n: nat)
        requires
            prop_parse_well_behaved(parser)
        ensures
            prop_parse_well_behaved(spec_parse_repeat_n(parser, n)),
            forall |s| {
                if let Ok((_, _, res)) = #[trigger] spec_parse_repeat_n(parser, n)(s) {
                    res.len() == n
                } else {
                    true
                }
            }
        decreases n
    {
        reveal(prop_parse_well_behaved);
        assert forall |s:SpecStream| prop_parse_well_behaved_on(spec_parse_repeat_n(parser, n), s) by {
            lemma_parse_repeat_n_well_behaved_on(parser, n, s);
        }
        assert forall |s:SpecStream| {
            if let Ok((_, _, res)) = #[trigger] spec_parse_repeat_n(parser, n)(s) {
                res.len() == n
            } else {
                true
            }
        } by {
            lemma_parse_repeat_n_well_behaved_on(parser, n, s);
        }
    }

    pub proof fn lemma_serialize_repeat_n_well_behaved<T>(
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat)
        requires
            prop_serialize_well_behaved(serializer),
        ensures
            prop_serialize_well_behaved(spec_serialize_repeat_n(serializer, n))
    {
        reveal(prop_serialize_well_behaved);
        assert forall |s:SpecStream, vs: Seq<T>| prop_serialize_well_behaved_on(spec_serialize_repeat_n(serializer, n), s, vs) by {
            lemma_serialize_repeat_n_well_behaved_on(serializer, n, s, vs);
        }
    }

    pub proof fn lemma_serialize_repeat_n_deterministic<T>(
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat)
        requires
            prop_serialize_well_behaved(serializer),
            prop_serialize_deterministic(serializer)
        ensures
            prop_serialize_deterministic(spec_serialize_repeat_n(serializer, n))
    {
        reveal(prop_serialize_deterministic);
        assert forall |s1, s2, v| prop_serialize_deterministic_on(spec_serialize_repeat_n(serializer, n), s1, s2, v) by {
            lemma_serialize_repeat_n_deterministic_on(serializer, n, s1, s2, v);
        }
    }

    pub proof fn lemma_parse_repeat_n_nonmalleable<T>(
        parser: FnSpec(SpecStream) -> SpecParseResult<T>,
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat)
        requires
            prop_parse_serialize_inverse(spec_parse_repeat_n(parser, n),
                                        spec_serialize_repeat_n(serializer, n)),
            prop_serialize_deterministic(spec_serialize_repeat_n(serializer, n)),
        ensures
            prop_parse_nonmalleable(spec_parse_repeat_n(parser, n))
    {
        lemma_parse_serialize_inverse_implies_nonmalleable(spec_parse_repeat_n(parser, n),
                                        spec_serialize_repeat_n(serializer, n));
    }

    pub proof fn lemma_parse_repeat_n_strong_prefix<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        n: nat)
        requires
            prop_parse_well_behaved(parser),
            prop_parse_strong_prefix(parser),
        ensures
            prop_parse_strong_prefix(spec_parse_repeat_n(parser, n))
    {
        reveal(prop_parse_strong_prefix);
        assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_repeat_n(parser, n), s1, s2) by {
            lemma_parse_repeat_n_strong_prefix_on(s1, s2, parser, n);
        }
    }

    proof fn lemma_parse_repeat_n_correct_on<T>(
        parser: FnSpec(SpecStream) -> SpecParseResult<T>,
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat,
        s: SpecStream,
        vs: Seq<T>)
        requires
            prop_parse_well_behaved(parser),
            prop_serialize_well_behaved(serializer),
            prop_parse_strong_prefix(parser),
            prop_parse_correct(parser, serializer)
        ensures
            prop_parse_correct_on(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n), s, vs)
        decreases n, vs.len()
    {
        if vs.len() != n {
        } else if s.start < 0 {
        } else if s.start > s.data.len() {
        } else if n == 0 {
            assert(vs =~= seq![]);
        } else {
            // induction
            lemma_parse_repeat_n_correct_on(parser, serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1));
            lemma_serialize_repeat_n_well_behaved_on(serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1));
            if let Ok((s0, n0)) = spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1)) {
                lemma_serialize_well_behaved_on(serializer, s0, vs[vs.len() as int - 1]);
                if let Ok((s1, n1)) = serializer(s0, vs[vs.len() as int - 1]) {
                    assert(s0.data.subrange(s.start, s.start + n0) == s1.data.subrange(s.start, s.start + n0)) by {
                        assert(s0.data.subrange(0, s0.start).subrange(s.start, s.start + n0) =~= s0.data.subrange(s.start, s.start + n0));
                        assert(s1.data.subrange(0, s0.start).subrange(s.start, s.start + n0) =~= s1.data.subrange(s.start, s.start + n0));
                    }
                    lemma_parse_repeat_n_strong_prefix(parser, (n - 1) as nat);
                    lemma_parse_strong_prefix_on(spec_parse_repeat_n(parser, (n - 1) as nat), SpecStream { start: s.start, ..s0 }, SpecStream { start: s.start, ..s1 });
                    lemma_parse_correct_on(parser, serializer, s0, vs[vs.len() as int - 1]);
                    lemma_parse_repeat_n_well_behaved_on(parser, (n - 1) as nat, SpecStream { start: s.start, ..s1 });
                    if let Ok((s2, n2, x0)) = spec_parse_repeat_n_rec(parser, (n - 1) as nat, SpecStream { start: s.start, ..s1 }) {
                        if let Ok((s3, n3, x1)) = parser(s2) {
                            assert(n3 == n1 && x1 == vs[vs.len() as int - 1]);
                            assert(n2 + n3 == n0 + n1);
                            assert(x0 == vs.subrange(0, vs.len() as int - 1));
                            assert(x0.push(x1) =~= vs);
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_parse_repeat_n_serialize_inverse_on<T>(
        parser: FnSpec(SpecStream) -> SpecParseResult<T>,
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat,
        s: SpecStream)
        requires
            prop_parse_well_behaved(parser),
            prop_serialize_well_behaved(serializer),
            prop_parse_serialize_inverse(parser, serializer)
        ensures
            prop_parse_serialize_inverse_on(spec_parse_repeat_n(parser, n), spec_serialize_repeat_n(serializer, n), s)
        decreases n
    {
        if s.start < 0 {
        } else if s.start > s.data.len() {
        } else if n == 0 {
        } else {
            // induction
            lemma_parse_repeat_n_serialize_inverse_on(parser, serializer, (n - 1) as nat, s);
            lemma_parse_repeat_n_well_behaved_on(parser, (n - 1) as nat, s);
            if let Ok((s0, n0, x0)) = spec_parse_repeat_n_rec(parser, (n - 1) as nat, s) {
                lemma_parse_well_behaved_on(parser, s0);
                if let Ok((s1, n1, x1)) = parser(s0) {
                    assert(x0.push(x1).subrange(0, x0.push(x1).len() as int - 1) =~= x0);
                    lemma_serialize_repeat_n_well_behaved_on(serializer, (n - 1) as nat, s, x0);
                    if let Ok((s2, n2)) = spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s, x0) {
                        lemma_serialize_well_behaved_on(serializer, s2, x1);
                        lemma_parse_serialize_inverse_on(parser, serializer, s0);
                        assert(s2 == s0);
                        if let Ok((s3, n3)) = serializer(s2, x1) {
                            assert(n0 + n1 == n2 + n3);
                            assert(s3.data == s.data);
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_parse_repeat_n_well_behaved_on<R>(
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        n: nat,
        s: SpecStream)
        requires
            prop_parse_well_behaved(parser)
        ensures
            prop_parse_well_behaved_on(spec_parse_repeat_n(parser, n), s)
            &&
            if let Ok((_, _, res)) = spec_parse_repeat_n(parser, n)(s) {
                res.len() == n
            } else {
                true
            }
        decreases n
    {
        if n == 0 {
        } else {
            match spec_parse_repeat_n(parser, n)(s) {
                Ok((sout, n_total, res)) => {
                    assert(
                        sout.data == s.data &&
                        sout.start == s.start + n_total &&
                        0 <= s.start <= sout.start <= s.data.len() &&
                        res.len() == n) by {
                            if let Ok((s1, n1, res1)) = spec_parse_repeat_n(parser, (n - 1) as nat)(s) {
                                assert(
                                    s1.data == s.data &&
                                    s1.start == s.start + n1 &&
                                    0 <= s.start <= s1.start <= s.data.len() &&
                                    res1.len() == n - 1) by { // induction on n
                                    lemma_parse_repeat_n_well_behaved_on(parser, (n - 1) as nat, s);
                                }
                                if let Ok((s2, n2, res2)) = parser(s1) {
                                    assert(
                                        s2.data == s1.data &&
                                        s2.start == s1.start + n2 &&
                                        0 <= s1.start <= s2.start <= s1.data.len()) by {
                                            lemma_parse_well_behaved_on(parser, s1);
                                        }
                                    assert(
                                        sout == s2 &&
                                        n_total == n1 + n2 &&
                                        res == res1.push(res2) &&
                                        res.len() == n
                                    );
                                }
                            }
                        }
                }
                Err(_) => {}
            }
        }
    }

    proof fn lemma_serialize_repeat_n_well_behaved_on<T>(
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat,
        s: SpecStream,
        vs: Seq<T>)
        requires
            prop_serialize_well_behaved(serializer),
        ensures
            prop_serialize_well_behaved_on(spec_serialize_repeat_n(serializer, n), s, vs)
        decreases n
    {
        if vs.len() != n {}
        else if s.start < 0 {}
        else if s.start > s.data.len() {}
        else if n == 0 {}
        else {
            lemma_serialize_repeat_n_well_behaved_on(serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1));
            match spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s, vs.subrange(0, vs.len() as int - 1)) {
                Ok((s1, n1)) =>
                {
                    assert(s.start + n1 == s1.start);
                    assert(s1.data.subrange(0, s.start) == s.data.subrange(0, s.start));
                    assert(s1.data.subrange(s.start + n1, s.data.len() as int) == s.data.subrange(s.start + n1, s.data.len() as int));
                    lemma_serialize_well_behaved_on(serializer, s1, vs[vs.len() as int - 1]);
                    match serializer(s1, vs[vs.len() as int - 1]) {
                        Ok((s2, n2)) => {
                            assert(s1.start + n2 == s2.start);
                            assert(s2.data.subrange(0, s1.start) == s1.data.subrange(0, s1.start));
                            assert(s2.data.subrange(s1.start + n2, s.data.len() as int) == s1.data.subrange(s1.start + n2, s.data.len() as int));

                            assert(s.start + n1 + n2 == s2.start);
                            assert(s2.data.subrange(0, s.start) == s.data.subrange(0, s.start)) by {
                                assert(s2.data.subrange(0, s1.start).subrange(0, s.start) =~= s2.data.subrange(0, s.start));
                                assert(s1.data.subrange(0, s1.start).subrange(0, s.start) =~= s.data.subrange(0, s.start));
                            }
                            assert(s2.data.subrange(s.start + n1 + n2, s.data.len() as int) == s.data.subrange(s.start + n1 + n2, s.data.len() as int)) by {
                                assert(s1.data.subrange(s.start + n1, s.data.len() as int).subrange(n2 as int, s.data.len() - s.start - n1) =~= s1.data.subrange(s.start + n1 + n2, s.data.len() as int));
                                assert(s.data.subrange(s.start + n1, s.data.len() as int).subrange(n2 as int, s.data.len() - s.start - n1) =~= s.data.subrange(s.start + n1 + n2, s.data.len() as int));
                            }
                        }
                        Err(e) => {}
                    }
                },
                Err(e) => {}
            }
        }
    }

    proof fn lemma_serialize_repeat_n_deterministic_on<T>(
        serializer: FnSpec(SpecStream, T) -> SpecSerializeResult,
        n: nat,
        s1: SpecStream,
        s2: SpecStream,
        vs: Seq<T>)
        requires
            prop_serialize_well_behaved(serializer),
            prop_serialize_deterministic(serializer)
        ensures
            prop_serialize_deterministic_on(spec_serialize_repeat_n(serializer, n), s1, s2, vs)
        decreases n, vs.len()
    {
        if let (Ok((sn1, m1)), Ok((sn2, m2))) = (spec_serialize_repeat_n(serializer, n)(s1, vs), spec_serialize_repeat_n(serializer, n)(s2, vs))
        {
            if vs.len() != n {}
            else if s1.start < 0 || s2.start < 0 {}
            else if s1.start > s1.data.len() || s2.start > s2.data.len() {}
            else if n == 0 {}
            else {
                // induction on n
                lemma_serialize_repeat_n_well_behaved_on(serializer, (n - 1) as nat, s1, vs.subrange(0, vs.len() as int - 1));
                lemma_serialize_repeat_n_well_behaved_on(serializer, (n - 1) as nat, s2, vs.subrange(0, vs.len() as int - 1));
                lemma_serialize_repeat_n_deterministic_on(serializer, (n - 1) as nat, s1, s2, vs.subrange(0, vs.len() as int - 1));
                if let (Ok((snn1, nn1)), Ok((snn2, nn2))) = (spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s1, vs.subrange(0, vs.len() as int - 1)), spec_serialize_repeat_n_rec(serializer, (n - 1) as nat, s2, vs.subrange(0, vs.len() as int - 1))) {
                    assert(nn1 == nn2);
                    assert(snn1.data.subrange(s1.start, s1.start + nn1) == snn2.data.subrange(s2.start, s2.start + nn2));

                    lemma_serialize_well_behaved_on(serializer, snn1, vs[vs.len() as int - 1]);
                    lemma_serialize_well_behaved_on(serializer, snn2, vs[vs.len() as int - 1]);
                    lemma_serialize_deterministic_on(serializer, snn1, snn2, vs[vs.len() as int - 1]);
                    if let Ok((sout1, n1)) = serializer(snn1, vs[vs.len() as int - 1]) {
                        if let Ok((sout2, n2)) = serializer(snn2, vs[vs.len() as int - 1]) {
                            assert(n1 + nn1 == n2 + nn2);
                            assert(sout1.data.subrange(snn1.start, snn1.start + n1) == sout2.data.subrange(snn2.start, snn2.start + n2));

                            assert(sout1.data.subrange(s1.start, s1.start + n1 + nn1) == sout2.data.subrange(s2.start, s2.start + n2 + nn2)) by {
                                assert(sout1.data.subrange(s1.start, s1.start + n1 + nn1) =~= sout1.data.subrange(s1.start, s1.start + nn1) + sout1.data.subrange(s1.start + nn1, s1.start + n1 + nn1));
                                assert(sout2.data.subrange(s2.start, s2.start + n2 + nn2) =~= sout2.data.subrange(s2.start, s2.start + nn2) + sout2.data.subrange(s2.start + nn2, s2.start + n2 + nn2));

                                assert(sout1.data.subrange(s1.start, s1.start + nn1) =~= sout1.data.subrange(0, s1.start + nn1).subrange(s1.start, s1.start + nn1));
                                assert(sout2.data.subrange(s2.start, s2.start + nn2) =~= sout2.data.subrange(0, s2.start + nn2).subrange(s2.start, s2.start + nn2));

                                assert(snn1.data.subrange(s1.start, s1.start + nn1) =~= snn1.data.subrange(0, s1.start + nn1).subrange(s1.start, s1.start + nn1));
                                assert(snn2.data.subrange(s2.start, s2.start + nn2) =~= snn2.data.subrange(0, s2.start + nn2).subrange(s2.start, s2.start + nn2));
                            }
                        }
                    }
                }
            }
        assert(m1 == m2);
        assert(sn1.data.subrange(s1.start, s1.start + m1) =~= sn2.data.subrange(s2.start, s2.start + m2));
        }
    }


    proof fn lemma_parse_repeat_n_strong_prefix_on<R>(
        s1: SpecStream,
        s2: SpecStream,
        parser: FnSpec(SpecStream) -> SpecParseResult<R>,
        n: nat)
        requires
            prop_parse_well_behaved(parser),
            prop_parse_strong_prefix(parser),
        ensures
            prop_parse_strong_prefix_on(spec_parse_repeat_n(parser, n), s1, s2)
        decreases n
    {
        if let Ok((sout1, n1, x1)) = spec_parse_repeat_n(parser, n)(s1) {
            if 0 <= s1.start <= s1.start + n1 <= s1.data.len()
            && 0 <= s2.start <= s2.start + n1 <= s2.data.len()
            && s1.data.subrange(s1.start, s1.start + n1) == s2.data.subrange(s2.start, s2.start + n1) {
                if n == 0 {
                } else {
                    // induction on n
                    lemma_parse_repeat_n_well_behaved_on(parser, (n - 1) as nat, s1);
                    lemma_parse_repeat_n_well_behaved_on(parser, (n - 1) as nat, s2);
                    lemma_parse_repeat_n_strong_prefix_on(s1, s2, parser, (n - 1) as nat);
                    if let Ok((sn1, nn1, xn1)) = spec_parse_repeat_n_rec(parser, (n - 1) as nat, s1) {
                        assert(s1.data.subrange(s1.start, s1.start + nn1) == s2.data.subrange(s2.start, s2.start + nn1)) by {
                            assert(s1.data.subrange(s1.start, s1.start + n1).subrange(0, nn1 as int) =~= s1.data.subrange(s1.start, s1.start + nn1));
                            assert(s2.data.subrange(s2.start, s2.start + n1).subrange(0, nn1 as int) =~= s2.data.subrange(s2.start, s2.start + nn1));
                        }
                        if let Ok((sn2, nn2, xn2)) = spec_parse_repeat_n_rec(parser, (n - 1) as nat, s2) {
                            assert(nn1 == nn2 && xn1 == xn2);
                            lemma_parse_well_behaved_on(parser, sn1);
                            lemma_parse_well_behaved_on(parser, sn2);
                            lemma_parse_strong_prefix_on(parser, sn1, sn2);
                            if let Ok((sn1_, nn1_, xn1_)) = parser(sn1) {
                                // assert(n1 == nn1 + nn1_);
                                assert(s1.data.subrange(s1.start + nn1, s1.start + n1) == s2.data.subrange(s2.start + nn1, s2.start + n1)) by {
                                    assert(s1.data.subrange(s1.start, s1.start + n1).subrange(nn1 as int, n1 as int) =~= s1.data.subrange(s1.start + nn1, s1.start + n1));
                                    assert(s2.data.subrange(s2.start, s2.start + n1).subrange(nn1 as int, n1 as int) =~= s2.data.subrange(s2.start + nn1, s2.start + n1));
                                }
                                assert(sn1.data.subrange(sn1.start, sn1.start + nn1_) == sn2.data.subrange(sn2.start, sn2.start + nn1_));
                                if let Ok((sn2_, nn2_, xn2_)) = parser(sn2) {
                                    assert(nn1_ == nn2_ && xn1_ == xn2_);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// A parser that consumes the rest of the input.
    pub open spec fn spec_parse_tail(s: SpecStream) -> SpecParseResult<Seq<u8>>
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.data.len() > usize::MAX {
            Err(ParseError::IntegerOverflow)
        } else if s.start > s.data.len() {
            Err(ParseError::Eof) // don't fail when start == data.len(), which is different from the uint parsers
        } else {
            let n = s.data.len() as int;
            Ok((
                SpecStream {
                    start: n,
                    ..s
                },
                (n - s.start) as nat,
                s.data.subrange(s.start, n),
            ))
        }
    }

    pub open spec fn spec_serialize_tail(s: SpecStream, v: Seq<u8>) -> SpecSerializeResult
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.start + v.len() > usize::MAX {
            Err(SerializeError::IntegerOverflow)
        } else if s.start + v.len() > s.data.len() {
            Err(SerializeError::NotEnoughSpace)
        } else if v.len() != s.data.len() - s.start {
            Err(SerializeError::TailLengthMismatch)
        } else {
            let n = v.len() as int;
            Ok((
                SpecStream {
                    start: s.start + n,
                    data: s.data.subrange(0, s.start) + v,
                },
                n as nat,
            ))
        }
    }

    pub exec fn parse_tail(s: Stream) -> (res: ParseResult<Vec<u8>>)
        ensures
            prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_tail(s))
    {
        if s.start < 0 {
            Err(ParseError::NegativeIndex)
        } else if s.start > s.data.length() {
            Err(ParseError::Eof)
        } else {
            let n = s.data.length();
            // data is the rest of the input starting from s.start
            let data = slice_to_vec(slice_subrange(vec_as_slice(&s.data), s.start, n));
            Ok((
                Stream {
                    start: n,
                    ..s
                },
                (n - s.start),
                data,
            ))
        }
    }

    pub exec fn serialize_tail(s: Stream, v: Vec<u8>) -> (res: SerializeResult)
        ensures
            prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_tail(s, v))
    {
        if s.start < 0 {
            Err(SerializeError::NegativeIndex)
        } else if s.start > usize::MAX - v.length() {
            Err(SerializeError::IntegerOverflow)
        } else if s.start + v.length() > s.data.length() {
            Err(SerializeError::NotEnoughSpace)
        } else if v.length() != s.data.length() - s.start {
            Err(SerializeError::TailLengthMismatch)
        } else {
            let n = v.length();

            let mut data: Vec<u8> = slice_to_vec(slice_subrange(vec_as_slice(&s.data), 0, s.start));
            let mut v = v;
            vec_append(&mut data, &mut v);
            Ok((
                Stream {
                    start: s.start + n,
                    data
                },
                n,
            ))
        }
    }

    pub proof fn lemma_parse_tail_well_behaved()
        ensures
            prop_parse_well_behaved(|s| spec_parse_tail(s))
    {
        reveal(prop_parse_well_behaved::<Seq<u8>>);
        let spec_parse_tail = |s| spec_parse_tail(s);
        assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_tail, s) by {
            lemma_parse_tail_well_behaved_on(s)
        }
    }

    pub proof fn lemma_serialize_tail_well_behaved()
        ensures
            prop_serialize_well_behaved(|s, v| spec_serialize_tail(s, v))
    {
        reveal(prop_serialize_well_behaved::<Seq<u8>>);
        let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
        assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_tail, s, v) by {
            lemma_serialize_tail_well_behaved_on(s, v)
        }
    }

    pub proof fn lemma_serialize_tail_deterministic()
        ensures
            prop_serialize_deterministic(|s, v| spec_serialize_tail(s, v))
    {
        reveal(prop_serialize_deterministic::<Seq<u8>>);
        let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
        assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_tail, s1, s2, v) by {
            lemma_serialize_tail_deterministic_on(s1, s2, v)
        }
    }

    /// tail does not has strong prefix property!

    pub proof fn lemma_parse_tail_correct()
        ensures
            prop_parse_correct(|s| spec_parse_tail(s), |s, v| spec_serialize_tail(s, v))
    {
        reveal(prop_parse_correct::<Seq<u8>>);
        let spec_parse_tail = |s| spec_parse_tail(s);
        let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
        assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_tail, spec_serialize_tail, s, v) by {
            lemma_parse_tail_correct_on(s, v)
        }
    }

    pub proof fn lemma_parse_tail_serialize_inverse()
        ensures
            prop_parse_serialize_inverse(|s| spec_parse_tail(s), |s, v| spec_serialize_tail(s, v))
    {
        reveal(prop_parse_serialize_inverse::<Seq<u8>>);
        let spec_parse_tail = |s| spec_parse_tail(s);
        let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
        assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_tail, spec_serialize_tail, s) by {
            lemma_parse_tail_serialize_inverse_on(s)
        }
    }

    pub proof fn lemma_parse_tail_nonmalleable()
        ensures
            prop_parse_nonmalleable(|s| spec_parse_tail(s))
    {
        lemma_parse_tail_serialize_inverse();
        lemma_serialize_tail_deterministic();
        lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_tail(s), |s, v| spec_serialize_tail(s, v));
    }

    proof fn lemma_parse_tail_well_behaved_on(s: SpecStream)
        ensures
            prop_parse_well_behaved_on(|s| spec_parse_tail(s), s)
    {}

    proof fn lemma_serialize_tail_well_behaved_on(s: SpecStream, v: Seq<u8>)
        ensures
            prop_serialize_well_behaved_on(|s, v| spec_serialize_tail(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_tail(s, v) {
            assert(n == v.len());
            assert(sout.data.len() =~= s.data.len());
            assert(sout.data.subrange(0, s.start) =~= s.data.subrange(0, s.start));
            assert(sout.data.subrange(s.start + n, s.data.len() as int) =~= s.data.subrange(s.start + n, s.data.len() as int));
        }
    }

    proof fn lemma_serialize_tail_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
        ensures
            prop_serialize_deterministic_on(|s, v| spec_serialize_tail(s, v), s1, s2, v)
    {
        let n = v.len();
        if let (Ok((sout1, n1)), Ok((sout2, n2))) = (spec_serialize_tail(s1, v), spec_serialize_tail(s2, v)) {
            assert(n1 == n && n2 == n);
            assert(sout1.data.subrange(s1.start, s1.start + n) =~= sout2.data.subrange(s2.start, s2.start + n));
        }
    }

    /// tail does not has strong prefix property! which is fine!

    proof fn lemma_parse_tail_correct_on(s: SpecStream, v: Seq<u8>)
        ensures
            prop_parse_correct_on(|s| spec_parse_tail(s), |s, v| spec_serialize_tail(s, v), s, v)
    {
        if let Ok((sout, n)) = spec_serialize_tail(s, v) {
            if let Ok((_, m, res)) = spec_parse_tail(SpecStream {start: s.start, ..sout}) {
                assert(n == m);
                assert(res =~= v);
            }
        }
    }

    proof fn lemma_parse_tail_serialize_inverse_on(s: SpecStream)
        ensures
            prop_parse_serialize_inverse_on(|s| spec_parse_tail(s), |s, v| spec_serialize_tail(s, v), s)
    {
        if let Ok((sout, n, x)) = spec_parse_tail(s) {
            if let Ok((sout2, m)) = spec_serialize_tail(s, x) {
                assert(n == m);
                assert(sout.data =~= sout2.data);
            } else {
                assert(false);
            }
        }
    }
}
verus!{

pub open spec fn spec_parse_4_u8s(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    spec_parse_repeat_n(spec_parse_u8_le, 4)(s)
}

pub open spec fn spec_serialize_4_u8s(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    spec_serialize_repeat_n(spec_serialize_u8_le, 4)(s, vs)
}

pub proof fn lemma_parse_4_u8s_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_4_u8s(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_4_u8s, s) by {
        lemma_parse_4_u8s_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_4_u8s_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_4_u8s(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_4_u8s = |s, vs| spec_serialize_4_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_4_u8s, s, vs) by {
        lemma_serialize_4_u8s_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_4_u8s_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_4_u8s(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_4_u8s = |s, vs| spec_serialize_4_u8s(s, vs);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_4_u8s, s1, s2, v) by {
        lemma_serialize_4_u8s_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_4_u8s_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_4_u8s(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_4_u8s, s1, s2) by {
        lemma_parse_4_u8s_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_4_u8s_correct()
    ensures prop_parse_correct(|s| spec_parse_4_u8s(s), |s, vs| spec_serialize_4_u8s(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_serialize_4_u8s = |s, vs| spec_serialize_4_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_4_u8s, spec_serialize_4_u8s, s, vs) by {
        lemma_parse_4_u8s_correct_on(s, vs);
    }
}

pub proof fn lemma_parse_4_u8s_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_4_u8s(s), |s, v| spec_serialize_4_u8s(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_serialize_4_u8s = |s, vs| spec_serialize_4_u8s(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_4_u8s, spec_serialize_4_u8s, s) by {
        lemma_parse_4_u8s_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_4_u8s_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_4_u8s(s))
{
    lemma_parse_4_u8s_serialize_inverse();
    lemma_serialize_4_u8s_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_4_u8s(s), |s, v| spec_serialize_4_u8s(s, v));
}

proof fn lemma_parse_4_u8s_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_4_u8s(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 4, s);
}

proof fn lemma_serialize_4_u8s_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_4_u8s(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 4, s, vs);
}

proof fn lemma_serialize_4_u8s_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_4_u8s(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 4, s1, s2, v);
}

proof fn lemma_parse_4_u8s_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_4_u8s(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 4);
}

proof fn lemma_parse_4_u8s_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_4_u8s(s), |s, vs| spec_serialize_4_u8s(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 4, s, vs);
}

proof fn lemma_parse_4_u8s_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_4_u8s(s), |s, v| spec_serialize_4_u8s(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 4, s);
}

pub exec fn parse_4_u8s(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 4, s)
}

pub exec fn serialize_4_u8s(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_4_u8s(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 4, s, vs)
}

pub open spec fn spec_parse_4_u8s_6523411079649600299(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    match spec_parse_repeat_n(spec_parse_u8_le, 4)(s) {
        Ok((s, n, xs)) => {
            if xs == seq![1u8, 0u8, 0u8, 0u8] {
                Ok((s, n, xs))
            } else {
                Err(ParseError::ConstMismatch)
            }
        }
        Err(e) => Err(e),
    }
}

pub open spec fn spec_serialize_4_u8s_6523411079649600299(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    if vs == seq![1u8, 0u8, 0u8, 0u8] {
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        spec_serialize_repeat_n(spec_serialize_u8_le, 4)(s, vs)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub proof fn lemma_parse_4_u8s_6523411079649600299_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_4_u8s_6523411079649600299(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_4_u8s_6523411079649600299 = |s| spec_parse_4_u8s_6523411079649600299(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_4_u8s_6523411079649600299, s) by {
        lemma_parse_4_u8s_6523411079649600299_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_4_u8s_6523411079649600299_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_4_u8s_6523411079649600299(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_4_u8s_6523411079649600299 = |s, vs| spec_serialize_4_u8s_6523411079649600299(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_4_u8s_6523411079649600299, s, vs) by {
        lemma_serialize_4_u8s_6523411079649600299_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_4_u8s_6523411079649600299_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_4_u8s_6523411079649600299(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_4_u8s_6523411079649600299 = |s, v| spec_serialize_4_u8s_6523411079649600299(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_4_u8s_6523411079649600299, s1, s2, v) by {
        lemma_serialize_4_u8s_6523411079649600299_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_4_u8s_6523411079649600299_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_4_u8s_6523411079649600299(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_4_u8s_6523411079649600299 = |s| spec_parse_4_u8s_6523411079649600299(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_4_u8s_6523411079649600299, s1, s2) by {
        lemma_parse_4_u8s_6523411079649600299_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_4_u8s_6523411079649600299_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_4_u8s_6523411079649600299(s), |s, vs| spec_serialize_4_u8s_6523411079649600299(s, vs))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_4_u8s_6523411079649600299 = |s| spec_parse_4_u8s_6523411079649600299(s);
    let spec_serialize_4_u8s_6523411079649600299 = |s, vs| spec_serialize_4_u8s_6523411079649600299(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_4_u8s_6523411079649600299, spec_serialize_4_u8s_6523411079649600299, s) by {
        lemma_parse_4_u8s_6523411079649600299_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_4_u8s_6523411079649600299_correct()
    ensures prop_parse_correct(|s| spec_parse_4_u8s_6523411079649600299(s), |s, vs| spec_serialize_4_u8s_6523411079649600299(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_4_u8s_6523411079649600299 = |s| spec_parse_4_u8s_6523411079649600299(s);
    let spec_serialize_4_u8s_6523411079649600299 = |s, vs| spec_serialize_4_u8s_6523411079649600299(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_4_u8s_6523411079649600299, spec_serialize_4_u8s_6523411079649600299, s, vs) by {
        lemma_parse_4_u8s_6523411079649600299_correct_on(s, vs);
    }
}

proof fn lemma_parse_4_u8s_6523411079649600299_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_4_u8s_6523411079649600299(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 4, s);
}

proof fn lemma_serialize_4_u8s_6523411079649600299_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_4_u8s_6523411079649600299(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 4, s, vs);
}

pub proof fn lemma_serialize_4_u8s_6523411079649600299_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_4_u8s_6523411079649600299(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 4, s1, s2, v);
}

proof fn lemma_parse_4_u8s_6523411079649600299_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_4_u8s_6523411079649600299(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 4);
}

proof fn lemma_parse_4_u8s_6523411079649600299_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_4_u8s_6523411079649600299(s), |s, v| spec_serialize_4_u8s_6523411079649600299(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 4, s);
}

proof fn lemma_parse_4_u8s_6523411079649600299_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_4_u8s_6523411079649600299(s), |s, vs| spec_serialize_4_u8s_6523411079649600299(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 4, s, vs);
}

pub exec fn vec_u8_check_6523411079649600299(xs : &Vec<u8>) -> (res : bool)
    requires xs.dview().len() == 4
    ensures res <==> xs.dview() == seq![1u8, 0u8, 0u8, 0u8]
{
    let mut constant = vec_new();
    vec_push(&mut constant, 1u8);
    vec_push(&mut constant, 0u8);
    vec_push(&mut constant, 0u8);
    vec_push(&mut constant, 0u8);
    let mut i = 0;
    while i < 4
        invariant
            0 <= i <= 4,
            constant.dview() == seq![1u8, 0u8, 0u8, 0u8],
            xs.dview().len() == 4,
            xs.dview().subrange(0, i as int) =~= constant.dview().subrange(0, i as int),
    {
        let (constant_i, xi) = (*vec_index(&constant, i), *vec_index(&xs, i));
        if constant_i == xi {
            i = i + 1;
            assert(xs.dview().subrange(0, i as int) =~= xs.dview().subrange(0, i as int - 1).push(xi));
        } else {
            return false;
        }
    }
    assert(xs.dview() =~= seq![1u8, 0u8, 0u8, 0u8]) by {
        assert(xs.dview().subrange(0, 4) =~= xs.dview());
    }

    true
}

pub exec fn parse_4_u8s_6523411079649600299(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s_6523411079649600299(s)),
        res.is_ok() ==> res.unwrap().2.dview() == seq![1u8, 0u8, 0u8, 0u8]
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    match parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 4, s) {
        Ok((s0, n, xs)) => {
            assert(xs.dview().len() == 4) by {
                lemma_parse_u8_le_well_behaved(); lemma_parse_repeat_n_well_behaved(spec_parse_u8_le, 4);
            }

            if vec_u8_check_6523411079649600299(&xs) {
                Ok((s0, n, xs))
            } else {
                Err(ParseError::ConstMismatch)
            }
        }
        Err(e) => Err(e),
    }
}

pub exec fn serialize_4_u8s_6523411079649600299(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_4_u8s_6523411079649600299(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    if vs.length() == 4 && vec_u8_check_6523411079649600299(&vs) {
        serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 4, s, vs)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub open spec fn spec_parse_91_u8s(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    spec_parse_repeat_n(spec_parse_u8_le, 91)(s)
}

pub open spec fn spec_serialize_91_u8s(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    spec_serialize_repeat_n(spec_serialize_u8_le, 91)(s, vs)
}

pub proof fn lemma_parse_91_u8s_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_91_u8s(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_91_u8s, s) by {
        lemma_parse_91_u8s_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_91_u8s_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_91_u8s(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_91_u8s = |s, vs| spec_serialize_91_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_91_u8s, s, vs) by {
        lemma_serialize_91_u8s_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_91_u8s_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_91_u8s(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_91_u8s = |s, vs| spec_serialize_91_u8s(s, vs);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_91_u8s, s1, s2, v) by {
        lemma_serialize_91_u8s_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_91_u8s_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_91_u8s(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_91_u8s, s1, s2) by {
        lemma_parse_91_u8s_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_91_u8s_correct()
    ensures prop_parse_correct(|s| spec_parse_91_u8s(s), |s, vs| spec_serialize_91_u8s(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_serialize_91_u8s = |s, vs| spec_serialize_91_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_91_u8s, spec_serialize_91_u8s, s, vs) by {
        lemma_parse_91_u8s_correct_on(s, vs);
    }
}

pub proof fn lemma_parse_91_u8s_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_91_u8s(s), |s, v| spec_serialize_91_u8s(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_serialize_91_u8s = |s, vs| spec_serialize_91_u8s(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_91_u8s, spec_serialize_91_u8s, s) by {
        lemma_parse_91_u8s_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_91_u8s_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_91_u8s(s))
{
    lemma_parse_91_u8s_serialize_inverse();
    lemma_serialize_91_u8s_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_91_u8s(s), |s, v| spec_serialize_91_u8s(s, v));
}

proof fn lemma_parse_91_u8s_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_91_u8s(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 91, s);
}

proof fn lemma_serialize_91_u8s_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_91_u8s(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 91, s, vs);
}

proof fn lemma_serialize_91_u8s_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_91_u8s(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 91, s1, s2, v);
}

proof fn lemma_parse_91_u8s_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_91_u8s(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 91);
}

proof fn lemma_parse_91_u8s_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_91_u8s(s), |s, vs| spec_serialize_91_u8s(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 91, s, vs);
}

proof fn lemma_parse_91_u8s_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_91_u8s(s), |s, v| spec_serialize_91_u8s(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 91, s);
}

pub exec fn parse_91_u8s(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_91_u8s(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 91, s)
}

pub exec fn serialize_91_u8s(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_91_u8s(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 91, s, vs)
}

pub open spec fn spec_parse_107_u8s(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    spec_parse_repeat_n(spec_parse_u8_le, 107)(s)
}

pub open spec fn spec_serialize_107_u8s(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    spec_serialize_repeat_n(spec_serialize_u8_le, 107)(s, vs)
}

pub proof fn lemma_parse_107_u8s_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_107_u8s(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_107_u8s = |s| spec_parse_107_u8s(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_107_u8s, s) by {
        lemma_parse_107_u8s_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_107_u8s_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_107_u8s(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_107_u8s = |s, vs| spec_serialize_107_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_107_u8s, s, vs) by {
        lemma_serialize_107_u8s_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_107_u8s_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_107_u8s(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_107_u8s = |s, vs| spec_serialize_107_u8s(s, vs);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_107_u8s, s1, s2, v) by {
        lemma_serialize_107_u8s_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_107_u8s_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_107_u8s(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_107_u8s = |s| spec_parse_107_u8s(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_107_u8s, s1, s2) by {
        lemma_parse_107_u8s_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_107_u8s_correct()
    ensures prop_parse_correct(|s| spec_parse_107_u8s(s), |s, vs| spec_serialize_107_u8s(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_107_u8s = |s| spec_parse_107_u8s(s);
    let spec_serialize_107_u8s = |s, vs| spec_serialize_107_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_107_u8s, spec_serialize_107_u8s, s, vs) by {
        lemma_parse_107_u8s_correct_on(s, vs);
    }
}

pub proof fn lemma_parse_107_u8s_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_107_u8s(s), |s, v| spec_serialize_107_u8s(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_107_u8s = |s| spec_parse_107_u8s(s);
    let spec_serialize_107_u8s = |s, vs| spec_serialize_107_u8s(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_107_u8s, spec_serialize_107_u8s, s) by {
        lemma_parse_107_u8s_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_107_u8s_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_107_u8s(s))
{
    lemma_parse_107_u8s_serialize_inverse();
    lemma_serialize_107_u8s_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_107_u8s(s), |s, v| spec_serialize_107_u8s(s, v));
}

proof fn lemma_parse_107_u8s_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_107_u8s(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 107, s);
}

proof fn lemma_serialize_107_u8s_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_107_u8s(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 107, s, vs);
}

proof fn lemma_serialize_107_u8s_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_107_u8s(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 107, s1, s2, v);
}

proof fn lemma_parse_107_u8s_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_107_u8s(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 107);
}

proof fn lemma_parse_107_u8s_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_107_u8s(s), |s, vs| spec_serialize_107_u8s(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 107, s, vs);
}

proof fn lemma_parse_107_u8s_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_107_u8s(s), |s, v| spec_serialize_107_u8s(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 107, s);
}

pub exec fn parse_107_u8s(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_107_u8s(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 107, s)
}

pub exec fn serialize_107_u8s(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_107_u8s(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 107, s, vs)
}

pub open spec fn spec_parse_28_u8s(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    spec_parse_repeat_n(spec_parse_u8_le, 28)(s)
}

pub open spec fn spec_serialize_28_u8s(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    spec_serialize_repeat_n(spec_serialize_u8_le, 28)(s, vs)
}

pub proof fn lemma_parse_28_u8s_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_28_u8s(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_28_u8s = |s| spec_parse_28_u8s(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_28_u8s, s) by {
        lemma_parse_28_u8s_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_28_u8s_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_28_u8s(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_28_u8s = |s, vs| spec_serialize_28_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_28_u8s, s, vs) by {
        lemma_serialize_28_u8s_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_28_u8s_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_28_u8s(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_28_u8s = |s, vs| spec_serialize_28_u8s(s, vs);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_28_u8s, s1, s2, v) by {
        lemma_serialize_28_u8s_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_28_u8s_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_28_u8s(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_28_u8s = |s| spec_parse_28_u8s(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_28_u8s, s1, s2) by {
        lemma_parse_28_u8s_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_28_u8s_correct()
    ensures prop_parse_correct(|s| spec_parse_28_u8s(s), |s, vs| spec_serialize_28_u8s(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_28_u8s = |s| spec_parse_28_u8s(s);
    let spec_serialize_28_u8s = |s, vs| spec_serialize_28_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_28_u8s, spec_serialize_28_u8s, s, vs) by {
        lemma_parse_28_u8s_correct_on(s, vs);
    }
}

pub proof fn lemma_parse_28_u8s_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_28_u8s(s), |s, v| spec_serialize_28_u8s(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_28_u8s = |s| spec_parse_28_u8s(s);
    let spec_serialize_28_u8s = |s, vs| spec_serialize_28_u8s(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_28_u8s, spec_serialize_28_u8s, s) by {
        lemma_parse_28_u8s_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_28_u8s_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_28_u8s(s))
{
    lemma_parse_28_u8s_serialize_inverse();
    lemma_serialize_28_u8s_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_28_u8s(s), |s, v| spec_serialize_28_u8s(s, v));
}

proof fn lemma_parse_28_u8s_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_28_u8s(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 28, s);
}

proof fn lemma_serialize_28_u8s_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_28_u8s(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 28, s, vs);
}

proof fn lemma_serialize_28_u8s_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_28_u8s(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 28, s1, s2, v);
}

proof fn lemma_parse_28_u8s_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_28_u8s(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 28);
}

proof fn lemma_parse_28_u8s_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_28_u8s(s), |s, vs| spec_serialize_28_u8s(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 28, s, vs);
}

proof fn lemma_parse_28_u8s_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_28_u8s(s), |s, v| spec_serialize_28_u8s(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 28, s);
}

pub exec fn parse_28_u8s(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_28_u8s(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 28, s)
}

pub exec fn serialize_28_u8s(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_28_u8s(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 28, s, vs)
}

pub open spec fn spec_parse_64_u8s(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    spec_parse_repeat_n(spec_parse_u8_le, 64)(s)
}

pub open spec fn spec_serialize_64_u8s(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    spec_serialize_repeat_n(spec_serialize_u8_le, 64)(s, vs)
}

pub proof fn lemma_parse_64_u8s_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_64_u8s(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_64_u8s, s) by {
        lemma_parse_64_u8s_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_64_u8s_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_64_u8s(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_64_u8s = |s, vs| spec_serialize_64_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_64_u8s, s, vs) by {
        lemma_serialize_64_u8s_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_64_u8s_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_64_u8s(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_64_u8s = |s, vs| spec_serialize_64_u8s(s, vs);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_64_u8s, s1, s2, v) by {
        lemma_serialize_64_u8s_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_64_u8s_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_64_u8s(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_64_u8s, s1, s2) by {
        lemma_parse_64_u8s_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_64_u8s_correct()
    ensures prop_parse_correct(|s| spec_parse_64_u8s(s), |s, vs| spec_serialize_64_u8s(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    let spec_serialize_64_u8s = |s, vs| spec_serialize_64_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_64_u8s, spec_serialize_64_u8s, s, vs) by {
        lemma_parse_64_u8s_correct_on(s, vs);
    }
}

pub proof fn lemma_parse_64_u8s_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_64_u8s(s), |s, v| spec_serialize_64_u8s(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    let spec_serialize_64_u8s = |s, vs| spec_serialize_64_u8s(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_64_u8s, spec_serialize_64_u8s, s) by {
        lemma_parse_64_u8s_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_64_u8s_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_64_u8s(s))
{
    lemma_parse_64_u8s_serialize_inverse();
    lemma_serialize_64_u8s_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_64_u8s(s), |s, v| spec_serialize_64_u8s(s, v));
}

proof fn lemma_parse_64_u8s_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_64_u8s(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 64, s);
}

proof fn lemma_serialize_64_u8s_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_64_u8s(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 64, s, vs);
}

proof fn lemma_serialize_64_u8s_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_64_u8s(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 64, s1, s2, v);
}

proof fn lemma_parse_64_u8s_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_64_u8s(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 64);
}

proof fn lemma_parse_64_u8s_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_64_u8s(s), |s, vs| spec_serialize_64_u8s(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 64, s, vs);
}

proof fn lemma_parse_64_u8s_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_64_u8s(s), |s, v| spec_serialize_64_u8s(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 64, s);
}

pub exec fn parse_64_u8s(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_64_u8s(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 64, s)
}

pub exec fn serialize_64_u8s(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_64_u8s(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 64, s, vs)
}
pub struct SpecOwlMsg1 {
    owl__msg1_tag: Seq<u8>,
    owl__msg1_sender: Seq<u8>,
    owl__msg1_ephemeral: Seq<u8>,
    owl__msg1_static: Seq<u8>,
    owl__msg1_timestamp: Seq<u8>,
    owl__msg1_mac1: Seq<u8>,

}
pub struct OwlMsg1 {
    owl__msg1_tag: Vec<u8>,
    owl__msg1_sender: Vec<u8>,
    owl__msg1_ephemeral: Vec<u8>,
    owl__msg1_static: Vec<u8>,
    owl__msg1_timestamp: Vec<u8>,
    owl__msg1_mac1: Vec<u8>,

}

pub open spec fn spec_parse_6_fold<R1, R2, R3, R4, R5, R6>(
    parser1: FnSpec(SpecStream) -> SpecParseResult<R1>,
    parser2: FnSpec(SpecStream) -> SpecParseResult<R2>,
    parser3: FnSpec(SpecStream) -> SpecParseResult<R3>,
    parser4: FnSpec(SpecStream) -> SpecParseResult<R4>,
    parser5: FnSpec(SpecStream) -> SpecParseResult<R5>,
    parser6: FnSpec(SpecStream) -> SpecParseResult<R6>) -> FnSpec(SpecStream) -> SpecParseResult<(((((R1, R2), R3), R4), R5), R6)>
{
    spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(parser1, parser2), parser3), parser4), parser5), parser6)
}

pub exec fn parse_6_fold<P1, P2, P3, P4, P5, P6, R1, R2, R3, R4, R5, R6>(
    exec_parser1: P1,
    exec_parser2: P2,
    exec_parser3: P3,
    exec_parser4: P4,
    exec_parser5: P5,
    exec_parser6: P6,
    Ghost(spec_parser1): Ghost<FnSpec(SpecStream) -> SpecParseResult<R1::V>>,
    Ghost(spec_parser2): Ghost<FnSpec(SpecStream) -> SpecParseResult<R2::V>>,
    Ghost(spec_parser3): Ghost<FnSpec(SpecStream) -> SpecParseResult<R3::V>>,
    Ghost(spec_parser4): Ghost<FnSpec(SpecStream) -> SpecParseResult<R4::V>>,
    Ghost(spec_parser5): Ghost<FnSpec(SpecStream) -> SpecParseResult<R5::V>>,
    Ghost(spec_parser6): Ghost<FnSpec(SpecStream) -> SpecParseResult<R6::V>>,
    s: Stream) -> (res: ParseResult<(((((R1, R2), R3), R4), R5), R6)>)
    where
    R1: DView,
    P1: FnOnce(Stream) -> ParseResult<R1>,
    R2: DView,
    P2: FnOnce(Stream) -> ParseResult<R2>,
    R3: DView,
    P3: FnOnce(Stream) -> ParseResult<R3>,
    R4: DView,
    P4: FnOnce(Stream) -> ParseResult<R4>,
    R5: DView,
    P5: FnOnce(Stream) -> ParseResult<R5>,
    R6: DView,
    P6: FnOnce(Stream) -> ParseResult<R6>,
    requires
        prop_parse_exec_spec_equiv(exec_parser1, spec_parser1),
        prop_parse_exec_spec_equiv(exec_parser2, spec_parser2),
        prop_parse_exec_spec_equiv(exec_parser3, spec_parser3),
        prop_parse_exec_spec_equiv(exec_parser4, spec_parser4),
        prop_parse_exec_spec_equiv(exec_parser5, spec_parser5),
        prop_parse_exec_spec_equiv(exec_parser6, spec_parser6),
    ensures
        prop_parse_exec_spec_equiv_on(s, res, spec_parse_6_fold(spec_parser1, spec_parser2, spec_parser3, spec_parser4, spec_parser5, spec_parser6))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_2_fold = |s| -> (res: ParseResult<(R1, R2)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parser1, spec_parser2)), { parse_pair(exec_parser1, exec_parser2, Ghost(spec_parser1), Ghost(spec_parser2), s) };
    let parse_3_fold = |s| -> (res: ParseResult<((R1, R2), R3)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)), { parse_pair(parse_2_fold, exec_parser3, Ghost(spec_parse_pair(spec_parser1, spec_parser2)), Ghost(spec_parser3), s) };
    let parse_4_fold = |s| -> (res: ParseResult<(((R1, R2), R3), R4)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4)), { parse_pair(parse_3_fold, exec_parser4, Ghost(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)), Ghost(spec_parser4), s) };
    let parse_5_fold = |s| -> (res: ParseResult<((((R1, R2), R3), R4), R5)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4), spec_parser5)), { parse_pair(parse_4_fold, exec_parser5, Ghost(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4)), Ghost(spec_parser5), s) };
    parse_pair(parse_5_fold, exec_parser6, Ghost(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4), spec_parser5)), Ghost(spec_parser6), s)
}



pub open spec fn spec_serialize_6_fold<T1, T2, T3, T4, T5, T6>(
    serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
    serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult,
    serializer3: FnSpec(SpecStream, T3) -> SpecSerializeResult,
    serializer4: FnSpec(SpecStream, T4) -> SpecSerializeResult,
    serializer5: FnSpec(SpecStream, T5) -> SpecSerializeResult,
    serializer6: FnSpec(SpecStream, T6) -> SpecSerializeResult) -> FnSpec(SpecStream, (((((T1, T2), T3), T4), T5), T6)) -> SpecSerializeResult
{
    spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(serializer1, serializer2), serializer3), serializer4), serializer5), serializer6)
}
pub exec fn serialize_6_fold<S1, S2, S3, S4, S5, S6, T1, T2, T3, T4, T5, T6>(
    exec_serializer1: S1,
    exec_serializer2: S2,
    exec_serializer3: S3,
    exec_serializer4: S4,
    exec_serializer5: S5,
    exec_serializer6: S6,
    Ghost(spec_serializer1): Ghost<FnSpec(SpecStream, T1::V) -> SpecSerializeResult>,
    Ghost(spec_serializer2): Ghost<FnSpec(SpecStream, T2::V) -> SpecSerializeResult>,
    Ghost(spec_serializer3): Ghost<FnSpec(SpecStream, T3::V) -> SpecSerializeResult>,
    Ghost(spec_serializer4): Ghost<FnSpec(SpecStream, T4::V) -> SpecSerializeResult>,
    Ghost(spec_serializer5): Ghost<FnSpec(SpecStream, T5::V) -> SpecSerializeResult>,
    Ghost(spec_serializer6): Ghost<FnSpec(SpecStream, T6::V) -> SpecSerializeResult>,
    s: Stream, v: (((((T1, T2), T3), T4), T5), T6)) -> (res: SerializeResult)
    where
    T1: std::fmt::Debug + DView,
    S1: FnOnce(Stream, T1) -> SerializeResult,
    T2: std::fmt::Debug + DView,
    S2: FnOnce(Stream, T2) -> SerializeResult,
    T3: std::fmt::Debug + DView,
    S3: FnOnce(Stream, T3) -> SerializeResult,
    T4: std::fmt::Debug + DView,
    S4: FnOnce(Stream, T4) -> SerializeResult,
    T5: std::fmt::Debug + DView,
    S5: FnOnce(Stream, T5) -> SerializeResult,
    T6: std::fmt::Debug + DView,
    S6: FnOnce(Stream, T6) -> SerializeResult,
    requires
        prop_serialize_exec_spec_equiv(exec_serializer1, spec_serializer1),
        prop_serialize_exec_spec_equiv(exec_serializer2, spec_serializer2),
        prop_serialize_exec_spec_equiv(exec_serializer3, spec_serializer3),
        prop_serialize_exec_spec_equiv(exec_serializer4, spec_serializer4),
        prop_serialize_exec_spec_equiv(exec_serializer5, spec_serializer5),
        prop_serialize_exec_spec_equiv(exec_serializer6, spec_serializer6),
    ensures
        prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_6_fold(spec_serializer1, spec_serializer2, spec_serializer3, spec_serializer4, spec_serializer5, spec_serializer6))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }
    let serialize_2_fold = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serializer1, spec_serializer2)), { serialize_pair(exec_serializer1, exec_serializer2, Ghost(spec_serializer1), Ghost(spec_serializer2), s, v) };
    let serialize_3_fold = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3)), { serialize_pair(serialize_2_fold, exec_serializer3, Ghost(spec_serialize_pair(spec_serializer1, spec_serializer2)), Ghost(spec_serializer3), s, v) };
    let serialize_4_fold = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3), spec_serializer4)), { serialize_pair(serialize_3_fold, exec_serializer4, Ghost(spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3)), Ghost(spec_serializer4), s, v) };
    let serialize_5_fold = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3), spec_serializer4), spec_serializer5)), { serialize_pair(serialize_4_fold, exec_serializer5, Ghost(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3), spec_serializer4)), Ghost(spec_serializer5), s, v) };
    serialize_pair(serialize_5_fold, exec_serializer6, Ghost(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3), spec_serializer4), spec_serializer5)), Ghost(spec_serializer6), s, v)
}


pub open spec fn spec_parse_owl_msg1(s: SpecStream) -> SpecParseResult<(((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)>
{
    let spec_parse_4_u8s_6523411079649600299 = |s| spec_parse_4_u8s_6523411079649600299(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_107_u8s = |s| spec_parse_107_u8s(s);
    let spec_parse_28_u8s = |s| spec_parse_28_u8s(s);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);

    spec_parse_6_fold(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s, spec_parse_91_u8s, spec_parse_107_u8s, spec_parse_28_u8s, spec_parse_64_u8s)(s)
}

pub open spec fn spec_serialize_owl_msg1(s: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)) -> SpecSerializeResult
{
    let spec_serialize_4_u8s_6523411079649600299 = |s, v| spec_serialize_4_u8s_6523411079649600299(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_107_u8s = |s, v| spec_serialize_107_u8s(s, v);
    let spec_serialize_28_u8s = |s, v| spec_serialize_28_u8s(s, v);
    let spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);

    spec_serialize_6_fold(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s, spec_serialize_91_u8s, spec_serialize_107_u8s, spec_serialize_28_u8s, spec_serialize_64_u8s)(s, v)
}

pub proof fn lemma_parse_owl_msg1_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_owl_msg1(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_owl_msg1 = |s| spec_parse_owl_msg1(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_owl_msg1, s) by {
        lemma_parse_owl_msg1_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_owl_msg1_well_behaved()
    ensures prop_serialize_well_behaved(|s, v| spec_serialize_owl_msg1(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_owl_msg1 = |s, v| spec_serialize_owl_msg1(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_owl_msg1, s, v) by {
        lemma_serialize_owl_msg1_well_behaved_on(s, v);
    }
}

pub proof fn lemma_serialize_owl_msg1_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_owl_msg1(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_owl_msg1 = |s, v| spec_serialize_owl_msg1(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_owl_msg1, s1, s2, v) by {
        lemma_serialize_owl_msg1_deterministic_on(s1, s2, v);
    }
}
    
pub proof fn lemma_parse_owl_msg1_correct()
    ensures prop_parse_correct(|s| spec_parse_owl_msg1(s), |s, v| spec_serialize_owl_msg1(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_owl_msg1 = |s| spec_parse_owl_msg1(s);
    let spec_serialize_owl_msg1 = |s, v| spec_serialize_owl_msg1(s, v);
    assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_owl_msg1, spec_serialize_owl_msg1, s, v) by {
        lemma_parse_owl_msg1_correct_on(s, v);
    }
}

pub proof fn lemma_parse_owl_msg1_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_owl_msg1(s), |s, v| spec_serialize_owl_msg1(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_owl_msg1 = |s| spec_parse_owl_msg1(s);
    let spec_serialize_owl_msg1 = |s, v| spec_serialize_owl_msg1(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_owl_msg1, spec_serialize_owl_msg1, s) by {
        lemma_parse_owl_msg1_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_owl_msg1_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_owl_msg1(s))
{
    lemma_parse_owl_msg1_serialize_inverse();
    lemma_serialize_owl_msg1_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_owl_msg1(s), |s, v| spec_serialize_owl_msg1(s, v));
}

pub proof fn lemma_parse_owl_msg1_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_owl_msg1(s), s)
{
    let spec_parse_4_u8s_6523411079649600299 = |s| spec_parse_4_u8s_6523411079649600299(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_107_u8s = |s| spec_parse_107_u8s(s);
    let spec_parse_28_u8s = |s| spec_parse_28_u8s(s);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    lemma_parse_4_u8s_6523411079649600299_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_107_u8s_well_behaved();
    lemma_parse_28_u8s_well_behaved();
    lemma_parse_64_u8s_well_behaved();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s);
    lemma_parse_pair_well_behaved_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s), spec_parse_64_u8s, s);
}

pub proof fn lemma_serialize_owl_msg1_well_behaved_on(s: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_well_behaved_on(|s, v| spec_serialize_owl_msg1(s, v), s, v)
{
    let spec_serialize_4_u8s_6523411079649600299 = |s, v| spec_serialize_4_u8s_6523411079649600299(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_107_u8s = |s, v| spec_serialize_107_u8s(s, v);
    let spec_serialize_28_u8s = |s, v| spec_serialize_28_u8s(s, v);
    let spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);
    lemma_serialize_4_u8s_6523411079649600299_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_107_u8s_well_behaved();
    lemma_serialize_28_u8s_well_behaved();
    lemma_serialize_64_u8s_well_behaved();
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s);
    lemma_serialize_pair_well_behaved_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s), spec_serialize_64_u8s, s, v);
}

pub proof fn lemma_serialize_owl_msg1_deterministic_on(s1: SpecStream, s2: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_owl_msg1(s, v), s1, s2, v)
{
    let spec_serialize_4_u8s_6523411079649600299 = |s, v| spec_serialize_4_u8s_6523411079649600299(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_107_u8s = |s, v| spec_serialize_107_u8s(s, v);
    let spec_serialize_28_u8s = |s, v| spec_serialize_28_u8s(s, v);
    let spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);
    lemma_serialize_4_u8s_6523411079649600299_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_107_u8s_well_behaved();
    lemma_serialize_28_u8s_well_behaved();
    lemma_serialize_64_u8s_well_behaved();
    lemma_serialize_4_u8s_6523411079649600299_deterministic();
    lemma_serialize_4_u8s_deterministic();
    lemma_serialize_91_u8s_deterministic();
    lemma_serialize_107_u8s_deterministic();
    lemma_serialize_28_u8s_deterministic();
    lemma_serialize_64_u8s_deterministic();
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s);
    lemma_serialize_pair_deterministic_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s), spec_serialize_64_u8s, s1, s2, v);
}

pub proof fn lemma_parse_owl_msg1_correct_on(s: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_parse_correct_on(|s| spec_parse_owl_msg1(s), |s, v| spec_serialize_owl_msg1(s, v), s, v)
{
    let spec_parse_4_u8s_6523411079649600299 = |s| spec_parse_4_u8s_6523411079649600299(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_107_u8s = |s| spec_parse_107_u8s(s);
    let spec_parse_28_u8s = |s| spec_parse_28_u8s(s);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    let spec_serialize_4_u8s_6523411079649600299 = |s, v| spec_serialize_4_u8s_6523411079649600299(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_107_u8s = |s, v| spec_serialize_107_u8s(s, v);
    let spec_serialize_28_u8s = |s, v| spec_serialize_28_u8s(s, v);
    let spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);
    lemma_serialize_4_u8s_6523411079649600299_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_107_u8s_well_behaved();
    lemma_serialize_28_u8s_well_behaved();
    lemma_serialize_64_u8s_well_behaved();
    lemma_parse_4_u8s_6523411079649600299_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_107_u8s_well_behaved();
    lemma_parse_28_u8s_well_behaved();
    lemma_parse_64_u8s_well_behaved();
    lemma_parse_4_u8s_6523411079649600299_strong_prefix();
    lemma_parse_4_u8s_strong_prefix();
    lemma_parse_91_u8s_strong_prefix();
    lemma_parse_107_u8s_strong_prefix();
    lemma_parse_28_u8s_strong_prefix();
    lemma_parse_64_u8s_strong_prefix();
    lemma_parse_4_u8s_6523411079649600299_correct();
    lemma_parse_4_u8s_correct();
    lemma_parse_91_u8s_correct();
    lemma_parse_107_u8s_correct();
    lemma_parse_28_u8s_correct();
    lemma_parse_64_u8s_correct();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s);
    lemma_parse_pair_correct(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s, spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s);
    lemma_parse_pair_correct_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s), spec_parse_64_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s), spec_serialize_64_u8s, s, v);
}

pub proof fn lemma_parse_owl_msg1_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_owl_msg1(s), |s, v| spec_serialize_owl_msg1(s, v), s)
{
    let spec_parse_4_u8s_6523411079649600299 = |s| spec_parse_4_u8s_6523411079649600299(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_107_u8s = |s| spec_parse_107_u8s(s);
    let spec_parse_28_u8s = |s| spec_parse_28_u8s(s);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    let spec_serialize_4_u8s_6523411079649600299 = |s, v| spec_serialize_4_u8s_6523411079649600299(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_107_u8s = |s, v| spec_serialize_107_u8s(s, v);
    let spec_serialize_28_u8s = |s, v| spec_serialize_28_u8s(s, v);
    let spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);
    lemma_parse_4_u8s_6523411079649600299_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_107_u8s_well_behaved();
    lemma_parse_28_u8s_well_behaved();
    lemma_parse_64_u8s_well_behaved();
    lemma_serialize_4_u8s_6523411079649600299_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_107_u8s_well_behaved();
    lemma_serialize_28_u8s_well_behaved();
    lemma_serialize_64_u8s_well_behaved();
    lemma_parse_4_u8s_6523411079649600299_serialize_inverse();
    lemma_parse_4_u8s_serialize_inverse();
    lemma_parse_91_u8s_serialize_inverse();
    lemma_parse_107_u8s_serialize_inverse();
    lemma_parse_28_u8s_serialize_inverse();
    lemma_parse_64_u8s_serialize_inverse();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s, spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s);
    lemma_parse_pair_serialize_inverse_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s), spec_parse_64_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_107_u8s), spec_serialize_28_u8s), spec_serialize_64_u8s, s);
}

pub proof fn lemma_parse_owl_msg1_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_owl_msg1(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_owl_msg1 = |s| spec_parse_owl_msg1(s);
    assert forall |s1, s2| prop_parse_strong_prefix_on(spec_parse_owl_msg1, s1, s2) by {
        lemma_parse_owl_msg1_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_owl_msg1_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_owl_msg1(s), s1, s2)
{
    let spec_parse_4_u8s_6523411079649600299 = |s| spec_parse_4_u8s_6523411079649600299(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_107_u8s = |s| spec_parse_107_u8s(s);
    let spec_parse_28_u8s = |s| spec_parse_28_u8s(s);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    lemma_parse_4_u8s_6523411079649600299_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_107_u8s_well_behaved();
    lemma_parse_28_u8s_well_behaved();
    lemma_parse_64_u8s_well_behaved();
    lemma_parse_4_u8s_6523411079649600299_strong_prefix();
    lemma_parse_4_u8s_strong_prefix();
    lemma_parse_91_u8s_strong_prefix();
    lemma_parse_107_u8s_strong_prefix();
    lemma_parse_28_u8s_strong_prefix();
    lemma_parse_64_u8s_strong_prefix();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s);
    lemma_parse_pair_strong_prefix_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_107_u8s), spec_parse_28_u8s), spec_parse_64_u8s, s1, s2);
}

pub exec fn parse_owl_msg1(s: Stream) -> (res: ParseResult<(((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)>)
    ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_owl_msg1(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_4_u8s_6523411079649600299 = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s_6523411079649600299(s)) { parse_4_u8s_6523411079649600299(s) };
    let parse_4_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s(s)) { parse_4_u8s(s) };
    let parse_91_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_91_u8s(s)) { parse_91_u8s(s) };
    let parse_107_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_107_u8s(s)) { parse_107_u8s(s) };
    let parse_28_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_28_u8s(s)) { parse_28_u8s(s) };
    let parse_64_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_64_u8s(s)) { parse_64_u8s(s) };
    let ghost spec_parse_4_u8s_6523411079649600299 = |s| spec_parse_4_u8s_6523411079649600299(s);
    let ghost spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let ghost spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let ghost spec_parse_107_u8s = |s| spec_parse_107_u8s(s);
    let ghost spec_parse_28_u8s = |s| spec_parse_28_u8s(s);
    let ghost spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    let ghost spec_parse_owl_msg1 = spec_parse_6_fold(spec_parse_4_u8s_6523411079649600299, spec_parse_4_u8s, spec_parse_91_u8s, spec_parse_107_u8s, spec_parse_28_u8s, spec_parse_64_u8s);

    let parse_owl_msg1 = |s| -> (res: ParseResult<(((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_owl_msg1) { parse_6_fold(parse_4_u8s_6523411079649600299, parse_4_u8s, parse_91_u8s, parse_107_u8s, parse_28_u8s, parse_64_u8s, Ghost(spec_parse_4_u8s_6523411079649600299), Ghost(spec_parse_4_u8s), Ghost(spec_parse_91_u8s), Ghost(spec_parse_107_u8s), Ghost(spec_parse_28_u8s), Ghost(spec_parse_64_u8s), s) };
    assert(prop_parse_exec_spec_equiv(parse_owl_msg1, spec_parse_owl_msg1));

    parse_owl_msg1(s)
}
pub exec fn serialize_owl_msg1(s: Stream, v: (((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)) -> (res: SerializeResult)
    ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_owl_msg1(s, v))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }
    let serialize_4_u8s_6523411079649600299 = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_4_u8s_6523411079649600299(s, v)) { serialize_4_u8s_6523411079649600299(s, v) };
    let serialize_4_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_4_u8s(s, v)) { serialize_4_u8s(s, v) };
    let serialize_91_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_91_u8s(s, v)) { serialize_91_u8s(s, v) };
    let serialize_107_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_107_u8s(s, v)) { serialize_107_u8s(s, v) };
    let serialize_28_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_28_u8s(s, v)) { serialize_28_u8s(s, v) };
    let serialize_64_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_64_u8s(s, v)) { serialize_64_u8s(s, v) };
    let ghost spec_serialize_4_u8s_6523411079649600299 = |s, v| spec_serialize_4_u8s_6523411079649600299(s, v);
    let ghost spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let ghost spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let ghost spec_serialize_107_u8s = |s, v| spec_serialize_107_u8s(s, v);
    let ghost spec_serialize_28_u8s = |s, v| spec_serialize_28_u8s(s, v);
    let ghost spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);
    let ghost spec_serialize_owl_msg1 = spec_serialize_6_fold(spec_serialize_4_u8s_6523411079649600299, spec_serialize_4_u8s, spec_serialize_91_u8s, spec_serialize_107_u8s, spec_serialize_28_u8s, spec_serialize_64_u8s);

    let serialize_owl_msg1 = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_owl_msg1) { serialize_6_fold(serialize_4_u8s_6523411079649600299, serialize_4_u8s, serialize_91_u8s, serialize_107_u8s, serialize_28_u8s, serialize_64_u8s, Ghost(spec_serialize_4_u8s_6523411079649600299), Ghost(spec_serialize_4_u8s), Ghost(spec_serialize_91_u8s), Ghost(spec_serialize_107_u8s), Ghost(spec_serialize_28_u8s), Ghost(spec_serialize_64_u8s), s, v) };
    assert(prop_serialize_exec_spec_equiv(serialize_owl_msg1, spec_serialize_owl_msg1));

    serialize_owl_msg1(s, v)
}

pub open spec fn spec_parse_4_u8s_15022962709655904708(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    match spec_parse_repeat_n(spec_parse_u8_le, 4)(s) {
        Ok((s, n, xs)) => {
            if xs == seq![2u8, 0u8, 0u8, 0u8] {
                Ok((s, n, xs))
            } else {
                Err(ParseError::ConstMismatch)
            }
        }
        Err(e) => Err(e),
    }
}

pub open spec fn spec_serialize_4_u8s_15022962709655904708(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    if vs == seq![2u8, 0u8, 0u8, 0u8] {
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        spec_serialize_repeat_n(spec_serialize_u8_le, 4)(s, vs)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub proof fn lemma_parse_4_u8s_15022962709655904708_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_4_u8s_15022962709655904708(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_4_u8s_15022962709655904708 = |s| spec_parse_4_u8s_15022962709655904708(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_4_u8s_15022962709655904708, s) by {
        lemma_parse_4_u8s_15022962709655904708_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_4_u8s_15022962709655904708_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_4_u8s_15022962709655904708(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_4_u8s_15022962709655904708 = |s, vs| spec_serialize_4_u8s_15022962709655904708(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_4_u8s_15022962709655904708, s, vs) by {
        lemma_serialize_4_u8s_15022962709655904708_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_4_u8s_15022962709655904708_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_4_u8s_15022962709655904708(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_4_u8s_15022962709655904708 = |s, v| spec_serialize_4_u8s_15022962709655904708(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_4_u8s_15022962709655904708, s1, s2, v) by {
        lemma_serialize_4_u8s_15022962709655904708_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_4_u8s_15022962709655904708_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_4_u8s_15022962709655904708(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_4_u8s_15022962709655904708 = |s| spec_parse_4_u8s_15022962709655904708(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_4_u8s_15022962709655904708, s1, s2) by {
        lemma_parse_4_u8s_15022962709655904708_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_4_u8s_15022962709655904708_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_4_u8s_15022962709655904708(s), |s, vs| spec_serialize_4_u8s_15022962709655904708(s, vs))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_4_u8s_15022962709655904708 = |s| spec_parse_4_u8s_15022962709655904708(s);
    let spec_serialize_4_u8s_15022962709655904708 = |s, vs| spec_serialize_4_u8s_15022962709655904708(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_4_u8s_15022962709655904708, spec_serialize_4_u8s_15022962709655904708, s) by {
        lemma_parse_4_u8s_15022962709655904708_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_4_u8s_15022962709655904708_correct()
    ensures prop_parse_correct(|s| spec_parse_4_u8s_15022962709655904708(s), |s, vs| spec_serialize_4_u8s_15022962709655904708(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_4_u8s_15022962709655904708 = |s| spec_parse_4_u8s_15022962709655904708(s);
    let spec_serialize_4_u8s_15022962709655904708 = |s, vs| spec_serialize_4_u8s_15022962709655904708(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_4_u8s_15022962709655904708, spec_serialize_4_u8s_15022962709655904708, s, vs) by {
        lemma_parse_4_u8s_15022962709655904708_correct_on(s, vs);
    }
}

proof fn lemma_parse_4_u8s_15022962709655904708_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_4_u8s_15022962709655904708(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 4, s);
}

proof fn lemma_serialize_4_u8s_15022962709655904708_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_4_u8s_15022962709655904708(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 4, s, vs);
}

pub proof fn lemma_serialize_4_u8s_15022962709655904708_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_4_u8s_15022962709655904708(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 4, s1, s2, v);
}

proof fn lemma_parse_4_u8s_15022962709655904708_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_4_u8s_15022962709655904708(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 4);
}

proof fn lemma_parse_4_u8s_15022962709655904708_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_4_u8s_15022962709655904708(s), |s, v| spec_serialize_4_u8s_15022962709655904708(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 4, s);
}

proof fn lemma_parse_4_u8s_15022962709655904708_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_4_u8s_15022962709655904708(s), |s, vs| spec_serialize_4_u8s_15022962709655904708(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 4, s, vs);
}

pub exec fn vec_u8_check_15022962709655904708(xs : &Vec<u8>) -> (res : bool)
    requires xs.dview().len() == 4
    ensures res <==> xs.dview() == seq![2u8, 0u8, 0u8, 0u8]
{
    let mut constant = vec_new();
    vec_push(&mut constant, 2u8);
    vec_push(&mut constant, 0u8);
    vec_push(&mut constant, 0u8);
    vec_push(&mut constant, 0u8);
    let mut i = 0;
    while i < 4
        invariant
            0 <= i <= 4,
            constant.dview() == seq![2u8, 0u8, 0u8, 0u8],
            xs.dview().len() == 4,
            xs.dview().subrange(0, i as int) =~= constant.dview().subrange(0, i as int),
    {
        let (constant_i, xi) = (*vec_index(&constant, i), *vec_index(&xs, i));
        if constant_i == xi {
            i = i + 1;
            assert(xs.dview().subrange(0, i as int) =~= xs.dview().subrange(0, i as int - 1).push(xi));
        } else {
            return false;
        }
    }
    assert(xs.dview() =~= seq![2u8, 0u8, 0u8, 0u8]) by {
        assert(xs.dview().subrange(0, 4) =~= xs.dview());
    }

    true
}

pub exec fn parse_4_u8s_15022962709655904708(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s_15022962709655904708(s)),
        res.is_ok() ==> res.unwrap().2.dview() == seq![2u8, 0u8, 0u8, 0u8]
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    match parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 4, s) {
        Ok((s0, n, xs)) => {
            assert(xs.dview().len() == 4) by {
                lemma_parse_u8_le_well_behaved(); lemma_parse_repeat_n_well_behaved(spec_parse_u8_le, 4);
            }

            if vec_u8_check_15022962709655904708(&xs) {
                Ok((s0, n, xs))
            } else {
                Err(ParseError::ConstMismatch)
            }
        }
        Err(e) => Err(e),
    }
}

pub exec fn serialize_4_u8s_15022962709655904708(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_4_u8s_15022962709655904708(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    if vs.length() == 4 && vec_u8_check_15022962709655904708(&vs) {
        serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 4, s, vs)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub open spec fn spec_parse_16_u8s(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    spec_parse_repeat_n(spec_parse_u8_le, 16)(s)
}

pub open spec fn spec_serialize_16_u8s(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    spec_serialize_repeat_n(spec_serialize_u8_le, 16)(s, vs)
}

pub proof fn lemma_parse_16_u8s_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_16_u8s(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_16_u8s = |s| spec_parse_16_u8s(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_16_u8s, s) by {
        lemma_parse_16_u8s_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_16_u8s_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_16_u8s(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_16_u8s = |s, vs| spec_serialize_16_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_16_u8s, s, vs) by {
        lemma_serialize_16_u8s_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_16_u8s_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_16_u8s(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_16_u8s = |s, vs| spec_serialize_16_u8s(s, vs);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_16_u8s, s1, s2, v) by {
        lemma_serialize_16_u8s_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_16_u8s_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_16_u8s(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_16_u8s = |s| spec_parse_16_u8s(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_16_u8s, s1, s2) by {
        lemma_parse_16_u8s_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_16_u8s_correct()
    ensures prop_parse_correct(|s| spec_parse_16_u8s(s), |s, vs| spec_serialize_16_u8s(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_16_u8s = |s| spec_parse_16_u8s(s);
    let spec_serialize_16_u8s = |s, vs| spec_serialize_16_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_16_u8s, spec_serialize_16_u8s, s, vs) by {
        lemma_parse_16_u8s_correct_on(s, vs);
    }
}

pub proof fn lemma_parse_16_u8s_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_16_u8s(s), |s, v| spec_serialize_16_u8s(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_16_u8s = |s| spec_parse_16_u8s(s);
    let spec_serialize_16_u8s = |s, vs| spec_serialize_16_u8s(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_16_u8s, spec_serialize_16_u8s, s) by {
        lemma_parse_16_u8s_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_16_u8s_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_16_u8s(s))
{
    lemma_parse_16_u8s_serialize_inverse();
    lemma_serialize_16_u8s_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_16_u8s(s), |s, v| spec_serialize_16_u8s(s, v));
}

proof fn lemma_parse_16_u8s_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_16_u8s(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 16, s);
}

proof fn lemma_serialize_16_u8s_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_16_u8s(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 16, s, vs);
}

proof fn lemma_serialize_16_u8s_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_16_u8s(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 16, s1, s2, v);
}

proof fn lemma_parse_16_u8s_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_16_u8s(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 16);
}

proof fn lemma_parse_16_u8s_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_16_u8s(s), |s, vs| spec_serialize_16_u8s(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 16, s, vs);
}

proof fn lemma_parse_16_u8s_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_16_u8s(s), |s, v| spec_serialize_16_u8s(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 16, s);
}

pub exec fn parse_16_u8s(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_16_u8s(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 16, s)
}

pub exec fn serialize_16_u8s(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_16_u8s(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 16, s, vs)
}
pub struct SpecOwlMsg2 {
    owl__msg2_tag: Seq<u8>,
    owl__msg2_sender: Seq<u8>,
    owl__msg2_receiver: Seq<u8>,
    owl__msg2_ephemeral: Seq<u8>,
    owl__msg2_empty: Seq<u8>,
    owl__msg2_mac1: Seq<u8>,

}
pub struct OwlMsg2 {
    owl__msg2_tag: Vec<u8>,
    owl__msg2_sender: Vec<u8>,
    owl__msg2_receiver: Vec<u8>,
    owl__msg2_ephemeral: Vec<u8>,
    owl__msg2_empty: Vec<u8>,
    owl__msg2_mac1: Vec<u8>,

}

pub open spec fn spec_parse_owl_msg2(s: SpecStream) -> SpecParseResult<(((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)>
{
    let spec_parse_4_u8s_15022962709655904708 = |s| spec_parse_4_u8s_15022962709655904708(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_16_u8s = |s| spec_parse_16_u8s(s);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);

    spec_parse_6_fold(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s, spec_parse_4_u8s, spec_parse_91_u8s, spec_parse_16_u8s, spec_parse_64_u8s)(s)
}

pub open spec fn spec_serialize_owl_msg2(s: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)) -> SpecSerializeResult
{
    let spec_serialize_4_u8s_15022962709655904708 = |s, v| spec_serialize_4_u8s_15022962709655904708(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_16_u8s = |s, v| spec_serialize_16_u8s(s, v);
    let spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);

    spec_serialize_6_fold(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s, spec_serialize_4_u8s, spec_serialize_91_u8s, spec_serialize_16_u8s, spec_serialize_64_u8s)(s, v)
}

pub proof fn lemma_parse_owl_msg2_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_owl_msg2(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_owl_msg2 = |s| spec_parse_owl_msg2(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_owl_msg2, s) by {
        lemma_parse_owl_msg2_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_owl_msg2_well_behaved()
    ensures prop_serialize_well_behaved(|s, v| spec_serialize_owl_msg2(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_owl_msg2 = |s, v| spec_serialize_owl_msg2(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_owl_msg2, s, v) by {
        lemma_serialize_owl_msg2_well_behaved_on(s, v);
    }
}

pub proof fn lemma_serialize_owl_msg2_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_owl_msg2(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_owl_msg2 = |s, v| spec_serialize_owl_msg2(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_owl_msg2, s1, s2, v) by {
        lemma_serialize_owl_msg2_deterministic_on(s1, s2, v);
    }
}
    
pub proof fn lemma_parse_owl_msg2_correct()
    ensures prop_parse_correct(|s| spec_parse_owl_msg2(s), |s, v| spec_serialize_owl_msg2(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_owl_msg2 = |s| spec_parse_owl_msg2(s);
    let spec_serialize_owl_msg2 = |s, v| spec_serialize_owl_msg2(s, v);
    assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_owl_msg2, spec_serialize_owl_msg2, s, v) by {
        lemma_parse_owl_msg2_correct_on(s, v);
    }
}

pub proof fn lemma_parse_owl_msg2_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_owl_msg2(s), |s, v| spec_serialize_owl_msg2(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_owl_msg2 = |s| spec_parse_owl_msg2(s);
    let spec_serialize_owl_msg2 = |s, v| spec_serialize_owl_msg2(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_owl_msg2, spec_serialize_owl_msg2, s) by {
        lemma_parse_owl_msg2_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_owl_msg2_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_owl_msg2(s))
{
    lemma_parse_owl_msg2_serialize_inverse();
    lemma_serialize_owl_msg2_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_owl_msg2(s), |s, v| spec_serialize_owl_msg2(s, v));
}

pub proof fn lemma_parse_owl_msg2_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_owl_msg2(s), s)
{
    let spec_parse_4_u8s_15022962709655904708 = |s| spec_parse_4_u8s_15022962709655904708(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_16_u8s = |s| spec_parse_16_u8s(s);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    lemma_parse_4_u8s_15022962709655904708_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_16_u8s_well_behaved();
    lemma_parse_64_u8s_well_behaved();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s);
    lemma_parse_pair_well_behaved_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s), spec_parse_64_u8s, s);
}

pub proof fn lemma_serialize_owl_msg2_well_behaved_on(s: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_well_behaved_on(|s, v| spec_serialize_owl_msg2(s, v), s, v)
{
    let spec_serialize_4_u8s_15022962709655904708 = |s, v| spec_serialize_4_u8s_15022962709655904708(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_16_u8s = |s, v| spec_serialize_16_u8s(s, v);
    let spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);
    lemma_serialize_4_u8s_15022962709655904708_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_16_u8s_well_behaved();
    lemma_serialize_64_u8s_well_behaved();
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s);
    lemma_serialize_pair_well_behaved_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s), spec_serialize_64_u8s, s, v);
}

pub proof fn lemma_serialize_owl_msg2_deterministic_on(s1: SpecStream, s2: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_owl_msg2(s, v), s1, s2, v)
{
    let spec_serialize_4_u8s_15022962709655904708 = |s, v| spec_serialize_4_u8s_15022962709655904708(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_16_u8s = |s, v| spec_serialize_16_u8s(s, v);
    let spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);
    lemma_serialize_4_u8s_15022962709655904708_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_16_u8s_well_behaved();
    lemma_serialize_64_u8s_well_behaved();
    lemma_serialize_4_u8s_15022962709655904708_deterministic();
    lemma_serialize_4_u8s_deterministic();
    lemma_serialize_91_u8s_deterministic();
    lemma_serialize_16_u8s_deterministic();
    lemma_serialize_64_u8s_deterministic();
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s);
    lemma_serialize_pair_deterministic_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s), spec_serialize_64_u8s, s1, s2, v);
}

pub proof fn lemma_parse_owl_msg2_correct_on(s: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_parse_correct_on(|s| spec_parse_owl_msg2(s), |s, v| spec_serialize_owl_msg2(s, v), s, v)
{
    let spec_parse_4_u8s_15022962709655904708 = |s| spec_parse_4_u8s_15022962709655904708(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_16_u8s = |s| spec_parse_16_u8s(s);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    let spec_serialize_4_u8s_15022962709655904708 = |s, v| spec_serialize_4_u8s_15022962709655904708(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_16_u8s = |s, v| spec_serialize_16_u8s(s, v);
    let spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);
    lemma_serialize_4_u8s_15022962709655904708_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_16_u8s_well_behaved();
    lemma_serialize_64_u8s_well_behaved();
    lemma_parse_4_u8s_15022962709655904708_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_16_u8s_well_behaved();
    lemma_parse_64_u8s_well_behaved();
    lemma_parse_4_u8s_15022962709655904708_strong_prefix();
    lemma_parse_4_u8s_strong_prefix();
    lemma_parse_91_u8s_strong_prefix();
    lemma_parse_16_u8s_strong_prefix();
    lemma_parse_64_u8s_strong_prefix();
    lemma_parse_4_u8s_15022962709655904708_correct();
    lemma_parse_4_u8s_correct();
    lemma_parse_91_u8s_correct();
    lemma_parse_16_u8s_correct();
    lemma_parse_64_u8s_correct();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s);
    lemma_parse_pair_correct(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s, spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s, spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s);
    lemma_parse_pair_correct_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s), spec_parse_64_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s), spec_serialize_64_u8s, s, v);
}

pub proof fn lemma_parse_owl_msg2_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_owl_msg2(s), |s, v| spec_serialize_owl_msg2(s, v), s)
{
    let spec_parse_4_u8s_15022962709655904708 = |s| spec_parse_4_u8s_15022962709655904708(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_16_u8s = |s| spec_parse_16_u8s(s);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    let spec_serialize_4_u8s_15022962709655904708 = |s, v| spec_serialize_4_u8s_15022962709655904708(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_16_u8s = |s, v| spec_serialize_16_u8s(s, v);
    let spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);
    lemma_parse_4_u8s_15022962709655904708_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_16_u8s_well_behaved();
    lemma_parse_64_u8s_well_behaved();
    lemma_serialize_4_u8s_15022962709655904708_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_16_u8s_well_behaved();
    lemma_serialize_64_u8s_well_behaved();
    lemma_parse_4_u8s_15022962709655904708_serialize_inverse();
    lemma_parse_4_u8s_serialize_inverse();
    lemma_parse_91_u8s_serialize_inverse();
    lemma_parse_16_u8s_serialize_inverse();
    lemma_parse_64_u8s_serialize_inverse();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s, spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s, spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s);
    lemma_parse_pair_serialize_inverse_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s), spec_parse_64_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s), spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_16_u8s), spec_serialize_64_u8s, s);
}

pub proof fn lemma_parse_owl_msg2_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_owl_msg2(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_owl_msg2 = |s| spec_parse_owl_msg2(s);
    assert forall |s1, s2| prop_parse_strong_prefix_on(spec_parse_owl_msg2, s1, s2) by {
        lemma_parse_owl_msg2_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_owl_msg2_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_owl_msg2(s), s1, s2)
{
    let spec_parse_4_u8s_15022962709655904708 = |s| spec_parse_4_u8s_15022962709655904708(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_16_u8s = |s| spec_parse_16_u8s(s);
    let spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    lemma_parse_4_u8s_15022962709655904708_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_16_u8s_well_behaved();
    lemma_parse_64_u8s_well_behaved();
    lemma_parse_4_u8s_15022962709655904708_strong_prefix();
    lemma_parse_4_u8s_strong_prefix();
    lemma_parse_91_u8s_strong_prefix();
    lemma_parse_16_u8s_strong_prefix();
    lemma_parse_64_u8s_strong_prefix();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s);
    lemma_parse_pair_strong_prefix_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s), spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_16_u8s), spec_parse_64_u8s, s1, s2);
}

pub exec fn parse_owl_msg2(s: Stream) -> (res: ParseResult<(((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)>)
    ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_owl_msg2(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_4_u8s_15022962709655904708 = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s_15022962709655904708(s)) { parse_4_u8s_15022962709655904708(s) };
    let parse_4_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s(s)) { parse_4_u8s(s) };
    let parse_91_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_91_u8s(s)) { parse_91_u8s(s) };
    let parse_16_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_16_u8s(s)) { parse_16_u8s(s) };
    let parse_64_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_64_u8s(s)) { parse_64_u8s(s) };
    let ghost spec_parse_4_u8s_15022962709655904708 = |s| spec_parse_4_u8s_15022962709655904708(s);
    let ghost spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let ghost spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let ghost spec_parse_16_u8s = |s| spec_parse_16_u8s(s);
    let ghost spec_parse_64_u8s = |s| spec_parse_64_u8s(s);
    let ghost spec_parse_owl_msg2 = spec_parse_6_fold(spec_parse_4_u8s_15022962709655904708, spec_parse_4_u8s, spec_parse_4_u8s, spec_parse_91_u8s, spec_parse_16_u8s, spec_parse_64_u8s);

    let parse_owl_msg2 = |s| -> (res: ParseResult<(((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_owl_msg2) { parse_6_fold(parse_4_u8s_15022962709655904708, parse_4_u8s, parse_4_u8s, parse_91_u8s, parse_16_u8s, parse_64_u8s, Ghost(spec_parse_4_u8s_15022962709655904708), Ghost(spec_parse_4_u8s), Ghost(spec_parse_4_u8s), Ghost(spec_parse_91_u8s), Ghost(spec_parse_16_u8s), Ghost(spec_parse_64_u8s), s) };
    assert(prop_parse_exec_spec_equiv(parse_owl_msg2, spec_parse_owl_msg2));

    parse_owl_msg2(s)
}
pub exec fn serialize_owl_msg2(s: Stream, v: (((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)) -> (res: SerializeResult)
    ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_owl_msg2(s, v))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }
    let serialize_4_u8s_15022962709655904708 = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_4_u8s_15022962709655904708(s, v)) { serialize_4_u8s_15022962709655904708(s, v) };
    let serialize_4_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_4_u8s(s, v)) { serialize_4_u8s(s, v) };
    let serialize_91_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_91_u8s(s, v)) { serialize_91_u8s(s, v) };
    let serialize_16_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_16_u8s(s, v)) { serialize_16_u8s(s, v) };
    let serialize_64_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_64_u8s(s, v)) { serialize_64_u8s(s, v) };
    let ghost spec_serialize_4_u8s_15022962709655904708 = |s, v| spec_serialize_4_u8s_15022962709655904708(s, v);
    let ghost spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let ghost spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let ghost spec_serialize_16_u8s = |s, v| spec_serialize_16_u8s(s, v);
    let ghost spec_serialize_64_u8s = |s, v| spec_serialize_64_u8s(s, v);
    let ghost spec_serialize_owl_msg2 = spec_serialize_6_fold(spec_serialize_4_u8s_15022962709655904708, spec_serialize_4_u8s, spec_serialize_4_u8s, spec_serialize_91_u8s, spec_serialize_16_u8s, spec_serialize_64_u8s);

    let serialize_owl_msg2 = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_owl_msg2) { serialize_6_fold(serialize_4_u8s_15022962709655904708, serialize_4_u8s, serialize_4_u8s, serialize_91_u8s, serialize_16_u8s, serialize_64_u8s, Ghost(spec_serialize_4_u8s_15022962709655904708), Ghost(spec_serialize_4_u8s), Ghost(spec_serialize_4_u8s), Ghost(spec_serialize_91_u8s), Ghost(spec_serialize_16_u8s), Ghost(spec_serialize_64_u8s), s, v) };
    assert(prop_serialize_exec_spec_equiv(serialize_owl_msg2, spec_serialize_owl_msg2));

    serialize_owl_msg2(s, v)
}

pub open spec fn spec_parse_4_u8s_11861915643473238517(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    match spec_parse_repeat_n(spec_parse_u8_le, 4)(s) {
        Ok((s, n, xs)) => {
            if xs == seq![4u8, 0u8, 0u8, 0u8] {
                Ok((s, n, xs))
            } else {
                Err(ParseError::ConstMismatch)
            }
        }
        Err(e) => Err(e),
    }
}

pub open spec fn spec_serialize_4_u8s_11861915643473238517(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    if vs == seq![4u8, 0u8, 0u8, 0u8] {
        let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
        spec_serialize_repeat_n(spec_serialize_u8_le, 4)(s, vs)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub proof fn lemma_parse_4_u8s_11861915643473238517_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_4_u8s_11861915643473238517(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_4_u8s_11861915643473238517 = |s| spec_parse_4_u8s_11861915643473238517(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_4_u8s_11861915643473238517, s) by {
        lemma_parse_4_u8s_11861915643473238517_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_4_u8s_11861915643473238517_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_4_u8s_11861915643473238517(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_4_u8s_11861915643473238517 = |s, vs| spec_serialize_4_u8s_11861915643473238517(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_4_u8s_11861915643473238517, s, vs) by {
        lemma_serialize_4_u8s_11861915643473238517_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_4_u8s_11861915643473238517_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_4_u8s_11861915643473238517(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_4_u8s_11861915643473238517 = |s, v| spec_serialize_4_u8s_11861915643473238517(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_4_u8s_11861915643473238517, s1, s2, v) by {
        lemma_serialize_4_u8s_11861915643473238517_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_4_u8s_11861915643473238517_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_4_u8s_11861915643473238517(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_4_u8s_11861915643473238517 = |s| spec_parse_4_u8s_11861915643473238517(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_4_u8s_11861915643473238517, s1, s2) by {
        lemma_parse_4_u8s_11861915643473238517_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_4_u8s_11861915643473238517_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_4_u8s_11861915643473238517(s), |s, vs| spec_serialize_4_u8s_11861915643473238517(s, vs))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_4_u8s_11861915643473238517 = |s| spec_parse_4_u8s_11861915643473238517(s);
    let spec_serialize_4_u8s_11861915643473238517 = |s, vs| spec_serialize_4_u8s_11861915643473238517(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_4_u8s_11861915643473238517, spec_serialize_4_u8s_11861915643473238517, s) by {
        lemma_parse_4_u8s_11861915643473238517_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_4_u8s_11861915643473238517_correct()
    ensures prop_parse_correct(|s| spec_parse_4_u8s_11861915643473238517(s), |s, vs| spec_serialize_4_u8s_11861915643473238517(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_4_u8s_11861915643473238517 = |s| spec_parse_4_u8s_11861915643473238517(s);
    let spec_serialize_4_u8s_11861915643473238517 = |s, vs| spec_serialize_4_u8s_11861915643473238517(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_4_u8s_11861915643473238517, spec_serialize_4_u8s_11861915643473238517, s, vs) by {
        lemma_parse_4_u8s_11861915643473238517_correct_on(s, vs);
    }
}

proof fn lemma_parse_4_u8s_11861915643473238517_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_4_u8s_11861915643473238517(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 4, s);
}

proof fn lemma_serialize_4_u8s_11861915643473238517_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_4_u8s_11861915643473238517(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 4, s, vs);
}

pub proof fn lemma_serialize_4_u8s_11861915643473238517_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_4_u8s_11861915643473238517(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 4, s1, s2, v);
}

proof fn lemma_parse_4_u8s_11861915643473238517_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_4_u8s_11861915643473238517(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 4);
}

proof fn lemma_parse_4_u8s_11861915643473238517_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_4_u8s_11861915643473238517(s), |s, v| spec_serialize_4_u8s_11861915643473238517(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 4, s);
}

proof fn lemma_parse_4_u8s_11861915643473238517_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_4_u8s_11861915643473238517(s), |s, vs| spec_serialize_4_u8s_11861915643473238517(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 4, s, vs);
}

pub exec fn vec_u8_check_11861915643473238517(xs : &Vec<u8>) -> (res : bool)
    requires xs.dview().len() == 4
    ensures res <==> xs.dview() == seq![4u8, 0u8, 0u8, 0u8]
{
    let mut constant = vec_new();
    vec_push(&mut constant, 4u8);
    vec_push(&mut constant, 0u8);
    vec_push(&mut constant, 0u8);
    vec_push(&mut constant, 0u8);
    let mut i = 0;
    while i < 4
        invariant
            0 <= i <= 4,
            constant.dview() == seq![4u8, 0u8, 0u8, 0u8],
            xs.dview().len() == 4,
            xs.dview().subrange(0, i as int) =~= constant.dview().subrange(0, i as int),
    {
        let (constant_i, xi) = (*vec_index(&constant, i), *vec_index(&xs, i));
        if constant_i == xi {
            i = i + 1;
            assert(xs.dview().subrange(0, i as int) =~= xs.dview().subrange(0, i as int - 1).push(xi));
        } else {
            return false;
        }
    }
    assert(xs.dview() =~= seq![4u8, 0u8, 0u8, 0u8]) by {
        assert(xs.dview().subrange(0, 4) =~= xs.dview());
    }

    true
}

pub exec fn parse_4_u8s_11861915643473238517(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s_11861915643473238517(s)),
        res.is_ok() ==> res.unwrap().2.dview() == seq![4u8, 0u8, 0u8, 0u8]
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    match parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 4, s) {
        Ok((s0, n, xs)) => {
            assert(xs.dview().len() == 4) by {
                lemma_parse_u8_le_well_behaved(); lemma_parse_repeat_n_well_behaved(spec_parse_u8_le, 4);
            }

            if vec_u8_check_11861915643473238517(&xs) {
                Ok((s0, n, xs))
            } else {
                Err(ParseError::ConstMismatch)
            }
        }
        Err(e) => Err(e),
    }
}

pub exec fn serialize_4_u8s_11861915643473238517(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_4_u8s_11861915643473238517(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    if vs.length() == 4 && vec_u8_check_11861915643473238517(&vs) {
        serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 4, s, vs)
    } else {
        Err(SerializeError::ConstMismatch)
    }
}

pub open spec fn spec_parse_8_u8s(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    spec_parse_repeat_n(spec_parse_u8_le, 8)(s)
}

pub open spec fn spec_serialize_8_u8s(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    spec_serialize_repeat_n(spec_serialize_u8_le, 8)(s, vs)
}

pub proof fn lemma_parse_8_u8s_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_8_u8s(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_8_u8s = |s| spec_parse_8_u8s(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_8_u8s, s) by {
        lemma_parse_8_u8s_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_8_u8s_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_8_u8s(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_8_u8s = |s, vs| spec_serialize_8_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_8_u8s, s, vs) by {
        lemma_serialize_8_u8s_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_8_u8s_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_8_u8s(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_8_u8s = |s, vs| spec_serialize_8_u8s(s, vs);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_8_u8s, s1, s2, v) by {
        lemma_serialize_8_u8s_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_8_u8s_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_8_u8s(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_8_u8s = |s| spec_parse_8_u8s(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_8_u8s, s1, s2) by {
        lemma_parse_8_u8s_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_8_u8s_correct()
    ensures prop_parse_correct(|s| spec_parse_8_u8s(s), |s, vs| spec_serialize_8_u8s(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_8_u8s = |s| spec_parse_8_u8s(s);
    let spec_serialize_8_u8s = |s, vs| spec_serialize_8_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_8_u8s, spec_serialize_8_u8s, s, vs) by {
        lemma_parse_8_u8s_correct_on(s, vs);
    }
}

pub proof fn lemma_parse_8_u8s_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_8_u8s(s), |s, v| spec_serialize_8_u8s(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_8_u8s = |s| spec_parse_8_u8s(s);
    let spec_serialize_8_u8s = |s, vs| spec_serialize_8_u8s(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_8_u8s, spec_serialize_8_u8s, s) by {
        lemma_parse_8_u8s_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_8_u8s_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_8_u8s(s))
{
    lemma_parse_8_u8s_serialize_inverse();
    lemma_serialize_8_u8s_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_8_u8s(s), |s, v| spec_serialize_8_u8s(s, v));
}

proof fn lemma_parse_8_u8s_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_8_u8s(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 8, s);
}

proof fn lemma_serialize_8_u8s_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_8_u8s(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 8, s, vs);
}

proof fn lemma_serialize_8_u8s_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_8_u8s(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 8, s1, s2, v);
}

proof fn lemma_parse_8_u8s_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_8_u8s(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 8);
}

proof fn lemma_parse_8_u8s_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_8_u8s(s), |s, vs| spec_serialize_8_u8s(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 8, s, vs);
}

proof fn lemma_parse_8_u8s_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_8_u8s(s), |s, v| spec_serialize_8_u8s(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 8, s);
}

pub exec fn parse_8_u8s(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_8_u8s(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 8, s)
}

pub exec fn serialize_8_u8s(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_8_u8s(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 8, s, vs)
}
pub struct SpecOwlTransp {
    owl__transp_tag: Seq<u8>,
    owl__transp_receiver: Seq<u8>,
    owl__transp_counter: Seq<u8>,
    owl__transp_packet: Vec<u8>,

}
pub struct OwlTransp {
    owl__transp_tag: Vec<u8>,
    owl__transp_receiver: Vec<u8>,
    owl__transp_counter: Vec<u8>,
    owl__transp_packet: Vec<u8>,

}

pub open spec fn spec_parse_4_fold<R1, R2, R3, R4>(
    parser1: FnSpec(SpecStream) -> SpecParseResult<R1>,
    parser2: FnSpec(SpecStream) -> SpecParseResult<R2>,
    parser3: FnSpec(SpecStream) -> SpecParseResult<R3>,
    parser4: FnSpec(SpecStream) -> SpecParseResult<R4>) -> FnSpec(SpecStream) -> SpecParseResult<(((R1, R2), R3), R4)>
{
    spec_parse_pair(spec_parse_pair(spec_parse_pair(parser1, parser2), parser3), parser4)
}

pub exec fn parse_4_fold<P1, P2, P3, P4, R1, R2, R3, R4>(
    exec_parser1: P1,
    exec_parser2: P2,
    exec_parser3: P3,
    exec_parser4: P4,
    Ghost(spec_parser1): Ghost<FnSpec(SpecStream) -> SpecParseResult<R1::V>>,
    Ghost(spec_parser2): Ghost<FnSpec(SpecStream) -> SpecParseResult<R2::V>>,
    Ghost(spec_parser3): Ghost<FnSpec(SpecStream) -> SpecParseResult<R3::V>>,
    Ghost(spec_parser4): Ghost<FnSpec(SpecStream) -> SpecParseResult<R4::V>>,
    s: Stream) -> (res: ParseResult<(((R1, R2), R3), R4)>)
    where
    R1: DView,
    P1: FnOnce(Stream) -> ParseResult<R1>,
    R2: DView,
    P2: FnOnce(Stream) -> ParseResult<R2>,
    R3: DView,
    P3: FnOnce(Stream) -> ParseResult<R3>,
    R4: DView,
    P4: FnOnce(Stream) -> ParseResult<R4>,
    requires
        prop_parse_exec_spec_equiv(exec_parser1, spec_parser1),
        prop_parse_exec_spec_equiv(exec_parser2, spec_parser2),
        prop_parse_exec_spec_equiv(exec_parser3, spec_parser3),
        prop_parse_exec_spec_equiv(exec_parser4, spec_parser4),
    ensures
        prop_parse_exec_spec_equiv_on(s, res, spec_parse_4_fold(spec_parser1, spec_parser2, spec_parser3, spec_parser4))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_2_fold = |s| -> (res: ParseResult<(R1, R2)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parser1, spec_parser2)), { parse_pair(exec_parser1, exec_parser2, Ghost(spec_parser1), Ghost(spec_parser2), s) };
    let parse_3_fold = |s| -> (res: ParseResult<((R1, R2), R3)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)), { parse_pair(parse_2_fold, exec_parser3, Ghost(spec_parse_pair(spec_parser1, spec_parser2)), Ghost(spec_parser3), s) };
    parse_pair(parse_3_fold, exec_parser4, Ghost(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)), Ghost(spec_parser4), s)
}



pub open spec fn spec_serialize_4_fold<T1, T2, T3, T4>(
    serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
    serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult,
    serializer3: FnSpec(SpecStream, T3) -> SpecSerializeResult,
    serializer4: FnSpec(SpecStream, T4) -> SpecSerializeResult) -> FnSpec(SpecStream, (((T1, T2), T3), T4)) -> SpecSerializeResult
{
    spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(serializer1, serializer2), serializer3), serializer4)
}
pub exec fn serialize_4_fold<S1, S2, S3, S4, T1, T2, T3, T4>(
    exec_serializer1: S1,
    exec_serializer2: S2,
    exec_serializer3: S3,
    exec_serializer4: S4,
    Ghost(spec_serializer1): Ghost<FnSpec(SpecStream, T1::V) -> SpecSerializeResult>,
    Ghost(spec_serializer2): Ghost<FnSpec(SpecStream, T2::V) -> SpecSerializeResult>,
    Ghost(spec_serializer3): Ghost<FnSpec(SpecStream, T3::V) -> SpecSerializeResult>,
    Ghost(spec_serializer4): Ghost<FnSpec(SpecStream, T4::V) -> SpecSerializeResult>,
    s: Stream, v: (((T1, T2), T3), T4)) -> (res: SerializeResult)
    where
    T1: std::fmt::Debug + DView,
    S1: FnOnce(Stream, T1) -> SerializeResult,
    T2: std::fmt::Debug + DView,
    S2: FnOnce(Stream, T2) -> SerializeResult,
    T3: std::fmt::Debug + DView,
    S3: FnOnce(Stream, T3) -> SerializeResult,
    T4: std::fmt::Debug + DView,
    S4: FnOnce(Stream, T4) -> SerializeResult,
    requires
        prop_serialize_exec_spec_equiv(exec_serializer1, spec_serializer1),
        prop_serialize_exec_spec_equiv(exec_serializer2, spec_serializer2),
        prop_serialize_exec_spec_equiv(exec_serializer3, spec_serializer3),
        prop_serialize_exec_spec_equiv(exec_serializer4, spec_serializer4),
    ensures
        prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_4_fold(spec_serializer1, spec_serializer2, spec_serializer3, spec_serializer4))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }
    let serialize_2_fold = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serializer1, spec_serializer2)), { serialize_pair(exec_serializer1, exec_serializer2, Ghost(spec_serializer1), Ghost(spec_serializer2), s, v) };
    let serialize_3_fold = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3)), { serialize_pair(serialize_2_fold, exec_serializer3, Ghost(spec_serialize_pair(spec_serializer1, spec_serializer2)), Ghost(spec_serializer3), s, v) };
    serialize_pair(serialize_3_fold, exec_serializer4, Ghost(spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3)), Ghost(spec_serializer4), s, v)
}


pub open spec fn spec_parse_owl_transp(s: SpecStream) -> SpecParseResult<(((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>)>
{
    let spec_parse_4_u8s_11861915643473238517 = |s| spec_parse_4_u8s_11861915643473238517(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_8_u8s = |s| spec_parse_8_u8s(s);
    let spec_parse_tail = |s| spec_parse_tail(s);

    spec_parse_4_fold(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s, spec_parse_8_u8s, spec_parse_tail)(s)
}

pub open spec fn spec_serialize_owl_transp(s: SpecStream, v: (((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>)) -> SpecSerializeResult
{
    let spec_serialize_4_u8s_11861915643473238517 = |s, v| spec_serialize_4_u8s_11861915643473238517(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_8_u8s = |s, v| spec_serialize_8_u8s(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);

    spec_serialize_4_fold(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s, spec_serialize_8_u8s, spec_serialize_tail)(s, v)
}

pub proof fn lemma_parse_owl_transp_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_owl_transp(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_owl_transp = |s| spec_parse_owl_transp(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_owl_transp, s) by {
        lemma_parse_owl_transp_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_owl_transp_well_behaved()
    ensures prop_serialize_well_behaved(|s, v| spec_serialize_owl_transp(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_owl_transp = |s, v| spec_serialize_owl_transp(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_owl_transp, s, v) by {
        lemma_serialize_owl_transp_well_behaved_on(s, v);
    }
}

pub proof fn lemma_serialize_owl_transp_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_owl_transp(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_owl_transp = |s, v| spec_serialize_owl_transp(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_owl_transp, s1, s2, v) by {
        lemma_serialize_owl_transp_deterministic_on(s1, s2, v);
    }
}
    
pub proof fn lemma_parse_owl_transp_correct()
    ensures prop_parse_correct(|s| spec_parse_owl_transp(s), |s, v| spec_serialize_owl_transp(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_owl_transp = |s| spec_parse_owl_transp(s);
    let spec_serialize_owl_transp = |s, v| spec_serialize_owl_transp(s, v);
    assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_owl_transp, spec_serialize_owl_transp, s, v) by {
        lemma_parse_owl_transp_correct_on(s, v);
    }
}

pub proof fn lemma_parse_owl_transp_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_owl_transp(s), |s, v| spec_serialize_owl_transp(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_owl_transp = |s| spec_parse_owl_transp(s);
    let spec_serialize_owl_transp = |s, v| spec_serialize_owl_transp(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_owl_transp, spec_serialize_owl_transp, s) by {
        lemma_parse_owl_transp_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_owl_transp_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_owl_transp(s))
{
    lemma_parse_owl_transp_serialize_inverse();
    lemma_serialize_owl_transp_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_owl_transp(s), |s, v| spec_serialize_owl_transp(s, v));
}

pub proof fn lemma_parse_owl_transp_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_owl_transp(s), s)
{
    let spec_parse_4_u8s_11861915643473238517 = |s| spec_parse_4_u8s_11861915643473238517(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_8_u8s = |s| spec_parse_8_u8s(s);
    let spec_parse_tail = |s| spec_parse_tail(s);
    lemma_parse_4_u8s_11861915643473238517_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_8_u8s_well_behaved();
    lemma_parse_tail_well_behaved();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s), spec_parse_8_u8s);
    lemma_parse_pair_well_behaved_on(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s), spec_parse_8_u8s), spec_parse_tail, s);
}

pub proof fn lemma_serialize_owl_transp_well_behaved_on(s: SpecStream, v: (((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_well_behaved_on(|s, v| spec_serialize_owl_transp(s, v), s, v)
{
    let spec_serialize_4_u8s_11861915643473238517 = |s, v| spec_serialize_4_u8s_11861915643473238517(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_8_u8s = |s, v| spec_serialize_8_u8s(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_serialize_4_u8s_11861915643473238517_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_8_u8s_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s);
    lemma_serialize_pair_well_behaved_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s), spec_serialize_tail, s, v);
}

pub proof fn lemma_serialize_owl_transp_deterministic_on(s1: SpecStream, s2: SpecStream, v: (((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_owl_transp(s, v), s1, s2, v)
{
    let spec_serialize_4_u8s_11861915643473238517 = |s, v| spec_serialize_4_u8s_11861915643473238517(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_8_u8s = |s, v| spec_serialize_8_u8s(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_serialize_4_u8s_11861915643473238517_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_8_u8s_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_serialize_4_u8s_11861915643473238517_deterministic();
    lemma_serialize_4_u8s_deterministic();
    lemma_serialize_8_u8s_deterministic();
    lemma_serialize_tail_deterministic();
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s);
    lemma_serialize_pair_deterministic_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s), spec_serialize_tail, s1, s2, v);
}

pub proof fn lemma_parse_owl_transp_correct_on(s: SpecStream, v: (((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_parse_correct_on(|s| spec_parse_owl_transp(s), |s, v| spec_serialize_owl_transp(s, v), s, v)
{
    let spec_parse_4_u8s_11861915643473238517 = |s| spec_parse_4_u8s_11861915643473238517(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_8_u8s = |s| spec_parse_8_u8s(s);
    let spec_parse_tail = |s| spec_parse_tail(s);
    let spec_serialize_4_u8s_11861915643473238517 = |s, v| spec_serialize_4_u8s_11861915643473238517(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_8_u8s = |s, v| spec_serialize_8_u8s(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_serialize_4_u8s_11861915643473238517_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_8_u8s_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_parse_4_u8s_11861915643473238517_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_8_u8s_well_behaved();
    lemma_parse_tail_well_behaved();
    lemma_parse_4_u8s_11861915643473238517_strong_prefix();
    lemma_parse_4_u8s_strong_prefix();
    lemma_parse_8_u8s_strong_prefix();
    
    lemma_parse_4_u8s_11861915643473238517_correct();
    lemma_parse_4_u8s_correct();
    lemma_parse_8_u8s_correct();
    lemma_parse_tail_correct();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s);
    lemma_parse_pair_correct(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s, spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s), spec_parse_8_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s), spec_parse_8_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s), spec_parse_8_u8s, spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s);
    lemma_parse_pair_correct_on(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s), spec_parse_8_u8s), spec_parse_tail, spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s), spec_serialize_tail, s, v);
}

pub proof fn lemma_parse_owl_transp_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_owl_transp(s), |s, v| spec_serialize_owl_transp(s, v), s)
{
    let spec_parse_4_u8s_11861915643473238517 = |s| spec_parse_4_u8s_11861915643473238517(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_8_u8s = |s| spec_parse_8_u8s(s);
    let spec_parse_tail = |s| spec_parse_tail(s);
    let spec_serialize_4_u8s_11861915643473238517 = |s, v| spec_serialize_4_u8s_11861915643473238517(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_8_u8s = |s, v| spec_serialize_8_u8s(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_parse_4_u8s_11861915643473238517_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_8_u8s_well_behaved();
    lemma_parse_tail_well_behaved();
    lemma_serialize_4_u8s_11861915643473238517_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_8_u8s_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_parse_4_u8s_11861915643473238517_serialize_inverse();
    lemma_parse_4_u8s_serialize_inverse();
    lemma_parse_8_u8s_serialize_inverse();
    lemma_parse_tail_serialize_inverse();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s, spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s), spec_parse_8_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s), spec_parse_8_u8s, spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s);
    lemma_parse_pair_serialize_inverse_on(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s), spec_parse_8_u8s), spec_parse_tail, spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s), spec_serialize_8_u8s), spec_serialize_tail, s);
}
pub exec fn parse_owl_transp(s: Stream) -> (res: ParseResult<(((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>)>)
    ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_owl_transp(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_4_u8s_11861915643473238517 = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s_11861915643473238517(s)) { parse_4_u8s_11861915643473238517(s) };
    let parse_4_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s(s)) { parse_4_u8s(s) };
    let parse_8_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_8_u8s(s)) { parse_8_u8s(s) };
    let parse_tail = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_tail(s)) { parse_tail(s) };
    let ghost spec_parse_4_u8s_11861915643473238517 = |s| spec_parse_4_u8s_11861915643473238517(s);
    let ghost spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let ghost spec_parse_8_u8s = |s| spec_parse_8_u8s(s);
    let ghost spec_parse_tail = |s| spec_parse_tail(s);
    let ghost spec_parse_owl_transp = spec_parse_4_fold(spec_parse_4_u8s_11861915643473238517, spec_parse_4_u8s, spec_parse_8_u8s, spec_parse_tail);

    let parse_owl_transp = |s| -> (res: ParseResult<(((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_owl_transp) { parse_4_fold(parse_4_u8s_11861915643473238517, parse_4_u8s, parse_8_u8s, parse_tail, Ghost(spec_parse_4_u8s_11861915643473238517), Ghost(spec_parse_4_u8s), Ghost(spec_parse_8_u8s), Ghost(spec_parse_tail), s) };
    assert(prop_parse_exec_spec_equiv(parse_owl_transp, spec_parse_owl_transp));

    parse_owl_transp(s)
}
pub exec fn serialize_owl_transp(s: Stream, v: (((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>)) -> (res: SerializeResult)
    ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_owl_transp(s, v))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }
    let serialize_4_u8s_11861915643473238517 = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_4_u8s_11861915643473238517(s, v)) { serialize_4_u8s_11861915643473238517(s, v) };
    let serialize_4_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_4_u8s(s, v)) { serialize_4_u8s(s, v) };
    let serialize_8_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_8_u8s(s, v)) { serialize_8_u8s(s, v) };
    let serialize_tail = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_tail(s, v)) { serialize_tail(s, v) };
    let ghost spec_serialize_4_u8s_11861915643473238517 = |s, v| spec_serialize_4_u8s_11861915643473238517(s, v);
    let ghost spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let ghost spec_serialize_8_u8s = |s, v| spec_serialize_8_u8s(s, v);
    let ghost spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    let ghost spec_serialize_owl_transp = spec_serialize_4_fold(spec_serialize_4_u8s_11861915643473238517, spec_serialize_4_u8s, spec_serialize_8_u8s, spec_serialize_tail);

    let serialize_owl_transp = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_owl_transp) { serialize_4_fold(serialize_4_u8s_11861915643473238517, serialize_4_u8s, serialize_8_u8s, serialize_tail, Ghost(spec_serialize_4_u8s_11861915643473238517), Ghost(spec_serialize_4_u8s), Ghost(spec_serialize_8_u8s), Ghost(spec_serialize_tail), s, v) };
    assert(prop_serialize_exec_spec_equiv(serialize_owl_transp, spec_serialize_owl_transp));

    serialize_owl_transp(s, v)
}

pub open spec fn spec_parse_12_u8s(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    spec_parse_repeat_n(spec_parse_u8_le, 12)(s)
}

pub open spec fn spec_serialize_12_u8s(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    spec_serialize_repeat_n(spec_serialize_u8_le, 12)(s, vs)
}

pub proof fn lemma_parse_12_u8s_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_12_u8s(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_12_u8s, s) by {
        lemma_parse_12_u8s_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_12_u8s_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_12_u8s(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_12_u8s = |s, vs| spec_serialize_12_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_12_u8s, s, vs) by {
        lemma_serialize_12_u8s_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_12_u8s_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_12_u8s(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_12_u8s = |s, vs| spec_serialize_12_u8s(s, vs);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_12_u8s, s1, s2, v) by {
        lemma_serialize_12_u8s_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_12_u8s_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_12_u8s(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_12_u8s, s1, s2) by {
        lemma_parse_12_u8s_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_12_u8s_correct()
    ensures prop_parse_correct(|s| spec_parse_12_u8s(s), |s, vs| spec_serialize_12_u8s(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_serialize_12_u8s = |s, vs| spec_serialize_12_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_12_u8s, spec_serialize_12_u8s, s, vs) by {
        lemma_parse_12_u8s_correct_on(s, vs);
    }
}

pub proof fn lemma_parse_12_u8s_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_12_u8s(s), |s, v| spec_serialize_12_u8s(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_serialize_12_u8s = |s, vs| spec_serialize_12_u8s(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_12_u8s, spec_serialize_12_u8s, s) by {
        lemma_parse_12_u8s_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_12_u8s_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_12_u8s(s))
{
    lemma_parse_12_u8s_serialize_inverse();
    lemma_serialize_12_u8s_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_12_u8s(s), |s, v| spec_serialize_12_u8s(s, v));
}

proof fn lemma_parse_12_u8s_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_12_u8s(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 12, s);
}

proof fn lemma_serialize_12_u8s_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_12_u8s(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 12, s, vs);
}

proof fn lemma_serialize_12_u8s_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_12_u8s(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 12, s1, s2, v);
}

proof fn lemma_parse_12_u8s_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_12_u8s(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 12);
}

proof fn lemma_parse_12_u8s_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_12_u8s(s), |s, vs| spec_serialize_12_u8s(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 12, s, vs);
}

proof fn lemma_parse_12_u8s_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_12_u8s(s), |s, v| spec_serialize_12_u8s(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 12, s);
}

pub exec fn parse_12_u8s(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_12_u8s(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 12, s)
}

pub exec fn serialize_12_u8s(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_12_u8s(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 12, s, vs)
}
pub struct SpecOwlInitiatorMsg1Val {
    owl__initiator_msg1_c3: Seq<u8>,
    owl__initiator_msg1_h4: Vec<u8>,

}
pub struct OwlInitiatorMsg1Val {
    owl__initiator_msg1_c3: Vec<u8>,
    owl__initiator_msg1_h4: Vec<u8>,

}

pub open spec fn spec_parse_owl_initiator_msg1_val(s: SpecStream) -> SpecParseResult<(Seq<u8>, Seq<u8>)>
{
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_parse_tail = |s| spec_parse_tail(s);

    spec_parse_pair(spec_parse_12_u8s, spec_parse_tail)(s)
}

pub open spec fn spec_serialize_owl_initiator_msg1_val(s: SpecStream, v: (Seq<u8>, Seq<u8>)) -> SpecSerializeResult
{
    let spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);

    spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_tail)(s, v)
}

pub proof fn lemma_parse_owl_initiator_msg1_val_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_owl_initiator_msg1_val(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_owl_initiator_msg1_val = |s| spec_parse_owl_initiator_msg1_val(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_owl_initiator_msg1_val, s) by {
        lemma_parse_owl_initiator_msg1_val_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_owl_initiator_msg1_val_well_behaved()
    ensures prop_serialize_well_behaved(|s, v| spec_serialize_owl_initiator_msg1_val(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_owl_initiator_msg1_val = |s, v| spec_serialize_owl_initiator_msg1_val(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_owl_initiator_msg1_val, s, v) by {
        lemma_serialize_owl_initiator_msg1_val_well_behaved_on(s, v);
    }
}

pub proof fn lemma_serialize_owl_initiator_msg1_val_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_owl_initiator_msg1_val(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_owl_initiator_msg1_val = |s, v| spec_serialize_owl_initiator_msg1_val(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_owl_initiator_msg1_val, s1, s2, v) by {
        lemma_serialize_owl_initiator_msg1_val_deterministic_on(s1, s2, v);
    }
}
    
pub proof fn lemma_parse_owl_initiator_msg1_val_correct()
    ensures prop_parse_correct(|s| spec_parse_owl_initiator_msg1_val(s), |s, v| spec_serialize_owl_initiator_msg1_val(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_owl_initiator_msg1_val = |s| spec_parse_owl_initiator_msg1_val(s);
    let spec_serialize_owl_initiator_msg1_val = |s, v| spec_serialize_owl_initiator_msg1_val(s, v);
    assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_owl_initiator_msg1_val, spec_serialize_owl_initiator_msg1_val, s, v) by {
        lemma_parse_owl_initiator_msg1_val_correct_on(s, v);
    }
}

pub proof fn lemma_parse_owl_initiator_msg1_val_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_owl_initiator_msg1_val(s), |s, v| spec_serialize_owl_initiator_msg1_val(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_owl_initiator_msg1_val = |s| spec_parse_owl_initiator_msg1_val(s);
    let spec_serialize_owl_initiator_msg1_val = |s, v| spec_serialize_owl_initiator_msg1_val(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_owl_initiator_msg1_val, spec_serialize_owl_initiator_msg1_val, s) by {
        lemma_parse_owl_initiator_msg1_val_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_owl_initiator_msg1_val_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_owl_initiator_msg1_val(s))
{
    lemma_parse_owl_initiator_msg1_val_serialize_inverse();
    lemma_serialize_owl_initiator_msg1_val_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_owl_initiator_msg1_val(s), |s, v| spec_serialize_owl_initiator_msg1_val(s, v));
}

pub proof fn lemma_parse_owl_initiator_msg1_val_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_owl_initiator_msg1_val(s), s)
{
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_parse_tail = |s| spec_parse_tail(s);
    lemma_parse_12_u8s_well_behaved();
    lemma_parse_tail_well_behaved();
    lemma_parse_pair_well_behaved_on(spec_parse_12_u8s, spec_parse_tail, s);
}

pub proof fn lemma_serialize_owl_initiator_msg1_val_well_behaved_on(s: SpecStream, v: (Seq<u8>, Seq<u8>))
    ensures prop_serialize_well_behaved_on(|s, v| spec_serialize_owl_initiator_msg1_val(s, v), s, v)
{
    let spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_serialize_12_u8s_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_serialize_pair_well_behaved_on(spec_serialize_12_u8s, spec_serialize_tail, s, v);
}

pub proof fn lemma_serialize_owl_initiator_msg1_val_deterministic_on(s1: SpecStream, s2: SpecStream, v: (Seq<u8>, Seq<u8>))
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_owl_initiator_msg1_val(s, v), s1, s2, v)
{
    let spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_serialize_12_u8s_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_serialize_12_u8s_deterministic();
    lemma_serialize_tail_deterministic();
    lemma_serialize_pair_deterministic_on(spec_serialize_12_u8s, spec_serialize_tail, s1, s2, v);
}

pub proof fn lemma_parse_owl_initiator_msg1_val_correct_on(s: SpecStream, v: (Seq<u8>, Seq<u8>))
    ensures prop_parse_correct_on(|s| spec_parse_owl_initiator_msg1_val(s), |s, v| spec_serialize_owl_initiator_msg1_val(s, v), s, v)
{
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_parse_tail = |s| spec_parse_tail(s);
    let spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_serialize_12_u8s_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_parse_12_u8s_well_behaved();
    lemma_parse_tail_well_behaved();
    lemma_parse_12_u8s_strong_prefix();
    
    lemma_parse_12_u8s_correct();
    lemma_parse_tail_correct();
    lemma_parse_pair_correct_on(spec_parse_12_u8s, spec_parse_tail, spec_serialize_12_u8s, spec_serialize_tail, s, v);
}

pub proof fn lemma_parse_owl_initiator_msg1_val_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_owl_initiator_msg1_val(s), |s, v| spec_serialize_owl_initiator_msg1_val(s, v), s)
{
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_parse_tail = |s| spec_parse_tail(s);
    let spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    lemma_parse_12_u8s_well_behaved();
    lemma_parse_tail_well_behaved();
    lemma_serialize_12_u8s_well_behaved();
    lemma_serialize_tail_well_behaved();
    lemma_parse_12_u8s_serialize_inverse();
    lemma_parse_tail_serialize_inverse();
    lemma_parse_pair_serialize_inverse_on(spec_parse_12_u8s, spec_parse_tail, spec_serialize_12_u8s, spec_serialize_tail, s);
}
pub exec fn parse_owl_initiator_msg1_val(s: Stream) -> (res: ParseResult<(Vec<u8>, Vec<u8>)>)
    ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_owl_initiator_msg1_val(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_12_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_12_u8s(s)) { parse_12_u8s(s) };
    let parse_tail = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_tail(s)) { parse_tail(s) };
    let ghost spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let ghost spec_parse_tail = |s| spec_parse_tail(s);
    let ghost spec_parse_owl_initiator_msg1_val = spec_parse_pair(spec_parse_12_u8s, spec_parse_tail);

    let parse_owl_initiator_msg1_val = |s| -> (res: ParseResult<(Vec<u8>, Vec<u8>)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_owl_initiator_msg1_val) { parse_pair(parse_12_u8s, parse_tail, Ghost(spec_parse_12_u8s), Ghost(spec_parse_tail), s) };
    assert(prop_parse_exec_spec_equiv(parse_owl_initiator_msg1_val, spec_parse_owl_initiator_msg1_val));

    parse_owl_initiator_msg1_val(s)
}
pub exec fn serialize_owl_initiator_msg1_val(s: Stream, v: (Vec<u8>, Vec<u8>)) -> (res: SerializeResult)
    ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_owl_initiator_msg1_val(s, v))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }
    let serialize_12_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_12_u8s(s, v)) { serialize_12_u8s(s, v) };
    let serialize_tail = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_tail(s, v)) { serialize_tail(s, v) };
    let ghost spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let ghost spec_serialize_tail = |s, v| spec_serialize_tail(s, v);
    let ghost spec_serialize_owl_initiator_msg1_val = spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_tail);

    let serialize_owl_initiator_msg1_val = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_owl_initiator_msg1_val) { serialize_pair(serialize_12_u8s, serialize_tail, Ghost(spec_serialize_12_u8s), Ghost(spec_serialize_tail), s, v) };
    assert(prop_serialize_exec_spec_equiv(serialize_owl_initiator_msg1_val, spec_serialize_owl_initiator_msg1_val));

    serialize_owl_initiator_msg1_val(s, v)
}

pub open spec fn spec_parse_32_u8s(s: SpecStream) -> SpecParseResult<Seq<u8>>
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    spec_parse_repeat_n(spec_parse_u8_le, 32)(s)
}

pub open spec fn spec_serialize_32_u8s(s: SpecStream, vs: Seq<u8>) -> SpecSerializeResult
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    spec_serialize_repeat_n(spec_serialize_u8_le, 32)(s, vs)
}

pub proof fn lemma_parse_32_u8s_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_32_u8s(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_32_u8s, s) by {
        lemma_parse_32_u8s_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_32_u8s_well_behaved()
    ensures prop_serialize_well_behaved(|s, vs| spec_serialize_32_u8s(s, vs))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_32_u8s = |s, vs| spec_serialize_32_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_serialize_well_behaved_on(spec_serialize_32_u8s, s, vs) by {
        lemma_serialize_32_u8s_well_behaved_on(s, vs);
    }
}

pub proof fn lemma_serialize_32_u8s_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_32_u8s(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_32_u8s = |s, vs| spec_serialize_32_u8s(s, vs);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_32_u8s, s1, s2, v) by {
        lemma_serialize_32_u8s_deterministic_on(s1, s2, v);
    }
}

pub proof fn lemma_parse_32_u8s_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_32_u8s(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    assert forall |s1: SpecStream, s2: SpecStream| prop_parse_strong_prefix_on(spec_parse_32_u8s, s1, s2) by {
        lemma_parse_32_u8s_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_32_u8s_correct()
    ensures prop_parse_correct(|s| spec_parse_32_u8s(s), |s, vs| spec_serialize_32_u8s(s, vs))
{
    reveal(prop_parse_correct);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let spec_serialize_32_u8s = |s, vs| spec_serialize_32_u8s(s, vs);
    assert forall |s, vs| #[trigger] prop_parse_correct_on(spec_parse_32_u8s, spec_serialize_32_u8s, s, vs) by {
        lemma_parse_32_u8s_correct_on(s, vs);
    }
}

pub proof fn lemma_parse_32_u8s_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_32_u8s(s), |s, v| spec_serialize_32_u8s(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let spec_serialize_32_u8s = |s, vs| spec_serialize_32_u8s(s, vs);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_32_u8s, spec_serialize_32_u8s, s) by {
        lemma_parse_32_u8s_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_32_u8s_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_32_u8s(s))
{
    lemma_parse_32_u8s_serialize_inverse();
    lemma_serialize_32_u8s_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_32_u8s(s), |s, v| spec_serialize_32_u8s(s, v));
}

proof fn lemma_parse_32_u8s_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_32_u8s(s), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_repeat_n_well_behaved_on(spec_parse_u8_le, 32, s);
}

proof fn lemma_serialize_32_u8s_well_behaved_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_serialize_well_behaved_on(|s, vs| spec_serialize_32_u8s(s, vs), s, vs)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_repeat_n_well_behaved_on(spec_serialize_u8_le, 32, s, vs);
}

proof fn lemma_serialize_32_u8s_deterministic_on(s1: SpecStream, s2: SpecStream, v: Seq<u8>)
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_32_u8s(s, v), s1, s2, v)
{
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_serialize_u8_le_deterministic();
    lemma_serialize_repeat_n_deterministic_on(spec_serialize_u8_le, 32, s1, s2, v);
}

proof fn lemma_parse_32_u8s_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_32_u8s(s), s1, s2)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_repeat_n_strong_prefix_on(s1, s2, spec_parse_u8_le, 32);
}

proof fn lemma_parse_32_u8s_correct_on(s: SpecStream, vs: Seq<u8>)
    ensures prop_parse_correct_on(|s| spec_parse_32_u8s(s), |s, vs| spec_serialize_32_u8s(s, vs), s, vs)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_strong_prefix();
    lemma_parse_u8_le_correct();
    lemma_parse_repeat_n_correct_on(spec_parse_u8_le, spec_serialize_u8_le, 32, s, vs);
}

proof fn lemma_parse_32_u8s_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_32_u8s(s), |s, v| spec_serialize_32_u8s(s, v), s)
{
    let spec_parse_u8_le = |s| spec_parse_u8_le(s);
    let spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);
    lemma_serialize_u8_le_well_behaved();
    lemma_parse_u8_le_well_behaved();
    lemma_parse_u8_le_serialize_inverse();
    lemma_parse_repeat_n_serialize_inverse_on(spec_parse_u8_le, spec_serialize_u8_le, 32, s);
}

pub exec fn parse_32_u8s(s: Stream) -> (res: ParseResult<Vec<u8>>)
    ensures
        prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_32_u8s(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }

        let parse_u8_le = |s| -> (res: ParseResult<u8>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_u8_le(s)) { parse_u8_le(s) };
    let ghost spec_parse_u8_le = |s| spec_parse_u8_le(s);

    parse_repeat_n(parse_u8_le, Ghost(spec_parse_u8_le), 32, s)
}

pub exec fn serialize_32_u8s(s: Stream, vs: Vec<u8>) -> (res: SerializeResult)
    ensures
        prop_serialize_exec_spec_equiv_on(s, vs, res, |s, vs| spec_serialize_32_u8s(s, vs))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }

    let serialize_u8_le = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_u8_le(s, v)) { serialize_u8_le(s, v) };
    let ghost spec_serialize_u8_le = |s, v| spec_serialize_u8_le(s, v);

    serialize_repeat_n(serialize_u8_le, Ghost(spec_serialize_u8_le), 32, s, vs)
}
pub struct SpecOwlTranspKeys {
    owl__transp_keys_initiator: Seq<u8>,
    owl__transp_keys_responder: Seq<u8>,
    owl__transp_keys_init_ephemeral: Seq<u8>,
    owl__transp_keys_resp_ephemeral: Seq<u8>,
    owl__transp_keys_t_init_send: Seq<u8>,
    owl__transp_keys_t_resp_send: Seq<u8>,

}
pub struct OwlTranspKeys {
    owl__transp_keys_initiator: Vec<u8>,
    owl__transp_keys_responder: Vec<u8>,
    owl__transp_keys_init_ephemeral: Vec<u8>,
    owl__transp_keys_resp_ephemeral: Vec<u8>,
    owl__transp_keys_t_init_send: Vec<u8>,
    owl__transp_keys_t_resp_send: Vec<u8>,

}

pub open spec fn spec_parse_owl_transp_keys(s: SpecStream) -> SpecParseResult<(((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)>
{
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);

    spec_parse_6_fold(spec_parse_4_u8s, spec_parse_4_u8s, spec_parse_91_u8s, spec_parse_91_u8s, spec_parse_32_u8s, spec_parse_32_u8s)(s)
}

pub open spec fn spec_serialize_owl_transp_keys(s: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)) -> SpecSerializeResult
{
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);

    spec_serialize_6_fold(spec_serialize_4_u8s, spec_serialize_4_u8s, spec_serialize_91_u8s, spec_serialize_91_u8s, spec_serialize_32_u8s, spec_serialize_32_u8s)(s, v)
}

pub proof fn lemma_parse_owl_transp_keys_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_owl_transp_keys(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_owl_transp_keys = |s| spec_parse_owl_transp_keys(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_owl_transp_keys, s) by {
        lemma_parse_owl_transp_keys_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_owl_transp_keys_well_behaved()
    ensures prop_serialize_well_behaved(|s, v| spec_serialize_owl_transp_keys(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_owl_transp_keys = |s, v| spec_serialize_owl_transp_keys(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_owl_transp_keys, s, v) by {
        lemma_serialize_owl_transp_keys_well_behaved_on(s, v);
    }
}

pub proof fn lemma_serialize_owl_transp_keys_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_owl_transp_keys(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_owl_transp_keys = |s, v| spec_serialize_owl_transp_keys(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_owl_transp_keys, s1, s2, v) by {
        lemma_serialize_owl_transp_keys_deterministic_on(s1, s2, v);
    }
}
    
pub proof fn lemma_parse_owl_transp_keys_correct()
    ensures prop_parse_correct(|s| spec_parse_owl_transp_keys(s), |s, v| spec_serialize_owl_transp_keys(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_owl_transp_keys = |s| spec_parse_owl_transp_keys(s);
    let spec_serialize_owl_transp_keys = |s, v| spec_serialize_owl_transp_keys(s, v);
    assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_owl_transp_keys, spec_serialize_owl_transp_keys, s, v) by {
        lemma_parse_owl_transp_keys_correct_on(s, v);
    }
}

pub proof fn lemma_parse_owl_transp_keys_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_owl_transp_keys(s), |s, v| spec_serialize_owl_transp_keys(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_owl_transp_keys = |s| spec_parse_owl_transp_keys(s);
    let spec_serialize_owl_transp_keys = |s, v| spec_serialize_owl_transp_keys(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_owl_transp_keys, spec_serialize_owl_transp_keys, s) by {
        lemma_parse_owl_transp_keys_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_owl_transp_keys_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_owl_transp_keys(s))
{
    lemma_parse_owl_transp_keys_serialize_inverse();
    lemma_serialize_owl_transp_keys_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_owl_transp_keys(s), |s, v| spec_serialize_owl_transp_keys(s, v));
}

pub proof fn lemma_parse_owl_transp_keys_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_owl_transp_keys(s), s)
{
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_32_u8s_well_behaved();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s, spec_parse_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s);
    lemma_parse_pair_well_behaved_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s), spec_parse_32_u8s, s);
}

pub proof fn lemma_serialize_owl_transp_keys_well_behaved_on(s: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_well_behaved_on(|s, v| spec_serialize_owl_transp_keys(s, v), s, v)
{
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_32_u8s_well_behaved();
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s, spec_serialize_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s);
    lemma_serialize_pair_well_behaved_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s), spec_serialize_32_u8s, s, v);
}

pub proof fn lemma_serialize_owl_transp_keys_deterministic_on(s1: SpecStream, s2: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_owl_transp_keys(s, v), s1, s2, v)
{
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_32_u8s_well_behaved();
    lemma_serialize_4_u8s_deterministic();
    lemma_serialize_91_u8s_deterministic();
    lemma_serialize_32_u8s_deterministic();
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s, spec_serialize_4_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_4_u8s, spec_serialize_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s);
    lemma_serialize_pair_deterministic_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s), spec_serialize_32_u8s, s1, s2, v);
}

pub proof fn lemma_parse_owl_transp_keys_correct_on(s: SpecStream, v: (((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_parse_correct_on(|s| spec_parse_owl_transp_keys(s), |s, v| spec_serialize_owl_transp_keys(s, v), s, v)
{
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_32_u8s_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_32_u8s_well_behaved();
    lemma_parse_4_u8s_strong_prefix();
    lemma_parse_91_u8s_strong_prefix();
    lemma_parse_32_u8s_strong_prefix();
    lemma_parse_4_u8s_correct();
    lemma_parse_91_u8s_correct();
    lemma_parse_32_u8s_correct();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s, spec_parse_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s, spec_serialize_4_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_4_u8s, spec_parse_4_u8s);
    lemma_parse_pair_correct(spec_parse_4_u8s, spec_parse_4_u8s, spec_serialize_4_u8s, spec_serialize_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s);
    lemma_parse_pair_correct_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s), spec_parse_32_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s), spec_serialize_32_u8s, s, v);
}

pub proof fn lemma_parse_owl_transp_keys_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_owl_transp_keys(s), |s, v| spec_serialize_owl_transp_keys(s, v), s)
{
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_32_u8s_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_32_u8s_well_behaved();
    lemma_parse_4_u8s_serialize_inverse();
    lemma_parse_91_u8s_serialize_inverse();
    lemma_parse_32_u8s_serialize_inverse();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s, spec_parse_4_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_4_u8s, spec_serialize_4_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_4_u8s, spec_parse_4_u8s, spec_serialize_4_u8s, spec_serialize_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s);
    lemma_parse_pair_serialize_inverse_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s), spec_parse_32_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_4_u8s, spec_serialize_4_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_32_u8s), spec_serialize_32_u8s, s);
}

pub proof fn lemma_parse_owl_transp_keys_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_owl_transp_keys(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_owl_transp_keys = |s| spec_parse_owl_transp_keys(s);
    assert forall |s1, s2| prop_parse_strong_prefix_on(spec_parse_owl_transp_keys, s1, s2) by {
        lemma_parse_owl_transp_keys_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_owl_transp_keys_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_owl_transp_keys(s), s1, s2)
{
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_32_u8s_well_behaved();
    lemma_parse_4_u8s_strong_prefix();
    lemma_parse_91_u8s_strong_prefix();
    lemma_parse_32_u8s_strong_prefix();
    lemma_parse_pair_well_behaved(spec_parse_4_u8s, spec_parse_4_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_4_u8s, spec_parse_4_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s);
    lemma_parse_pair_strong_prefix_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_4_u8s, spec_parse_4_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_32_u8s), spec_parse_32_u8s, s1, s2);
}

pub exec fn parse_owl_transp_keys(s: Stream) -> (res: ParseResult<(((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)>)
    ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_owl_transp_keys(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_4_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s(s)) { parse_4_u8s(s) };
    let parse_91_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_91_u8s(s)) { parse_91_u8s(s) };
    let parse_32_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_32_u8s(s)) { parse_32_u8s(s) };
    let ghost spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let ghost spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let ghost spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let ghost spec_parse_owl_transp_keys = spec_parse_6_fold(spec_parse_4_u8s, spec_parse_4_u8s, spec_parse_91_u8s, spec_parse_91_u8s, spec_parse_32_u8s, spec_parse_32_u8s);

    let parse_owl_transp_keys = |s| -> (res: ParseResult<(((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_owl_transp_keys) { parse_6_fold(parse_4_u8s, parse_4_u8s, parse_91_u8s, parse_91_u8s, parse_32_u8s, parse_32_u8s, Ghost(spec_parse_4_u8s), Ghost(spec_parse_4_u8s), Ghost(spec_parse_91_u8s), Ghost(spec_parse_91_u8s), Ghost(spec_parse_32_u8s), Ghost(spec_parse_32_u8s), s) };
    assert(prop_parse_exec_spec_equiv(parse_owl_transp_keys, spec_parse_owl_transp_keys));

    parse_owl_transp_keys(s)
}
pub exec fn serialize_owl_transp_keys(s: Stream, v: (((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)) -> (res: SerializeResult)
    ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_owl_transp_keys(s, v))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }
    let serialize_4_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_4_u8s(s, v)) { serialize_4_u8s(s, v) };
    let serialize_91_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_91_u8s(s, v)) { serialize_91_u8s(s, v) };
    let serialize_32_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_32_u8s(s, v)) { serialize_32_u8s(s, v) };
    let ghost spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let ghost spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let ghost spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    let ghost spec_serialize_owl_transp_keys = spec_serialize_6_fold(spec_serialize_4_u8s, spec_serialize_4_u8s, spec_serialize_91_u8s, spec_serialize_91_u8s, spec_serialize_32_u8s, spec_serialize_32_u8s);

    let serialize_owl_transp_keys = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_owl_transp_keys) { serialize_6_fold(serialize_4_u8s, serialize_4_u8s, serialize_91_u8s, serialize_91_u8s, serialize_32_u8s, serialize_32_u8s, Ghost(spec_serialize_4_u8s), Ghost(spec_serialize_4_u8s), Ghost(spec_serialize_91_u8s), Ghost(spec_serialize_91_u8s), Ghost(spec_serialize_32_u8s), Ghost(spec_serialize_32_u8s), s, v) };
    assert(prop_serialize_exec_spec_equiv(serialize_owl_transp_keys, spec_serialize_owl_transp_keys));

    serialize_owl_transp_keys(s, v)
}
pub struct SpecOwlResponderMsg1Val {
    owl__responder_msg1_c3: Seq<u8>,
    owl__responder_msg1_h4: Seq<u8>,
    owl__responder_msg1_ephemeral: Seq<u8>,
    owl__responder_msg1_sender_pk: Seq<u8>,
    owl__responder_msg1_sender: Seq<u8>,

}
pub struct OwlResponderMsg1Val {
    owl__responder_msg1_c3: Vec<u8>,
    owl__responder_msg1_h4: Vec<u8>,
    owl__responder_msg1_ephemeral: Vec<u8>,
    owl__responder_msg1_sender_pk: Vec<u8>,
    owl__responder_msg1_sender: Vec<u8>,

}

pub open spec fn spec_parse_5_fold<R1, R2, R3, R4, R5>(
    parser1: FnSpec(SpecStream) -> SpecParseResult<R1>,
    parser2: FnSpec(SpecStream) -> SpecParseResult<R2>,
    parser3: FnSpec(SpecStream) -> SpecParseResult<R3>,
    parser4: FnSpec(SpecStream) -> SpecParseResult<R4>,
    parser5: FnSpec(SpecStream) -> SpecParseResult<R5>) -> FnSpec(SpecStream) -> SpecParseResult<((((R1, R2), R3), R4), R5)>
{
    spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_pair(parser1, parser2), parser3), parser4), parser5)
}

pub exec fn parse_5_fold<P1, P2, P3, P4, P5, R1, R2, R3, R4, R5>(
    exec_parser1: P1,
    exec_parser2: P2,
    exec_parser3: P3,
    exec_parser4: P4,
    exec_parser5: P5,
    Ghost(spec_parser1): Ghost<FnSpec(SpecStream) -> SpecParseResult<R1::V>>,
    Ghost(spec_parser2): Ghost<FnSpec(SpecStream) -> SpecParseResult<R2::V>>,
    Ghost(spec_parser3): Ghost<FnSpec(SpecStream) -> SpecParseResult<R3::V>>,
    Ghost(spec_parser4): Ghost<FnSpec(SpecStream) -> SpecParseResult<R4::V>>,
    Ghost(spec_parser5): Ghost<FnSpec(SpecStream) -> SpecParseResult<R5::V>>,
    s: Stream) -> (res: ParseResult<((((R1, R2), R3), R4), R5)>)
    where
    R1: DView,
    P1: FnOnce(Stream) -> ParseResult<R1>,
    R2: DView,
    P2: FnOnce(Stream) -> ParseResult<R2>,
    R3: DView,
    P3: FnOnce(Stream) -> ParseResult<R3>,
    R4: DView,
    P4: FnOnce(Stream) -> ParseResult<R4>,
    R5: DView,
    P5: FnOnce(Stream) -> ParseResult<R5>,
    requires
        prop_parse_exec_spec_equiv(exec_parser1, spec_parser1),
        prop_parse_exec_spec_equiv(exec_parser2, spec_parser2),
        prop_parse_exec_spec_equiv(exec_parser3, spec_parser3),
        prop_parse_exec_spec_equiv(exec_parser4, spec_parser4),
        prop_parse_exec_spec_equiv(exec_parser5, spec_parser5),
    ensures
        prop_parse_exec_spec_equiv_on(s, res, spec_parse_5_fold(spec_parser1, spec_parser2, spec_parser3, spec_parser4, spec_parser5))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_2_fold = |s| -> (res: ParseResult<(R1, R2)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parser1, spec_parser2)), { parse_pair(exec_parser1, exec_parser2, Ghost(spec_parser1), Ghost(spec_parser2), s) };
    let parse_3_fold = |s| -> (res: ParseResult<((R1, R2), R3)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)), { parse_pair(parse_2_fold, exec_parser3, Ghost(spec_parse_pair(spec_parser1, spec_parser2)), Ghost(spec_parser3), s) };
    let parse_4_fold = |s| -> (res: ParseResult<(((R1, R2), R3), R4)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4)), { parse_pair(parse_3_fold, exec_parser4, Ghost(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3)), Ghost(spec_parser4), s) };
    parse_pair(parse_4_fold, exec_parser5, Ghost(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parser1, spec_parser2), spec_parser3), spec_parser4)), Ghost(spec_parser5), s)
}



pub open spec fn spec_serialize_5_fold<T1, T2, T3, T4, T5>(
    serializer1: FnSpec(SpecStream, T1) -> SpecSerializeResult,
    serializer2: FnSpec(SpecStream, T2) -> SpecSerializeResult,
    serializer3: FnSpec(SpecStream, T3) -> SpecSerializeResult,
    serializer4: FnSpec(SpecStream, T4) -> SpecSerializeResult,
    serializer5: FnSpec(SpecStream, T5) -> SpecSerializeResult) -> FnSpec(SpecStream, ((((T1, T2), T3), T4), T5)) -> SpecSerializeResult
{
    spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(serializer1, serializer2), serializer3), serializer4), serializer5)
}
pub exec fn serialize_5_fold<S1, S2, S3, S4, S5, T1, T2, T3, T4, T5>(
    exec_serializer1: S1,
    exec_serializer2: S2,
    exec_serializer3: S3,
    exec_serializer4: S4,
    exec_serializer5: S5,
    Ghost(spec_serializer1): Ghost<FnSpec(SpecStream, T1::V) -> SpecSerializeResult>,
    Ghost(spec_serializer2): Ghost<FnSpec(SpecStream, T2::V) -> SpecSerializeResult>,
    Ghost(spec_serializer3): Ghost<FnSpec(SpecStream, T3::V) -> SpecSerializeResult>,
    Ghost(spec_serializer4): Ghost<FnSpec(SpecStream, T4::V) -> SpecSerializeResult>,
    Ghost(spec_serializer5): Ghost<FnSpec(SpecStream, T5::V) -> SpecSerializeResult>,
    s: Stream, v: ((((T1, T2), T3), T4), T5)) -> (res: SerializeResult)
    where
    T1: std::fmt::Debug + DView,
    S1: FnOnce(Stream, T1) -> SerializeResult,
    T2: std::fmt::Debug + DView,
    S2: FnOnce(Stream, T2) -> SerializeResult,
    T3: std::fmt::Debug + DView,
    S3: FnOnce(Stream, T3) -> SerializeResult,
    T4: std::fmt::Debug + DView,
    S4: FnOnce(Stream, T4) -> SerializeResult,
    T5: std::fmt::Debug + DView,
    S5: FnOnce(Stream, T5) -> SerializeResult,
    requires
        prop_serialize_exec_spec_equiv(exec_serializer1, spec_serializer1),
        prop_serialize_exec_spec_equiv(exec_serializer2, spec_serializer2),
        prop_serialize_exec_spec_equiv(exec_serializer3, spec_serializer3),
        prop_serialize_exec_spec_equiv(exec_serializer4, spec_serializer4),
        prop_serialize_exec_spec_equiv(exec_serializer5, spec_serializer5),
    ensures
        prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_5_fold(spec_serializer1, spec_serializer2, spec_serializer3, spec_serializer4, spec_serializer5))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }
    let serialize_2_fold = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serializer1, spec_serializer2)), { serialize_pair(exec_serializer1, exec_serializer2, Ghost(spec_serializer1), Ghost(spec_serializer2), s, v) };
    let serialize_3_fold = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3)), { serialize_pair(serialize_2_fold, exec_serializer3, Ghost(spec_serialize_pair(spec_serializer1, spec_serializer2)), Ghost(spec_serializer3), s, v) };
    let serialize_4_fold = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3), spec_serializer4)), { serialize_pair(serialize_3_fold, exec_serializer4, Ghost(spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3)), Ghost(spec_serializer4), s, v) };
    serialize_pair(serialize_4_fold, exec_serializer5, Ghost(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serializer1, spec_serializer2), spec_serializer3), spec_serializer4)), Ghost(spec_serializer5), s, v)
}


pub open spec fn spec_parse_owl_responder_msg1_val(s: SpecStream) -> SpecParseResult<((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)>
{
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);

    spec_parse_5_fold(spec_parse_12_u8s, spec_parse_32_u8s, spec_parse_91_u8s, spec_parse_91_u8s, spec_parse_4_u8s)(s)
}

pub open spec fn spec_serialize_owl_responder_msg1_val(s: SpecStream, v: ((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>)) -> SpecSerializeResult
{
    let spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);

    spec_serialize_5_fold(spec_serialize_12_u8s, spec_serialize_32_u8s, spec_serialize_91_u8s, spec_serialize_91_u8s, spec_serialize_4_u8s)(s, v)
}

pub proof fn lemma_parse_owl_responder_msg1_val_well_behaved()
    ensures prop_parse_well_behaved(|s| spec_parse_owl_responder_msg1_val(s))
{
    reveal(prop_parse_well_behaved);
    let spec_parse_owl_responder_msg1_val = |s| spec_parse_owl_responder_msg1_val(s);
    assert forall |s| #[trigger] prop_parse_well_behaved_on(spec_parse_owl_responder_msg1_val, s) by {
        lemma_parse_owl_responder_msg1_val_well_behaved_on(s);
    }
}

pub proof fn lemma_serialize_owl_responder_msg1_val_well_behaved()
    ensures prop_serialize_well_behaved(|s, v| spec_serialize_owl_responder_msg1_val(s, v))
{
    reveal(prop_serialize_well_behaved);
    let spec_serialize_owl_responder_msg1_val = |s, v| spec_serialize_owl_responder_msg1_val(s, v);
    assert forall |s, v| #[trigger] prop_serialize_well_behaved_on(spec_serialize_owl_responder_msg1_val, s, v) by {
        lemma_serialize_owl_responder_msg1_val_well_behaved_on(s, v);
    }
}

pub proof fn lemma_serialize_owl_responder_msg1_val_deterministic()
    ensures prop_serialize_deterministic(|s, v| spec_serialize_owl_responder_msg1_val(s, v))
{
    reveal(prop_serialize_deterministic);
    let spec_serialize_owl_responder_msg1_val = |s, v| spec_serialize_owl_responder_msg1_val(s, v);
    assert forall |s1, s2, v| #[trigger] prop_serialize_deterministic_on(spec_serialize_owl_responder_msg1_val, s1, s2, v) by {
        lemma_serialize_owl_responder_msg1_val_deterministic_on(s1, s2, v);
    }
}
    
pub proof fn lemma_parse_owl_responder_msg1_val_correct()
    ensures prop_parse_correct(|s| spec_parse_owl_responder_msg1_val(s), |s, v| spec_serialize_owl_responder_msg1_val(s, v))
{
    reveal(prop_parse_correct);
    let spec_parse_owl_responder_msg1_val = |s| spec_parse_owl_responder_msg1_val(s);
    let spec_serialize_owl_responder_msg1_val = |s, v| spec_serialize_owl_responder_msg1_val(s, v);
    assert forall |s, v| #[trigger] prop_parse_correct_on(spec_parse_owl_responder_msg1_val, spec_serialize_owl_responder_msg1_val, s, v) by {
        lemma_parse_owl_responder_msg1_val_correct_on(s, v);
    }
}

pub proof fn lemma_parse_owl_responder_msg1_val_serialize_inverse()
    ensures prop_parse_serialize_inverse(|s| spec_parse_owl_responder_msg1_val(s), |s, v| spec_serialize_owl_responder_msg1_val(s, v))
{
    reveal(prop_parse_serialize_inverse);
    let spec_parse_owl_responder_msg1_val = |s| spec_parse_owl_responder_msg1_val(s);
    let spec_serialize_owl_responder_msg1_val = |s, v| spec_serialize_owl_responder_msg1_val(s, v);
    assert forall |s| #[trigger] prop_parse_serialize_inverse_on(spec_parse_owl_responder_msg1_val, spec_serialize_owl_responder_msg1_val, s) by {
        lemma_parse_owl_responder_msg1_val_serialize_inverse_on(s);
    }
}

pub proof fn lemma_parse_owl_responder_msg1_val_nonmalleable()
    ensures prop_parse_nonmalleable(|s| spec_parse_owl_responder_msg1_val(s))
{
    lemma_parse_owl_responder_msg1_val_serialize_inverse();
    lemma_serialize_owl_responder_msg1_val_deterministic();
    lemma_parse_serialize_inverse_implies_nonmalleable(|s| spec_parse_owl_responder_msg1_val(s), |s, v| spec_serialize_owl_responder_msg1_val(s, v));
}

pub proof fn lemma_parse_owl_responder_msg1_val_well_behaved_on(s: SpecStream)
    ensures prop_parse_well_behaved_on(|s| spec_parse_owl_responder_msg1_val(s), s)
{
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    lemma_parse_12_u8s_well_behaved();
    lemma_parse_32_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_pair_well_behaved(spec_parse_12_u8s, spec_parse_32_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_4_u8s, s);
}

pub proof fn lemma_serialize_owl_responder_msg1_val_well_behaved_on(s: SpecStream, v: ((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_well_behaved_on(|s, v| spec_serialize_owl_responder_msg1_val(s, v), s, v)
{
    let spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    lemma_serialize_12_u8s_well_behaved();
    lemma_serialize_32_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_pair_well_behaved(spec_serialize_12_u8s, spec_serialize_32_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_4_u8s, s, v);
}

pub proof fn lemma_serialize_owl_responder_msg1_val_deterministic_on(s1: SpecStream, s2: SpecStream, v: ((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_serialize_deterministic_on(|s, v| spec_serialize_owl_responder_msg1_val(s, v), s1, s2, v)
{
    let spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    lemma_serialize_12_u8s_well_behaved();
    lemma_serialize_32_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_serialize_12_u8s_deterministic();
    lemma_serialize_32_u8s_deterministic();
    lemma_serialize_91_u8s_deterministic();
    lemma_serialize_4_u8s_deterministic();
    lemma_serialize_pair_well_behaved(spec_serialize_12_u8s, spec_serialize_32_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_12_u8s, spec_serialize_32_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_deterministic(spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_serialize_pair_deterministic_on(spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_4_u8s, s1, s2, v);
}

pub proof fn lemma_parse_owl_responder_msg1_val_correct_on(s: SpecStream, v: ((((Seq<u8>, Seq<u8>), Seq<u8>), Seq<u8>), Seq<u8>))
    ensures prop_parse_correct_on(|s| spec_parse_owl_responder_msg1_val(s), |s, v| spec_serialize_owl_responder_msg1_val(s, v), s, v)
{
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    lemma_serialize_12_u8s_well_behaved();
    lemma_serialize_32_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_parse_12_u8s_well_behaved();
    lemma_parse_32_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_12_u8s_strong_prefix();
    lemma_parse_32_u8s_strong_prefix();
    lemma_parse_91_u8s_strong_prefix();
    lemma_parse_4_u8s_strong_prefix();
    lemma_parse_12_u8s_correct();
    lemma_parse_32_u8s_correct();
    lemma_parse_91_u8s_correct();
    lemma_parse_4_u8s_correct();
    lemma_parse_pair_well_behaved(spec_parse_12_u8s, spec_parse_32_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_12_u8s, spec_serialize_32_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_12_u8s, spec_parse_32_u8s);
    lemma_parse_pair_correct(spec_parse_12_u8s, spec_parse_32_u8s, spec_serialize_12_u8s, spec_serialize_32_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_parse_pair_correct(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_correct_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_4_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_4_u8s, s, v);
}

pub proof fn lemma_parse_owl_responder_msg1_val_serialize_inverse_on(s: SpecStream)
    ensures prop_parse_serialize_inverse_on(|s| spec_parse_owl_responder_msg1_val(s), |s, v| spec_serialize_owl_responder_msg1_val(s, v), s)
{
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    let spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    lemma_parse_12_u8s_well_behaved();
    lemma_parse_32_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_serialize_12_u8s_well_behaved();
    lemma_serialize_32_u8s_well_behaved();
    lemma_serialize_91_u8s_well_behaved();
    lemma_serialize_4_u8s_well_behaved();
    lemma_parse_12_u8s_serialize_inverse();
    lemma_parse_32_u8s_serialize_inverse();
    lemma_parse_91_u8s_serialize_inverse();
    lemma_parse_4_u8s_serialize_inverse();
    lemma_parse_pair_well_behaved(spec_parse_12_u8s, spec_parse_32_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_12_u8s, spec_serialize_32_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_12_u8s, spec_parse_32_u8s, spec_serialize_12_u8s, spec_serialize_32_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_serialize_pair_well_behaved(spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_serialize_inverse(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s);
    lemma_parse_pair_serialize_inverse_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_4_u8s, spec_serialize_pair(spec_serialize_pair(spec_serialize_pair(spec_serialize_12_u8s, spec_serialize_32_u8s), spec_serialize_91_u8s), spec_serialize_91_u8s), spec_serialize_4_u8s, s);
}

pub proof fn lemma_parse_owl_responder_msg1_val_strong_prefix()
    ensures prop_parse_strong_prefix(|s| spec_parse_owl_responder_msg1_val(s))
{
    reveal(prop_parse_strong_prefix);
    let spec_parse_owl_responder_msg1_val = |s| spec_parse_owl_responder_msg1_val(s);
    assert forall |s1, s2| prop_parse_strong_prefix_on(spec_parse_owl_responder_msg1_val, s1, s2) by {
        lemma_parse_owl_responder_msg1_val_strong_prefix_on(s1, s2);
    }
}

pub proof fn lemma_parse_owl_responder_msg1_val_strong_prefix_on(s1: SpecStream, s2: SpecStream)
    ensures prop_parse_strong_prefix_on(|s| spec_parse_owl_responder_msg1_val(s), s1, s2)
{
    let spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    lemma_parse_12_u8s_well_behaved();
    lemma_parse_32_u8s_well_behaved();
    lemma_parse_91_u8s_well_behaved();
    lemma_parse_4_u8s_well_behaved();
    lemma_parse_12_u8s_strong_prefix();
    lemma_parse_32_u8s_strong_prefix();
    lemma_parse_91_u8s_strong_prefix();
    lemma_parse_4_u8s_strong_prefix();
    lemma_parse_pair_well_behaved(spec_parse_12_u8s, spec_parse_32_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_12_u8s, spec_parse_32_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s);
    lemma_parse_pair_well_behaved(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_parse_pair_strong_prefix(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s);
    lemma_parse_pair_strong_prefix_on(spec_parse_pair(spec_parse_pair(spec_parse_pair(spec_parse_12_u8s, spec_parse_32_u8s), spec_parse_91_u8s), spec_parse_91_u8s), spec_parse_4_u8s, s1, s2);
}

pub exec fn parse_owl_responder_msg1_val(s: Stream) -> (res: ParseResult<((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)>)
    ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_owl_responder_msg1_val(s))
{
    proof { reveal(prop_parse_exec_spec_equiv); }
    let parse_12_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_12_u8s(s)) { parse_12_u8s(s) };
    let parse_32_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_32_u8s(s)) { parse_32_u8s(s) };
    let parse_91_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_91_u8s(s)) { parse_91_u8s(s) };
    let parse_4_u8s = |s| -> (res: ParseResult<Vec<u8>>) ensures prop_parse_exec_spec_equiv_on(s, res, |s| spec_parse_4_u8s(s)) { parse_4_u8s(s) };
    let ghost spec_parse_12_u8s = |s| spec_parse_12_u8s(s);
    let ghost spec_parse_32_u8s = |s| spec_parse_32_u8s(s);
    let ghost spec_parse_91_u8s = |s| spec_parse_91_u8s(s);
    let ghost spec_parse_4_u8s = |s| spec_parse_4_u8s(s);
    let ghost spec_parse_owl_responder_msg1_val = spec_parse_5_fold(spec_parse_12_u8s, spec_parse_32_u8s, spec_parse_91_u8s, spec_parse_91_u8s, spec_parse_4_u8s);

    let parse_owl_responder_msg1_val = |s| -> (res: ParseResult<((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)>) ensures prop_parse_exec_spec_equiv_on(s, res, spec_parse_owl_responder_msg1_val) { parse_5_fold(parse_12_u8s, parse_32_u8s, parse_91_u8s, parse_91_u8s, parse_4_u8s, Ghost(spec_parse_12_u8s), Ghost(spec_parse_32_u8s), Ghost(spec_parse_91_u8s), Ghost(spec_parse_91_u8s), Ghost(spec_parse_4_u8s), s) };
    assert(prop_parse_exec_spec_equiv(parse_owl_responder_msg1_val, spec_parse_owl_responder_msg1_val));

    parse_owl_responder_msg1_val(s)
}
pub exec fn serialize_owl_responder_msg1_val(s: Stream, v: ((((Vec<u8>, Vec<u8>), Vec<u8>), Vec<u8>), Vec<u8>)) -> (res: SerializeResult)
    ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_owl_responder_msg1_val(s, v))
{
    proof { reveal(prop_serialize_exec_spec_equiv); }
    let serialize_12_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_12_u8s(s, v)) { serialize_12_u8s(s, v) };
    let serialize_32_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_32_u8s(s, v)) { serialize_32_u8s(s, v) };
    let serialize_91_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_91_u8s(s, v)) { serialize_91_u8s(s, v) };
    let serialize_4_u8s = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_4_u8s(s, v)) { serialize_4_u8s(s, v) };
    let ghost spec_serialize_12_u8s = |s, v| spec_serialize_12_u8s(s, v);
    let ghost spec_serialize_32_u8s = |s, v| spec_serialize_32_u8s(s, v);
    let ghost spec_serialize_91_u8s = |s, v| spec_serialize_91_u8s(s, v);
    let ghost spec_serialize_4_u8s = |s, v| spec_serialize_4_u8s(s, v);
    let ghost spec_serialize_owl_responder_msg1_val = spec_serialize_5_fold(spec_serialize_12_u8s, spec_serialize_32_u8s, spec_serialize_91_u8s, spec_serialize_91_u8s, spec_serialize_4_u8s);

    let serialize_owl_responder_msg1_val = |s, v| -> (res: SerializeResult) ensures prop_serialize_exec_spec_equiv_on(s, v, res, spec_serialize_owl_responder_msg1_val) { serialize_5_fold(serialize_12_u8s, serialize_32_u8s, serialize_91_u8s, serialize_91_u8s, serialize_4_u8s, Ghost(spec_serialize_12_u8s), Ghost(spec_serialize_32_u8s), Ghost(spec_serialize_91_u8s), Ghost(spec_serialize_91_u8s), Ghost(spec_serialize_4_u8s), s, v) };
    assert(prop_serialize_exec_spec_equiv(serialize_owl_responder_msg1_val, spec_serialize_owl_responder_msg1_val));

    serialize_owl_responder_msg1_val(s, v)
}

fn main() {}
}
