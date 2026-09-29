use vest_lib::core::spec::*;
use vest_lib::core::exec::{
    OutputBuf, PResult, ParseError, Parser, PreSerializeError, Prepare, Serializer,
};
use vstd::prelude::*;
use crate::execlib::{OwlBuf, slice_eq};

verus! {

/// Combinator for parsing and serializing a fixed, statically known byte string. The
/// parsed value is `()`.
pub struct OwlConstBytes<const N: usize>(pub [u8; N]);

impl<const N: usize> View for OwlConstBytes<N> {
    type V = OwlConstBytes<N>;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl<const N: usize> SpecParser for OwlConstBytes<N> {
    type PVal = ();

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, ())> {
        if N <= s.len() && s.take(N as int) == self.0@ {
            Some((N as int, ()))
        } else {
            None
        }
    }
}

impl<const N: usize> SafeParser for OwlConstBytes<N> {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }
}

impl<const N: usize> Consistency for OwlConstBytes<N> {
    type Val = ();

    open spec fn consistent(&self, v: ()) -> bool {
        true
    }
}

impl<const N: usize> SpecByteLen for OwlConstBytes<N> {
    type T = ();

    open spec fn byte_len(&self, v: ()) -> nat {
        N as nat
    }
}

impl<const N: usize> SpecSerializer for OwlConstBytes<N> {
    type SVal = ();

    open spec fn spec_serialize(&self, v: ()) -> Seq<u8> {
        self.0@
    }
}

impl<const N: usize> SpecSerializerDps for OwlConstBytes<N> {
    type SValue = ();

    open spec fn spec_serialize_dps(&self, v: (), obuf: Seq<u8>) -> Seq<u8> {
        self.0@ + obuf
    }
}

// Parsing compares bytes, which Vest's generic `InputBuf` does not expose, so the
// parser is specific to `OwlBuf` (constants only occur in public formats).
impl<'x, const N: usize> Parser<OwlBuf<'x>> for OwlConstBytes<N> {
    type PT = ();

    fn parse(&self, s: &OwlBuf<'x>) -> (res: PResult<()>) {
        if N <= s.len() {
            let prefix = s.another_ref().subrange(0, N);
            if slice_eq(prefix.as_slice(), self.0.as_slice()) {
                Ok((N, ()))
            } else {
                Err(ParseError::invalid_tag())
            }
        } else {
            Err(ParseError::unexpected_eof())
        }
    }
}

impl<Output: OutputBuf, const N: usize> Serializer<Output, ()> for OwlConstBytes<N> {
    fn serialize_into(&self, v: &(), obuf: &mut Output) {
        obuf.write_bytes(self.0.as_slice());
    }
}

impl<const N: usize> Prepare<()> for OwlConstBytes<N> {
    fn prepare(&self, v: &()) -> (checked: Result<usize, PreSerializeError>) {
        Ok(N)
    }
}

} // verus!
