use vest::properties::*;
use vstd::prelude::*;

verus! {

/// Combinator for parsing and serializing a fixed number of bytes (statically known).
pub struct OwlConstBytes<const N: usize>(pub [u8; N]);

impl<const N: usize> View for OwlConstBytes<N> {
    type V = OwlConstBytes<N>;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl<const N: usize> SpecCombinator for OwlConstBytes<N> {
    type Type = ();

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        if N <= s.len() && s.subrange(0, N as int) == self.0@ {
            Ok((N, ()))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, _v: Self::Type) -> Result<Seq<u8>, ()> {
        Ok(self.0@)
    }

    // proof fn spec_parse_wf(&self, s: Seq<u8>) {
    // }
}

impl<const N: usize> SecureSpecCombinator for OwlConstBytes<N> {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        assert(s1.add(s2).len() == s1.len() + s2.len());
        if let Ok((n, v)) = self.spec_parse(s1) {
            assert(s1.add(s2).subrange(0, n as int) == s1.subrange(0, n as int))
        } else {
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if let Ok(buf) = self.spec_serialize(v) {
            assert(buf.subrange(0, buf.len() as int) == self.0@);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    open spec fn is_productive(&self) -> bool {
        N > 0
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<const N: usize, I, O> Combinator<I, O> for OwlConstBytes<N> where
    I: VestPublicInput,
    O: VestPublicOutput<I>,
 {
    type Type = ();

    open spec fn spec_length(&self) -> Option<usize> {
        Some(N)
    }

    fn length(&self) -> Option<usize> {
        Some(N)
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        if N <= s.len() {
            let s_ = s.subrange(0, N);
            if compare_slice(s_.as_byte_slice(), self.0.as_slice()) {
                Ok((N, ()))
            } else {
                Err(ParseError::Other("OwlConstBytes: mismatch".to_string()))
            }
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let s = self.0.as_slice();
        if s.len() <= data.len() && s.len() == N && pos <= data.len() - s.len() {
            data.set_byte_range(pos, s);
            assert(data@.subrange(pos as int, pos + N as int) == self@.spec_serialize(v@).unwrap());
            Ok(N)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
