use std::rc::Rc;
pub use vstd::{modes::*, prelude::*, seq::*, view::*, slice::*};
use crate::{*, speclib::*};
// (the other Vest names are re-exported by the preamble)
use vest_lib::core::exec::{PreSerializeError, ComplianceErrorKind};

// The KEM implementation (libcrux-ml-kem on libsignal's serialized keys and ciphertexts);
// its trusted Verus wrappers are owl_kem_encaps, owl_kem_decaps and owl_kem_pk below
#[path = "owl_kem.rs"]
pub mod owl_kem;


verus! {
    
enum OwlBufInner<'a> {
    Borrowed(&'a [u8]),
    Owned(Rc<Vec<u8>>, usize, usize), // buffer, start, len
}

pub struct OwlBuf<'a> {
    inner: OwlBufInner<'a>
}

impl View for OwlBuf<'_> {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Self::V {
        match self.inner {
            OwlBufInner::Borrowed(s) => s.view(),
            OwlBufInner::Owned(v, start, len) => v.view().subrange(start as int, (start + len) as int),
        }
    }
}

impl<'x> OwlBuf<'x> {
    // Invariants
    #[verifier::opaque]
    #[verifier::type_invariant]
    pub closed spec fn len_valid(&self) -> bool {
        match self.inner {
            OwlBufInner::Borrowed(s) => true,
            OwlBufInner::Owned(v, start, len) => 
                (start as int + len as int <= v.view().len()) 
                && v.view().len() <= usize::MAX as int,
        }
    }

    // Constructors
    pub fn from_slice(s: &[u8]) -> (result: OwlBuf)
        ensures result.view() == s.view(),
                result.len_valid(),
    {
        reveal(OwlBuf::len_valid);
        OwlBuf { inner: OwlBufInner::Borrowed(s) }
    }

    pub fn from_vec(v: Vec<u8>) -> (result: OwlBuf<'x>)
        ensures result.view() == v.view(),
    {
        reveal(OwlBuf::len_valid);
        broadcast use axiom_spec_len;
        let len = v.len();
        proof { assert_seqs_equal!(v.view(), v.view().subrange(0int, len as int)); }
        OwlBuf { inner: OwlBufInner::Owned(Rc::new(v), 0, len) }
    }
    
    pub fn from_vec_option(v: Option<Vec<u8>>) -> (result: Option<OwlBuf<'x>>)
        ensures view_option(result) == view_option(v),
    {
        match v {
            Some(v) => Some(OwlBuf::from_vec(v)),
            None => None,
        }
    }

    // Member functions
    pub fn len(&self) -> (result: usize)
        ensures result == self.view().len()
    {
        proof { use_type_invariant(&self) }
        match &self.inner {
            OwlBufInner::Borrowed(s) => {
                proof { assert_seqs_equal!(s.view(), self.view()); }
                slice_len(s)
            },
            OwlBufInner::Owned(v, start, len) => {
                reveal(OwlBuf::len_valid);
                *len
            },
        }
    }

    pub fn as_slice<'a>(&'a self) -> (result: &'a [u8])
        ensures  result.view() == self.view()
    {
        proof { use_type_invariant(&self) }
        match &self.inner {
            OwlBufInner::Borrowed(s) => s,
            OwlBufInner::Owned(v, start, len) => {
                reveal(OwlBuf::len_valid);
                slice_subrange((**v).as_slice(), *start, *start + *len)
            },
        }
    }

    pub fn subrange(self, start: usize, end: usize) -> (result: OwlBuf<'x>)
        requires 0 <= start <= end <= self.view().len(),
        ensures  result.view() == self.view().subrange(start as int, end as int),
    {
        proof { use_type_invariant(&self) }
        reveal(OwlBuf::len_valid);
        match &self.inner {
            OwlBufInner::Borrowed(s) => OwlBuf { inner: OwlBufInner::Borrowed(slice_subrange(s, start, end)) },
            OwlBufInner::Owned(v, start0, _) => {
                let new_start = start0 + start;
                let len = end - start;
                proof { 
                    assert_seqs_equal!(
                        self.view().subrange(start as int, end as int), 
                        (*v).view().subrange(new_start as int, new_start as int + len as int)
                    ); 
                }
                OwlBuf { inner: OwlBufInner::Owned(Rc::clone(&v), new_start, len) }
            },
        }
    }

    pub fn eq_contents(&self, other: &OwlBuf) -> (result: bool)
        ensures  result == (self.view() == other.view())
    {
        proof { 
            use_type_invariant(&self);
            use_type_invariant(&other);
        }
        reveal(OwlBuf::len_valid);
        let self_slice = self.as_slice();
        let other_slice = other.as_slice();
        slice_eq(self_slice, other_slice)
    }

    pub fn another_ref<'a>(&'a self) -> (result: OwlBuf<'x>)
        ensures  result.view() == self.view(),
    {
        proof { use_type_invariant(&self) }
        reveal(OwlBuf::len_valid);
        match &self.inner {
            OwlBufInner::Borrowed(s) => OwlBuf { inner: OwlBufInner::Borrowed(s) },
            OwlBufInner::Owned(v, start, len) => {
                OwlBuf { inner: OwlBufInner::Owned(Rc::clone(&v), *start, *len) }
            },
        }
    }

    pub fn another_ref_option<'a>(x: &'a Option<Self>) -> (result: Option<OwlBuf<'x>>)
        ensures view_option(result) == view_option(*x),
    {
        match x {
            Some(x) => Some(OwlBuf::another_ref(x)),
            None => None,
        }
    }

    pub fn into_owned(self) -> (result: OwlBuf<'x>)
        ensures  result.view() == self.view(),
    {
        proof { use_type_invariant(&self) }
        reveal(OwlBuf::len_valid);
        match &self.inner {
            OwlBufInner::Borrowed(s) => OwlBuf::from_vec(slice_to_vec(s)),
            OwlBufInner::Owned(v, start, len) => OwlBuf { inner: OwlBufInner::Owned(Rc::clone(&v), *start, *len) },
        }
    }

    pub fn into_secret(self) -> (result: SecretBuf<'x>)
        ensures  result.view() == self.view(),
    {
        proof { use_type_invariant(&self) }
        reveal(OwlBuf::len_valid);
        SecretBuf::from_buf(self)
    }
}

///////// Vest 2.0 integration for OwlBuf

impl DeepView for OwlBuf<'_> {
    type V = Seq<u8>;

    open spec fn deep_view(&self) -> Seq<u8> {
        self.view()
    }
}

impl InputSlice for OwlBuf<'_> {
    proof fn deep_view_eq_view(&self) {
    }
}

impl<'x> InputBuf for OwlBuf<'x> {
    fn len(&self) -> (len: usize) {
        OwlBuf::len(self)
    }

    fn subrange(&self, i: usize, j: usize) -> (sliced: Self) {
        OwlBuf::subrange(self.another_ref(), i, j)
    }
}

impl<'x> Parser<OwlBuf<'x>> for U8 {
    type PT = u8;

    fn parse(&self, ibuf: &OwlBuf<'x>) -> (r: PResult<u8>) {
        let s = ibuf.as_slice();
        <U8 as Parser<&[u8]>>::parse(&U8, &s)
    }
}

impl<Len: AsLen> Serializer<Vec<u8>, OwlBuf<'_>> for Varied<Len> {
    fn serialize_into(&self, v: &OwlBuf<'_>, obuf: &mut Vec<u8>) {
        obuf.write_bytes(v.as_slice());
    }
}

impl Serializer<Vec<u8>, OwlBuf<'_>> for Tail {
    fn serialize_into(&self, v: &OwlBuf<'_>, obuf: &mut Vec<u8>) {
        obuf.write_bytes(v.as_slice());
    }
}

impl<Len: AsLen> Prepare<OwlBuf<'_>> for Varied<Len> {
    fn prepare(&self, v: &OwlBuf<'_>) -> (checked: Result<usize, PreSerializeError>) {
        if v.len() == self.0.get() {
            Ok(v.len())
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::LengthInconsistent))
        }
    }
}

impl Prepare<OwlBuf<'_>> for Tail {
    fn prepare(&self, v: &OwlBuf<'_>) -> (checked: Result<usize, PreSerializeError>) {
        Ok(v.len())
    }
}


// KEM lengths, see owl_kem.rs. Secret keys and ciphertexts are in libsignal's serialized
// forms, which start with a one-byte key type (0x08 = Kyber1024, 0x0A = ML-KEM-1024); a
// public key (the model's kem_pk) is a raw Kyber1024 key, as Bob signs 0x08 ++ kem_pk.
// OwlC names them after the Owl length constants kem_pk, kem_cipherlen and name kind kemkey.
pub spec const SPEC_KEMKEY_SIZE: usize = 3169usize; // 1 + 3168 (decapsulation key)
pub spec const SPEC_KEM_PK_SIZE: usize = 1568usize; // raw Kyber1024 encapsulation key
pub spec const SPEC_KEM_CIPHERLEN_SIZE: usize = 1569usize; // 1 + 1568 (ciphertext)
pub spec const SPEC_KEM_COINS_SIZE: usize = 32usize; // randomness of one encapsulation

#[verifier::when_used_as_spec(SPEC_KEMKEY_SIZE)]
pub exec const KEMKEY_SIZE: usize ensures KEMKEY_SIZE == SPEC_KEMKEY_SIZE { 3169usize }

#[verifier::when_used_as_spec(SPEC_KEM_PK_SIZE)]
pub exec const KEM_PK_SIZE: usize ensures KEM_PK_SIZE == SPEC_KEM_PK_SIZE { 1568usize }

#[verifier::when_used_as_spec(SPEC_KEM_CIPHERLEN_SIZE)]
pub exec const KEM_CIPHERLEN_SIZE: usize ensures KEM_CIPHERLEN_SIZE == SPEC_KEM_CIPHERLEN_SIZE { 1569usize }

#[verifier::when_used_as_spec(SPEC_KEM_COINS_SIZE)]
pub exec const KEM_COINS_SIZE: usize ensures KEM_COINS_SIZE == SPEC_KEM_COINS_SIZE { 32usize }

pub fn owl_unit() -> (res: ())
{ () }

pub fn owl_ghost_unit() -> (res: Ghost<()>)
{ Ghost(()) }

#[verifier(external_body)]
pub exec fn slice_eq(s1: &[u8], s2: &[u8]) -> (res: bool)
    ensures res == (s1.view() == s2.view())
{
    s1 == s2
}

#[verifier(external_body)]
pub exec fn slice_len<T: View>(slice: &[T]) -> (length: usize)
    ensures 
        length >= 0,
        length == slice.view().len()
{
    slice.len()
}

#[verifier(external_body)]
pub exec fn vec_eq(v1: &Vec<u8>, v2: &Vec<u8>) -> (res: bool)
    ensures res == (v1.view() == v2.view())
{
    v1 == v2
}

#[verifier(external_body)]
pub exec fn rc_vec_eq(v1: &Vec<u8>, v2: &Vec<u8>) -> (res: bool)
    ensures res == (v1.view() == v2.view())
{
    v1 == v2
}

#[verifier(external_body)]
pub exec fn clone_vec_u8(v: &Vec<u8>) -> (res: Vec<u8>)
    ensures res.view() == v.view()
{
    v.clone()
}

#[verifier(external_body)]
pub exec fn extend_vec_u8(v: &mut Vec<u8>, s: &[u8])
    ensures final(v).view() == old(v).view().add(s.view())
{
    v.extend(s);
}

#[verifier::external_body]
pub exec fn vec_truncate(vec: &mut Vec<u8>, len: usize)
    ensures
        final(vec).view() == seq_truncate(old(vec).view(), len as nat)
{
    vec.truncate(len)
}

pub exec fn owl_concat(a: &[u8], b: &[u8]) -> (res: Vec<u8>)
    ensures res.view() == concat(a.view(), b.view())
{
    let mut v = slice_to_vec(a);
    extend_vec_u8(&mut v, b);
    v
}


#[verifier(external_body)]
pub exec fn owl_crh(x: &[u8]) -> (res: Vec<u8>)
    ensures res.view() == crh(x.view())
{
    owl_hmac::blake2s(x)
}

#[verifier(external_body)]
pub exec fn vec_u8_from_elem(e: u8, n: usize) -> (res: Vec<u8>)
    ensures res.view() == Seq::new(n as nat, |i| e)
{
    // let mut v = vec_new();
    // let mut i = 0;
    // proof { assert_seqs_equal!(v.view(), Seq::new(0, |i| e)); }
    // while i < n
    //     invariant
    //         i <= n,
    //         v.view() == Seq::new(i as nat, |j| e)
    // {
    //     vec_push(&mut v, e);
    //     i = i + 1;
    //     proof { assert_seqs_equal!(v.view(), Seq::new(i as nat, |j| e)); }
    // }
    // v
    vec![e; n]
}

pub exec fn vec_u8_of_len(n: usize) -> (res: Vec<u8>)
    ensures res.view() == seq_u8_of_len(n as nat)
{
    vec_u8_from_elem(0u8, n)
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! mk_vec_u8 {
    ($($e:expr),* $(,)?) => {
        verus_exec_expr!{{
            #[allow(unused_mut)]
            let mut v = Vec::new();
            $(
                v.push($e);
            )*
            v
        }}
    };
}
// pub(crate) use mk_vec_u8;


pub open spec fn view_first_byte_pair(x: (u8, SecretBuf<'_>)) -> Seq<u8>
{
    seq![x.0].add(x.1.view())
}

pub open spec fn view_first_byte_pair_opt(x: Option<(u8, SecretBuf<'_>)>) -> Seq<u8>
{
    match x {
        Some(y) => seq![y.0].add(y.1.view()),
        None => seq![]
    }
}


pub fn owl_is_some<T>(x: Option<T>) -> (res: bool)
    ensures res <==> x.is_some()
{
    x.is_some()   
}

pub fn owl_is_none<T>(x: Option<T>) -> (res: bool)
    ensures res <==> x.is_none()
{
    x.is_none()   
}

}


////////////////////////////////////////////////////////////////////////////////
///////////////////// Secret buffer abstraction ////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

pub mod secret {
    use crate::execlib::*;
    use vstd::*;
    
    verus! {
    
    pub struct SecretBuf<'a> {
        buf: OwlBuf<'a>
    }

    impl View for SecretBuf<'_> {
        type V = Seq<u8>;

        closed spec fn view(&self) -> Self::V {
            self.buf.view()
        }
    }

    impl<'x> SecretBuf<'x> {
        #[verifier::opaque]
        #[verifier::type_invariant]
        pub closed spec fn len_valid(&self) -> bool {
            self.buf.len_valid()
        }

        pub fn from_buf(buf: OwlBuf<'x>) -> (result: SecretBuf<'x>)
            ensures result.view() == buf.view(),
        {
            reveal(SecretBuf::len_valid);
            reveal(OwlBuf::len_valid);
            proof { use_type_invariant(&buf) }
            SecretBuf { buf }
        }

        pub fn another_ref<'a>(&'a self) -> (result: SecretBuf<'x>)
            ensures  result.view() == self.view(),
        {
            reveal(SecretBuf::len_valid);
            let buf = self.buf.another_ref();
            proof { 
                use_type_invariant(&buf);
            }
            SecretBuf { buf }
        }

        pub fn another_ref_option<'a>(x: &'a Option<Self>) -> (result: Option<SecretBuf<'x>>)
            ensures view_option(result) == view_option(*x),
        {
            match x {
                Some(x) => Some(SecretBuf::another_ref(x)),
                None => None,
            }
        }

        pub fn subrange(self, start: usize, end: usize) -> (result: SecretBuf<'x>)
            requires 0 <= start <= end <= self.view().len(),
            ensures  result.view() == self.view().subrange(start as int, end as int),
        {
            reveal(SecretBuf::len_valid);
            let buf = self.buf.subrange(start, end);
            proof { use_type_invariant(&buf) }
            SecretBuf { buf }
        }

        pub fn len(&self) -> (result: usize)
            ensures result == self.view().len()
        {
            self.buf.len()
        }

        ///////// Declassifying operations on SecretBufs

        #[verifier::external_body]
        pub fn declassify<'a>(&'a self, Tracked(t): Tracked<DeclassifyingOpToken>) -> (result: OwlBuf<'x>)
            requires t.view() matches DeclassifyingOp::ControlFlow(b) && b == self.view()
            ensures result.view() == self.view(),
        {
            reveal(SecretBuf::len_valid);
            proof { use_type_invariant(&self) }
            self.buf.another_ref()
        }

        #[verifier::external_body]
        pub fn declassify_first_byte<'a>(
            &'a self, 
            Tracked(t): Tracked<DeclassifyingOpToken>
        ) -> (result: Option<(u8, SecretBuf<'x>)>)
            requires t.view() matches DeclassifyingOp::EnumParse(b) && b == self.view()
            ensures result matches Some(p) ==> self.view() == view_first_byte_pair(p),
                    result is None ==> self.view().len() == 0,
        {
            proof { use_type_invariant(&self) }
            if self.buf.len() == 0 {
                None
            } else {
                let first_byte = self.buf.as_slice()[0];
                let rest = SecretBuf { buf: self.buf.another_ref().subrange(1, self.buf.len()) };
                Some((first_byte, rest))
            }
        }

        #[verifier::external_body]
        pub fn secret_eq(&self, other: &SecretBuf, Tracked(t): Tracked<DeclassifyingOpToken>) -> (result: bool)
            requires t.view() matches DeclassifyingOp::EqCheck(l,r) && 
                        ((self@ == l && other@ == r) || (self@ == r && other@ == l))
            ensures  result <==> self.view() == other.view()
        {
            // self.buf.eq_contents(&other.buf)
            todo!("implement secret_eq")
        }
        
        // Private function for declassification---can only be used in the `secret` module
        // needed to get values out of the SecretBuf to send to the crypto library
        // TODO: if we ever have a Verus crypto library, we could connect the secret buffer type from
        // that library directly
        fn private_as_slice(&self) -> (result: &[u8])
            ensures  result.view() == self.view()
        {
            reveal(SecretBuf::len_valid);
            self.buf.as_slice()
        }
    }

    pub fn owl_secret_concat<'a>(a: SecretBuf<'a>, b: SecretBuf<'_>) -> (res: SecretBuf<'a>)
        ensures res.view() == concat(a.view(), b.view())
    {
        let v = owl_concat(a.private_as_slice(), b.private_as_slice());
        SecretBuf::from_buf(OwlBuf::from_vec(v))
    }

    ///////// Vest 2.0 integration for SecretBuf

    impl DeepView for SecretBuf<'_> {
        type V = Seq<u8>;

        open spec fn deep_view(&self) -> Seq<u8> {
            self.view()
        }
    }

    impl InputSlice for SecretBuf<'_> {
        proof fn deep_view_eq_view(&self) {
        }
    }

    impl<'x> InputBuf for SecretBuf<'x> {
        fn len(&self) -> (len: usize) {
            SecretBuf::len(self)
        }

        fn subrange(&self, i: usize, j: usize) -> (sliced: Self) {
            SecretBuf::subrange(self.another_ref(), i, j)
        }
    }

    pub struct SecretOutputBuf {
        obuf: Vec<u8>
    }

    impl View for SecretOutputBuf {
        type V = Seq<u8>;

        closed spec fn view(&self) -> Self::V {
            self.obuf.view()
        }
    }

    impl SecretOutputBuf {
        pub fn new_obuf() -> (result: SecretOutputBuf)
            ensures result.view() == Seq::<u8>::empty()
        {
            SecretOutputBuf { obuf: Vec::new() }
        }

        pub fn len(&self) -> (result: usize)
            ensures result == self.view().len()
        {
            self.obuf.len()
        }

        // Private: appends the contents of a SecretBuf, only used by the serializers below
        fn write_secret(&mut self, input: &SecretBuf)
            ensures
                final(self)@ == old(self)@ + input@,
        {
            let slice = input.private_as_slice();
            extend_vec_u8(&mut self.obuf, slice);
        }

        pub fn into_secret_buf<'x>(self) -> (result: SecretBuf<'x>)
            ensures result.view() == self.view()
        {
            SecretBuf::from_buf(OwlBuf::from_vec(self.obuf))
        }
    }

    impl OutputBuf for SecretOutputBuf {
        open spec fn fits(&self, _len: nat) -> bool {
            true
        }

        proof fn lemma_fits_mono(&self, _shorter: nat, _longer: nat) {
        }

        #[verifier::prophetic]
        open spec fn same_destination(&self, _other: &Self) -> bool {
            true
        }

        proof fn lemma_same_destination_reflexive(&self) {
        }

        proof fn lemma_same_destination_transitive(&self, _middle: &Self, _last: &Self) {
        }

        fn write_byte(&mut self, byte: u8) {
            self.obuf.push(byte);
        }

        fn write_bytes(&mut self, bytes: &[u8]) {
            extend_vec_u8(&mut self.obuf, bytes);
        }
    }

    impl<Len: AsLen> Serializer<SecretOutputBuf, SecretBuf<'_>> for Varied<Len> {
        fn serialize_into(&self, v: &SecretBuf<'_>, obuf: &mut SecretOutputBuf) {
            obuf.write_secret(v);
        }
    }

    impl Serializer<SecretOutputBuf, SecretBuf<'_>> for Tail {
        fn serialize_into(&self, v: &SecretBuf<'_>, obuf: &mut SecretOutputBuf) {
            obuf.write_secret(v);
        }
    }

    impl<Len: AsLen> Prepare<SecretBuf<'_>> for Varied<Len> {
        fn prepare(&self, v: &SecretBuf<'_>) -> (checked: Result<usize, PreSerializeError>) {
            if v.len() == self.0.get() {
                Ok(v.len())
            } else {
                Err(PreSerializeError::not_compliant(ComplianceErrorKind::LengthInconsistent))
            }
        }
    }

    impl Prepare<SecretBuf<'_>> for Tail {
        fn prepare(&self, v: &SecretBuf<'_>) -> (checked: Result<usize, PreSerializeError>) {
            Ok(v.len())
        }
    }


    }



    verus!{

    // By convention, we include the nonce at the start of the ciphertext. (TODO check wrt wire formats)

    #[verifier(external_body)]
    pub exec fn owl_enc(k: SecretBuf<'_>, msg: SecretBuf<'_>, iv: SecretBuf<'_>) -> (ctxt: Vec<u8>)
        ensures
            ctxt.view() == enc(k.view(), msg.view(), iv.view())
    {
        let k = k.private_as_slice();
        let msg = msg.private_as_slice();
        let iv = iv.private_as_slice();
        match owl_aead::encrypt_combined(CIPHER, k, msg, iv, &[]) {
            Ok(mut c) => {
                let mut v = iv.to_owned();
                v.append(&mut c);
                v
            },
            Err(_e) => {
                // dbg!(e);
                vec![]
            }
        }
    }

    #[verifier(external_body)]
    pub exec fn owl_dec<'a>(k: SecretBuf<'_>, c: OwlBuf<'a>, Tracked(t): Tracked<DeclassifyingOpToken>) -> (x: Option<SecretBuf<'a>>)
        requires
            t.view() matches DeclassifyingOp::ADec(k_spec, c_spec) && k@ == k_spec && c@ == c_spec
        ensures
            view_option(x) == dec(k.view(), c.view()),
            x matches Some(b) ==> b.len_valid()
    {
        let k = k.private_as_slice();
        let c = c.as_slice();
        match owl_aead::decrypt_combined(CIPHER, k, &c[NONCE_SIZE..], &c[..NONCE_SIZE], &[]) {
            Ok(p) => Some(OwlBuf::from_vec(p).into_secret()),
            Err(_e) => {
                // dbg!(e);
                None
            }
        }
    }

    #[verifier(external_body)]
    pub exec fn owl_sign(privkey: SecretBuf, msg: OwlBuf) -> (signature: Vec<u8>)
        ensures signature.view() == sign(privkey.view(), msg.view())
    {
        let privkey = privkey.private_as_slice();
        let msg = msg.as_slice();
        owl_pke::sign(privkey, msg)
    }

    #[verifier(external_body)]
    pub exec fn owl_vrfy<'a>(pubkey: OwlBuf<'_>, msg: SecretBuf<'a>, signature: OwlBuf<'_>, Tracked(t): Tracked<DeclassifyingOpToken>) -> (x: Option<SecretBuf<'a>>)
        requires
            t.view() matches DeclassifyingOp::SigVrfy(pubkey_spec, msg_spec, signature_spec) 
            && pubkey@ == pubkey_spec && msg@ == msg_spec && signature@ == signature_spec
        ensures 
            view_option(x) == vrfy(pubkey.view(), msg.view(), signature.view())
    {
        let pubkey_slice = pubkey.as_slice();
        let msg_slice = msg.private_as_slice();
        let signature_slice = signature.as_slice();
        if owl_pke::verify(pubkey_slice, signature_slice, msg_slice) {
            Some(msg.another_ref())
        } else {
            None
        }
    }

    #[verifier(external_body)]
    pub exec fn owl_dhpk(privkey: SecretBuf) -> (pubkey: Vec<u8>)
        ensures pubkey.view() == dhpk(privkey.view())
    {
        owl_dhke::ecdh_dhpk(privkey.private_as_slice())
    }


    #[verifier(external_body)]
    pub exec fn owl_dh_combine<'a>(pubkey: SecretBuf, privkey: SecretBuf) -> (ss: SecretBuf<'a>)
        ensures
            ss.view() == dh_combine(pubkey.view(), privkey.view())
    {
        let ss = owl_dhke::ecdh_combine(privkey.private_as_slice(), pubkey.private_as_slice());
        OwlBuf::from_vec(ss).into_secret()
    }

    #[verifier(external_body)]
    pub exec fn owl_extract_expand_to_len<'a>(len: usize, salt: SecretBuf, ikm: SecretBuf, info: OwlBuf) -> (h: SecretBuf<'a>) 
        ensures h.view() == kdf(len.view(), salt.view(), ikm.view(), info.view()),
                h.view().len() == len
    {
        let h = owl_hkdf::extract_expand_to_len(ikm.private_as_slice(), salt.private_as_slice(), info.as_slice(), len);
        OwlBuf::from_vec(h).into_secret()
    }

    #[verifier(external_body)]
    pub exec fn owl_mac(mackey: SecretBuf, msg: OwlBuf) -> (mac_val: Vec<u8>)
        ensures mac_val.view() == mac(mackey.view(), msg.view())
    {
        owl_hmac::hmac(HMAC_MODE, mackey.private_as_slice(), msg.as_slice(), None)
    }

    #[verifier(external_body)]
    pub exec fn owl_mac_vrfy<'a>(mackey: SecretBuf<'_>, msg: SecretBuf<'a>, mac: OwlBuf<'_>, Tracked(t): Tracked<DeclassifyingOpToken>) -> (x: Option<SecretBuf<'a>>)
        requires
            t.view() matches DeclassifyingOp::MacVrfy(mackey_spec, msg_spec, mac_spec)
            && mackey@ == mackey_spec && msg@ == msg_spec && mac@ == mac_spec
        ensures 
            view_option(x) == mac_vrfy(mackey.view(), msg.view(), mac.view())
    {
        if owl_hmac::verify(HMAC_MODE, mackey.private_as_slice(), msg.private_as_slice(), mac.as_slice(), None) {
            Some(msg.another_ref())
        } else {
            None
        }
    }

    #[verifier(external_body)]
    pub exec fn owl_pkenc(pubkey: OwlBuf<'_>, msg: SecretBuf<'_>) -> (ctxt: Vec<u8>)
        ensures ctxt.view() == pkenc(pubkey.view(), msg.view())
    {
        owl_pke::encrypt(pubkey.as_slice(), msg.private_as_slice())
    }

    #[verifier(external_body)]
    pub exec fn owl_pkdec<'a>(privkey: SecretBuf<'_>, ctxt: OwlBuf<'_>, Tracked(t): Tracked<DeclassifyingOpToken>) -> (msg: Option<SecretBuf<'a>>)
        requires
            t.view() matches DeclassifyingOp::PkDec(privkey_spec, ctxt_spec) 
            && privkey@ == privkey_spec && ctxt@ == ctxt_spec
        ensures 
            view_option(msg) == pkdec(privkey.view(), ctxt.view())
    {
        let p = owl_pke::decrypt(privkey.private_as_slice(), ctxt.as_slice())?;
        Some(OwlBuf::from_vec(p).into_secret())
    }


    // Builder for stateful AEAD encryption
    pub struct OwlStAEADBuilder<'a> {
        pub k: SecretBuf<'a>,
        pub msg: SecretBuf<'a>,
        pub iv: SecretBuf<'a>,
        pub aad: SecretBuf<'a>,
    }

    impl<'a> OwlStAEADBuilder<'a> {
        pub fn into_fresh_vec(&self) -> (res: Vec<u8>)
            ensures
                res@ == self.value(),
        {
            let mut res = vec_u8_of_len(self.length());
            self.into_mut_vec(&mut res, 0);
            assert(res@.subrange(0, 0).add(self.value()).add(
                res@.subrange(0 + self.value().len() as int, self.value().len() as int),
            ) == res@);
            assert(res@.subrange(0, 0).add(self.value()).add(
                res@.subrange(0 + self.value().len() as int, self.value().len() as int),
            ) == self.value());
            res
        }
    }


    // (Vest 1.0 had a `Builder` trait for these methods; Vest 2.0 does not)
    impl<'a> OwlStAEADBuilder<'a> {
        pub open spec fn value(&self) -> Seq<u8> {
            enc_st_aead(self.k.view(), self.msg.view(), self.iv.view(), self.aad.view())
        }

        #[verifier::external_body]
        pub fn length(&self) -> (res: usize)
            ensures res == self.value().len()
        {
            self.msg.len() + TAG_SIZE
        }

        #[verifier::external_body]
        pub fn into_mut_vec(&self, data: &mut Vec<u8>, pos: usize)
            requires pos + self.value().len() <= old(data)@.len(),
            ensures final(data)@ == old(data)@.subrange(0, pos as int).add(self.value()).add(
                old(data)@.subrange(pos + self.value().len() as int, old(data)@.len() as int)),
        {
            let mut iv_sized = self.iv.private_as_slice().to_vec();
            iv_sized.resize(NONCE_SIZE, 0u8);
            match owl_aead::encrypt_combined_into(
                CIPHER, 
                self.k.private_as_slice(), 
                self.msg.private_as_slice(), 
                &iv_sized[..], 
                self.aad.private_as_slice(), 
                data, 
                pos,
            ) {
                Ok(()) => (),
                Err(_e) => {
                    // dbg!(e);
                    ()
                }
            };
        }
    }

    impl View for OwlStAEADBuilder<'_> {
        type V = Seq<u8>;

        open spec fn view(&self) -> Self::V {
            self.value()
        }
    }

    #[verifier(external_body)]
    pub exec fn owl_enc_st_aead_builder<'a>(k: SecretBuf<'a>, msg: SecretBuf<'a>, iv: SecretBuf<'a>, aad: SecretBuf<'a>) -> (res: OwlStAEADBuilder<'a>)
        ensures  
            res.view() == enc_st_aead(k.view(), msg.view(), iv.view(), aad.view()),
    {
        OwlStAEADBuilder { k, msg, iv, aad }
    }


    #[verifier(external_body)]
    pub exec fn owl_enc_st_aead(k: SecretBuf<'_>, msg: SecretBuf<'_>, iv: SecretBuf<'_>, aad: SecretBuf<'_>) -> (res: Vec<u8>)
        ensures
            res.view() == enc_st_aead(k.view(), msg.view(), iv.view(), aad.view()),
    {
        let mut iv_sized = iv.private_as_slice().to_vec();
        iv_sized.resize(NONCE_SIZE, 0u8);
        let res = match owl_aead::encrypt_combined(CIPHER, k.private_as_slice(), msg.private_as_slice(), &iv_sized[..], aad.private_as_slice()) {
            Ok(c) => c,
            Err(_e) => {
                // dbg!(e);
                vec![]
            }
        };
        res
    }

    #[verifier(external_body)]
    pub exec fn owl_dec_st_aead<'a>(k: SecretBuf<'_>, c: OwlBuf<'a>, nonce: SecretBuf<'_>, aad: SecretBuf<'_>, Tracked(t): Tracked<DeclassifyingOpToken>) -> (x: Option<SecretBuf<'a>>)
        requires
            t.view() matches DeclassifyingOp::StAeadDec(k_spec, c_spec, nonce_spec, aad_spec) 
            && k@ == k_spec && c@ == c_spec && nonce@ == nonce_spec && aad@ == aad_spec
        ensures
            view_option(x) == dec_st_aead(k.view(), c.view(), nonce.view(), aad.view())
    {
        match owl_aead::decrypt_combined(CIPHER, k.private_as_slice(), c.as_slice(), nonce.private_as_slice(), aad.private_as_slice()) {
            Ok(p) => Some(OwlBuf::from_vec(p).into_secret()),
            Err(_e) => {
                // dbg!(e);
                None
            }
        }
    }

    // KEM encapsulation, deterministic in the public key and the coins (sampled by the
    // caller through the sampling effect). The public key is a raw Kyber1024 key; None if
    // it has the wrong length (see owl_kem.rs).
    #[verifier(external_body)]
    pub exec fn owl_kem_encaps<'a>(pk: OwlBuf<'_>, coins: SecretBuf<'_>) -> (res: Option<(SecretBuf<'a>, Vec<u8>)>)
        ensures
            res matches Some(r) ==> r.0.view() == kem_encaps_ss(pk.view(), coins.view())
                                    && r.1.view() == kem_encaps_ct(pk.view(), coins.view()),
    {
        let (ss, ct) = owl_kem::encapsulate_kyber1024_raw(pk.as_slice(), coins.private_as_slice())?;
        Some((OwlBuf::from_vec(ss).into_secret(), ct))
    }

    // KEM decapsulation. It is not a declassifying operation: ML-KEM (and Kyber) use
    // implicit rejection, so the result is None only when the lengths or key types of the
    // key and the ciphertext are wrong, which is public; otherwise it is a (pseudorandom)
    // shared secret.
    #[verifier(external_body)]
    pub exec fn owl_kem_decaps<'a>(sk: SecretBuf<'_>, ct: OwlBuf<'_>) -> (ss: Option<SecretBuf<'a>>)
        ensures
            view_option(ss) == kem_decaps(sk.view(), ct.view()),
    {
        let ss = owl_kem::decapsulate(sk.private_as_slice(), ct.as_slice())?;
        Some(OwlBuf::from_vec(ss).into_secret())
    }

    // The raw public key of a Kyber1024 secret key (empty if the secret key is malformed or
    // of another key type)
    #[verifier(external_body)]
    pub exec fn owl_kem_pk(sk: SecretBuf) -> (pk: Vec<u8>)
        ensures pk.view() == kem_pk(sk.view())
    {
        owl_kem::kyber1024_raw_public_key_of(sk.private_as_slice()).unwrap_or(vec![])
    }

    #[verifier(external_body)]
    pub exec fn owl_is_group_elem(x: SecretBuf) -> (b: bool)
        ensures b == is_group_elem(x.view())
    {
        x.len() == 32
    }

    #[verifier(external_body)]
    pub exec fn owl_secret_crh<'a>(x: SecretBuf) -> (res: SecretBuf<'a>)
        ensures res.view() == crh(x.view())
    {
        let h = owl_hmac::blake2s(x.private_as_slice());
        OwlBuf::from_vec(h).into_secret()
    }

    #[verifier(external_body)]
    pub exec fn owl_bytes_as_counter(x: &[u8]) -> (res: usize)
        ensures res == bytes_as_counter(x.view())
    {
        todo!("implement bytes_as_counter")
    }

    #[verifier(external_body)]
    pub exec fn owl_counter_as_bytes<'a>(x: &usize) -> (res: [u8; 8])
        ensures res.view() == counter_as_bytes(x.view())
    {
        let v = x.to_le_bytes();
        v
    }

    #[verifier(external_body)]
    pub exec fn owl_xor(a: &[u8], b: &[u8]) -> (res: Vec<u8>)
        ensures res.view() == xor(a.view(), b.view())
    {
        let mut res = vec_u8_of_len(a.len());
        for i in 0..a.len() {
            res.set(i, a[i] ^ b[i]);
        }
        res
    }

    #[verifier(external_body)]
    pub exec fn owl_secret_xor<'a>(a: SecretBuf<'a>, b: SecretBuf<'_>) -> (res: SecretBuf<'a>)
        ensures res.view() == xor(a.view(), b.view())
    {
        let v = owl_xor(a.private_as_slice(), b.private_as_slice());
        SecretBuf::from_buf(OwlBuf::from_vec(v))
    }

    } // verus!

} // mod secret

pub use crate::execlib::secret::*;
pub use crate::*;