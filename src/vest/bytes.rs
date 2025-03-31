use vstd::prelude::*;

use super::*;
use crate::owl::{Data, SecPred};

verus! {

broadcast use crate::owl::axioms;

// TODO: Verus panic
// broadcast use Data::axioms;

/// Bytes { len, pred } parses exactly `len` bytes
/// with requirements that the bytes satisfy the security policy `pred`.
pub struct Bytes {
    /// Number of bytes to read
    pub len: usize,

    /// Ghost predicate on the label and types of the bytes being parsed
    pub pred: Ghost<SecPred>,
}

impl View for Bytes {
    type V = Bytes;

    open spec fn view(&self) -> Bytes {
        *self
    }
}

impl SpecCombinator for Bytes {
    type Type = Seq<u8>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(usize, Self::Type)> {
        if s.len() < self.len {
            None
        } else {
            Some((self.len, s.take(self.len as int)))
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Option<Seq<u8>> {
        if v.len() != self.len {
            None
        } else {
            Some(v)
        }
    }

    open spec fn spec_input_security_policy(&self, s: &Data) -> bool {
        s@.len() >= self.len ==> self.pred@(s.subrange(0, self.len))
    }

    open spec fn spec_input_security_policy_corrupt(&self, s: &Data) -> bool {
        s@.len() >= self.len ==> s.subrange(0, self.len).is_public()
    }

    proof fn prop_parse_length(&self, s: Seq<u8>) {}
    proof fn prop_serialize_parse_roundtrip(&self, v: Self::Type) {}
    proof fn prop_parse_serialize_roundtrip(&self, s: Seq<u8>) {}
    proof fn prop_input_security_policy_indiscern(&self, s1: &Data, s2: &Data) {}
    proof fn prop_input_security_policy_corrupt(&self, s: &Data) {}
}

impl PrefixSecure for Bytes {
    proof fn prop_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
    proof fn prop_prefix_secure_policy_concat(&self, s1: &Data, s2: &Data) {}
    proof fn prop_prefix_secure_policy_subrange(&self, s: &Data, n: usize) {}
}

/// TODO: performance
impl Combinator for Bytes {
    type Type = Data;

    open spec fn spec_output_security_policy(&self, v: &Self::Type) -> bool {
        self.pred@(*v)
    }

    open spec fn spec_output_security_policy_corrupt(&self, v: &Self::Type) -> bool {
        v.is_public()
    }

    proof fn prop_policy_consistency(&self, other: &Self, v: &Self::Type) {}

    fn parse(&self, s: &Data) -> (res: Result<(usize, Self::Type), ParseError>) {
        if s.len() < self.len {
            return Err(ParseError::Invalid);
        }

        Ok((self.len, s.subrange(0, self.len)))
    }

    fn serialize(&self, v: &Self::Type, buf: &mut Data) -> (res: Result<usize, SerializeError>) {
        if v.len() != self.len {
            return Err(SerializeError::Invalid);
        }

        let ghost old_buf = *buf;
        buf.append(v);

        Ok(self.len)
    }
}

}
