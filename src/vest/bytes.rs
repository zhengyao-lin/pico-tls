#![allow(dead_code)]

use vstd::prelude::*;

use super::*;
use crate::owl::{Data, SecPred};

verus! {

// TODO: Verus panic
// broadcast use Data::axioms;

/// Bytes { len, pred } parses exactly `len` bytes
/// with requirements that the bytes satisfy the security policy `pred`.
struct Bytes {
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

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(usize, Self::Type)> {
        if s.len() < self.len {
            None
        } else {
            Some((self.len, s.take(self.len as int)))
        }
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Option<Seq<u8>> {
        if v.len() != self.len {
            None
        } else {
            Some(v)
        }
    }

    open spec fn spec_security_policy(&self, s: &Data) -> bool {
        self.pred@(s.subrange(0, self.len))
    }

    proof fn prop_parse_length(&self, s: Seq<u8>) {}
    proof fn prop_serialize_parse_roundtrip(&self, v: Self::Type) {}
    proof fn prop_parse_serialize_roundtrip(&self, s: Seq<u8>) {}
}

/// TODO: performance
impl Combinator for Bytes {
    type Type = Data;

    open spec fn parse_requires(&self) -> bool {
        true
    }

    open spec fn serialize_requires(&self, v: &Self::Type) -> bool {
        self.pred@(*v)
    }

    fn parse(&self, s: &Data) -> (res: Result<(usize, Self::Type), ParseError>)
        ensures res matches Ok((_, v)) ==> self.pred@(v)
    {
        broadcast use Data::axiom_spec_subrange;

        if s.len() < self.len {
            return Err(ParseError::Invalid);
        }

        Ok((self.len, s.subrange(0, self.len)))
    }

    fn serialize(&self, v: &Self::Type, buf: &mut Data) -> (res: Result<usize, SerializeError>)
    {
        // TODO: use Data::axioms instead but this currently causes Verus panic
        broadcast use
            Data::axiom_spec_concat,
            Data::axiom_spec_subrange,
            Data::axiom_subrange_type,
            Data::axiom_concat_type_left,
            Data::axiom_concat_type_right,
            Data::axiom_subrange_label,
            Data::axiom_concat_label_left,
            Data::axiom_concat_label_right,
            Data::axiom_indiscern,
            Data::axiom_len_bounded,
            Data::lemma_flows_data_trans,
            Data::lemma_flows_data_trans_alt,
            Data::lemma_flows_data_to_public,
            Data::lemma_cover_label;

        if v.len() != self.len {
            return Err(SerializeError::Invalid);
        }

        let ghost old_buf = *buf;
        buf.append(v);

        Ok(self.len)
    }
}

}
