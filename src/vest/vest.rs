#![allow(dead_code)]

use vstd::prelude::*;
use crate::owl::Data;

verus! {

/// Specification and core properties of a (spec) combinator
pub trait SpecCombinator {
    type Type;

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(usize, Self::Type)>;
    spec fn spec_serialize(&self, v: Self::Type) -> Option<Seq<u8>>;

    /// Security policy on the input being parsed
    spec fn spec_input_security_policy(&self, s: &Data) -> bool;

    proof fn prop_parse_length(&self, s: Seq<u8>)
        ensures
            self.spec_parse(s) matches Some((n, _)) ==> n <= s.len();

    proof fn prop_serialize_parse_roundtrip(&self, v: Self::Type)
        ensures
            self.spec_serialize(v) matches Some(b) ==>
                self.spec_parse(b) =~= Some((b.len() as usize, v));

    proof fn prop_parse_serialize_roundtrip(&self, s: Seq<u8>)
        ensures
            self.spec_parse(s) matches Some((n, v)) ==>
                self.spec_serialize(v) =~= Some(s.take(n as int));
}

pub trait PrefixSecure: SpecCombinator {
    proof fn prop_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
        requires s1.len() + s2.len() <= usize::MAX,
        ensures self.spec_parse(s1) is Some ==>
            self.spec_parse(s1 + s2) =~= self.spec_parse(s1);
}

pub enum ParseError {
    Invalid,
}

pub enum SerializeError {
    Invalid,
}

pub trait Combinator: View where
    Self::V: SpecCombinator,
{
    type Type: View<V = <Self::V as SpecCombinator>::Type>;

    /// Security policy on the output type
    spec fn spec_output_security_policy(&self, v: &Self::Type) -> bool;

    open spec fn parse_requires(&self) -> bool {
        true
    }

    open spec fn serialize_requires(&self) -> bool {
        true
    }

    fn parse(&self, s: &Data) -> (res: Result<(usize, Self::Type), ParseError>)
        requires
            self.parse_requires(),
            self@.spec_input_security_policy(s),

        ensures
            res matches Ok((n, v)) ==> {
                &&& self@.spec_parse(s@) =~~= Some((n, v@))
                &&& self.spec_output_security_policy(&v)
            },
            res is Err ==> self@.spec_parse(s@) is None,
    ;

    fn serialize(&self, v: &Self::Type, buf: &mut Data) -> (res: Result<usize, SerializeError>)
        requires
            self.serialize_requires(),
            self.spec_output_security_policy(v),

        ensures
            res matches Ok(n) ==> {
                let old_len = old(buf)@.len() as usize;

                &&& self@.spec_serialize(v@) matches Some(buf2)

                // i.e. buf == old(buf).concat(Data(buf2)
                &&& buf2.len() == n
                &&& buf@.len() == old_len + n
                &&& buf.take(old_len).eq(old(buf))
                &&& buf.skip(old_len)@ =~= buf2

                // &&& self.parse_requires(&buf.skip(old_len))
                &&& self@.spec_input_security_policy(&buf.skip(old_len))
            },
            res is Err ==> self@.spec_serialize(v@) is None,
    ;
}

}
