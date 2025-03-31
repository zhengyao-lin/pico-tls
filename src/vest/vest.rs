#![allow(dead_code)]

use vstd::prelude::*;
use crate::owl::Data;

verus! {

pub broadcast group combinator_props {
    SpecCombinator::prop_parse_length,
    SpecCombinator::prop_serialize_parse_roundtrip,
    SpecCombinator::prop_parse_serialize_roundtrip,
    SpecCombinator::prop_input_security_policy_indiscern,
    SpecCombinator::prop_input_security_policy_corrupt,
    PrefixSecure::prop_prefix_secure,
    PrefixSecure::prop_prefix_secure_policy_concat,
    PrefixSecure::prop_prefix_secure_policy_subrange,
    Combinator::prop_policy_consistency,
}

/// Specification and core properties of a (spec) combinator
pub trait SpecCombinator {
    type Type;

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(usize, Self::Type)>;
    spec fn spec_serialize(&self, v: Self::Type) -> Option<Seq<u8>>;

    /// Security policy on the input being parsed
    spec fn spec_input_security_policy(&self, s: &Data) -> bool;
    spec fn spec_input_security_policy_corrupt(&self, s: &Data) -> bool;

    broadcast proof fn prop_parse_length(&self, s: Seq<u8>)
        ensures
            (#[trigger] self.spec_parse(s)) matches Some((n, _)) ==> n <= s.len();

    broadcast proof fn prop_serialize_parse_roundtrip(&self, v: Self::Type)
        ensures
            (#[trigger] self.spec_serialize(v)) matches Some(b) ==>
                self.spec_parse(b) =~= Some((b.len() as usize, v));

    broadcast proof fn prop_parse_serialize_roundtrip(&self, s: Seq<u8>)
        ensures
            (#[trigger] self.spec_parse(s)) matches Some((n, v)) ==>
                self.spec_serialize(v) =~= Some(s.take(n as int));

    /// The security policy should not distinguish "equal" Data
    broadcast proof fn prop_input_security_policy_indiscern(&self, s1: &Data, s2: &Data)
        requires s1.eq(s2)
        ensures
            #![trigger s1.eq(s2), self.spec_input_security_policy(s1)]
            #![trigger s1.eq(s2), self.spec_input_security_policy_corrupt(s1)]
            self.spec_input_security_policy(s1)
            == self.spec_input_security_policy(s2),
            self.spec_input_security_policy_corrupt(s1)
            == self.spec_input_security_policy_corrupt(s2);

    /// A property that the corrupt policy can be weakened to public
    broadcast proof fn prop_input_security_policy_corrupt(&self, s: &Data)
        ensures s.is_public() ==> #[trigger] self.spec_input_security_policy_corrupt(s);
}

pub trait PrefixSecure: SpecCombinator {
    broadcast proof fn prop_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
        requires s1.len() + s2.len() <= usize::MAX,
        ensures self.spec_parse(s1) is Some ==>
            #[trigger] self.spec_parse(s1 + s2) =~= self.spec_parse(s1);

    /// The security policy is "prefix secure" if it does not "talk about"
    /// the data that is not being parsed
    broadcast proof fn prop_prefix_secure_policy_concat(&self, s1: &Data, s2: &Data)
        requires s1@.len() + s2@.len() <= usize::MAX,
        ensures
            #![trigger self.spec_input_security_policy(s1), s1.concat(s2)]
            #![trigger self.spec_input_security_policy_corrupt(s1), s1.concat(s2)]

            self.spec_parse(s1@) is Some ==>
                self.spec_input_security_policy(s1)
                == self.spec_input_security_policy(&s1.concat(s2)),

            self.spec_parse(s1@) is Some ==>
                #[trigger] self.spec_input_security_policy_corrupt(s1)
                == self.spec_input_security_policy_corrupt(#[trigger] &s1.concat(s2)),;

    /// Similar to `prop_prefix_secure_policy_concat` but for subrange
    /// TODO: unify these two?
    broadcast proof fn prop_prefix_secure_policy_subrange(&self, s: &Data, n: usize)
        requires n <= s@.len()
        ensures
            #![trigger self.spec_input_security_policy(s), s.subrange(0, n)]
            #![trigger self.spec_input_security_policy_corrupt(s), s.subrange(0, n)]

            self.spec_parse(s@.subrange(0, n as int)) is Some ==>
                self.spec_input_security_policy(s)
                == self.spec_input_security_policy(&s.subrange(0, n)),

            self.spec_parse(s@.subrange(0, n as int)) is Some ==>
                self.spec_input_security_policy_corrupt(s)
                == self.spec_input_security_policy_corrupt(&s.subrange(0, n));
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

    /// Same but for the corrupt/public case
    spec fn spec_output_security_policy_corrupt(&self, v: &Self::Type) -> bool;

    /// A technical condition to make sure that combinators with equal spec
    /// has the same security policy on the output type
    broadcast proof fn prop_policy_consistency(&self, other: &Self, v: &Self::Type)
        requires self@ == other@
        ensures
            #![trigger self.spec_output_security_policy(v), other.spec_output_security_policy(v)]
            #![trigger self.spec_output_security_policy_corrupt(v), other.spec_output_security_policy_corrupt(v)]
            self.spec_output_security_policy(v) == other.spec_output_security_policy(v),
            self.spec_output_security_policy_corrupt(v) == other.spec_output_security_policy_corrupt(v);

    open spec fn parse_requires(&self) -> bool {
        true
    }

    open spec fn serialize_requires(&self) -> bool {
        true
    }

    fn parse(&self, s: &Data) -> (res: Result<(usize, Self::Type), ParseError>)
        requires
            self.parse_requires(),
            self@.spec_input_security_policy(s) || self@.spec_input_security_policy_corrupt(s),

        ensures
            res matches Ok((n, v)) ==> {
                &&& self@.spec_parse(s@) =~~= Some((n, v@))

                &&& self@.spec_input_security_policy(s) ==> self.spec_output_security_policy(&v)
                &&& self@.spec_input_security_policy_corrupt(s) ==> self.spec_output_security_policy_corrupt(&v)
            },
            res is Err ==> self@.spec_parse(s@) is None,
    ;

    fn serialize(&self, v: &Self::Type, buf: &mut Data) -> (res: Result<usize, SerializeError>)
        requires
            self.serialize_requires(),
            self.spec_output_security_policy(v) || self.spec_output_security_policy_corrupt(v),

        ensures
            res matches Ok(n) ==> {
                let old_len = old(buf)@.len() as usize;

                &&& self@.spec_serialize(v@) matches Some(buf2)

                // i.e. buf == old(buf).concat(Data(buf2)
                &&& buf2.len() == n
                &&& buf@.len() == old_len + n
                &&& buf.take(old_len).eq(old(buf))
                &&& buf.skip(old_len)@ =~= buf2

                &&& self.spec_output_security_policy(v) ==> self@.spec_input_security_policy(&buf.skip(old_len))
                &&& self.spec_output_security_policy_corrupt(v) ==> self@.spec_input_security_policy_corrupt(&buf.skip(old_len))
            },
            res is Err ==> self@.spec_serialize(v@) is None,
    ;
}

}
