use vstd::prelude::*;

use super::*;
use crate::owl::Data;

verus! {

broadcast use crate::owl::axioms, combinator_props;

/// An ordinary pair, redefined to avoid trait impl issues
pub struct Pair<A, B>(pub A, pub B);

// TODO: switch to this when Verus supports function pointers
/// A pair of spec (A::V -> B::V) and exec functions (A -> B) verified to be equivalent
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(B)]
pub struct SpecExecFn<A: View, B: View, F: Fn(&A) -> B> {
    spec_f: Ghost<spec_fn(A::V) -> B::V>,
    f: F,
}

impl<A: View, B: View, F: Fn(&A) -> B> SpecExecFn<A, B, F> {
    /// The type invariant of an `SpecExecFn` says that
    /// ensure clause of `f` must ensure that the result is
    /// equal to the result of `spec_f`,
    /// And the requires clause should be trivial.
    #[verifier::type_invariant]
    pub open spec fn wf(&self) -> bool {
        &&& forall |x: A| #[trigger] self.requires(&x)
        &&& forall |x: A, y: B| #[trigger] self.ensures(&x, y)
                        ==> self.spec_call(x@) == y@
    }

    pub closed spec fn requires(&self, x: &A) -> bool {
        self.f.requires((x,))
    }

    pub closed spec fn ensures(&self, x: &A, y: B) -> bool {
        self.f.ensures((x,), y)
    }

    pub closed spec fn spec_call(&self, x: A::V) -> B::V {
        (self.spec_f@)(x)
    }

    pub fn call(&self, x: &A) -> (y: B)
        requires self.requires(x)
        ensures self.ensures(x, y) && self.spec_call(x@) == y@
    {
        let y = (self.f)(x);
        proof {
            use_type_invariant(self);
            assert(self.ensures(x, y));
        }
        y
    }

    /// Constructs a new `SpecExecFn`
    pub fn new(spec_f: Ghost<spec_fn(A::V) -> B::V>, f: F) -> Self
        requires
            forall |x: A| f.requires((&x,)),
            forall |x: A, y: B| f.ensures((&x,), y)
                    ==> spec_f@(x@) == y@,
    {
        Self { spec_f, f }
    }
}

/// `SpecCombinator` impl for a dependent pair
impl<A: SpecCombinator + PrefixSecure, B: SpecCombinator> SpecCombinator for Pair<A, spec_fn(A::Type) -> B> {
    type Type = (A::Type, B::Type);

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(usize, Self::Type)> {
        if let Some((n, a)) = self.0.spec_parse(s) {
            if let Some((m, b)) = (self.1)(a).spec_parse(s.skip(n as int)) {
                if n + m <= usize::MAX {
                    Some(((n + m) as usize, (a, b)))
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Option<Seq<u8>> {
        if let Some(s1) = self.0.spec_serialize(v.0) {
            if let Some(s2) = (self.1)(v.0).spec_serialize(v.1) {
                if s1.len() + s2.len() <= usize::MAX {
                    Some(s1 + s2)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    open spec fn spec_input_security_policy(&self, s: &Data) -> bool {
        &&& self.0.spec_input_security_policy(s)
        &&& self.0.spec_parse(s@) matches Some((n, a))
                ==> self.1(a).spec_input_security_policy(&s.skip(n))
    }

    proof fn prop_parse_length(&self, s: Seq<u8>) {}

    proof fn prop_serialize_parse_roundtrip(&self, v: Self::Type) {
        if let Some(s1) = self.0.spec_serialize(v.0) {
            if let Some(s2) = (self.1)(v.0).spec_serialize(v.1) {
                if s1.len() + s2.len() <= usize::MAX {
                    assert((s1 + s2).skip(s1.len() as int) == s2);
                }
            }
        }
    }

    proof fn prop_parse_serialize_roundtrip(&self, s: Seq<u8>) {}

    proof fn prop_input_security_policy_indiscern(&self, s1: &Data, s2: &Data) {
        if let Some((n1, a1)) = self.0.spec_parse(s1@) {
            if let Some((n2, a2)) = self.0.spec_parse(s2@) {
                assert(s1.skip(n1).eq(&s2.skip(n2)));
            }
        }
    }
}

/// View for an exec dependent pair
impl<A: Combinator, B: Combinator, F: Fn(&A::Type) -> B> View for Pair<A, SpecExecFn<A::Type, B, F>> where
    A::V: SpecCombinator + PrefixSecure,
    B::V: SpecCombinator,
{
    type V = Pair<A::V, spec_fn(<A::V as SpecCombinator>::Type) -> B::V>;

    closed spec fn view(&self) -> Self::V {
        Pair(self.0@, self.1.spec_f@)
    }
}

/// Exec `Combinator` impl for a dependent pair
impl<A: Combinator, B: Combinator, F: Fn(&A::Type) -> B> Combinator for Pair<A, SpecExecFn<A::Type, B, F>> where
    A::V: SpecCombinator + PrefixSecure,
    B::V: SpecCombinator,
{
    type Type = (A::Type, B::Type);

    open spec fn parse_requires(&self) -> bool {
        &&& self.0.parse_requires()
        &&& forall |x, y| self.1.ensures(x, y) ==> y.parse_requires()
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& self.0.serialize_requires()
        &&& forall |x, y| self.1.ensures(x, y) ==> y.serialize_requires()
    }

    open spec fn spec_output_security_policy(&self, v: &Self::Type) -> bool {
        &&& self.0.spec_output_security_policy(&v.0)

        // This (together with `prop_policy_consistency`) is
        // a bit of hack to "call" an exec function `self.1` in spec mode
        &&& forall |c: B| c@ == self.1.spec_call(v.0@) ==> #[trigger] c.spec_output_security_policy(&v.1)
    }

    proof fn prop_policy_consistency(&self, other: &Self, v: &Self::Type) {}

    fn parse(&self, s: &Data) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (n, a) = self.0.parse(s)?;

        proof {
            self.0@.prop_parse_length(s@);
            use_type_invariant(&self.1);
        }

        let snd_comb = self.1.call(&a);
        let (m, b) = snd_comb.parse(&s.subrange(n, s.len()))?;

        if m > usize::MAX - n {
            return Err(ParseError::Invalid);
        }

        Ok((n + m, (a, b)))
    }

    fn serialize(&self, v: &Self::Type, buf: &mut Data) -> (res: Result<usize, SerializeError>) {
        let ghost old_len = buf@.len() as usize;
        let n = self.0.serialize(&v.0, buf)?;
        let ghost buf0 = buf.skip(old_len);

        proof {
            use_type_invariant(&self.1);
        }

        let m = self.1.call(&v.0).serialize(&v.1, buf)?;

        if m > usize::MAX - n {
            return Err(SerializeError::Invalid);
        }

        // TODO: automate some of these equality reasoning better
        proof {
            assert(buf.skip(old_len)@ =~= buf0.concat(&buf.skip((old_len + n) as usize))@);

            // First part of self@.spec_input_security_policy
            assert(buf.skip(old_len).take(n).eq(&buf0));
            assert(self.0@.spec_input_security_policy(&buf.skip(old_len).take(n)));
            assert(self.0@.spec_input_security_policy(&buf.skip(old_len)));

            assert(self.0@.spec_parse(buf.skip(old_len)@) is Some);
            let (n2, v0) = self.0@.spec_parse(buf.skip(old_len)@).unwrap();
            assert(n2 == n);
            assert(v0 == v.0@);

            // Second part of self@.spec_input_security_policy
            assert(buf.skip(old_len).skip(n2).eq(&buf.skip((old_len + n2) as usize)));
            assert(self.1.spec_call(v0).spec_input_security_policy(&buf.skip(old_len).skip(n2)));
        }

        Ok(n + m)
    }
}

}
