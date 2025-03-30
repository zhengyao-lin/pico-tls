use vstd::prelude::*;

use super::*;
use crate::owl::Data;

verus! {

broadcast use crate::owl::axioms;

/// An ordinary pair, redefined to avoid trait impl issues
pub struct Pair<A, B>(pub A, pub B);

// /// A pair of spec (A::V -> B::V) and exec functions (A -> B) verified to be equivalent
// pub trait SpecExecFn {
//     type A: View;
//     type B: View;

//     spec fn spec_call(a: <Self::A as View>::V) -> <Self::B as View>::V;

//     spec fn requires(a: Self::A) -> bool;
//     spec fn ensures(a: Self::A, b: Self::B) -> bool;
//     fn call(a: Self::A) -> (b: Self::B)
//         requires Self::requires(a)
//         ensures Self::ensures(a, b);

//     /// The ensures clause of `call` must ensure that the result is
//     /// equal to the result of `spec_call`,
//     /// and the requires clause should be trivial.
//     proof fn prop_call()
//         ensures
//             forall |x: Self::A| #[trigger] Self::requires(x),
//             forall |x: Self::A, y: Self::B| #[trigger] Self::ensures(x, y)
//                 ==> Self::spec_call(x@) == y@;
// }

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

// fn test() {
//     let ghost g = |x: u32| x;
//     let f = SpecExecFn::new(
//         Ghost(g),
//         |x: u32| -> (r: u32)
//             ensures r == g(x@)
//         { x }
//     );
// }

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

    proof fn prop_parse_length(&self, s: Seq<u8>) {
        if let Some((n, a)) = self.0.spec_parse(s) {
            self.0.prop_parse_length(s);
            (self.1)(a).prop_parse_length(s.skip(n as int));
        }
    }

    proof fn prop_serialize_parse_roundtrip(&self, v: Self::Type) {
        if let Some(s1) = self.0.spec_serialize(v.0) {
            if let Some(s2) = (self.1)(v.0).spec_serialize(v.1) {
                if s1.len() + s2.len() <= usize::MAX {
                    self.0.prop_serialize_parse_roundtrip(v.0);
                    self.0.prop_prefix_secure(s1, s2);
                    (self.1)(v.0).prop_serialize_parse_roundtrip(v.1);
                    assert((s1 + s2).skip(s1.len() as int) == s2);
                }
            }
        }
    }

    proof fn prop_parse_serialize_roundtrip(&self, s: Seq<u8>) {
        if let Some((n, a)) = self.0.spec_parse(s) {
            if let Some((m, b)) = (self.1)(a).spec_parse(s.skip(n as int)) {
                if n + m <= usize::MAX {
                    self.0.prop_parse_serialize_roundtrip(s);
                    self.0.prop_parse_length(s);
                    (self.1)(a).prop_parse_serialize_roundtrip(s.skip(n as int));
                    (self.1)(a).prop_parse_length(s.skip(n as int));
                    // assert(s.take(n as int) + s.skip(n as int).take(m as int) =~= s.take(n + m));
                }
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
        // // Continuation's parsing requirements should always be satisfied
        // &&& self.0@.spec_parse(s@) matches Some((n, a))
        //         ==> forall |x, y| #[trigger] self.1.ensures(x, y) && x@ == a
        //             ==> y.parse_requires(&s.skip(n))
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& self.0.serialize_requires()
        &&& forall |x, y| self.1.ensures(x, y) ==> y.serialize_requires()
        // &&& forall |y| #[trigger] self.1.ensures(&v.0, y)
        //         ==> y.serialize_requires(&v.1)
    }

    open spec fn spec_output_security_policy(&self, v: &Self::Type) -> bool {
        &&& self.0.spec_output_security_policy(&v.0)

        // TODO
        // &&& self.1(v.0).spec_output_security_policy(&v.1)
    }

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
        assume(false);
        Err(SerializeError::Invalid)
    }
}

}
