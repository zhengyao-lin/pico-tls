// Based on https://gist.github.com/gancherj/7f80e6d4fd813dc613d8bdee96ffdf5c

use vstd::prelude::*;

verus! {

pub broadcast group label_axioms {
    Label::axiom_flows_refl,
    Label::axiom_flows_trans,
    Label::axiom_flows_zero,
    Label::axiom_public_zero,
    Label::axiom_join_comm,
    Label::axiom_join_public,
    Label::axiom_flows_join,
}

pub broadcast group data_axioms {
    Data::axiom_spec_concat,
    Data::axiom_spec_subrange,
    Data::axiom_subrange_type,
    Data::axiom_concat_type_left,
    Data::axiom_concat_type_right,
    Data::axiom_subrange_label,
    Data::axiom_concat_label_left,
    Data::axiom_concat_label_right,
    // Data::axiom_concat_undefined,
    Data::axiom_indiscern,
    Data::axiom_len_bounded,
    Data::lemma_flows_data_trans,
    Data::lemma_flows_data_trans_alt,
    Data::lemma_flows_data_to_public,
    Data::lemma_cover_label,
    Data::lemma_eq_is_public,
}

pub broadcast group axioms {
    label_axioms,
    data_axioms,
}

#[verifier::external_body]
pub struct Label;

/// Semi-lattice structure of labels with `public` being the zero element
impl Label {
    pub uninterp spec fn public() -> Label;
    pub uninterp spec fn join(self, l: Label) -> Label;
    pub uninterp spec fn flows(self, l: Label) -> bool;

    pub open spec fn is_public(self) -> bool {
        self.flows(Label::public())
    }

    pub open spec fn flows_data(self, data: &Data) -> bool {
        forall |i| 0 <= i < data@.len() ==> self.flows(#[trigger] data.label_at(i))
    }

    #[verifier::external_body]
    pub broadcast proof fn axiom_flows_refl(l: Label)
        ensures #[trigger] l.flows(l);

    #[verifier::external_body]
    pub broadcast proof fn axiom_flows_trans(l1: Label, l2: Label, l3: Label)
        requires #[trigger] l1.flows(l2), #[trigger] l2.flows(l3)
        ensures l1.flows(l3);

    #[verifier::external_body]
    pub broadcast proof fn axiom_flows_zero(l: Label)
        requires #[trigger] l.flows(Label::public())
        ensures l == Label::public();

    #[verifier::external_body]
    pub broadcast proof fn axiom_public_zero(l: Label)
        ensures #[trigger] Label::public().flows(l);

    #[verifier::external_body]
    pub broadcast proof fn axiom_join_comm(l1: Label, l2: Label)
        ensures #[trigger] l1.join(l2) == l2.join(l1);

    #[verifier::external_body]
    pub broadcast proof fn axiom_join_public(l1: Label, l2: Label)
        requires l2.is_public()
        ensures #[trigger] l1.join(l2) == l2;

    #[verifier::external_body]
    pub broadcast proof fn axiom_flows_join(l1: Label, l2: Label, l3: Label)
        requires l1.flows(l2)
        ensures #[trigger] l1.flows(l2.join(l3));
}

pub type SecPred = spec_fn(Data) -> bool;

/// TODO: want to avoid case analysis of types
/// on a piece of unknown Data
pub enum Type {
    ExtractKey(Box<Type>),
    ExpandKey(spec_fn(Seq<u8>) -> Option<Type>),
    EncKey(Label, SecPred),
    Nonce,
    Undefined,
}

pub struct Data(Vec<u8>);

impl View for Data {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Seq<u8> {
        self.0@
    }
}

/// `Data` is similar to `SecretBuf` in OwlC
/// with two basic operations `concat` and `subrange`,
/// but augmented with more structure: `range_type` and `label_at`
///
/// User specification can mark a subrange of data with
/// a specific type (`range_type`), or mark a byte with
/// a specific label (`label_at`).
impl Data {
    /// The subrange `[start, end)` of `self` can be used as `self.range_type(start, end)`
    /// TODO: or change to a relation?
    pub uninterp spec fn range_type(&self, start: usize, end: usize) -> Type;

    /// The byte `self[i]` has label `self.label_at(i)`
    pub uninterp spec fn label_at(&self, i: usize) -> Label;

    /// Concatenates two `Data`s
    #[verifier::when_used_as_spec(spec_concat)]
    #[verifier::external_body]
    pub fn concat(&self, other: &Data) -> (res: Data)
        ensures res == self.spec_concat(other)
    {
        Data(self.0.iter().chain(other.0.iter()).copied().collect())
    }

    pub uninterp spec fn spec_concat(&self, other: &Data) -> Data;

    /// Take the subrange of a `Data`
    #[verifier::when_used_as_spec(spec_subrange)]
    #[verifier::external_body]
    pub fn subrange(&self, start: usize, end: usize) -> (res: Data)
        requires 0 <= start <= end <= self@.len()
        ensures res == self.subrange(start, end)
    {
        Data(self.0[start..end].to_vec())
    }

    pub uninterp spec fn spec_subrange(&self, start: usize, end: usize) -> Data;

    // TODO: length is always public currently
    pub fn len(&self) -> (res: usize)
        ensures res == self@.len()
    {
        self.0.len()
    }
}

/// Axioms about how `range_type`, `label`, `concat`, and `subrange` interact
impl Data {
    /// `subrange` preserves the type of a sub-subrange
    #[verifier::external_body]
    pub broadcast proof fn axiom_subrange_type(&self, start1: usize, end1: usize, start2: usize, end2: usize)
        // [start1, end1) contains [start2 + start1, end2 + start1)
        requires
            0 <= start1 <= end1 <= self@.len(),
            0 <= start2 <= end2 <= end1 - start1,

        // Type of the subrange carries over
        ensures #[trigger] self.subrange(start1, end1).range_type(start2, end2)
            == self.range_type((start2 + start1) as usize, (end2 + start1) as usize);

    /// `concat` preserves the types of both parts (left chunk)
    #[verifier::external_body]
    pub broadcast proof fn axiom_concat_type_left(&self, other: &Data, start: usize, end: usize)
        requires 0 <= start <= end <= self@.len()
        ensures #[trigger] self.concat(other).range_type(start, end) == self.range_type(start, end);

    /// `concat` preserves the types of both parts (right chunk)
    #[verifier::external_body]
    pub broadcast proof fn axiom_concat_type_right(&self, other: &Data, start: usize, end: usize)
        requires self@.len() <= start <= end <= self@.len() + other@.len()
        ensures #[trigger] self.concat(other).range_type(start, end)
                == other.range_type((start - self@.len()) as usize, (end - self@.len()) as usize);

    // /// Types are destroyed across the concat boundary
    // #[verifier::external_body]
    // pub broadcast proof fn axiom_concat_undefined(&self, other: &Data, start: usize, end: usize)
    //     requires 0 <= start < self@.len() < end <= self@.len() + other@.len()
    //     ensures #[trigger] self.concat(other).range_type(start, end) == Type::Undefined;

    /// `subrange` preserves labels
    #[verifier::external_body]
    pub broadcast proof fn axiom_subrange_label(&self, start: usize, end: usize, i: usize)
        requires
            0 <= start <= end <= self@.len(),
            0 <= i < end - start,
        ensures #[trigger] self.subrange(start, end).label_at(i) == self.label_at((i + start) as usize);

    /// `concat` preserves labels (left)
    #[verifier::external_body]
    pub broadcast proof fn axiom_concat_label_left(&self, other: &Data, i: usize)
        requires 0 <= i < self@.len()
        ensures #[trigger] self.concat(other).label_at(i) == self.label_at(i);

    /// `concat` preserves labels (right)
    #[verifier::external_body]
    pub broadcast proof fn axiom_concat_label_right(&self, other: &Data, i: usize)
        requires self@.len() <= i < self@.len() + other@.len()
        ensures #[trigger] self.concat(other).label_at(i) == other.label_at((i - self@.len()) as usize);

    /// Definition of spec_concat
    #[verifier::external_body]
    pub broadcast proof fn axiom_spec_concat(&self, other: &Data)
        ensures (#[trigger] self.concat(other))@ == self@ + other@;

    /// Definition of spec_subrange
    #[verifier::external_body]
    pub broadcast proof fn axiom_spec_subrange(&self, start: usize, end: usize)
        requires 0 <= start <= end <= self@.len()
        ensures (#[trigger] self.subrange(start, end))@ == self@.subrange(start as int, end as int);

    /// TODO: do we need this?
    #[verifier::external_body]
    pub broadcast proof fn axiom_len_bounded(&self)
        ensures #[trigger] self@.len() <= usize::MAX;
}

/// Axioms for declassification
impl Data {
    pub fn index(&self, i: usize) -> (res: u8)
        requires
            0 <= i < self@.len(),
            self.label_at(i).is_public(),
        ensures res == self@[i as int]
    {
        self.0[i]
    }
}

/// Axiom about (spec-level) equality
impl Data {
    /// Two `Data`s are considered equal at the spec level
    /// if they have the same labels, types, and underlying data
    pub open spec fn eq(&self, other: &Data) -> bool {
        &&& self@ =~= other@
        &&& forall |i|
                #![trigger self.label_at(i)]
                #![trigger other.label_at(i)]
                0 <= i < self@.len() ==> self.label_at(i) == other.label_at(i)
        &&& forall |i, j|
                #![trigger self.range_type(i, j)]
                #![trigger other.range_type(i, j)]
                0 <= i <= j < self@.len() ==>
                self.range_type(i, j) == other.range_type(i, j)
    }

    /// Any predicate cannot discern between two equal `Data`s
    /// TODO: maybe too strong? could be made a property of a predicate
    #[verifier::external_body]
    pub broadcast proof fn axiom_indiscern(&self, other: &Data, pred: SecPred)
        requires self.eq(other)
        ensures #[trigger] pred(*self) == #[trigger] pred(*other);
}

/// Some macros
impl Data {
    pub open spec fn typ(&self) -> Type {
        self.range_type(0, self@.len() as usize)
    }

    pub open spec fn cover_label_helper(&self, i: usize) -> Label
        decreases self@.len() - i when self@.len() <= usize::MAX
    {
        if i >= self@.len() {
            Label::public()
        } else {
            self.label_at(i).join(self.cover_label_helper((i + 1) as usize))
        }
    }

    /// Covering label of all bytes
    #[verifier::opaque]
    pub open spec fn cover_label(&self) -> Label {
        self.cover_label_helper(0)
    }

    pub open spec fn flows(&self, label: Label) -> bool {
        forall |i| 0 <= i < self@.len() ==> (#[trigger] self.label_at(i)).flows(label)
    }

    pub open spec fn flows_data(&self, other: &Data) -> bool {
        forall |i, j| 0 <= i < self@.len() && 0 <= j < other@.len() ==>
            (#[trigger] self.label_at(i)).flows(#[trigger] other.label_at(j))
    }

    pub open spec fn is_public(&self) -> bool {
        self.flows(Label::public())
    }

    pub open spec fn take(&self, n: usize) -> Data {
        self.subrange(0, n)
    }

    pub open spec fn skip(&self, n: usize) -> Data {
        self.subrange(n, self@.len() as usize)
    }

    #[verifier::external_body]
    pub fn append(&mut self, other: &Data)
        ensures self == old(self).concat(other)
    {
        self.0.extend_from_slice(&other.0);
    }

    /// Createa a `Data` from the environment, which is assumd to be public
    #[verifier::external_body]
    pub fn from_vec(data: Vec<u8>) -> (res: Data)
        ensures
            res.is_public(),
            res@ == data@,
    {
        Data(data)
    }

    pub broadcast proof fn lemma_flows_data_trans(&self, l: Label, other: &Data)
        requires #[trigger] self.flows(l) && #[trigger] l.flows_data(other)
        ensures self.flows_data(other)
    {
        broadcast use label_axioms;
    }

    pub broadcast proof fn lemma_flows_data_trans_alt(&self, other1: &Data, other2: &Data)
        requires
            #[trigger] self.flows_data(other1),
            #[trigger] other1.flows_data(other2),
            other1@.len() != 0,

        ensures self.flows_data(other2)
    {
        broadcast use label_axioms;
        assert(self.flows(other1.label_at(0)));
    }

    pub broadcast proof fn lemma_flows_data_to_public(&self, other: &Data)
        requires
            #[trigger] self.flows_data(other),
            other.is_public(),
            other@.len() != 0,

        ensures self.is_public()
    {
        broadcast use label_axioms;
        assert(other.label_at(0).flows(Label::public()));
    }

    pub proof fn lemma_cover_label_helper(&self, i: usize, j: usize)
        requires 0 <= j <= i < self@.len()
        ensures self.label_at(i).flows(self.cover_label_helper(j))
        decreases i - j
    {
        broadcast use label_axioms, Data::axiom_len_bounded;
        if j < i {
            self.lemma_cover_label_helper(i, (j + 1) as usize);
        }
    }

    pub broadcast proof fn lemma_cover_label(&self, i: usize)
        requires 0 <= i < self@.len()
        ensures (#[trigger] self.label_at(i)).flows(self.cover_label())
    {
        broadcast use label_axioms, Data::axiom_len_bounded;
        reveal(Data::cover_label);
        self.lemma_cover_label_helper(i, 0);
    }

    pub broadcast proof fn lemma_eq_is_public(&self, other: &Data)
        requires self.eq(other)
        ensures #[trigger] self.is_public() == #[trigger] other.is_public()
    {}

    // pub broadcast proof fn lemma_cover_label_to_flows_data(d1: &Data, d2: &Data)
    //     requires d1.label().flows(d2.label())
    //     ensures d1.flows_data(d2)
    // {
    //     broadcast use Label::axioms;

    // }

    // pub broadcast proof fn lemma_flows_data_to_cover_label(d1: &Data, d2: &Data)
    //     ensures d1.flows_data(d2) == d1.label().flows(d2.label())
    // {
    //     broadcast use Label::axioms;
    // }
}

/// Axioms for symmetric encryption
impl Data {
    #[verifier::external_body]
    pub fn fresh_enckey(Ghost(msg_label): Ghost<Label>, Ghost(pred): Ghost<SecPred>) -> (res: Data)
        ensures
            res.typ() == Type::EncKey(msg_label, pred),
            msg_label.flows_data(&res),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn encrypt(key: &Data, msg: &Data) -> (res: Data)
        requires ({
            // Corrupt case
            ||| key.is_public() && msg.is_public()

            // Well-formed case
            ||| {
                &&& !key.is_public()
                &&& key.typ() matches Type::EncKey(label, pred)
                &&& msg.flows(label)
                &&& pred(*msg)
            }
        })
        ensures res.is_public()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn decrypt(key: &Data, ctxt: &Data) -> (res: Option<Data>)
        requires ({
            // Corrupt case
            ||| key.is_public() && ctxt.is_public()

            // Well-formed case
            ||| {
                &&& !key.is_public()
                &&& key.typ() matches Type::EncKey(..)
                &&& ctxt.is_public()
            }
        })

        ensures res matches Some(res) ==> {
            ||| key.is_public() && res.is_public()
            ||| {
                &&& !key.is_public()
                &&& key.typ() matches Type::EncKey(label, pred)
                &&& res.flows(label)
                &&& pred(res)
            }
        }
    {
        unimplemented!()
    }
}

/// Axioms for nonce
impl Data {
    #[verifier::external_body]
    pub fn fresh_nonce() -> (res: Data)
        ensures res.typ() == Type::Nonce
    {
        unimplemented!()
    }
}

/// Axioms for KDF
impl Data {
    #[verifier::external_body]
    pub fn extract(salt: &Data, ikm: &Data) -> (res: Data)
        requires ({
            ||| salt.is_public() && ikm.is_public()
            // TODO: Do we want the other position to be public?
            // TODO: what if both positions have valid keys?
            ||| {
                &&& !salt.is_public()
                &&& salt.typ() matches Type::ExtractKey(..)
            }
            ||| {
                &&& !ikm.is_public()
                &&& ikm.typ() matches Type::ExtractKey(..)
            }
        })
        ensures ({
            ||| salt.is_public() && ikm.is_public() && res.is_public()
            ||| {
                &&& !salt.is_public()
                &&& salt.typ() matches Type::ExtractKey(res_type)
                &&& res.typ() == res_type
                &&& res.flows_data(salt)
                &&& !res.is_public() // Currently assuming strictness
                &&& res@.len() != 0
            }
            ||| {
                &&& !ikm.is_public()
                &&& ikm.typ() matches Type::ExtractKey(res_type)
                &&& res.typ() == res_type
                &&& res.flows_data(ikm)
                &&& !res.is_public() // Currently assuming strictness
                &&& res@.len() != 0
            }
        })
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn expand(prk: &Data, info: &Data) -> (res: Data)
        requires ({
            ||| prk.is_public() && info.is_public()
            ||| {
                &&& !prk.is_public()
                &&& prk.typ() matches Type::ExpandKey(res_type)
                &&& res_type(info@) is None ==> info.is_public()
            }
        })
        ensures ({
            ||| prk.is_public() && info.is_public() && res.is_public()
            ||| {
                &&& !prk.is_public()
                &&& prk.typ() matches Type::ExpandKey(res_type)
                &&& res_type(info@) is None ==> res.is_public()
                &&& res_type(info@) matches Some(res_type) ==>
                        res.typ() == res_type &&
                        res.flows_data(prk) &&
                        !res.is_public() && // We default to strict
                        res@.len() != 0
            }
        })
    {
        unimplemented!()
    }
}

pub trait Environment {
    fn output(&mut self, data: &Data)
        requires data.is_public();

    fn input(&mut self) -> (res: Data)
        ensures res.is_public();
}

}
