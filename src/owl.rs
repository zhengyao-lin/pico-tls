// Based on https://gist.github.com/gancherj/7f80e6d4fd813dc613d8bdee96ffdf5c

#![allow(dead_code)]

use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub struct Label;

/// Semi-lattice structure of labels with `public` being the zero element
impl Label {
    pub spec fn public() -> Label;
    pub spec fn join(self, l: Label) -> Label;
    pub spec fn flows(self, l: Label) -> bool;

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

    broadcast group axioms {
        Label::axiom_flows_refl,
        Label::axiom_flows_trans,
        Label::axiom_flows_zero,
        Label::axiom_public_zero,
        Label::axiom_join_comm,
        Label::axiom_join_public,
        Label::axiom_flows_join,
    }
}

pub type SecPred = spec_fn(Data) -> bool;

/// TODO: want to avoid case analysis of types
/// on a piece of unknown Data
pub enum Type {
    ExtractKey(Box<Type>),
    ExpandKey(spec_fn(Seq<u8>) -> Option<Type>),
    EncKey(Label, SecPred),
    Nonce,
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
    pub closed spec fn range_type(&self, start: usize, end: usize) -> Type;

    /// The byte `self[i]` has label `self.label_at(i)`
    pub closed spec fn label_at(&self, i: usize) -> Label;

    /// Concatenates two `Data`s
    #[verifier::when_used_as_spec(spec_concat)]
    #[verifier::external_body]
    pub fn concat(&self, other: &Data) -> (res: Data)
        ensures res == self.spec_concat(other)
    {
        Data(self.0.iter().chain(other.0.iter()).copied().collect())
    }

    pub spec fn spec_concat(&self, other: &Data) -> Data;

    /// Take the subrange of a `Data`
    #[verifier::when_used_as_spec(spec_subrange)]
    #[verifier::external_body]
    pub fn subrange(&self, start: usize, end: usize) -> (res: Data)
        requires 0 <= start <= end <= self@.len()
        ensures res == self.subrange(start, end)
    {
        Data(self.0[start..end].to_vec())
    }

    pub spec fn spec_subrange(&self, start: usize, end: usize) -> Data;

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
        ensures #[trigger] (#[trigger] self.subrange(start1, end1)).range_type(start2, end2)
            == self.range_type((start2 + start1) as usize, (end2 + start1) as usize);

    /// `concat` preserves the types of both parts (left chunk)
    #[verifier::external_body]
    pub broadcast proof fn axiom_concat_type_left(&self, other: &Data, start: usize, end: usize)
        requires 0 <= start <= end <= self@.len()
        ensures #[trigger] (#[trigger] self.concat(other)).range_type(start, end) == self.range_type(start, end);

    /// `concat` preserves the types of both parts (right chunk)
    #[verifier::external_body]
    pub broadcast proof fn axiom_concat_type_right(&self, other: &Data, start: usize, end: usize)
        requires self@.len() <= start <= end <= self@.len() + other@.len()
        ensures #[trigger] (#[trigger] self.concat(other)).range_type(start, end)
                == other.range_type((start - self@.len()) as usize, (end - self@.len()) as usize);

    /// `subrange` preserves labels
    #[verifier::external_body]
    pub broadcast proof fn axiom_subrange_label(&self, start: usize, end: usize, i: usize)
        requires
            0 <= start <= end <= self@.len(),
            0 <= i < end - start,
        ensures #[trigger] (#[trigger] self.subrange(start, end)).label_at(i) == self.label_at((i + start) as usize);

    /// `concat` preserves labels (left)
    #[verifier::external_body]
    pub broadcast proof fn axiom_concat_label_left(&self, other: &Data, i: usize)
        requires 0 <= i < self@.len()
        ensures #[trigger] (#[trigger] self.concat(other)).label_at(i) == self.label_at(i);

    /// `concat` preserves labels (right)
    #[verifier::external_body]
    pub broadcast proof fn axiom_concat_label_right(&self, other: &Data, i: usize)
        requires self@.len() <= i < self@.len() + other@.len()
        ensures #[trigger] (#[trigger] self.concat(other)).label_at(i) == other.label_at((i - self@.len()) as usize);

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
    /// TODO: maybe too strong?
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
        broadcast use Label::axioms;
    }

    pub broadcast proof fn lemma_flows_data_trans_alt(&self, other1: &Data, other2: &Data)
        requires
            #[trigger] self.flows_data(other1),
            #[trigger] other1.flows_data(other2),
            other1@.len() != 0,

        ensures self.flows_data(other2)
    {
        broadcast use Label::axioms;
        assert(self.flows(other1.label_at(0)));
    }

    pub broadcast proof fn lemma_flows_data_to_public(&self, other: &Data)
        requires
            #[trigger] self.flows_data(other),
            other.is_public(),
            other@.len() != 0,

        ensures self.is_public()
    {
        broadcast use Label::axioms;
        assert(other.label_at(0).flows(Label::public()));
    }

    pub proof fn lemma_cover_label_helper(&self, i: usize, j: usize)
        requires 0 <= j <= i < self@.len()
        ensures self.label_at(i).flows(self.cover_label_helper(j))
        decreases i - j
    {
        broadcast use Label::axioms, Data::axiom_len_bounded;
        if j < i {
            self.lemma_cover_label_helper(i, (j + 1) as usize);
        }
    }

    pub broadcast proof fn lemma_cover_label(&self, i: usize)
        requires 0 <= i < self@.len()
        ensures (#[trigger] self.label_at(i)).flows(self.cover_label())
    {
        broadcast use Label::axioms, Data::axiom_len_bounded;
        reveal(Data::cover_label);
        self.lemma_cover_label_helper(i, 0);
    }

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

impl Data {
    broadcast group axioms {
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
        Data::lemma_cover_label,
    }
}

pub trait Environment {
    fn output(&mut self, data: &Data)
        requires data.is_public();

    fn input(&mut self) -> (res: Data)
        ensures res.is_public();
}

/// Example from the Owl paper
/// TODO: Moving this to another fild causes panic (due to the broadcast)
mod example1 {
    use super::*;
    broadcast use Label::axioms, Data::axioms;

    /// Specification for the name context (trusted)
    pub open spec fn spec_name_context(data: &Data, key1: &Data, key2: &Data) -> bool {
        // name data: nonce
        &&& data.typ() == Type::Nonce

        // name key1: enckey Name(data)
        &&& key1.typ() matches Type::EncKey(l, p)
        &&& data.flows(l) && l.flows_data(key1)
        &&& p == |d: Data| d == data
        &&& key1@.len() != 0

        // name key2: enckey Name(key1)
        &&& key2.typ() matches Type::EncKey(l, p)
        &&& key1.flows(l) && l.flows_data(key2)
        &&& p == |d: Data| d == key1
        &&& key2@.len() != 0
    }

    pub fn alice<E: Environment>(
        env: &mut E,
        Ghost(data): Ghost<&Data>,
        Ghost(key1): Ghost<&Data>,
        key2: &Data,
    ) -> (res: Option<Data>)
        requires
            spec_name_context(data, key1, key2),
        ensures
            res matches Some(res) ==>
            !key1.is_public() ==> res == data,
    {
        if let Some(key) = Data::decrypt(key2, &env.input()) {
            if let Some(d) = Data::decrypt(&key, &env.input()) {
                return Some(d);
            }
        }
        None
    }

    pub fn bob<E: Environment>(
        env: &mut E,
        data: &Data,
        key1: &Data,
        key2: &Data,
    )
        requires
            spec_name_context(data, key1, key2),
    {
        env.output(&Data::encrypt(&key1, &data));
        // FAIL: env.output(&Data::encrypt(&key2, &data));
        // FAIL: env.output(&data);
        env.output(&Data::encrypt(&key2, &key1));
    }
}

/// Example with some dependent parsing
mod example2 {
    use super::*;

    broadcast use Label::axioms, Data::axioms;

    /// Specification for the name context (trusted)
    pub open spec fn spec_name_context(data: &Data, psk: &Data) -> bool {
        // name data: nonce
        &&& data.typ() == Type::Nonce

        // name psk: enckey struct {
        //     tag: Data<adv> |1|,
        //     data: if tag == 0 then Name(data) else Data<adv>
        // }
        &&& psk.typ() matches Type::EncKey(l, p)
        &&& data.flows(l) && l.flows_data(psk)
        &&& p == |d: Data|
                d.label_at(0).is_public() &&
                if d@[0] == 0 {
                    d@.subrange(1, d@.len() as int) == data@
                } else {
                    d.is_public()
                }
        &&& psk@.len() != 0
    }

    pub fn alice<E: Environment>(
        env: &mut E,
        Ghost(data): Ghost<&Data>,
        psk: &Data,
    ) -> (res: Option<Data>)
        requires
            spec_name_context(data, psk),

        ensures
            res matches Some(res) ==>
            !psk.is_public() ==>
            res@ == data@,
    {
        if let Some(tagged) = Data::decrypt(psk, &env.input()) {
            if tagged.len() > 0 { // This check is required for the corrupted case
                let tag = tagged.index(0);

                if tag == 0 {
                    // FAIL: assert(tagged.can_declassify(0, tagged@.len() as int));
                    assert(!psk.is_public() ==> tagged@.skip(1) == data@);
                    return Some(tagged.subrange(1, tagged.len()));
                } else {
                    assert(tagged.is_public());
                }
            }
        }

        None
    }

    pub fn bob<E: Environment>(
        env: &mut E,
        data: &Data,
        psk: &Data,
    )
        requires
            spec_name_context(data, psk),
    {
        let content = Data::from_vec(vec![1]).concat(&Data::from_vec(vec![1, 1, 0]));
        env.output(&Data::encrypt(psk, &content));

        // FAIL: env.output(&Data::encrypt(psk, &Data::from_vec(vec![0]).concat(&Data::from_vec(vec![1, 1, 0]))));

        let tagged = Data::from_vec(vec![0]).concat(data);
        assert(tagged@.subrange(1, tagged@.len() as int) == data@);
        env.output(&Data::encrypt(psk, &tagged));
    }
}

/// KDF (not quite working yet)
mod example3 {
    use super::*;

    broadcast use Label::axioms, Data::axioms;

    /// Specification for the name context (trusted)
    pub open spec fn spec_name_context(data1: &Data, data2: &Data, key: &Data) -> bool {
        // name data1: nonce
        &&& data1.typ() == Type::Nonce

        // name data2: nonce
        &&& data2.typ() == Type::Nonce

        // name key: extractkey expandkey { info.
        //     info == 0x01 -> strict enckey Name(data1),
        //     info == 0x02 -> strict enckey Name(data2)
        // }
        &&& key.typ() matches Type::ExtractKey(extract_result)
        &&& *extract_result == Type::ExpandKey(|info: Seq<u8>| {
            if info =~= seq![0u8] {
                Some(Type::EncKey(data1.cover_label(), |d: Data| d == data1))
            } else if info =~= seq![1u8] {
                Some(Type::EncKey(data2.cover_label(), |d: Data| d == data2))
            } else {
                None
            }
        })
        &&& data1.flows_data(key)
        &&& data2.flows_data(key)
        &&& key@.len() != 0
    }

    pub fn alice<E: Environment>(
        env: &mut E,
        data1: &Data,
        data2: &Data,
        key: &Data,
    )
        requires
            spec_name_context(data1, data2, key),
    {
        let exp_key = Data::extract(key, &Data::from_vec(vec![]));

        // assert(!key.is_public() ==> exp_key.typ() matches Type::ExpandKey(..));
        // assert(exp_key.label().flows(key.label()));

        let key1 = Data::expand(&exp_key, &Data::from_vec(vec![0]));
        let key2 = Data::expand(&exp_key, &Data::from_vec(vec![1]));
        let key3 = Data::expand(&exp_key, &Data::from_vec(vec![2]));
        assert(key3.is_public());

        // assert(info1@ =~= seq![0u8]);
        // assert(key1.label().flows(exp_key.label()));
        // assert(!key.label().is_public() ==> !exp_key.label().is_public());
        // assert(!exp_key.is_public() ==> key1.label().flows(exp_key.label()));
        // assert(!key.is_public() ==> key1.typ() matches Type::EncKey(..));
        // assert(!key.is_public() ==> data1.flows(key1.typ()->EncKey_0));

        Data::encrypt(&key1, &data1);
        //  FAIL: Data::encrypt(&key1, &data2);

        Data::encrypt(&key2, &data2);
    }
}

}
