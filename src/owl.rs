// Based on https://gist.github.com/gancherj/7f80e6d4fd813dc613d8bdee96ffdf5c

#![allow(dead_code)]

use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub struct Label;

// Defines the structure of labels
impl Label {
    pub spec fn public() -> Label;
    pub spec fn join(self, l: Label) -> Label;
    pub spec fn flows(self, l: Label) -> bool;

    pub open spec fn is_public(self) -> bool {
        self.flows(Label::public())
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
    pub broadcast proof fn axiom_join_comm(l1: Label, l2: Label)
        ensures #[trigger] l1.join(l2) == l2.join(l1);

    #[verifier::external_body]
    pub broadcast proof fn axiom_join_public(l1: Label, l2: Label)
        requires l2.is_public()
        ensures #[trigger] l1.join(l2) == l2;

    broadcast group axioms {
        Label::axiom_flows_refl,
        Label::axiom_flows_trans,
        Label::axiom_flows_zero,
        Label::axiom_join_comm,
        Label::axiom_join_public,
    }
}

pub type Pred = spec_fn(Data) -> bool;

pub enum Type {
    ExtractKey(Box<Type>),
    ExpandKey(spec_fn(Seq<u8>) -> Option<Type>),

    EncKey(Label, Pred),
    Nonce,
}

pub struct Data(Vec<u8>);

impl View for Data {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Seq<u8> {
        self.0@
    }
}

impl Data {
    pub spec fn typ(&self) -> Type;
    pub spec fn label(&self) -> Label;

    pub open spec fn is_public(&self) -> bool {
        self.label().is_public()
    }

    // pub open spec fn spec_len(&self) -> usize {
    //     self@.len() as usize
    // }

    // TODO: length is always public currently
    // #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (res: usize)
        ensures res == self@.len()
    {
        self.0.len()
    }

    #[verifier::external_body]
    pub fn from_vec(data: Vec<u8>) -> (res: Data)
        ensures
            res.is_public(),
            res@ == data@,
    {
        Data(data)
    }
}

/// Mechanisms for declassifying subranges of data
/// and how that interacts with labels, concat, etc.
/// So that we can handle more complex structs or enums
impl Data {
    pub spec fn can_declassify(&self, start: int, end: int) -> bool;

    pub spec fn spec_concat(&self, other: &Data) -> Data;

    #[verifier::when_used_as_spec(spec_concat)]
    #[verifier::external_body]
    pub fn concat(&self, other: &Data) -> (res: Data)
        ensures res == self.spec_concat(other)
    {
        Data(self.0.iter().chain(other.0.iter()).copied().collect())
    }

    pub spec fn spec_subrange(&self, start: usize, end: usize) -> Data;

    #[verifier::when_used_as_spec(spec_subrange)]
    #[verifier::external_body]
    pub fn subrange(&self, start: usize, end: usize) -> (res: Data)
        requires 0 <= start <= end <= self@.len()
        ensures res == self.subrange(start, end)
    {
        Data(self.0[start..end].to_vec())
    }

    #[verifier::external_body]
    pub fn declassify_range(&self, start: usize, end: usize) -> (res: &[u8])
        requires
            0 <= start <= end <= self@.len(),
            self.can_declassify(start as int, end as int),
        ensures res@ == self@.subrange(start as int, end as int)
    {
        &self.0[start..end]
    }

    #[verifier::external_body]
    pub broadcast proof fn axiom_concat(&self, other: &Data)
        ensures
            (#[trigger] self.concat(other))@ == self@ + other@,
            self.concat(other).label() == self.label().join(other.label());

    #[verifier::external_body]
    pub broadcast proof fn axiom_subrange(&self, start: usize, end: usize)
        requires 0 <= start <= end <= self@.len()
        ensures
            (#[trigger] self.subrange(start, end))@ == self@.subrange(start as int, end as int),
            self.subrange(start, end).label() == self.label();

    #[verifier::external_body]
    pub broadcast proof fn axiom_public_declassify(&self)
        ensures #[trigger] self.is_public() <==> self.can_declassify(0, self@.len() as int);

    #[verifier::external_body]
    pub broadcast proof fn axiom_declassify_combine(&self, start1: int, end1: int, start2: int, end2: int)
        ensures
            // [start2, end2) contained in [start1, end1)
            #[trigger] self.can_declassify(start1, end1) &&
            0 <= start1 <= start2 <= end2 <= end1
            ==> #[trigger] self.can_declassify(start2, end2),

            // [start1, end1) overlaps with [start2, end2)
            self.can_declassify(start1, end1) &&
            self.can_declassify(start2, end2) &&
            0 <= start1 <= start2 <= end1 <= end2
            ==> self.can_declassify(start1, end2);

    // Declassified regions in the first part
    #[verifier::external_body]
    pub broadcast proof fn axiom_declassify_concat_left(&self, other: &Data, start: int, end: int)
        requires
            0 <= start <= end <= self@.len(),
            #[trigger] self.can_declassify(start, end),
        ensures
            (#[trigger] self.concat(other))
                .can_declassify(start, end);

    // Declassified regions in the second part
    #[verifier::external_body]
    pub broadcast proof fn axiom_declassify_concat_right(&self, other: &Data, start: int, end: int)
        requires
            0 <= start <= end <= other@.len(),
            #[trigger] other.can_declassify(start, end),
        ensures
            (#[trigger] self.concat(other))
                .can_declassify(self@.len() + start, self@.len() + end);

    // Declassified regions in a subrange
    #[verifier::external_body]
    pub broadcast proof fn axiom_declassify_subrange(&self, start1: int, end1: int, start2: usize, end2: usize)
        requires
            0 <= start1 <= end1 <= self@.len(),
            0 <= start2 <= end2 <= self@.len(),
            #[trigger] self.can_declassify(start1, end1),

            // There is an intersection
            start1 <= end2 && start2 <= end1,

        ensures ({
            // Intersection start and end
            let start = if start1 <= start2 { start2 as int } else { start1 };
            let end = if end1 <= end2 { end1 } else { end2 as int };

            (#[trigger] self.subrange(start2 as usize, end2 as usize))
                .can_declassify(start - start2, end - start2)
        });

    broadcast group axioms {
        Data::axiom_concat,
        Data::axiom_subrange,
        Data::axiom_public_declassify,
        Data::axiom_declassify_combine,
        Data::axiom_declassify_concat_left,
        Data::axiom_declassify_concat_right,
        Data::axiom_declassify_subrange,
    }
}

/// Axioms for symmetric encryption
impl Data {
    #[verifier::external_body]
    pub fn fresh_enckey(msg_label: Ghost<Label>, pred: Ghost<Pred>) -> (res: Data)
        ensures
            res.typ() == Type::EncKey(msg_label@, pred@),
            msg_label@.flows(res.label()),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn encrypt(key: &Data, msg: &Data) -> (res: Data)
        requires ({
            ||| key.is_public() && msg.is_public()
            ||| {
                &&& !key.is_public()
                &&& key.typ() matches Type::EncKey(label, pred)
                &&& msg.label().flows(label)
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
            ||| key.is_public() && ctxt.is_public()
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
                &&& res.label().flows(label)
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
                &&& res.label().flows(salt.label())
                &&& !res.is_public() // We default to strict
            }
            ||| {
                &&& !ikm.is_public()
                &&& ikm.typ() matches Type::ExtractKey(res_type)
                &&& res.typ() == res_type
                &&& res.label().flows(ikm.label())
                &&& !res.is_public() // We default to strict
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
                        res.label().flows(prk.label()) &&
                        !res.is_public() // We default to strict
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
        &&& l == data.label()
        &&& p == |d: Data| d == data
        &&& l.flows(key1.label())

        // name key2: enckey Name(key1)
        &&& key2.typ() matches Type::EncKey(l, p)
        &&& l == key1.label()
        &&& p == |d: Data| d == key1
        &&& l.flows(key2.label())
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
        &&& l == data.label().join(Label::public())
        &&& p == |d: Data|
                d.can_declassify(0, 1) &&
                if d@[0] == 0 {
                    d@.subrange(1, d@.len() as int) == data@
                } else {
                    d.can_declassify(1, d@.len() as int)
                }
        &&& l.flows(psk.label())
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
                // assert(tagged.can_declassify(0, 1));
                let tag = tagged.declassify_range(0, 1);

                if tag[0] == 0 {
                    // FAIL: assert(tagged.can_declassify(0, tagged@.len() as int));
                    assert(!psk.is_public() ==> tagged@.skip(1) == data@);
                    return Some(tagged.subrange(1, tagged.len()));
                } else {
                    assert(tagged.can_declassify(0, tagged@.len() as int));
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
        env.output(&Data::encrypt(psk, &Data::from_vec(vec![1]).concat(&Data::from_vec(vec![1, 1, 0]))));

        // FAIL: env.output(&Data::encrypt(psk, &Data::from_vec(vec![0]).concat(&Data::from_vec(vec![1, 1, 0]))));

        let tagged = Data::from_vec(vec![0]).concat(data);
        assert(tagged@.subrange(1, tagged@.len() as int) == data@);
        env.output(&Data::encrypt(psk, &tagged));
    }
}

/// KDF
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
        &&& *extract_result matches Type::ExpandKey(cases)
        &&& cases == |info: Seq<u8>| {
            if info =~= seq![0u8] {
                Some(Type::EncKey(data1.label(), |d: Data| d == data1))
            } else if info =~= seq![1u8] {
                Some(Type::EncKey(data2.label(), |d: Data| d == data2))
            } else {
                None
            }
        }
        &&& data1.label().flows(key.label())
        &&& data2.label().flows(key.label())
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

        // assert(info1@ =~= seq![0u8]);
        // assert(key1.label().flows(exp_key.label()));
        // assert(!key.label().is_public() ==> !exp_key.label().is_public());
        // assert(!exp_key.is_public() ==> key1.label().flows(exp_key.label()));
        // assert(!key.is_public() ==> key1.typ() matches Type::EncKey(..));

        let key2 = Data::expand(&exp_key, &Data::from_vec(vec![1]));
        let key3 = Data::expand(&exp_key, &Data::from_vec(vec![2]));
        assert(key3.is_public());

        Data::encrypt(&key1, &data1);
        // FAIL: Data::encrypt(&key1, &data2);

        Data::encrypt(&key2, &data2);
    }
}

}
