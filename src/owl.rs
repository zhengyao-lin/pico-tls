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
    pub broadcast proof fn axiom_join_comm(l1: Label, l2: Label)
        ensures #[trigger] l1.join(l2) == l2.join(l1);

    #[verifier::external_body]
    pub broadcast proof fn axiom_join_public(l1: Label, l2: Label)
        requires l2.is_public()
        ensures #[trigger] l1.join(l2) == l2;

    broadcast group axioms {
        Label::axiom_flows_refl,
        Label::axiom_flows_trans,
        Label::axiom_join_comm,
        Label::axiom_join_public,
    }
}

pub type Pred = spec_fn(Data) -> bool;

pub enum Type {
    /// TODO
    ExtractKey(Label, Pred),
    ExpandKey(spec_fn(Seq<u8>) -> Type),
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

    #[verifier::external_body]
    pub fn from_vec(data: Vec<u8>) -> (res: Data)
        ensures res.is_public()
    {
        Data(data)
    }
    
    pub fn declassify(&self) -> (res: &[u8])
        requires self.is_public()
        ensures res@ == self@
    {
        self.0.as_slice()
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

pub trait Environment {
    fn output(&mut self, data: &Data)
        requires data.is_public();

    fn input(&mut self) -> (res: Data)
        ensures res.is_public();
}

/// TODO: Moving this to another fild causes panic (due to the broadcast)
mod example1 {

use super::*;

broadcast use Label::axioms;

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

}
