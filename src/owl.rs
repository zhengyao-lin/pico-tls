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

// pub fn test() {
//     broadcast use Label::axioms;

//     // name data: nonce
//     // name key1: enckey Name(data)
//     // name key2: enckey Name(key1)

//     let data = Data::fresh_nonce();
//     let key1 = Data::fresh_enckey(Ghost(data.label()), Ghost(|d| d == data));
//     let key2 = Data::fresh_enckey(Ghost(key1.label()), Ghost(|d| d == key1));

//     let ctxt1 = &Data::encrypt(&key1, &data);
//     let ctxt2 = &Data::encrypt(&key2, &key1);
//     // assert(data.label().flows(key1.label()));

//     let input1 = Data::from_vec(vstd::slice::slice_to_vec(ctxt1.declassify()));
//     let input2 = Data::from_vec(vstd::slice::slice_to_vec(ctxt2.declassify()));

//     match Data::decrypt(&key2, &input2) {
//         Some(res) => {
//             if let Some(data2) = Data::decrypt(&res, &input1) {
//                 assert(!key1.is_public() ==> data2 == data);
//             }
//         }
//         None => {}
//     }
// }

/// TODO: Moving this to another fild causes panic (due to the broadcast)
mod example {

use super::*;

broadcast use Label::axioms;

pub open spec fn name_context_spec(data: &Data, key1: &Data, key2: &Data) -> bool {
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

pub fn alice(Ghost(data): Ghost<&Data>, Ghost(key1): Ghost<&Data>, key2: &Data, input1: &Data, input2: &Data) -> (res: Option<Data>)
    requires
        name_context_spec(data, key1, key2),
        input1.is_public(),
        input2.is_public(),

    ensures
        res matches Some(res) ==>
        !key1.is_public() ==> res == data
{   
    if let Some(key) = Data::decrypt(key2, input1) {
        if let Some(d) = Data::decrypt(&key, input2) {
            return Some(d);
        }
    }
    None
}

pub fn bob(data: &Data, key1: &Data, key2: &Data) -> (res: (Data, Data))
    requires
        name_context_spec(data, key1, key2),

    ensures
        res.0.is_public(),
        res.1.is_public(),
{
    (Data::encrypt(&key1, &data), Data::encrypt(&key2, &key1))
}

}

}
