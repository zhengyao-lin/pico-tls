use crate::owl::*;

use vstd::prelude::*;

verus! {

/// Example from the Owl paper
mod example1 {
    use super::*;

    broadcast use crate::owl::axioms;

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

    broadcast use crate::owl::axioms;

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

    broadcast use crate::owl::axioms;

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
