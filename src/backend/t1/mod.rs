mod ldbc_populator;

use std::collections::HashMap;
use std::convert::TryInto;
use std::ops::Sub;
use std::time::Instant;
use rand::rngs::SmallRng;
use rand::{Rng, RngCore, SeedableRng};
use sled::IVec;
use sled::transaction::{TransactionError, TransactionResult};
use {
    byteorder::{BigEndian, LittleEndian, ByteOrder},
    zerocopy::{
        byteorder::U64, AsBytes, FromBytes, LayoutVerified, Unaligned, U16, U32,
    },
};

pub fn run() {
    use ldbc_populator;
    let mut engine = SE1::new();
    let rt_is_part_of = engine.rt_get_or_create(b"IS_PART_OF");
    let propk_name = engine.propk_get_or_create(b"name");
    let lbl_continent = engine.lbl_get_or_create(b"Continent");
    let lbl_country = engine.lbl_get_or_create(b"Country");

    let start = Instant::now();
    ldbc_populator::populate(&mut engine, 1);
    let delta = Instant::now().sub(start).as_secs();

    println!("delta={} secs", delta);
    println!("nodes={}, size={}", engine.db.generate_id().unwrap(), engine.db.size_on_disk().unwrap() / 1024);

    let mut countries = HashMap::new();
    for country in engine.node_scan(lbl_country) {
        countries.insert(countries.len(), country);
    }

    let mut random = SmallRng::seed_from_u64(1337);
    let mut rels_seen: u64 = 0;
    let mut hash: u64 = 0;
    let start = Instant::now();
    for i in 0..10_000 {
        // let random_node : u64 = random.gen_range(0, 1_000_000);
        let random_node = *countries.get(&random.gen_range(0, countries.len())).unwrap();
        for rel in engine.rel_scan(random_node, rt_is_part_of) {
            hash += rel.other;
            rels_seen += 1;
        }
    }
    let delta = Instant::now().sub(start).as_secs();
    // Need this to be 1sec for 1M random pick
    // Need this to be 22 sec for 10K countries pick
    println!("Expanded random nodes in {} secs / {} rels seen, hash is {}", delta, rels_seen, hash);
}

#[derive(FromBytes, AsBytes, Unaligned)]
#[repr(C)]
struct RelKey {
    node: U64<BigEndian>,
    rel_type: U16<BigEndian>,
    other_node: U64<LittleEndian>,
}

// These need to preserve lexical order.
// So, if we use uhh google style varints, what happens?
//
// 0000 0000 0000 0001 -> 0000 0001
// 0000 0001 0000 0001 -> 1000 0001 0000 0001
// 0000 0001 0000 0001 -> 1000 0001 0000 0001 hrm
fn encode_u64(v: u64, dst: &mut [u8]) -> usize {
    // dst[0] = (v >> (7 * 8)) as u8;
    // dst[1] = (v >> (6 * 8)) as u8;
    // dst[2] = (v >> (5 * 8)) as u8;
    // dst[3] = (v >> (4 * 8)) as u8;
    // dst[4] = (v >> (3 * 8)) as u8;
    // dst[5] = (v >> (2 * 8)) as u8;
    // dst[6] = (v >> (1 * 8)) as u8;
    // dst[7] = (v >> (0 * 8)) as u8;
    dst[0] = (v >> (3 * 8)) as u8;
    dst[1] = (v >> (2 * 8)) as u8;
    dst[2] = (v >> (1 * 8)) as u8;
    dst[3] = (v >> (0 * 8)) as u8;
    4
}

fn encode_u16(v: u16, dst: &mut [u8]) -> usize {
    // dst[0] = (v >> (1 * 8)) as u8;
    // dst[1] = (v >> (0 * 8)) as u8;
    dst[0] = (v >> (0 * 8)) as u8;
    1
}

fn decode_u64(src: &[u8]) -> (usize, u64) {
    let mut out: u64 = 0;
    // out |= (src[0] as u64) << (7 * 8);
    // out |= (src[1] as u64) << (6 * 8);
    // out |= (src[2] as u64) << (5 * 8);
    // out |= (src[3] as u64) << (4 * 8);
    // out |= (src[4] as u64) << (3 * 8);
    // out |= (src[5] as u64) << (2 * 8);
    // out |= (src[6] as u64) << (1 * 8);
    // out |= (src[7] as u64) << (0 * 8);
    out |= (src[0] as u64) << (3 * 8);
    out |= (src[1] as u64) << (2 * 8);
    out |= (src[2] as u64) << (1 * 8);
    out |= (src[3] as u64) << (0 * 8);
    (4, out)
}

fn decode_u16(src: &[u8]) -> (usize, u16) {
    let mut out: u16 = 0;
    // out |= (src[0] as u16) << 8;
    // out |= (src[1] as u16) << 0;
    out |= (src[0] as u16) << 0;
    (1, out)
}

fn encode_relkey(node: u64, other: u64, rt: u16) -> sled::IVec {
    let mut buf = [0 as u8; 8 + 8 + 2];
    let mut i = 0;
    i += encode_u64(node, &mut buf[i..i+8]);
    i += encode_u16(rt, &mut buf[i..i+2]);
    i += encode_u64(other, &mut buf[i..i+8]);

    sled::IVec::from(&buf[0..i])
}

fn encode_relkey_range(node: u64, rt: u16) -> (sled::IVec, sled::IVec) {
    let mut buf = [0 as u8; 8 + 2];
    let mut i = 0;
    i += encode_u64(node, &mut buf[i..i+8]);
    i += encode_u16(rt, &mut buf[i..i+2]);

    let start = sled::IVec::from(&buf[0..i]);

    let mut i = 0;
    i += encode_u64(node, &mut buf[i..i+8]);
    i += encode_u16(rt + 1, &mut buf[i..i+2]);
    let end = sled::IVec::from(&buf[0..i]);

    (start, end)
}


fn encode_node_propkey(node: u64, prop: u32) -> sled::IVec {
    let mut buf = [0 as u8; 8 + 4];
    // Prefix compression, so use big endian
    byteorder::BigEndian::write_u64(&mut buf, node);
    // Suffix compression, so use little endian
    byteorder::LittleEndian::write_u32(&mut buf[8..], prop);
    sled::IVec::from(&buf)
}

fn decode_rel_from_relkey(raw: &[u8]) -> Rel {
    let mut i = 0;
    let (l, _) = decode_u64(&raw[i..]);
    i += l;
    let (l, rt) = decode_u16(&raw[i..]);
    i += l;
    let (l, other) = decode_u64(&raw[i..]);
    Rel {
        rt,
        other
    }
}

#[derive(Debug)]
pub enum SE1Val {
    String(String),
}

fn encode_se1_val(val: &SE1Val) -> sled::IVec {
    match val {
        SE1Val::String(s) => {
            let sbytes = s.as_bytes();
            let mut out = Vec::with_capacity(1 + sbytes.len());
            out.push(0x10);
            out.extend_from_slice(sbytes);
            sled::IVec::from(out)
        }
    }
}

fn decode_se1_val(raw: &sled::IVec) -> SE1Val {
    let tbyte = raw[0];
    if tbyte == 0x10 {
        let raw_bytes = raw[1..].to_vec();
        // We trust that all strings *inside* the db are well-formed utf8, because we validate it
        // on insert; hence no need to double-check on the way back out.
        unsafe {
            SE1Val::String(String::from_utf8_unchecked(raw_bytes))
        }
    } else {
        panic!("..")
    }
}

const SK_RELTYPE: u8 = 0x01;
const SK_LABEL: u8 = 0x02;
const SK_PROPK: u8 = 0x03;
const SK_RELTYPE_IDGEN: u8 = 0x04;
const SK_LABEL_IDGEN: u8 = 0x05;
const SK_PROPK_IDGEN: u8 = 0x05;

fn encode_tokenkey(sk_type: u8, name: &[u8]) -> sled::IVec {
    let mut out = Vec::with_capacity(name.len() + 1);
    out.push(sk_type);
    out.extend_from_slice(name);
    return sled::IVec::from(out)
}

fn encode_schemakey_lbl(name: &[u8]) -> sled::IVec {
    let mut out = Vec::with_capacity(name.len() + 1);
    out[0] = SK_LABEL;
    out[1..].copy_from_slice(name);
    return sled::IVec::from(out)
}

fn encode_node_lblkey(node: u64, label: u32) -> sled::IVec {
    let mut out = [0 as u8; 4 + 8];
    BigEndian::write_u32(&mut out[0..4], label);
    LittleEndian::write_u64(&mut out[4..4+8], node);
    sled::IVec::from(&out)
}

fn encode_node_lblkey_range(label: u32) -> (sled::IVec, sled::IVec) {
    let mut start = [0 as u8; 4];
    BigEndian::write_u32(&mut start, label);
    let mut end = [0 as u8; 7];
    BigEndian::write_u32(&mut end, label + 1);
    (sled::IVec::from(&start), sled::IVec::from(&end))
}

fn decode_node_from_node_lblkey(raw: &[u8]) -> u64 {
    LittleEndian::read_u64(&raw[4..])
}

pub struct NodeScan {
    inner: sled::Iter,
}

impl Iterator for NodeScan {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(item) => {
                let (key, _) = item.unwrap();
                Some(decode_node_from_node_lblkey(key.as_bytes()))
            }
        }
    }
}

#[derive(Debug)]
pub struct Rel {
    rt: u16,
    other: u64,
}

pub struct RelIter {
    inner: sled::Iter,
}

impl Iterator for RelIter {
    type Item = Rel;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(relkey) => {
                let (key, _) = relkey.unwrap();
                Some(decode_rel_from_relkey(key.as_bytes()))
            }
        }
    }
}

pub struct SE1 {
    db: sled::Db,
    nodes: sled::Tree,
    rels: sled::Tree,

    labels: sled::Tree,

    schema: sled::Tree,
}

impl SE1 {
    pub fn new() -> Self {
        let db: sled::Db = sled::Config::new()
            .cache_capacity(1024 * 1024 * 64)
            .temporary(true)
            // .path("./hmm.db")
            .open().unwrap();

        let nodes = db.open_tree("nodes.1").unwrap();
        let rels = db.open_tree("rels.1").unwrap();
        let labels = db.open_tree("labels.1").unwrap();
        let schema = db.open_tree("schema.1").unwrap();
        Self {
            db,
            nodes,
            rels,
            schema,
            labels,
        }
    }
    pub fn node_create(&mut self, labels: &[u32]) -> u64 {
        let id = self.db.generate_id().unwrap();
        for lbl in labels {
            let key = encode_node_lblkey(id, *lbl);
            self.labels.insert(key, &[]);
        }
        id
    }

    pub fn node_scan(&mut self, label: u32) -> NodeScan {
        let (start, end) = encode_node_lblkey_range(label);
        NodeScan {
            inner: self.labels.range(start..end),
        }
    }

    pub fn node_prop_set(&mut self, node: u64, key: u32, val: SE1Val) {
        self.nodes.insert(encode_node_propkey(node, key), encode_se1_val(&val));
    }

    pub fn node_prop_get(&mut self, node: u64, key: u32) -> Option<SE1Val> {
        match self.nodes.get(encode_node_propkey(node, key)).unwrap() {
            None => None,
            Some(raw) => {
                Some(decode_se1_val(&raw))
            }
        }
    }

    pub fn rel_create(&mut self, from: u64, to: u64, rt: u16) {
        let res: TransactionResult<()> = self.rels.transaction(|tx| {
            let ob_key = encode_relkey(from, to, rt);
            let ib_key = encode_relkey(to, from, rt);
            tx.insert(ob_key, &[]).unwrap();
            tx.insert(ib_key, &[]).unwrap();
            Ok(())
        });
        res.unwrap();
    }

    pub fn rel_scan(&self, node: u64, rt: u16) -> RelIter {
        let (start, end) = encode_relkey_range(node, rt);
        RelIter {
            inner: self.rels.range(start..end),
        }
    }

    pub fn rt_get_or_create(&mut self, name: &[u8]) -> u16 {
        self.tok_get_or_create(encode_tokenkey(SK_RELTYPE, name), &[SK_RELTYPE_IDGEN]) as u16
    }

    pub fn propk_get_or_create(&mut self, name: &[u8]) -> u32 {
        self.tok_get_or_create(encode_tokenkey(SK_PROPK, name), &[SK_PROPK_IDGEN]) as u32
    }

    pub fn lbl_get_or_create(&mut self, name: &[u8]) -> u32 {
        self.tok_get_or_create(encode_tokenkey(SK_LABEL, name), &[SK_LABEL_IDGEN]) as u32
    }

    fn tok_get_or_create(&mut self, key: sled::IVec, idgen_key: &[u8]) -> u32 {
        fn decode_tok_id(raw: &[u8]) -> u32 {
            let intermediate: [u8;4] = raw.try_into().unwrap();
            u32::from_be_bytes(intermediate)
        }
        fn encode_tok_id(rtid: u32) -> sled::IVec {
            sled::IVec::from(rtid.to_be_bytes().as_bytes())
        }

        // Check if the rel type exists already
        if let Some(raw) = self.schema.get(&key).unwrap() {
            return decode_tok_id(raw.as_bytes())
        }

        // Alloc an id for it
        let rtid = decode_tok_id(
            self.schema.update_and_fetch(idgen_key, |current_rtid| {
                if current_rtid.is_none() {
                    let zero: u32 = 0;
                    return Some(sled::IVec::from(zero.to_be_bytes().as_bytes()))
                }
                let mut rtid = decode_tok_id(current_rtid.unwrap().as_bytes());
                rtid += 1;
                Some(encode_tok_id(rtid))
            }).unwrap().unwrap().as_bytes()
        );

        let empty: Option<&[u8]> = None;
        match self.schema.compare_and_swap(key, empty, Some(encode_tok_id(rtid))).unwrap() {
            Ok(_) => return rtid,
            Err(cas_err) => {
                return decode_tok_id(cas_err.current.unwrap().as_bytes())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryInto;
    use {
        byteorder::{BigEndian, LittleEndian},
        zerocopy::{
            byteorder::U64, AsBytes, FromBytes, LayoutVerified, Unaligned, U16, U32,
        },
    };
    use super::*;

    #[derive(FromBytes, AsBytes, Unaligned)]
    #[repr(C)]
    struct Key {
        a: U64<BigEndian>,
        b: U64<BigEndian>,
    }

    #[derive(FromBytes, AsBytes, Unaligned)]
    #[repr(C)]
    struct Value {
        count: U64<LittleEndian>,
        whatever: [u8; 16],
    }

    #[test]
    fn hmm() {


        let db: sled::Db = sled::open("db").unwrap();


        let key = Key { a: U64::new(21), b: U64::new(890) };


        db.insert(key.as_bytes(), sled::IVec::from(
            Value{
                count: U64::new(0x1337),
                whatever: [0;16],
            }.as_bytes()
        )).unwrap();
        assert_eq!(&db.get(key.as_bytes()).unwrap().unwrap(), Value{
            count: U64::new(0x1337),
            whatever: [0;16],
        }.as_bytes());
    }

    fn mkengine() -> SE1 {
        let db: sled::Db = sled::Config::new().cache_capacity(1024 * 1024 * 16).temporary(true).open().unwrap();

        let nodes = db.open_tree("nodes.1").unwrap();
        let rels = db.open_tree("rels.1").unwrap();
        let labels = db.open_tree("labels.1").unwrap();
        let schema = db.open_tree("schema.1").unwrap();
        SE1 {
            db,
            nodes,
            rels,
            schema,
            labels,
        }
    }

    #[test]
    fn hmm2() {
        let mut engine = mkengine();

        let p1 = engine.node_create(&[]);
        let p2 = engine.node_create(&[]);

        let rt_knows = engine.rt_get_or_create(b"KNOWS");
        let pk_name = engine.propk_get_or_create(b"name");

        engine.rel_create(p1, p2, rt_knows);

        engine.node_prop_set(p1, pk_name, SE1Val::String("hello".to_string()));

        let p1knows = engine.rel_scan(p1, rt_knows);
        for r in p1knows {
            println!("p1({}) {:?}", p1, r)
        }

        println!("{:?}", engine.node_prop_get(p1, pk_name));
        println!("{:?}", engine.node_prop_get(p2, pk_name));
    }

    #[test]
    fn ldbc() {
        use ldbc_populator;
        let mut engine = mkengine();
        let rt_is_part_of = engine.rt_get_or_create(b"IS_PART_OF");
        let propk_name = engine.propk_get_or_create(b"name");
        let lbl_continent = engine.lbl_get_or_create(b"Continent");

        ldbc_populator::populate(&mut engine, 1);

        for node in engine.node_scan(lbl_continent) {
            println!("{} name={:?}", node, engine.node_prop_get(node, propk_name));
            for country in engine.rel_scan(node, rt_is_part_of) {
                println!("  {} name={:?}", country.other, engine.node_prop_get(country.other, propk_name));
                for city_rel in engine.rel_scan(country.other, rt_is_part_of) {
                    println!("    {} name={:?}", city_rel.other, engine.node_prop_get(city_rel.other, propk_name));
                }
            }
        }

        println!("nodes={}, size={}", engine.db.generate_id().unwrap(), engine.db.size_on_disk().unwrap() / 1024);


    }

}