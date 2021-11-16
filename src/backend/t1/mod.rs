mod ldbc_populator;

use std::collections::HashMap;
use std::convert::TryInto;
use std::ops::{Add, Sub};
use std::time::{Duration, Instant};
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
use rocksdb::{DB, Options, ColumnFamilyDescriptor, BlockBasedOptions, Cache};

pub fn run() {
    use ldbc_populator;
    let mut engine = SE1::new();
    let rt_is_part_of = engine.rt_get_or_create(b"IS_PART_OF");
    let propk_name = engine.propk_get_or_create(b"name");
    let lbl_continent = engine.lbl_get_or_create(b"Continent");
    let lbl_country = engine.lbl_get_or_create(b"Country");

    let mut random = SmallRng::seed_from_u64(1337);
    let degree:u64 = 20;

    let total_rels: u64 = 2_000_000;
    let total_nodes: u64 = (total_rels / degree) / 2;

    // Create dataset in 14 seconds
    // Degree=20
    // Expanded 324312 random nodes in 10 secs / 25922880 rels seen, hash is 648322698218
    // Maximum resident set size (kbytes): 81280

    // Create dataset in 13 seconds
    // Degree=10
    // Expanded 409257 random nodes in 10 secs / 16365954 rels seen, hash is 818369521158

    // Create dataset in 13 seconds
    // Degree=1
    // Expanded 539012 random nodes in 10 secs / 2155466 rels seen, hash is 1077726210307
    // Maximum resident set size (kbytes): 81556

    let start = Instant::now();

    for i in 0..total_nodes {
        engine.node_create(&[]);
    }

    for i in 0..total_rels {
        let start: u64 = random.gen_range(0, total_nodes);
        let end: u64 = random.gen_range(0, total_nodes);
        engine.rel_create(start, end, rt_is_part_of);

        if i % 10_000 == 0 {
            println!("{} / {} rels", i, total_rels)
        }
    }

    let delta = Instant::now().sub(start).as_secs();

    println!("Create dataset in {} seconds", delta);
    println!("Degree={}", degree);

    let mut nodes_seen: u64 = 0;
    let mut rels_seen: u64 = 0;
    let mut hash: u64 = 0;
    let deadline = Instant::now().add(Duration::from_secs(10));
    while Instant::now() < deadline {
        // let random_node : u64 = random.gen_range(0, 1_000_000);
        let rand_node: u64 = random.gen_range(0, total_nodes);
        nodes_seen += 1;
        for rel in engine.rel_scan(rand_node, rt_is_part_of) {
            hash += rel.other;
            rels_seen += 1;
        }
    }
    println!("Expanded {} random nodes in 10 secs / {} rels seen, hash is {}", nodes_seen, rels_seen, hash);
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

pub struct NodeScan<'a> {
    inner: rocksdb::DBIterator<'a>,
    end: sled::IVec,
}

impl<'a> Iterator for NodeScan<'a> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(kvb) => {
                let key = kvb.0;
                if !(key.as_bytes()).lt(self.end.as_bytes()) {
                    return None
                }
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

pub struct RelIter<'a> {
    inner: rocksdb::DBIterator<'a>,
    end: sled::IVec,
}

impl<'a> Iterator for RelIter<'a> {
    type Item = Rel;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(kvb) => {
                let key = kvb.0;
                if !(key.as_bytes()).lt(self.end.as_bytes()) {
                    return None
                }
                Some(decode_rel_from_relkey(&key))
            }
        }
    }
}

pub struct SE1 {
    idgen: u64,
    schema_idgen: u32,

    db: rocksdb::DB,
}

impl SE1 {
    pub fn new() -> Self {
        // let db: sled::Db = sled::Config::new()
        //     .cache_capacity(1024 * 1024 * 64)
        //     .temporary(true)
        //     // .path("./hmm.db")
        //     .open().unwrap();

        let path = "rocks.db";
        let cf_nodes = ColumnFamilyDescriptor::new("nodes.1", Options::default());
        let cf_rels = ColumnFamilyDescriptor::new("rels.1", Options::default());
        let cf_schema = ColumnFamilyDescriptor::new("schema.1", Options::default());
        let cf_labels = ColumnFamilyDescriptor::new("labels.1", Options::default());

        let mut block_opts = BlockBasedOptions::default();
        let block_cache = Cache::new_lru_cache(1024 * 1024 * 64).unwrap();

        block_opts.set_block_cache(&block_cache);
        let mut db_opts = Options::default();

        db_opts.create_missing_column_families(true);
        db_opts.create_if_missing(true);
        db_opts.set_block_based_table_factory(&block_opts);
        // delta=11 secs
        // Expanded random nodes in 19 secs / 121024830 rels seen, hash is 81268423432147
        let db = DB::open_cf_descriptors(&db_opts, path, vec![
            cf_nodes, cf_rels, cf_schema, cf_labels]).unwrap();

        Self {
            idgen: 0,
            schema_idgen: 0,
            db,
        }
    }

    pub fn max_node_id(&self) -> u64 {
        self.idgen
    }

    pub fn node_create(&mut self, labels: &[u32]) -> u64 {
        let id = self.idgen;
        self.idgen += 1;
        for lbl in labels {
            let key = encode_node_lblkey(id, *lbl);
            self.db.put_cf(self.db.cf_handle("labels.1").unwrap(), key, &[]);
        }
        id
    }

    pub fn node_scan(&mut self, label: u32) -> NodeScan {
        let (start, end) = encode_node_lblkey_range(label);
        let iter = self.db.full_iterator_cf(self.db.cf_handle("labels.1").unwrap(), rocksdb::IteratorMode::From(&start, rocksdb::Direction::Forward));
        NodeScan {
            inner: iter,
            end
        }
    }

    pub fn node_prop_set(&mut self, node: u64, key: u32, val: SE1Val) {
        self.db.put_cf(self.db.cf_handle("nodes.1").unwrap(), encode_node_propkey(node, key), encode_se1_val(&val));
    }

    pub fn node_prop_get(&mut self, node: u64, key: u32) -> Option<SE1Val> {
        todo!()
    }

    pub fn rel_create(&mut self, from: u64, to: u64, rt: u16) {
        let ob_key = encode_relkey(from, to, rt);
        let ib_key = encode_relkey(to, from, rt);
        self.db.put(ob_key, &[]).unwrap();
        self.db.put(ib_key, &[]).unwrap();
    }

    pub fn rel_scan(&self, node: u64, rt: u16) -> RelIter {
        let (start, end) = encode_relkey_range(node, rt);
        let iter = self.db.full_iterator( rocksdb::IteratorMode::From(&start, rocksdb::Direction::Forward));
        RelIter {
            inner: iter,
            end,
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
        if let Some(raw) = self.db.get_cf(self.db.cf_handle("schema.1").unwrap(), &key).unwrap() {
            return decode_tok_id(raw.as_bytes())
        }

        // Alloc an id for it
        let rtid = self.schema_idgen;
        self.schema_idgen += 1;

        let empty: Option<&[u8]> = None;
        // Can't figure out how merge is surfaced here.. yolo it
        self.db.put_cf(self.db.cf_handle("schema.1").unwrap(), key, &encode_tok_id(rtid));
        rtid
        // match self.schema.compare_and_swap(key, empty, Some(encode_tok_id(rtid))).unwrap() {
        //     Ok(_) => return rtid,
        //     Err(cas_err) => {
        //         return decode_tok_id(cas_err.current.unwrap().as_bytes())
        //     }
        // }
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

    #[test]
    fn hmm2() {
        let mut engine = SE1::new();

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
        let mut engine = SE1::new();
        let rt_is_part_of = engine.rt_get_or_create(b"IS_PART_OF");
        let propk_name = engine.propk_get_or_create(b"name");
        let lbl_continent = engine.lbl_get_or_create(b"Continent");

        ldbc_populator::populate(&mut engine, 1);

    }

}