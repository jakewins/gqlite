use criterion::{black_box, criterion_group, criterion_main, Criterion};
use gqlite::frontend::{Frontend, LogicalPlan};
use gqlite::Result;
use gqlite::backend::BackendDesc;
use std::cell::RefCell;
use std::rc::Rc;

fn criterion_benchmark(c: &mut Criterion) {
    let f = Frontend{
        tokens: Rc::new(RefCell::new(Default::default())),
        backend_desc: BackendDesc { functions: vec![], aggregates: Default::default() }
    };

    c.bench_function("LDBC_IC2", |b| b.iter(|| f.plan(
        black_box("MATCH (:Person {id:1})-[:KNOWS]-(friend),
      (friend)<-[:HAS_CREATOR]-(message)
WHERE message.creationDate = date({year: 2010, month:10, day:10})
RETURN friend.id AS personId,
       friend.firstName AS personFirstName,
       friend.lastName AS personLastName,
       message.id AS messageId,
       coalesce(message.content, message.imageFile) AS messageContent,
       message.creationDate AS messageDate
ORDER BY messageDate DESC, messageId ASC
LIMIT 20
"))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
