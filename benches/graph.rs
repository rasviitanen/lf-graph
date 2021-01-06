use criterion::{black_box, criterion_group, criterion_main, Criterion};
use hypergraph::Graph;
use std::collections::HashMap;
use std::sync::RwLock;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("hypergraph-add-vertex", |b| {
        b.iter(|| {
            let graph = Graph::<u32, u32, u32>::new();
            for i in 0..100 {
                graph.add_vertex(black_box(i), 123);
            }
        })
    });

    c.bench_function("hashmap-add-vertex", |b| {
        b.iter(|| {
            let graph = RwLock::new(HashMap::new());
            for i in 0..100 {
                graph.write().unwrap().insert(black_box(i), 123);
            }
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);