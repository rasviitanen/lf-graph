use criterion::{black_box, criterion_group, criterion_main, Criterion};
use hypergraph::Graph;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| {
        
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);