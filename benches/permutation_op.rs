//! Benchmark: `Permutation::op` at sizes that span puzzle scale.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use groups::permutation::Permutation;
use groups::Magma;
use rand::SeedableRng;
use rand::rngs::StdRng;
use std::hint::black_box;

fn bench_op(c: &mut Criterion) {
    let mut group = c.benchmark_group("permutation_op");
    let mut rng = StdRng::seed_from_u64(0xc0ffee);

    macro_rules! bench_at {
        ($n:literal) => {{
            let a = Permutation::<$n>::random_with(&mut rng);
            let b = Permutation::<$n>::random_with(&mut rng);
            group.bench_with_input(BenchmarkId::from_parameter($n), &(a, b), |bch, (a, b)| {
                bch.iter(|| black_box(a).op(black_box(b)))
            });
        }};
    }

    bench_at!(8);    // cube corner perm
    bench_at!(12);   // cube edge perm
    bench_at!(24);   // cube corner stickers
    bench_at!(48);   // cube full sticker
    bench_at!(96);   // 7x7 perm-position scale

    group.finish();
}

criterion_group!(benches, bench_op);
criterion_main!(benches);
