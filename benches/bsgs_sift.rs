//! Benchmark: BSGS sift / membership testing — the inner loop of every
//! downstream query.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use groups::generators::GeneratingSet;
use groups::permutation::Permutation;
use groups::schreier_sims::deterministic::deterministic;
use rand::SeedableRng;
use rand::rngs::StdRng;
use std::hint::black_box;

fn bench_sift(c: &mut Criterion) {
    let mut g = c.benchmark_group("bsgs_sift_S_n");
    let mut rng = StdRng::seed_from_u64(0x5117);

    macro_rules! bench_sift_at {
        ($n:literal) => {{
            let gens_vec: Vec<Permutation<$n>> = (0..($n - 1))
                .map(|i| Permutation::<$n>::transposition(i, i + 1))
                .collect();
            let gens = GeneratingSet::with_inverses(gens_vec);
            let base: Vec<u16> = (0..($n - 1) as u16).collect();
            let bsgs = deterministic::<_, $n>(&gens, &base);

            // Sample a random in-group element to sift.
            let target = Permutation::<$n>::random_with(&mut rng);

            g.bench_with_input(BenchmarkId::from_parameter($n), &(bsgs, target), |bch, (bsgs, target)| {
                bch.iter(|| black_box(bsgs).sift(black_box(target)))
            });
        }};
    }

    bench_sift_at!(4);
    bench_sift_at!(5);
    bench_sift_at!(6);
    bench_sift_at!(7);
    bench_sift_at!(8);

    g.finish();
}

criterion_group!(benches, bench_sift);
criterion_main!(benches);
