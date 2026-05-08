//! Benchmark: deterministic Schreier–Sims chain construction across a range
//! of permutation groups.
//!
//! Future Monte Carlo and Las Vegas variants will be added here for
//! head-to-head comparison once implemented.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use groups::generators::GeneratingSet;
use groups::permutation::Permutation;
use groups::schreier_sims::deterministic::deterministic;
use std::hint::black_box;

fn s_n_adjacent_transpositions<const N: usize>() -> GeneratingSet<Permutation<N>> {
    let gens: Vec<Permutation<N>> = (0..N - 1)
        .map(|i| Permutation::<N>::transposition(i, i + 1))
        .collect();
    GeneratingSet::with_inverses(gens)
}

fn bench_sn(c: &mut Criterion) {
    let mut g = c.benchmark_group("schreier_sims_deterministic_S_n");

    macro_rules! bench_sn {
        ($n:literal) => {{
            let gens = s_n_adjacent_transpositions::<$n>();
            let base: Vec<u16> = (0..($n - 1) as u16).collect();
            g.bench_with_input(BenchmarkId::from_parameter($n), &(gens, base), |bch, (gens, base)| {
                bch.iter(|| {
                    let bsgs = deterministic::<_, $n>(black_box(gens), black_box(base));
                    black_box(bsgs.order())
                })
            });
        }};
    }

    bench_sn!(4);
    bench_sn!(5);
    bench_sn!(6);
    bench_sn!(7);
    bench_sn!(8);

    g.finish();
}

criterion_group!(benches, bench_sn);
criterion_main!(benches);
