//! Benchmark: `WreathProduct::op` at cube-corner and cube-edge scale.

use criterion::{criterion_group, criterion_main, Criterion};
use groups::cyclic::Cyclic;
use groups::permutation::Permutation;
use groups::product::WreathProduct;
use groups::Magma;
use rand::SeedableRng;
use rand::rngs::StdRng;
use std::hint::black_box;

fn random_wreath<const N: usize, R: rand::Rng + ?Sized, const M: usize>(
    rng: &mut R,
) -> WreathProduct<Cyclic<M>, N> {
    let mut fibers = [Cyclic::<M>::from_index(0); N];
    for f in fibers.iter_mut() {
        *f = Cyclic::<M>::random_with(rng);
    }
    WreathProduct::new(fibers, Permutation::<N>::random_with(rng))
}

fn bench_op(c: &mut Criterion) {
    let mut g = c.benchmark_group("wreath_op");
    let mut rng = StdRng::seed_from_u64(0xc0ffee);

    // Cube corners: C₃ ≀ S₈
    let a8: WreathProduct<Cyclic<3>, 8> = random_wreath(&mut rng);
    let b8: WreathProduct<Cyclic<3>, 8> = random_wreath(&mut rng);
    g.bench_function("C3_wr_S8 (cube corners)", |bch| {
        bch.iter(|| black_box(a8).op(black_box(&b8)))
    });

    // Cube edges: C₂ ≀ S₁₂
    let a12: WreathProduct<Cyclic<2>, 12> = random_wreath(&mut rng);
    let b12: WreathProduct<Cyclic<2>, 12> = random_wreath(&mut rng);
    g.bench_function("C2_wr_S12 (cube edges)", |bch| {
        bch.iter(|| black_box(a12).op(black_box(&b12)))
    });

    g.finish();
}

criterion_group!(benches, bench_op);
criterion_main!(benches);
