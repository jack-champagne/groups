//! Cross-puzzle benchmarks: state composition (`op`), sticker-perm
//! conversion, and Schreier-Sims `|G|` validation across all WCA-recognized
//! puzzles modeled in this crate.

use criterion::{criterion_group, criterion_main, Criterion};
use groups::generators::GeneratingSet;
use groups::schreier_sims::deterministic::deterministic;
use groups::Magma;
use std::hint::black_box;

use twisty_puzzles::cube::cube_2x2;
use twisty_puzzles::cube::cube_3x3;
use twisty_puzzles::pyraminx;
use twisty_puzzles::skewb;

fn bench_op(c: &mut Criterion) {
    let mut g = c.benchmark_group("state_op");

    {
        let a = cube_2x2::r();
        let b = cube_2x2::u();
        g.bench_function("2x2 op", |bch| bch.iter(|| black_box(a).op(black_box(&b))));
    }
    {
        let a = cube_3x3::r();
        let b = cube_3x3::u();
        g.bench_function("3x3 op", |bch| bch.iter(|| black_box(a).op(black_box(&b))));
    }
    {
        let a = pyraminx::u();
        let b = pyraminx::l();
        g.bench_function("pyraminx op", |bch| bch.iter(|| black_box(a).op(black_box(&b))));
    }
    {
        let a = skewb::u();
        let b = skewb::l();
        g.bench_function("skewb op", |bch| bch.iter(|| black_box(a).op(black_box(&b))));
    }

    g.finish();
}

fn bench_sticker_conversion(c: &mut Criterion) {
    let mut g = c.benchmark_group("to_sticker_perm");

    {
        let s = cube_2x2::r();
        g.bench_function("2x2", |bch| bch.iter(|| cube_2x2::to_sticker_perm(black_box(&s))));
    }
    {
        let s = cube_3x3::r();
        g.bench_function("3x3", |bch| bch.iter(|| cube_3x3::to_sticker_perm(black_box(&s))));
    }
    {
        let s = pyraminx::u();
        g.bench_function("pyraminx", |bch| bch.iter(|| pyraminx::to_sticker_perm(black_box(&s))));
    }
    {
        let s = skewb::u();
        g.bench_function("skewb", |bch| bch.iter(|| skewb::to_sticker_perm(black_box(&s))));
    }

    g.finish();
}

fn bench_ss_validation(c: &mut Criterion) {
    let mut g = c.benchmark_group("schreier_sims_|G|_validation");
    g.sample_size(10); // these are slow

    {
        let gens = GeneratingSet::with_inverses([
            cube_2x2::to_sticker_perm(&cube_2x2::r()),
            cube_2x2::to_sticker_perm(&cube_2x2::u()),
            cube_2x2::to_sticker_perm(&cube_2x2::f()),
        ]);
        let base: Vec<u16> = (0..8).map(|i| 3 * i).collect();
        g.bench_function("2x2 (|G|=3.7M)", |bch| {
            bch.iter(|| {
                let bsgs = deterministic::<_, { cube_2x2::N_STICKERS }>(black_box(&gens), black_box(&base));
                black_box(bsgs.order())
            })
        });
    }

    {
        let gens = GeneratingSet::with_inverses(cube_3x3::face_move_sticker_perms());
        let base: Vec<u16> = vec![
            0, 3, 6, 9, 12, 15, 18, 21, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46,
        ];
        g.bench_function("3x3 (|G|=43.3 quintillion)", |bch| {
            bch.iter(|| {
                let bsgs = deterministic::<_, { cube_3x3::N_STICKERS }>(black_box(&gens), black_box(&base));
                black_box(bsgs.order())
            })
        });
    }

    {
        let gens = GeneratingSet::with_inverses(pyraminx::face_move_sticker_perms());
        let base: Vec<u16> = vec![0, 3, 6, 9, 12, 14, 16, 18, 20, 22];
        g.bench_function("pyraminx (|G|=933K)", |bch| {
            bch.iter(|| {
                let bsgs = deterministic::<_, { pyraminx::N_STICKERS }>(black_box(&gens), black_box(&base));
                black_box(bsgs.order())
            })
        });
    }

    g.finish();
}

criterion_group!(benches, bench_op, bench_sticker_conversion, bench_ss_validation);
criterion_main!(benches);
