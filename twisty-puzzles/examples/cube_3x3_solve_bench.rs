//! Solve-time benchmark across scramble lengths.
//!
//! Measures `find_algorithm` end-to-end solve time and solution length for
//! random scrambles at varying depths. The current solver is bounded BFS
//! over the Cayley graph filtered by a full-state-pin partial state, with
//! an explicit max_depth cap. Honest about where it breaks.
//!
//! Run with: `cargo run --release -p twisty-puzzles --example cube_3x3_solve_bench`

use rand::seq::SliceRandom;
use rand::SeedableRng;

use groups::Monoid;
use twisty_puzzles::cube::cube_3x3 as core;
use twisty_puzzles::cube::cube_3x3_iface::{
    find_algorithm_max_depth, Algorithm, CubeBsgs, CubeQuery, Move,
};

fn main() {
    println!("=== 3×3 solve-time benchmark ===\n");
    println!("Reference target: 55 ms average, 30 moves average.\n");

    let cube = CubeBsgs::build_qtm();
    let full_pin = full_solved_query();

    // (depth, trials, max_bfs_depth) — at higher depths we run fewer trials
    // because BFS gets exponentially slower.
    let bench_plan: &[(usize, usize, u32)] = &[
        (1, 20, 3),
        (2, 20, 4),
        (3, 20, 5),
        (4, 20, 6),
        (5, 20, 7),
        (6, 5, 8),
    ];

    println!(
        "{:>10}  {:>10}  {:>10}  {:>14}  {:>14}",
        "scramble", "trials", "solved", "avg solve ms", "avg sol len"
    );
    println!("{}", "-".repeat(64));

    for &(depth, trials, bfs_depth_budget) in bench_plan {
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xc0ffee + depth as u64);
        let mut total_ms = 0u128;
        let mut total_len = 0usize;
        let mut solved_count = 0;

        for _ in 0..trials {
            let scramble = make_scramble(&mut rng, depth);
            let scrambled = scramble.apply_to(&core::Cube3x3State::identity());
            let t0 = std::time::Instant::now();
            let result = find_algorithm_max_depth(&cube, &scrambled, &full_pin, bfs_depth_budget);
            let elapsed = t0.elapsed();
            total_ms += elapsed.as_millis();
            if let Some(alg) = result {
                let after = alg.apply_to(&scrambled);
                if after == core::Cube3x3State::identity() {
                    solved_count += 1;
                    total_len += alg.len();
                }
            }
        }

        let avg_ms = total_ms as f64 / trials as f64;
        let avg_len = if solved_count > 0 {
            total_len as f64 / solved_count as f64
        } else {
            0.0
        };
        println!(
            "{:>8}m  {:>10}  {:>10}  {:>11.1} ms  {:>11.1} mv",
            depth, trials, solved_count, avg_ms, avg_len
        );
    }

    println!();
    println!("Where this breaks:");
    println!("  BFS visits ~11^d states at depth d. Memory and time both");
    println!("  blow up around d=10. Random 3×3 scrambles need optimal solve");
    println!("  depth 17-20 QTM, which is intractable for plain BFS.");
    println!();
    println!("To hit the 55 ms / 30-move target on random scrambles, the");
    println!("library needs one of the standard cube-solving algorithm tiers:");
    println!("  - Korf's IDA* with corner+edge pattern databases (~1 GB, optimal)");
    println!("  - Kociemba's two-phase algorithm (~50-100 MB tables, ~20 moves)");
    println!("  - Thistlethwaite's 4-phase (~10 MB tables, ~30-50 moves)");
    println!("  - CFOP with hand-coded OLL+PLL tables (~50-70 moves, no SS needed)");
    println!();
    println!("Each fits cleanly on top of the existing `groups::solver::Heuristic`");
    println!("trait surface — but the heuristic + tables are the work.");
}

fn make_scramble<R: rand::Rng>(rng: &mut R, len: usize) -> Algorithm {
    let mut moves: Vec<Move> = Vec::with_capacity(len);
    let mut last: Option<Move> = None;
    for _ in 0..len {
        loop {
            let m = *Move::ALL.choose(rng).unwrap();
            if let Some(l) = last {
                if m == l.inverse() {
                    continue;
                }
            }
            moves.push(m);
            last = Some(m);
            break;
        }
    }
    Algorithm(moves)
}

fn full_solved_query() -> CubeQuery {
    let mut q = CubeQuery::new();
    for c in 0..8 {
        q = q.pin_corner_solved(c);
    }
    for e in 0..12 {
        q = q.pin_edge_solved(e);
    }
    q
}
