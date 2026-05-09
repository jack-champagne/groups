//! End-to-end solve for short scrambles via full-state pinning.
//!
//! Generates a random scramble (capped to a few moves so plain BFS
//! finishes), then asks `find_algorithm` for the inverse algorithm by
//! pinning every cubie to its solved position. This is the genuine
//! end-to-end use case for the partial-state machinery.
//!
//! For longer scrambles you'd want Thistlethwaite, Kociemba, or Korf —
//! see `cube_3x3_solve_bench` for the cliff and the README for status.
//!
//! Pinning *progressively* during a solve isn't actually how solving
//! works (real layer-by-layer methods like CFOP use known algorithm
//! tables, not partial-state BFS); the pinning machinery is for
//! **algorithm exploration**, not solving. See `cube_3x3_queries`.
//!
//! Run with: `cargo run --release -p twisty-puzzles --example cube_3x3_solve`

use rand::seq::SliceRandom;
use rand::SeedableRng;

use groups::Monoid;
use twisty_puzzles::cube::cube_3x3 as core;
use twisty_puzzles::cube::cube_3x3_iface::{
    find_algorithm, Algorithm, CubeBsgs, CubeQuery, Move,
};

fn main() {
    println!("=== 3×3 end-to-end solve (short scramble) ===\n");

    let cube = CubeBsgs::build_qtm();
    println!("BSGS built. |G| = {}\n", cube.order());

    let mut rng = rand::rngs::StdRng::seed_from_u64(0xc0ffee_42);
    let scramble_len = 5;
    let scramble = make_scramble(&mut rng, scramble_len);
    let solved = core::Cube3x3State::identity();
    let scrambled = scramble.apply_to(&solved);
    println!("Scramble:  {scramble}  ({} moves)", scramble.len());
    println!("In group:  {}\n", cube.is_solvable(&scrambled));

    let full_pin = full_solved_query();
    let t0 = std::time::Instant::now();
    let solve = find_algorithm(&cube, &scrambled, &full_pin)
        .expect("BFS finds a solve for short scrambles");
    let solve_ms = t0.elapsed().as_millis();
    println!("Solve:     {solve}  ({} moves, {solve_ms} ms)", solve.len());
    let after = solve.apply_to(&scrambled);
    println!(
        "Result:    {}\n",
        if after == solved { "solved ✓" } else { "FAILED" }
    );

    println!("Notes:");
    println!("  • This is bounded BFS over the Cayley graph filtered by");
    println!("    a full-state-pin partial state. Works for short scrambles");
    println!("    (≤6 moves comfortably). For longer scrambles see");
    println!("    `cube_3x3_solve_bench` for the timing cliff.");
    println!("  • For real-world solving (17–20 move scrambles in ~50 ms)");
    println!("    you'd want Thistlethwaite or Kociemba — both fit on top");
    println!("    of `groups::solver::Heuristic` but aren't implemented yet.");
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
