//! End-to-end scramble + progressive solve demo.
//!
//! Applies a small random scramble, then demonstrates two solving modes:
//!
//! 1. **End-to-end**: find a single algorithm that fully restores the cube
//!    by pinning every U-layer cubie + every D-layer cubie (i.e., the full
//!    solved state).
//!
//! 2. **Progressive (sticker-driven)**: at each step, read the current
//!    cube state, identify a specific cubie that's currently misplaced,
//!    and ask `find_algorithm` for moves that solve it *while keeping the
//!    previously-solved cubies in place*. This is exactly the capability
//!    the user described in the original library design ("specify
//!    constraints, find moves") — each step's `CubeQuery` accumulates pins
//!    on cubies already solved, plus one new cubie to position correctly.
//!
//! Run with: `cargo run --example cube_3x3_solve -p twisty-puzzles`
//!
//! ## Scope
//!
//! `find_algorithm` uses bounded BFS over the Cayley graph (depth ≤ 30
//! with HashMap dedup). For scrambles up to ~6 QTM moves the optimal
//! solve depth fits comfortably; for full-random scrambles (typical
//! optimal-solve depth ~17–20 QTM) BFS is intractable and the right tool
//! is IDA* with a pattern-database heuristic — out of scope here. So we
//! use a short, bounded scramble for the demo.

use rand::seq::SliceRandom;
use rand::SeedableRng;

use groups::Monoid;
use twisty_puzzles::cube::cube_3x3 as core;
use twisty_puzzles::cube::cube_3x3_iface::{
    find_algorithm, find_algorithm_max_depth, Algorithm, CubeBsgs, CubeQuery, Move,
};

fn main() {
    println!("=== 3×3 progressive solver demo ===\n");

    // Build BSGS once (~15 ms).
    let cube = CubeBsgs::build_qtm();

    // Pick a random short scramble.
    //
    // We keep the scramble small (≤4 moves) because `find_algorithm` uses
    // bounded BFS over the Cayley graph filtered by the constraint pattern.
    // BFS scales as `branching^depth` (~11^d after free-reduction pruning):
    // depth 5 visits ~150K states, depth 8 ~200M, depth 10 ~25B.
    //
    // For the progressive Mode 2 below, each accumulated pin makes the
    // constrained search deeper than the optimal end-to-end solve, so even
    // 5-move scrambles can leave later steps requiring ≥10-move searches.
    // Real cube solvers use IDA* + pattern-database heuristics (Korf 1997)
    // or Kociemba's two-phase decomposition; both out of scope for this
    // demo, but the trait surface is in place via `groups::solver`.
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xc0ffee_42);
    let scramble_len = 4;
    let scramble = make_scramble(&mut rng, scramble_len);
    let solved = core::Cube3x3State::identity();
    let scrambled = scramble.apply_to(&solved);
    println!("Scramble ({scramble_len} moves): {scramble}");
    println!("In group: {}\n", cube.is_solvable(&scrambled));

    // ============ Mode 1: end-to-end solve ============
    println!("--- Mode 1: end-to-end solve via full-state pin ---");
    let full_pin = full_solved_query();
    let start = std::time::Instant::now();
    let solve_alg = find_algorithm(&cube, &scrambled, &full_pin)
        .expect("BFS should find the solve for short scrambles");
    let solve_ms = start.elapsed().as_millis();
    println!(
        "Solve found in {solve_ms} ms: \"{solve_alg}\" ({} moves)",
        solve_alg.len()
    );
    let after = solve_alg.apply_to(&scrambled);
    println!(
        "Cube state matches solved: {}\n",
        after == solved
    );

    // ============ Mode 2: progressive pinning ============
    println!("--- Mode 2: progressive sticker-driven solve ---");
    println!("(At each step, read the current state, identify a cubie to");
    println!("place, and ask find_algorithm for moves that solve it while");
    println!("keeping all previously-solved cubies pinned.)\n");

    let mut state = scrambled;
    let mut cumulative = Algorithm::new();
    let mut pinned_corners: Vec<u8> = Vec::new();
    let mut pinned_edges: Vec<u8> = Vec::new();

    // Solve order: 4 U-layer corners (slots 0,1,2,3), then 4 U-layer edges
    // (slots 0,1,2,3), then D-layer.
    let solve_order: [(&str, Slot); 20] = [
        ("URF corner", Slot::Corner(0)),
        ("UFL corner", Slot::Corner(1)),
        ("ULB corner", Slot::Corner(2)),
        ("UBR corner", Slot::Corner(3)),
        ("UF edge",    Slot::Edge(0)),
        ("UL edge",    Slot::Edge(1)),
        ("UB edge",    Slot::Edge(2)),
        ("UR edge",    Slot::Edge(3)),
        ("FR edge",    Slot::Edge(4)),
        ("FL edge",    Slot::Edge(5)),
        ("BL edge",    Slot::Edge(6)),
        ("BR edge",    Slot::Edge(7)),
        ("DFR corner", Slot::Corner(4)),
        ("DLF corner", Slot::Corner(5)),
        ("DBL corner", Slot::Corner(6)),
        ("DRB corner", Slot::Corner(7)),
        ("DF edge",    Slot::Edge(8)),
        ("DL edge",    Slot::Edge(9)),
        ("DB edge",    Slot::Edge(10)),
        ("DR edge",    Slot::Edge(11)),
    ];

    for (name, slot) in solve_order {
        // Build query: pin all previously-solved + this new cubie.
        let mut query = CubeQuery::new();
        for &c in &pinned_corners {
            query = query.pin_corner_solved(c);
        }
        for &e in &pinned_edges {
            query = query.pin_edge_solved(e);
        }
        match slot {
            Slot::Corner(s) => query = query.pin_corner_solved(s),
            Slot::Edge(s) => query = query.pin_edge_solved(s),
        }

        // Use a bounded depth so failure-to-find returns quickly rather
        // than spending minutes on BFS that would never finish at this scale.
        let start = std::time::Instant::now();
        let result = find_algorithm_max_depth(&cube, &state, &query, 7);
        let ms = start.elapsed().as_millis();

        match result {
            Some(alg) => {
                println!(
                    "  {name:14} → \"{alg}\" ({} moves, {ms} ms)",
                    alg.len()
                );
                state = alg.apply_to(&state);
                cumulative.0.extend(alg.0);
                match slot {
                    Slot::Corner(s) => pinned_corners.push(s),
                    Slot::Edge(s) => pinned_edges.push(s),
                }
            }
            None => {
                println!(
                    "  {name:14} → BFS exceeded search budget; \
                     stopping progressive solve here."
                );
                break;
            }
        }
    }

    println!(
        "\nProgressive solve total: {} moves: {cumulative}",
        cumulative.len()
    );
    println!("State matches solved: {}", state == solved);

    // For comparison: Mode 1's end-to-end solve was {solve_alg.len()} moves.
    println!(
        "\n(End-to-end mode produced: {} moves — typically shorter,",
        solve_alg.len()
    );
    println!(
        "since Mode 2 pays the cost of preserving each pin while \
         solving the next.)"
    );
}

#[derive(Copy, Clone)]
enum Slot {
    Corner(u8),
    Edge(u8),
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
