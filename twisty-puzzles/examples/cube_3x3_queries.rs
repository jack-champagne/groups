//! Algorithm exploration via partial-state pinning.
//!
//! This is what the partial-state machinery is *for* — not solving (use
//! Thistlethwaite/Kociemba/Korf for that), but answering questions of
//! the form "find me a short algorithm that does X without disturbing Y."
//!
//! Each query below pins some cubies and lets others be wildcards, then
//! asks `find_algorithm` for moves satisfying the constraint. The BFS
//! depth budget is set per-query so unsatisfiable or far-away targets
//! return None quickly rather than hanging.
//!
//! Run with: `cargo run --release -p twisty-puzzles --example cube_3x3_queries`

use std::time::Instant;

use groups::Monoid;
use twisty_puzzles::cube::cube_3x3 as core;
use twisty_puzzles::cube::cube_3x3_iface::{
    corner_orbit, edge_orbit, find_algorithm_max_depth, Algorithm, CubeBsgs, CubeQuery, Move,
};

fn main() {
    println!("=== 3×3 algorithm exploration via partial-state pinning ===\n");

    let cube = CubeBsgs::build_qtm();
    println!("BSGS: |G| = {} (built once, reused).\n", cube.order());

    let solved = core::Cube3x3State::identity();

    // ------------- Orbit queries -------------
    println!("--- Orbit queries ---");
    println!(
        "  Corner 0 (URF) reaches under full QTM: {:?}",
        corner_orbit(&cube, 0)
    );
    println!(
        "  Edge 0 (UF) reaches under full QTM:    {:?}",
        edge_orbit(&cube, 0)
    );
    println!(
        "  Corner 5 (DLF) reaches:                {:?}",
        corner_orbit(&cube, 5)
    );
    println!();

    // ------------- Constraint search queries -------------
    println!("--- Constraint search queries (from solved) ---");
    println!("(Pinning some cubies, leaving the rest wildcard.)\n");

    run_query(
        &cube,
        &solved,
        "Move URF cubie to slot 4 (DFR), keep no other constraints",
        CubeQuery::new().pin_corner_at(4, 0, 0),
        6,
    );

    run_query(
        &cube,
        &solved,
        "Move UF edge cubie to slot 8 (DF), no other constraints",
        CubeQuery::new().pin_edge_at(8, 0, 0),
        6,
    );

    run_query(
        &cube,
        &solved,
        "Move URF to slot 4, AND keep UFL/ULB/UBR pinned in place",
        CubeQuery::new()
            .pin_corner_at(4, 0, 0)
            .pin_corner_solved(1)
            .pin_corner_solved(2)
            .pin_corner_solved(3),
        7,
    );

    run_query(
        &cube,
        &solved,
        "Cycle U-layer corners: URF→UFL→ULB→URF, UBR fixed",
        CubeQuery::new()
            .pin_corner_at(1, 0, 0) // URF cubie ends up at slot 1 (UFL position)
            .pin_corner_at(2, 1, 0) // UFL → slot 2 (ULB position)
            .pin_corner_at(0, 2, 0) // ULB → slot 0 (URF position)
            .pin_corner_solved(3), // UBR stays
        6, // capped: the actual alg is 8 moves; full search takes ~1 minute
    );

    // From a scrambled state — restore one specific cubie.
    println!("--- From a scrambled state ---");
    let scramble = Algorithm::from_moves([Move::R, Move::U, Move::Fp]);
    let scrambled = scramble.apply_to(&solved);
    println!("Applied scramble: {scramble}\n");

    run_query(
        &cube,
        &scrambled,
        "Restore URF to its solved position (no other constraints)",
        CubeQuery::new().pin_corner_solved(0),
        6,
    );

    run_query(
        &cube,
        &scrambled,
        "Restore URF AND UF edge to solved",
        CubeQuery::new().pin_corner_solved(0).pin_edge_solved(0),
        7,
    );

    // ------------- Restricted-move-set orbits -------------
    println!("--- Restricted move sets (build a smaller BSGS) ---");
    let ru_only = make_restricted(&[core::r(), core::u()]);
    println!(
        "  ⟨R, U⟩ orbit of URF: {:?}",
        corner_orbit(&ru_only, 0)
    );
    println!(
        "  ⟨R, U⟩ orbit of DLF: {:?}  (untouched by R, U)",
        corner_orbit(&ru_only, 5)
    );
    let rf_only = make_restricted(&[core::r(), core::f()]);
    println!(
        "  ⟨R, F⟩ orbit of URF: {:?}",
        corner_orbit(&rf_only, 0)
    );
    println!(
        "  ⟨R, F⟩ orbit of UB edge: {:?}  (untouched by R, F)",
        edge_orbit(&rf_only, 2)
    );

    println!();
    println!("These are the queries the pinning + orbit machinery is for —");
    println!("not solving (which needs Thistlethwaite/Kociemba), but");
    println!("inventory: 'what's reachable, what's invariant, what short");
    println!("alg achieves this constraint.'");
}

fn run_query(
    cube: &CubeBsgs,
    start: &core::Cube3x3State,
    description: &str,
    query: CubeQuery,
    depth: u32,
) {
    print!("  {description}\n    ");
    let t0 = Instant::now();
    match find_algorithm_max_depth(cube, start, &query, depth) {
        Some(alg) if alg.is_empty() => {
            println!(
                "→ already satisfied ({} ms)",
                t0.elapsed().as_millis()
            );
        }
        Some(alg) => {
            println!(
                "→ \"{alg}\" ({} moves, {} ms)",
                alg.len(),
                t0.elapsed().as_millis()
            );
        }
        None => {
            println!(
                "→ no algorithm within depth {depth} ({} ms)",
                t0.elapsed().as_millis()
            );
        }
    }
}

fn make_restricted(gens: &[core::Cube3x3State]) -> CubeBsgs {
    use groups::generators::GeneratingSet;
    use groups::schreier_sims::deterministic::deterministic;
    let perms: Vec<core::Cube3x3StickerPerm> = gens.iter().map(core::to_sticker_perm).collect();
    let gen_set = GeneratingSet::with_inverses(perms);
    let base: Vec<u16> = vec![
        0, 3, 6, 9, 12, 15, 18, 21, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46,
    ];
    let bsgs = deterministic::<_, { core::N_STICKERS }>(&gen_set, &base);
    CubeBsgs { bsgs, gens: gen_set }
}
