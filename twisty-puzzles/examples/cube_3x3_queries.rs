//! End-to-end demo of the 3×3 puzzle interface.
//!
//! Shows: applying a scramble, validating the cube group order via
//! Schreier-Sims, solving partial queries (pin corners and edges, find an
//! algorithm), and listing orbits of cubies under face moves.
//!
//! Run with: `cargo run --example cube_3x3_queries -p twisty-puzzles`

use twisty_puzzles::cube::cube_3x3 as core;
use twisty_puzzles::cube::cube_3x3_iface::{
    corner_orbit, edge_orbit, find_algorithm, Algorithm, CubeBsgs, CubeQuery, Move,
};

fn main() {
    println!("=== 3×3 Rubik's Cube — puzzle interface demo ===\n");

    // 1. Build the cube BSGS once. ~15ms.
    let start = std::time::Instant::now();
    let cube = CubeBsgs::build_qtm();
    let build_ms = start.elapsed().as_millis();
    println!(
        "1. Built BSGS for QTM 3x3 in {build_ms} ms\n   |G| = {} (expected 43,252,003,274,489,856,000)\n",
        cube.order()
    );

    // 2. Apply a scramble and watch the state diverge.
    let scramble = Algorithm::from_moves([
        Move::R, Move::U, Move::Rp, Move::Up, Move::F, Move::B, Move::Up,
    ]);
    let scrambled = scramble.apply_to(&groups::Monoid::identity());
    println!("2. Applied scramble: {scramble}");
    println!("   In group: {}\n", cube.is_solvable(&scrambled));

    // 3. Inverse algorithm restores it.
    let inverse_alg = scramble.inverse();
    println!("3. Inverse: {inverse_alg}");
    let restored = inverse_alg.apply_to(&scrambled);
    println!(
        "   Restoration successful: {}\n",
        restored == groups::Monoid::identity()
    );

    // 4. Pinning queries.
    println!("4. Pinning queries (from solved state):");

    let q_solved = CubeQuery::new();
    let alg = find_algorithm(&cube, &groups::Monoid::identity(), &q_solved).unwrap();
    println!("   No constraints → empty algorithm. len={}\n", alg.len());

    let q_pin_urf = CubeQuery::new().pin_corner_solved(0);
    let alg = find_algorithm(&cube, &groups::Monoid::identity(), &q_pin_urf).unwrap();
    println!("   Pin URF in place from solved: \"{alg}\" ({} moves)", alg.len());

    let q_corner_to_4 = CubeQuery::new().pin_corner_at(4, 0, 0);
    let alg = find_algorithm(&cube, &groups::Monoid::identity(), &q_corner_to_4).unwrap();
    println!(
        "   Move URF cubie to slot 4 (DFR), twist 0: \"{alg}\" ({} moves)",
        alg.len()
    );

    let q_complex = CubeQuery::new()
        .pin_corner_solved(0) // URF stays
        .pin_corner_solved(3) // UBR stays
        .pin_edge_solved(0); // UF stays
    let alg = find_algorithm(&cube, &groups::Monoid::identity(), &q_complex).unwrap();
    println!(
        "   Pin URF, UBR, UF: \"{alg}\" ({} moves)\n",
        alg.len()
    );

    // 5. Orbits.
    println!("5. Orbits under QTM face moves (R, L, U, D, F, B):");
    println!("   Corner 0 orbit (slots reachable): {:?}", corner_orbit(&cube, 0));
    println!("   Edge 0 orbit (slots reachable):   {:?}", edge_orbit(&cube, 0));
    println!("   Both transitive — expected for the full QTM cube group.\n");

    // 6. Restricted-generators orbit: only U-face moves.
    println!("6. Orbit under R, U only (not all face moves):");
    let restricted = make_restricted_bsgs();
    println!(
        "   Corner 0 orbit: {:?}",
        corner_orbit(&restricted, 0)
    );
    println!(
        "   Corner 5 orbit (DLF, untouched by R,U): {:?}",
        corner_orbit(&restricted, 5)
    );

    println!("\nAll queries succeeded.");
}

/// Build a BSGS using only the R and U generators. Useful for showing how
/// orbits shrink when the move set is restricted.
fn make_restricted_bsgs() -> CubeBsgs {
    use groups::generators::GeneratingSet;
    use groups::schreier_sims::deterministic::deterministic;
    let gens = GeneratingSet::with_inverses([
        core::to_sticker_perm(&core::r()),
        core::to_sticker_perm(&core::u()),
    ]);
    let base: Vec<u16> = vec![
        0, 3, 6, 9, 12, 15, 18, 21, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46,
    ];
    let bsgs = deterministic::<_, { core::N_STICKERS }>(&gens, &base);
    CubeBsgs { bsgs, gens }
}
