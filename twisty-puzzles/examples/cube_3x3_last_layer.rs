//! Last-layer subgroup exploration on the 3×3.
//!
//! Demonstrates the structural shortcut described in the design notes: the
//! LL stabilizer is a single level of the Schreier-Sims chain, so once the
//! BSGS is built with a base ordered `[F2L stickers, LL stickers]`, the
//! strong generators at level 12 are by construction members of the
//! F2L-preserving subgroup. We extract them, pair with inverses, and
//! enumerate the entire orbit to validate `|LL| = 62,208`.
//!
//! Run with: `cargo run --release -p twisty-puzzles --example cube_3x3_last_layer`
//!
//! ## What this shows
//!
//! 1. SS chain construction with a custom base order (~30 ms with the F2L-
//!    first ordering).
//! 2. `Bsgs::stabilizer_generators(12)` extracts the LL-stabilizer
//!    generators — abstract sticker permutations, all F2L-preserving.
//! 3. `enumerate_orbit` builds the full LL state map (62,208 entries) with
//!    shortest words *in those LL generators*.
//! 4. Sample queries: pick a target LL state, look up its shortest word.
//!
//! ## What's still missing (post-v1)
//!
//! The LL gens extracted from the SS chain are abstract group elements with
//! no associated face-move history (they were built up via Schreier residues
//! during chain construction). So the "shortest words" enumerate_orbit
//! produces are sequences of these abstract gens, not face-turn algorithms.
//! Translating LL gens back to face-move products requires either
//! Schreier-vector tracing or maintaining (G, Word) pairs throughout SS
//! construction — both deferred.
//!
//! This demo therefore validates the *count* and the structural shortcut,
//! and exposes the remaining gap.

use groups::bsgs::Bsgs;
use groups::generators::GeneratingSet;
use groups::orbit::enumerate_orbit;
use groups::schreier_sims::deterministic::deterministic;
use groups::Monoid;

use twisty_puzzles::cube::cube_3x3 as core;

fn main() {
    println!("=== 3×3 last-layer subgroup exploration ===\n");

    // 1. Build the BSGS with F2L-first base ordering.
    //
    // F2L cubies (12 total): D-corners 4-7 + middle-edges 4-7 + D-edges 8-11.
    // We pick one sticker per cubie — the U/D-axis sticker, which is
    // sticker `3·corner_slot` for corners and `24 + 2·edge_slot` for edges
    // (these are the "primary" stickers in our convention).
    let f2l_first_base: Vec<u16> = vec![
        // F2L corners (4 D-layer corners): stickers 12, 15, 18, 21
        12, 15, 18, 21,
        // F2L middle-layer edges (slots 4-7): stickers 32, 34, 36, 38
        32, 34, 36, 38,
        // F2L D-layer edges (slots 8-11): stickers 40, 42, 44, 46
        40, 42, 44, 46,
        // LL corners (slots 0-3): stickers 0, 3, 6, 9
        0, 3, 6, 9,
        // LL edges (slots 0-3): stickers 24, 26, 28, 30
        24, 26, 28, 30,
    ];

    let face_gens = core::face_move_sticker_perms();
    let gens = GeneratingSet::with_inverses(face_gens);
    let start = std::time::Instant::now();
    let bsgs: Bsgs<_, { core::N_STICKERS }> =
        deterministic(&gens, &f2l_first_base);
    let build_ms = start.elapsed().as_millis();
    println!(
        "1. Built BSGS with F2L-first base in {build_ms} ms\n   \
         |G| = {} (expected 43,252,003,274,489,856,000)\n",
        bsgs.order()
    );

    // 2. Extract LL stabilizer generators (level 12).
    let ll_gens_raw = bsgs.stabilizer_generators(12);
    println!(
        "2. Extracted {} LL-stabilizer generators (level 12 of the chain)",
        ll_gens_raw.len()
    );
    println!("   Each is by construction F2L-preserving.\n");

    // 3. Sanity-check: verify that every extracted generator actually fixes
    //    the F2L base points.
    use groups::bsgs::PermutationLike;
    let mut all_preserving = true;
    for (idx, g) in ll_gens_raw.iter().enumerate() {
        for &b in &f2l_first_base[..12] {
            if g.apply_to(b) != b {
                println!(
                    "   ⚠ generator #{idx} moves base point {b} → {} (NOT F2L-preserving)",
                    g.apply_to(b)
                );
                all_preserving = false;
                break;
            }
        }
    }
    if all_preserving {
        println!("3. ✓ All {} extracted gens fix every F2L base point.\n",
            ll_gens_raw.len());
    }

    // 4. Build a GeneratingSet from these and enumerate the orbit.
    let ll_gens = GeneratingSet::with_inverses(ll_gens_raw.iter().copied());
    let identity = <core::Cube3x3StickerPerm as Monoid>::identity();
    let start = std::time::Instant::now();
    let orbit = enumerate_orbit(&identity, &ll_gens, 200_000);
    let enum_ms = start.elapsed().as_millis();
    println!(
        "4. Enumerated LL orbit in {enum_ms} ms: {} states reached, complete={}",
        orbit.len(),
        orbit.complete
    );
    println!("   Expected |LL_subgroup| = 4! · 3³ · 4! · 2³ / 2 = 62,208\n");

    if orbit.len() == 62_208 {
        println!("5. ✓ |LL| = 62,208 confirmed by exhaustive enumeration.\n");
    } else if !orbit.complete {
        println!(
            "5. Enumeration hit cap before completing; raise the cap to validate.\n"
        );
    } else {
        println!(
            "5. ⚠ Orbit size {} disagrees with expected 62,208 — \
             may indicate the extracted gens generate a sub-subgroup of LL.\n",
            orbit.len()
        );
    }

    // 6. Distribution of word lengths in the orbit.
    let mut depth_histogram = [0u32; 64];
    let mut max_depth = 0usize;
    for word in orbit.states.values() {
        let d = word.len();
        if d < depth_histogram.len() {
            depth_histogram[d] += 1;
        }
        if d > max_depth {
            max_depth = d;
        }
    }
    println!(
        "6. Word-length distribution (in LL gen indices, NOT face moves):"
    );
    for d in 0..=max_depth {
        if depth_histogram[d] > 0 {
            println!("     length {d:2}: {} states", depth_histogram[d]);
        }
    }
    println!(
        "   Diameter of the LL Cayley graph in these gens: {max_depth} steps."
    );
    println!(
        "   (This is the diameter under the EXTRACTED gens. Under face\n   \
         moves, the LL diameter is ~17 QTM moves.)\n"
    );

    println!("Done. Followups:");
    println!("  - Track Word histories alongside Schreier residues during SS");
    println!("    construction so extracted gens come with face-move expansions.");
    println!("  - Then enumerate_orbit produces shortest face-move algorithms");
    println!("    for every LL state (the OLL+PLL algorithm table).");
}
