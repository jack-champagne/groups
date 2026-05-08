//! Last-layer subgroup exploration on the 3×3, with **face-move algorithms**.
//!
//! Builds the BSGS with word-history tracking, extracts the LL stabilizer
//! generators (each paired with its face-move expansion), then enumerates
//! the entire LL orbit (62,208 states) producing a shortest face-move word
//! for every reachable LL state.
//!
//! Run with: `cargo run --release -p twisty-puzzles --example cube_3x3_last_layer`
//!
//! ## What this demonstrates
//!
//! 1. SS construction with `deterministic_with_words` tracks face-move words
//!    for every Schreier residue and transversal element. Adds modest
//!    overhead (~30% slower than vanilla SS).
//! 2. `BsgsWithWords::stabilizer_generators_with_words(level)` returns
//!    `Vec<(G, Word)>` — abstract LL gens paired with their face-move
//!    expansions. Words can be 30+ moves long for deep Schreier residues.
//! 3. `enumerate_orbit_translated` BFS-walks the LL subgroup using these
//!    tracked gens; the returned map's words are *shortest face-move
//!    expressions* (modulo the slack that comes from gens having
//!    long expansions).

use groups::generators::GeneratingSet;
use groups::orbit::enumerate_orbit_translated;
use groups::schreier_sims::deterministic_with_words::deterministic_with_words;
use groups::Monoid;

use twisty_puzzles::cube::cube_3x3 as core;
use twisty_puzzles::cube::cube_3x3_iface::{word_to_algorithm, Move};

fn main() {
    println!("=== 3×3 last-layer exploration with face-move algorithms ===\n");

    let f2l_first_base: Vec<u16> = vec![
        12, 15, 18, 21, // F2L corner U/D-axis stickers
        32, 34, 36, 38, // F2L middle-edge stickers
        40, 42, 44, 46, // F2L D-edge U/D-axis stickers
        0, 3, 6, 9,     // LL corner stickers
        24, 26, 28, 30, // LL edge stickers
    ];

    // Use the iface QTM gen ordering [R, L, U, D, F, B] so word_to_algorithm
    // works on the resulting Words.
    let face_perms: Vec<core::Cube3x3StickerPerm> = [
        Move::R, Move::L, Move::U, Move::D, Move::F, Move::B,
    ]
    .iter()
    .map(|m| core::to_sticker_perm(&m.to_state()))
    .collect();
    let gens = GeneratingSet::with_inverses(face_perms);

    let start = std::time::Instant::now();
    let bsgs_w = deterministic_with_words::<_, { core::N_STICKERS }>(&gens, &f2l_first_base);
    let build_ms = start.elapsed().as_millis();
    println!(
        "1. Built BSGS with face-move word histories in {build_ms} ms"
    );
    println!("   |G| = {}\n", bsgs_w.order());

    // Extract LL gens with their face-move expansions.
    let ll_gens_with_words = bsgs_w.stabilizer_generators_with_words(12);
    println!(
        "2. Extracted {} LL-stabilizer generators",
        ll_gens_with_words.len()
    );
    let max_word_len = ll_gens_with_words
        .iter()
        .map(|(_, w)| w.len())
        .max()
        .unwrap_or(0);
    let avg_word_len = ll_gens_with_words
        .iter()
        .map(|(_, w)| w.len())
        .sum::<usize>() as f64
        / ll_gens_with_words.len() as f64;
    println!(
        "   Face-move expansion length: avg {avg_word_len:.1}, max {max_word_len}\n"
    );

    // Sanity-check: the first few gens, printed with their face-move algs.
    println!("3. Sample LL generators with face-move expansions:");
    for (i, (_, w)) in ll_gens_with_words.iter().take(5).enumerate() {
        let alg = word_to_algorithm(w);
        println!("   gen {i:2} ({:>3} moves): {alg}", w.len());
    }
    println!();

    // Enumerate the orbit, getting face-move words for every LL state.
    let identity = <core::Cube3x3StickerPerm as Monoid>::identity();
    let start = std::time::Instant::now();
    let orbit = enumerate_orbit_translated(&identity, &ll_gens_with_words, 200_000);
    let enum_ms = start.elapsed().as_millis();
    println!(
        "4. Enumerated LL orbit in {enum_ms} ms: {} states reached, complete={}\n",
        orbit.len(),
        orbit.complete
    );

    // Distribution of face-move algorithm lengths.
    let mut histogram = vec![0u32; 200];
    let mut max_len = 0usize;
    for w in orbit.states.values() {
        let len = w.len();
        if len < histogram.len() {
            histogram[len] += 1;
        }
        if len > max_len {
            max_len = len;
        }
    }
    println!("5. Face-move algorithm length distribution:");
    for len in 0..=max_len {
        if histogram[len] > 0 {
            println!("     {len:3} moves: {} states", histogram[len]);
        }
    }
    let nonzero_min = histogram
        .iter()
        .position(|&c| c > 0)
        .map(|i| i)
        .unwrap_or(0);
    println!(
        "   Min: {nonzero_min}, Max: {max_len}.\n"
    );

    // Pick a few specific LL targets and print their algorithms.
    println!("6. Sample LL states and their algorithms:");
    let mut samples: Vec<(&core::Cube3x3StickerPerm, &groups::word::Word)> = orbit
        .states
        .iter()
        .filter(|(_, w)| !w.is_empty())
        .collect();
    samples.sort_by_key(|(_, w)| w.len());
    // Show the first few (shortest) and a sample at every depth.
    let mut shown_lengths = std::collections::HashSet::new();
    let mut shown = 0;
    for (_, w) in &samples {
        let len = w.len();
        if !shown_lengths.contains(&len) {
            shown_lengths.insert(len);
            let alg = word_to_algorithm(w);
            println!("   length {len:3}: {alg}");
            shown += 1;
            if shown > 10 {
                break;
            }
        }
    }

    println!("\nThe complete LL algorithm table is now in `orbit.states`:");
    println!("  • {} entries", orbit.len());
    println!("  • Each maps an LL state ↔ a face-move algorithm reaching it.");
    println!("  • Lookup is O(1) via the HashMap.");
}
