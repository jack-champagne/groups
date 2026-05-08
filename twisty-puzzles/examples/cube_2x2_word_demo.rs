//! 2×2 cube: word-tracked SS construction + face-move algorithm enumeration
//! over a small subgroup.
//!
//! The full 3×3 LL demo with word tracking is currently too slow due to
//! exponential Schreier-residue word growth on a 20-level chain. The 2×2
//! has only an 8-level chain over 24 stickers, which exercises the same
//! machinery in a tractable regime.
//!
//! Run with: `cargo run --release -p twisty-puzzles --example cube_2x2_word_demo`

use groups::generators::GeneratingSet;
use groups::orbit::enumerate_orbit_translated;
use groups::schreier_sims::deterministic_with_words::deterministic_with_words;
use groups::Monoid;

use twisty_puzzles::cube::cube_2x2 as core;
use twisty_puzzles::cube::cube_3x3_iface::word_to_algorithm;

fn main() {
    println!("=== 2×2 cube: word-tracked SS + algorithm enumeration ===\n");

    // Use the same QTM order as the iface (R, L, U, D, F, B), so
    // word_to_algorithm produces correct cube notation.
    let face_perms: Vec<_> = [core::r(), core::l(), core::u(), core::d(), core::f(), core::b()]
        .iter()
        .map(|m| core::to_sticker_perm(m))
        .collect();
    let gens = GeneratingSet::with_inverses(face_perms);
    let base: Vec<u16> = (0..8).map(|i| 3 * i).collect();

    let start = std::time::Instant::now();
    let bsgs_w = deterministic_with_words::<_, { core::N_STICKERS }>(&gens, &base);
    let build_ms = start.elapsed().as_millis();
    println!(
        "1. Built BSGS-with-words for 2×2 in {build_ms} ms\n   \
         |G| = {} (expected 88,179,840 for ⟨R,L,U,D,F,B⟩)\n",
        bsgs_w.order()
    );

    // Word-length statistics across the chain.
    println!("2. Word lengths across the SS chain:");
    for level_idx in 0..bsgs_w.bsgs.levels.len() {
        let words = &bsgs_w.strong_gen_words[level_idx];
        if words.is_empty() {
            continue;
        }
        let max = words.iter().map(|w| w.len()).max().unwrap();
        let avg = words.iter().map(|w| w.len()).sum::<usize>() as f64 / words.len() as f64;
        println!(
            "     level {level_idx}: {} strong gens, avg word len {avg:.1}, max {max}",
            words.len()
        );
    }
    println!();

    // Pick a small subgroup: stabilizer at level 6 (cubies 0,1,2,3,4,5 fixed).
    // This leaves a 2-corner subgroup → very small.
    let sub_level = 5;
    let sub_gens = bsgs_w.stabilizer_generators_with_words(sub_level);
    println!(
        "3. Stabilizer at level {sub_level} ({} cubies fixed): {} gens",
        sub_level,
        sub_gens.len()
    );
    if let Some(w) = sub_gens.iter().map(|(_, w)| w.len()).max() {
        println!("   Max gen word length: {w}");
    }

    // Show a few sample gens with their face-move algorithms.
    println!("\n4. Sample subgroup generators:");
    for (i, (_, w)) in sub_gens.iter().take(3).enumerate() {
        let alg = word_to_algorithm_2x2(w);
        println!("   gen {i}: {alg}  ({} moves)", w.len());
    }

    // Enumerate the subgroup orbit, getting face-move words for each.
    let identity = <core::Cube2x2StickerPerm as Monoid>::identity();
    let start = std::time::Instant::now();
    let orbit = enumerate_orbit_translated(&identity, &sub_gens, 100_000);
    let enum_ms = start.elapsed().as_millis();
    println!(
        "\n5. Enumerated subgroup orbit in {enum_ms} ms: {} states, complete={}",
        orbit.len(),
        orbit.complete
    );

    // Word length distribution.
    let max_len = orbit
        .states
        .values()
        .map(|w| w.len())
        .max()
        .unwrap_or(0);
    let mut histogram = vec![0u32; max_len + 1];
    for w in orbit.states.values() {
        histogram[w.len()] += 1;
    }
    println!("\n6. Face-move algorithm length distribution for this subgroup:");
    for len in 0..=max_len {
        if histogram[len] > 0 {
            println!("     {len:3} moves: {} states", histogram[len]);
        }
    }

    // Print a few sample (state, algorithm) pairs.
    println!("\n7. Sample states and their algorithms:");
    let mut samples: Vec<_> = orbit.states.iter().filter(|(_, w)| !w.is_empty()).collect();
    samples.sort_by_key(|(_, w)| w.len());
    let mut shown_lengths = std::collections::HashSet::new();
    let mut shown = 0;
    for (_, w) in &samples {
        let len = w.len();
        if !shown_lengths.contains(&len) {
            shown_lengths.insert(len);
            let alg = word_to_algorithm_2x2(w);
            println!("   length {len:3}: {alg}");
            shown += 1;
            if shown >= 8 {
                break;
            }
        }
    }
}

/// 2×2 has 6 face moves [R, L, U, D, F, B]; the 3×3-iface helper assumes the
/// same ordering (which we used in the GeneratingSet above), so we can
/// reuse it directly.
fn word_to_algorithm_2x2(w: &groups::word::Word) -> String {
    let alg = word_to_algorithm(w);
    format!("{alg}")
}
