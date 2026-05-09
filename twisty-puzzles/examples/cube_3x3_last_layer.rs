//! Last-layer subgroup exploration on the 3×3.
//!
//! Builds the BSGS with a base ordered `[F2L stickers, LL stickers]` and
//! extracts the LL-stabilizer generators from level 12 of the chain. Then
//! `enumerate_orbit` walks the entire LL subgroup (62,208 states) producing
//! shortest words **in those abstract LL generators** (NOT face moves —
//! see note at the bottom).
//!
//! Run with: `cargo run --release -p twisty-puzzles --example cube_3x3_last_layer`
//!
//! ## Implementation note
//!
//! Uses the *vanilla* `deterministic` Schreier–Sims (no word tracking).
//! The `deterministic_with_words` variant currently explodes on the
//! 20-level cube chain due to Schreier-residue word growth — fine for the
//! 8-level 2×2 (see `cube_2x2_word_demo`) but not yet practical at full
//! cube scale. For face-move algorithm tables, see followups in the README.

use groups::bsgs::Bsgs;
use groups::generators::GeneratingSet;
use groups::orbit::enumerate_orbit;
use groups::schreier_sims::deterministic::deterministic;
use groups::Monoid;

use twisty_puzzles::cube::cube_3x3 as core;

fn main() {
    println!("=== 3×3 last-layer subgroup exploration ===\n");

    // F2L cubies pinned first, LL cubies last. One sticker per cubie
    // suffices because each cubie's U/D-axis sticker uniquely determines
    // both its slot and its orientation.
    let f2l_first_base: Vec<u16> = vec![
        12, 15, 18, 21, // F2L corners (D-layer): stickers 12, 15, 18, 21
        32, 34, 36, 38, // F2L middle-layer edges (slots 4-7)
        40, 42, 44, 46, // F2L D-layer edges (slots 8-11)
        0, 3, 6, 9,     // LL corners (slots 0-3)
        24, 26, 28, 30, // LL edges (slots 0-3)
    ];

    let face_gens = core::face_move_sticker_perms();
    let gens = GeneratingSet::with_inverses(face_gens);

    let start = std::time::Instant::now();
    let bsgs: Bsgs<_, { core::N_STICKERS }> = deterministic(&gens, &f2l_first_base);
    let build_ms = start.elapsed().as_millis();
    println!(
        "1. Built BSGS with F2L-first base in {build_ms} ms\n   |G| = {}\n",
        bsgs.order()
    );

    // 2. Extract LL stabilizer generators (level 12).
    let ll_gens_raw = bsgs.stabilizer_generators(12);
    println!(
        "2. Extracted {} LL-stabilizer generators (level 12 of the chain)\n",
        ll_gens_raw.len()
    );

    // 3. Sanity check: every extracted gen fixes all 12 F2L base points.
    use groups::bsgs::PermutationLike;
    let mut all_preserve = true;
    for g in &ll_gens_raw {
        for &b in &f2l_first_base[..12] {
            if g.apply_to(b) != b {
                all_preserve = false;
                break;
            }
        }
    }
    println!(
        "3. {} every extracted gen fixes the F2L stickers.\n",
        if all_preserve { "✓" } else { "✗" }
    );

    // 4. Enumerate the entire LL orbit.
    let ll_gens = GeneratingSet::with_inverses(ll_gens_raw.iter().copied());
    let identity = <core::Cube3x3StickerPerm as Monoid>::identity();
    let start = std::time::Instant::now();
    let orbit = enumerate_orbit(&identity, &ll_gens, 200_000);
    let enum_ms = start.elapsed().as_millis();
    println!(
        "4. Enumerated LL orbit in {enum_ms} ms: {} states reached, complete={}\n",
        orbit.len(),
        orbit.complete
    );

    if orbit.len() == 62_208 {
        println!("5. ✓ |LL| = 62,208 confirmed (= 4! · 3³ · 4! · 2³ / 2)\n");
    }

    // 6. Word-length distribution in the abstract LL gens.
    let mut histogram = [0u32; 32];
    let mut max_depth = 0;
    for w in orbit.states.values() {
        let d = w.len();
        if d < histogram.len() {
            histogram[d] += 1;
        }
        if d > max_depth {
            max_depth = d;
        }
    }
    println!("6. Word-length distribution (in abstract LL-gen indices):");
    for d in 0..=max_depth {
        if histogram[d] > 0 {
            println!("     length {d:2}: {} states", histogram[d]);
        }
    }
    println!(
        "   Diameter under extracted gens: {max_depth}.\n   \
         (Under face moves the LL diameter is ~17 QTM.)\n"
    );

    println!("Note: the words above are sequences of LL-gen INDICES, not");
    println!("face moves. Translating them back to face-move algorithms");
    println!("requires the word-tracked SS path, which works on the 2×2");
    println!("(see `cube_2x2_word_demo`) but currently scales poorly to");
    println!("the 3×3's 20-level chain.");
}
