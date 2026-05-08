//! 3×3 cube corner group via the wreath product, demonstrating that
//! `R⁴ = I` (the bug in the user's existing puzzle-cube code) holds when
//! composition is performed correctly.
//!
//! Models only the corners — the edge subgroup is identical in structure
//! (`C₂ ≀ S₁₂`) and the full cube is `(C₃ ≀ S₈) × (C₂ ≀ S₁₂)` modulo three
//! parity constraints.
//!
//! Run with:
//! ```text
//! cargo run --example cube3_corners
//! ```

use groups::cyclic::Cyclic;
use groups::permutation::Permutation;
use groups::product::WreathProduct;
use groups::{Group, Magma, Monoid};

/// The corner group of the 3×3 cube: 8 corner cubies, each with a 3-fold
/// orientation, permuted by an element of `S_8`.
type CornerGroup = WreathProduct<Cyclic<3>, 8>;

/// Corner labelling (one common scheme; the specific labels don't matter for
/// the algebra, only that the moves below are mutually consistent):
///
/// ```text
/// 0 = URF   1 = UFL   2 = ULB   3 = UBR
/// 4 = DFR   5 = DLF   6 = DBL   7 = DRB
/// ```

/// Helper: build a `Cyclic<3>` from a small `usize`.
fn t(x: usize) -> Cyclic<3> {
    Cyclic::<3>::from_index(x)
}

/// Construct the R move: cycles 4 corners around the right face and twists
/// each by the appropriate amount in `C₃`.
fn move_r() -> CornerGroup {
    // R rotates the right face clockwise (looking from the right).
    // Corners on the right face: URF(0), UBR(3), DFR(4), DRB(7).
    // Permutation: URF → DRF, DFR → DRB, DRB → UBR, UBR → URF
    //   (i.e., the cycle 0 → 4 → 7 → 3 → 0)
    // Twists: any clockwise face turn imparts twists summing to 0 mod 3
    //   on its four corners. A standard convention: (2, 0, 0, 1) on
    //   (URF, DRF, DRB, UBR) — sum = 0 mod 3.
    let mut fibers = [t(0); 8];
    fibers[0] = t(2); // URF
    fibers[3] = t(1); // UBR
    fibers[4] = t(0); // DFR
    fibers[7] = t(0); // DRB
    // Adjust so total = 0 mod 3 with the standard scheme
    fibers[0] = t(2);
    fibers[4] = t(1);
    fibers[7] = t(2);
    fibers[3] = t(1);
    // Sum = 2 + 1 + 2 + 1 = 6 = 0 mod 3 ✓
    let perm = Permutation::<8>::cycle(&[0, 4, 7, 3]);
    CornerGroup::new(fibers, perm)
}

/// Construct the U move: cycles 4 corners around the up face. U does not
/// twist any corner (orientations are defined relative to the U/D axis, so
/// U/D moves are orientation-preserving).
fn move_u() -> CornerGroup {
    let perm = Permutation::<8>::cycle(&[0, 1, 2, 3]);
    CornerGroup::new([t(0); 8], perm)
}

/// Construct the F move: cycles 4 corners around the front face.
fn move_f() -> CornerGroup {
    // Front-face corners: URF(0), UFL(1), DFR(4), DLF(5).
    // F clockwise (from the front): URF → DRF, DRF → DLF, DLF → UFL, UFL → URF
    //   = cycle 0 → 4 → 5 → 1 → 0
    let mut fibers = [t(0); 8];
    fibers[0] = t(1); // URF
    fibers[4] = t(2); // DFR
    fibers[5] = t(1); // DLF
    fibers[1] = t(2); // UFL
    // Sum = 1 + 2 + 1 + 2 = 6 = 0 mod 3 ✓
    let perm = Permutation::<8>::cycle(&[0, 4, 5, 1]);
    CornerGroup::new(fibers, perm)
}

fn main() {
    let r = move_r();
    let u = move_u();
    let f = move_f();
    let id = CornerGroup::identity();

    println!("=== Cube corner group: WreathProduct<Cyclic<3>, 8> ===\n");

    // 1) Each face turn has order 4: M⁴ = I.
    let r2 = r.op(&r);
    let r4 = r2.op(&r2);
    println!("R⁴ = identity: {}", r4 == id);
    assert_eq!(r4, id, "R⁴ must be identity (this is the bug fixed by wreath product)");

    let u4 = u.op(&u).op(&u).op(&u);
    println!("U⁴ = identity: {}", u4 == id);
    assert_eq!(u4, id);

    let f4 = f.op(&f).op(&f).op(&f);
    println!("F⁴ = identity: {}", f4 == id);
    assert_eq!(f4, id);

    // 2) Inverse via the group: R · R⁻¹ = I.
    let r_inv = r.inv();
    println!("R · R⁻¹ = identity: {}", r.op(&r_inv) == id);
    assert_eq!(r.op(&r_inv), id);

    // 3) The "sexy move" R U R' U' has order 6 in the corner subgroup.
    //    (R U R' U')⁶ = I — a famous cubing identity.
    let sexy = r.op(&u).op(&r.inv()).op(&u.inv());
    let sexy6 = (0..6).fold(id, |acc, _| acc.op(&sexy));
    println!("(R U R' U')⁶ = identity: {}", sexy6 == id);
    assert_eq!(sexy6, id, "sexy move has order 6 in the corner subgroup");

    // 4) Total corner twist is preserved mod 3 (a parity constraint of the
    //    cube). Verify: starting from identity (twist = 0), every move keeps
    //    the total twist at 0 mod 3.
    let twist_sum = |g: &CornerGroup| -> u8 {
        g.fibers.iter().map(|c| c.index() as u8).sum::<u8>() % 3
    };
    println!("\nTwist-sum invariant (must be 0 mod 3 for any solvable state):");
    for (name, m) in [("R", &r), ("U", &u), ("F", &f)] {
        println!("  twist_sum({name}) = {}", twist_sum(m));
        assert_eq!(twist_sum(m), 0);
    }
    let composed = r.op(&u).op(&f).op(&r.inv()).op(&u.inv()).op(&f.inv());
    println!("  twist_sum(R U F R' U' F') = {}", twist_sum(&composed));
    assert_eq!(twist_sum(&composed), 0);

    println!("\nAll relations hold. The wreath product correctly models the\n\
              orientation-and-position interaction the existing puzzle-cube\n\
              code's direct-product representation cannot.");
}
