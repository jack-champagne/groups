//! Parametric NxN cubes (4×4 through 7×7 and beyond).
//!
//! ## Status (v1)
//!
//! Structural placeholder. The full NxN cube has multiple cubie types whose
//! algebraic structure varies with `N`:
//!
//! - 8 corners (always) → `WreathProduct<Cyclic<3>, 8>` factor.
//! - 12 edge "groups" each containing `N-2` edges. For N=3, 1 edge per
//!   group. For N≥4, multiple edges per group with no internal orientation
//!   (so they form `S_{12·(N-2)}` constrained by the geometry).
//! - 6 face-centre "groups" each with `(N-2)²` cubies. For N=3, 1 fixed
//!   centre. For N≥4, the centres permute under `S_{(N-2)²}` per face.
//! - For N≥5, edge-pairs become *chiral* — meaning some edges have a
//!   left/right asymmetry, complicating the structure further.
//!
//! Concrete impls for 4×4 through 7×7 are deferred to a follow-up; the 3×3
//! model in [`super::cube_3x3`] is the load-bearing reference. The
//! abstractions in this crate (wreath products, Schreier-Sims, partial
//! states) all extend cleanly — what's missing is the cubie inventory and
//! sticker mapping for each size.
//!
//! ## Why no parametric `NxNCube<const N: usize>`?
//!
//! Tempting but ill-fated for v1. The mathematical structure changes with N
//! in non-uniform ways:
//! - N=2: corners only.
//! - N=3: corners + edges + (fixed) centres.
//! - N=4: + non-fixed centres.
//! - N=5: + chiral edges.
//!
//! A single parametric type would either bake all four cases in (with
//! const-generic awkwardness) or punt to a runtime-typed cubie inventory
//! (heap allocation, lost perf). v1 ships separate per-size models; the
//! product combinators in `groups` make the boilerplate per-size light
//! (~50 LOC per size after the move-permutation tables are written).
