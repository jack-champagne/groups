//! Square-1 — shape-shifting cuboidal puzzle.
//!
//! ## Why this is a doc-only module in v1
//!
//! Square-1 is a *shape-shifting* puzzle: its layers can be turned by
//! arbitrary multiples of 30°, which means the *set of legal moves depends
//! on the current state*. After certain rotations the puzzle is no longer
//! cube-shaped and the slice move (which can only be applied when the
//! middle layer aligns to a square) is unavailable.
//!
//! This makes Square-1 a **semigroup**, not a group: not every move has an
//! inverse from every state. The library's `Magma → Semigroup → Monoid →
//! Group` trait stack accommodates this — `Square-1` would impl up through
//! `Semigroup` (associative composition) and stop short of `Monoid` because
//! there's no global identity-and-inverse structure that respects the move
//! constraints.
//!
//! ## Roadmap
//!
//! Once the `groups::partial_state` work is extended to handle "moves
//! conditional on state" (a feature beyond the current `PartialState`
//! design), Square-1 can be modeled here as:
//!
//! ```ignore
//! pub struct SquareOneState {
//!     // 16 wedge cubies in two layers + 1 middle slice piece
//!     wedges: [WedgeKind; 16],
//!     middle: MiddleSlicePosition,
//! }
//!
//! impl Semigroup for SquareOneState { ... }  // closure under legal moves
//! ```
//!
//! For now, this module exists to claim the namespace and document the
//! deferral.

#![allow(dead_code)]

#[cfg(test)]
mod tests {
    #[test]
    fn module_compiles_as_doc_only_placeholder() {
        // Smoke test: this file's docstring describes Square-1's
        // semigroup-not-group nature. The actual model lands when the
        // partial_state work supports state-conditional move sets.
    }
}
