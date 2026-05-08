//! Rubik's Clock — out-of-framework puzzle.
//!
//! ## Why this is a doc-only module
//!
//! The Rubik's Clock is **not a permutation puzzle**. Its state is 18 small
//! analog clock faces (9 on each side), and moves consist of turning pin
//! configurations and rotating wheels to add fixed amounts to subsets of
//! the clocks. The state space is `(Z/12Z)¹⁸` — a finite abelian group,
//! but the puzzle's group structure is **not a permutation group**: the
//! moves are translations in `(Z/12Z)¹⁸`, not permutations of stickers.
//!
//! This makes the Schreier-Sims machinery in `groups::bsgs` unsuitable
//! (SS requires a permutation action; the Clock's action is by translation
//! on a torus). However, the Clock's *abelian* structure makes it
//! algorithmically much *easier* — solving reduces to a system of linear
//! equations over `Z/12Z`, which Smith-normal-form / Hermite-form
//! techniques solve in polynomial time without needing SS.
//!
//! ## Modeling the Clock with this crate
//!
//! In the existing trait stack, the Clock could be modeled as:
//!
//! ```ignore
//! pub type ClockState = DirectProduct18<Cyclic<12>>;  // (Z/12Z)¹⁸
//! ```
//!
//! using a hypothetical `DirectProduct18` (we have only binary `DirectProduct`;
//! a tuple combinator macro would unblock this). The "moves" are specific
//! ClockState values that you `op` onto the current state. Composition is
//! associative (Z/12Z is abelian) and identity is well-defined, so this is
//! a `Group` — just not a permutation group.
//!
//! Solver: instead of Schreier-Sims, use Smith normal form over the move
//! generators viewed as a 18×k matrix over `Z/12Z`. Out of scope for
//! `groups` v1.

#![allow(dead_code)]
