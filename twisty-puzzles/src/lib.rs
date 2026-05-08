//! # twisty-puzzles
//!
//! Models of WCA-recognized twisty puzzles built on the [`groups`] crate.
//!
//! Each puzzle module defines:
//! - A `Group` newtype that captures the natural algebraic structure
//!   (typically a wreath product or product of wreath products).
//! - A `MoveEnum` for human notation.
//! - A "sticker representation" — a faithful permutation embedding into
//!   `Permutation<N>` for some `N`, suitable for [`groups::schreier_sims`]
//!   queries (|G|, membership, partial-state coset queries, IDA* search).
//!
//! ## WCA-recognized events as of 2026
//!
//! | Puzzle      | Module          | Status           |
//! |-------------|-----------------|------------------|
//! | 2×2×2       | [`cube`]        | full             |
//! | 3×3×3       | [`cube`]        | full             |
//! | 4×4×4       | [`cube`]        | full             |
//! | 5×5×5       | [`cube`]        | full             |
//! | 6×6×6       | [`cube`]        | full (parametric)|
//! | 7×7×7       | [`cube`]        | full (parametric)|
//! | Pyraminx    | [`pyraminx`]    | full             |
//! | Skewb       | [`skewb`]       | full             |
//! | Megaminx    | [`megaminx`]    | full             |
//! | Square-1    | [`square_one`]  | doc-only — see module note (semigroup, not group) |
//! | Clock       | [`clock`]       | doc-only — see module note (not a permutation puzzle) |
//!
//! 3BLD, 4BLD, 5BLD, MBLD, OH, FMC are *events* using puzzles already listed.

pub mod clock;
pub mod cube;
pub mod megaminx;
pub mod pyraminx;
pub mod skewb;
pub mod square_one;
