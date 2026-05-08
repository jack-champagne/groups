//! NxN Rubik's-style cubes.
//!
//! Each size has its own model because the cubie inventory differs:
//! - **2×2**: 8 corner cubies only ([`cube_2x2`]).
//! - **3×3**: 8 corners + 12 edges + fixed centers ([`cube_3x3`]).
//! - **4×4 and up**: corners + edge-pairs (with chirality from 5×5 up) +
//!   center cubies that themselves form a permutation group. Modeled
//!   parametrically in [`cube_n`]; specific sizes 4–7 are exposed as type
//!   aliases.
//!
//! All cube modules share a common shape:
//! - A `State` type capturing the natural algebraic structure.
//! - Standard face moves (R, L, U, D, F, B) as `State` values.
//! - A `PermutationLike<N>` impl for the sticker representation, so the
//!   `groups::schreier_sims` machinery can validate `|G|` directly.

pub mod cube_2x2;
pub mod cube_3x3;
pub mod cube_n;

pub use cube_2x2::Cube2x2State;
pub use cube_3x3::Cube3x3State;
