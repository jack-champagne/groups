//! Megaminx — dodecahedral puzzle.
//!
//! ## Group structure
//!
//! - **20 corners**, each with a `C_3` orientation, permuted by `S_20` mod
//!   parity constraints.
//! - **30 edges**, each with a `C_2` orientation, permuted by `S_30` mod
//!   parity constraints.
//! - 12 face centres are fixed.
//!
//! Total: `WreathProduct<Cyclic<3>, 20> × WreathProduct<Cyclic<2>, 30>`
//! modulo:
//! - corner-twist sum ≡ 0 mod 3
//! - edge-flip sum ≡ 0 mod 2
//! - corner-perm parity = edge-perm parity (one of multiple parity
//!   constraints; depending on convention there's also an "edge-pair
//!   parity")
//!
//! Published value: `|G_megaminx| ≈ 1.01 × 10⁶⁸`.
//!
//! Specifically: `(20! / 2) · 3¹⁹ · (30! / 2) · 2²⁹`.
//!
//! ## Status
//!
//! The structure is sketched; full move definitions and SS validation are
//! deferred — the megaminx has 12 face moves, each rotating 5 corners and
//! 5 edges, requiring careful indexing of the dodecahedron's geometry.
//! For v1 we expose the type aliases and a constant for `|G|` so consumers
//! can reference them; full move tables and SS validation will follow in a
//! subsequent commit.

use groups::cyclic::Cyclic;
use groups::product::{DirectProduct, WreathProduct};

pub type CornerGroup = WreathProduct<Cyclic<3>, 20>;
pub type EdgeGroup = WreathProduct<Cyclic<2>, 30>;
pub type MegaminxState = DirectProduct<CornerGroup, EdgeGroup>;

/// Sticker count: 20 corners × 3 + 30 edges × 2 = 120.
pub const N_STICKERS: usize = 120;

/// Approximate order of the megaminx group: ~1.01 × 10⁶⁸.
///
/// As a u128, this number is too large to represent exactly — u128's max is
/// ~3.4 × 10³⁸, so we can't hold the full order. Schreier-Sims's `order()`
/// method (which returns u128) will overflow when applied to the megaminx
/// group; future enhancement: switch to `BigUint` for arbitrary-precision
/// |G|, OR compute log₂ |G| as f64 (~226 bits, fits cleanly).
pub const APPROX_ORDER_LOG2: f64 = 225.6;
