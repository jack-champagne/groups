//! Product combinators: direct, semidirect, and wreath products.
//!
//! These are the load-bearing constructions for puzzle groups. Every twisty
//! puzzle can be expressed as a constrained subgroup of a product of wreath
//! products (one per cubie type). For example, the 3×3 cube is:
//!
//! ```text
//!     (C₃ ≀ S₈)  ×  (C₂ ≀ S₁₂)
//! ```
//!
//! with three parity constraints (corner-twist sum mod 3, edge-flip sum mod 2,
//! corner/edge perm-parity match) checked at the puzzle layer.

pub mod direct;
pub mod semidirect;
pub mod wreath;

pub use direct::DirectProduct;
pub use semidirect::SemidirectProduct;
pub use wreath::WreathProduct;
