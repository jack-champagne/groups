//! # groups
//!
//! Algebraic group theory primitives sized for puzzle-shaped computational
//! group theory: permutation groups, group actions, semidirect/wreath products,
//! Schreier–Sims, orbit and coset queries.
//!
//! The trait stack `Magma → Semigroup → Monoid → Group` is templated upfront
//! so future symmetry-breaking puzzles (which only form semigroups) slot in
//! without reshuffling the type hierarchy. v1 ships only `Group`-level impls.

pub mod bsgs;
pub mod cyclic;
pub mod generators;
pub mod partial_state;
pub mod permutation;
pub mod product;
pub mod schreier_sims;
pub mod solver;
pub mod word;

/// A set with a closed binary operation. No other axioms.
///
/// Closure is enforced by the type signature: `op` returns `Self`.
pub trait Magma: Copy + Eq {
    /// The binary operation. `self` is the left operand.
    fn op(&self, other: &Self) -> Self;

    /// In-place form of [`Magma::op`]. Default falls back to owned-return;
    /// override on hot paths if a measurably faster in-place form exists.
    #[inline]
    fn op_assign(&mut self, other: &Self) {
        *self = self.op(other);
    }
}

/// A magma whose operation is associative: `(a · b) · c = a · (b · c)`.
///
/// Marker trait — associativity is a contract enforced by tests, not by the
/// type system.
pub trait Semigroup: Magma {}

/// A semigroup with a two-sided identity element.
///
/// Contract: `identity().op(&x) == x` and `x.op(&identity()) == x`.
pub trait Monoid: Semigroup {
    fn identity() -> Self;
}

/// A monoid in which every element has a two-sided inverse.
///
/// Contract: `x.op(&x.inv()) == identity()` and `x.inv().op(&x) == identity()`.
pub trait Group: Monoid {
    fn inv(&self) -> Self;

    #[inline]
    fn invert(&mut self) {
        *self = self.inv();
    }
}

/// Blanket impl: every group acts on itself by right multiplication
/// (`x.act(g) = x · g` in our left-to-right op convention). This is the
/// regular right action — every group naturally has it.
impl<G: Group> Action<G> for G {
    #[inline]
    fn act(&self, g: &G) -> Self {
        self.op(g)
    }
}

/// A set on which a monoid `G` acts.
///
/// The `act` method lives on the receiver (state) so group types stay free of
/// `act_on` clutter — multiple state types can be acted on by the same group
/// without polluting its API.
///
/// Contract (right action): `state.act(&g.op(&h)) == state.act(&g).act(&h)`,
/// and `state.act(&G::identity()) == *state`.
///
/// Right action is chosen to match the cubing reading convention: applying
/// move `g` then move `h` to a state composes with `g.op(&h)` in the same
/// left-to-right order.
pub trait Action<G: Monoid>: Sized + Copy {
    fn act(&self, g: &G) -> Self;
}

/// A group whose elements can be enumerated. Opt-in: implement only when `|G|`
/// is small enough for enumeration to be useful.
pub trait Enumerable: Group {
    /// Iterates every element of the group exactly once. Iteration order is
    /// implementation-defined at this trait level; concrete impls may document
    /// a stable order.
    fn iter() -> impl Iterator<Item = Self>;

    /// `|G|`, the order of the group.
    fn order() -> u128;
}

pub mod prelude {
    pub use super::cyclic::Cyclic;
    pub use super::generators::GeneratingSet;
    pub use super::permutation::Permutation;
    pub use super::product::{DirectProduct, SemidirectProduct, WreathProduct};
    pub use super::word::Word;
    pub use super::{Action, Enumerable, Group, Magma, Monoid, Semigroup};
}
