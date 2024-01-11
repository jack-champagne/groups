//! # Algebraic Groups
//!
//! Library defines the group algebraic structure and
//! concrete examples of groups. See [`modules`]
//!
//! [`modules`]: #modules

pub mod cyclic;
pub mod permutation;

/// Minimal interface for an algebraic group
///
/// A group is a set S and a binary operator (*) such that:
/// 1. There is an identity `e` such that \forall x \in S : e * x = x
/// 2. Inverses exist for each element - \forall x \in S, \exists y \in S : x * y = e
/// 3. The group is closed under the operator (*) - \forall x, y \in S : x * y \in S
/// 4. The binary operator is associative - \forall x,y,z \in S : x * (y * z) = (x * y) * z
///
/// These rules must be enforced by the implementor and are provided as a contract to the user
/// For associativity, it _should_ checked by a unit test over all elements in the group.
///
pub trait Group {
    fn op(&self, other: &Self) -> Self;

    fn inv(&self) -> Self;

    fn identity() -> Self;
}
