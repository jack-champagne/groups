//! Partial states: the "fix these slots / wildcard those slots" headline
//! feature.
//!
//! A `PartialState<S>` describes a *coset* of a pointwise stabilizer:
//! "every state matching this pattern, where some slots are pinned to a
//! specific value and others are wildcards."
//!
//! ## Status (v1)
//!
//! Trait surface laid down; the algorithmic side (coset membership and word
//! reconstruction via Schreier–Sims with a base chosen to respect the
//! constraints) is stubbed. The trait shape is what consumers will program
//! against; implementation lands in a follow-up.

use crate::{Action, Group};

/// Per-slot constraint.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Constraint<V: Copy + Eq> {
    /// Slot value is irrelevant.
    Wildcard,
    /// Slot value must equal `V`.
    MustEqual(V),
}

/// Trait that a state type implements to expose its constraint pattern in a
/// form that Schreier–Sims-based queries can consume.
///
/// The library only needs `matches` (does a full state satisfy this pattern?)
/// and `constrained_indices` (which slots are non-wildcard?) to drive its
/// algorithms — concrete types choose how to store the mask compactly
/// (`u64` bitmask, `[bool; N]`, etc.).
pub trait PartiallyConstrainable: Sized + Copy {
    type G: Group;
    type Mask: Copy;
    type Slot: Copy + Eq;

    /// Returns `true` iff `self` satisfies the constraint pattern.
    fn matches(state: &Self, mask: &Self::Mask) -> bool;

    /// Iterator over slot indices that are non-wildcard in `mask`.
    fn constrained_indices(mask: &Self::Mask) -> Box<dyn Iterator<Item = u16>>;
}

/// A constraint-pattern view over a state type `S`.
///
/// Constructed at the puzzle layer with knowledge of the `MoveEnum` / cubie
/// labelling; consumed by [`crate::bsgs::Bsgs`] coset queries (post-v1).
#[derive(Debug, Copy, Clone)]
pub struct PartialState<S: PartiallyConstrainable> {
    pub mask: S::Mask,
}

impl<S: PartiallyConstrainable> PartialState<S> {
    pub fn new(mask: S::Mask) -> Self {
        Self { mask }
    }

    /// Whether `state` satisfies this pattern.
    #[inline]
    pub fn matches(&self, state: &S) -> bool {
        S::matches(state, &self.mask)
    }
}

/// Marker that an `Action`-able state is meaningfully approximable by a
/// partial state (stub trait — implementations to follow).
pub trait CosetQueryable<G: Group>: Action<G> + PartiallyConstrainable {}
