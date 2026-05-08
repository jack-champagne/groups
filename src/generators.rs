//! [`GeneratingSet`]: a labelless, plain-data set of group generators with
//! precomputed inverses.
//!
//! Algorithms (Schreier–Sims, IDA*, orbit BFS) consume `&GeneratingSet<G>` and
//! emit words as sequences of `u8` indices into the set. Caller code (e.g.
//! the `twisty-puzzles` crate) maps indices ↔ a domain-specific `MoveEnum` at
//! its own boundary.

use smallvec::SmallVec;

use crate::Group;

/// A set of group generators.
///
/// Two construction modes:
///
/// - [`GeneratingSet::new`] — accept generators as-is. Algorithms compute
///   inverses on demand by calling `g.inv()`.
/// - [`GeneratingSet::with_inverses`] — double the set so it includes each
///   generator's inverse as an explicit member, in even/odd-paired order:
///   `[g₀, g₀⁻¹, g₁, g₁⁻¹, …]`. The invariant `gens.inverse_index(i) = i ^ 1`
///   then holds, which Schreier–Sims and free reduction rely on for cheap
///   inverse lookups.
#[derive(Debug, Clone)]
pub struct GeneratingSet<G: Group> {
    gens: SmallVec<[G; 32]>,
    /// `true` iff the set was built via [`with_inverses`] and therefore
    /// satisfies the even/odd-pair inverse invariant. Built fresh by `new`
    /// without claiming the invariant.
    paired_inverses: bool,
}

impl<G: Group> GeneratingSet<G> {
    /// Constructs a generating set from the supplied elements as-is.
    /// `inverse_index` will fall back to a linear search.
    pub fn new(gens: impl IntoIterator<Item = G>) -> Self {
        Self {
            gens: gens.into_iter().collect(),
            paired_inverses: false,
        }
    }

    /// Constructs a generating set whose entries alternate `[gᵢ, gᵢ⁻¹, …]`.
    /// `inverse_index(i) == i ^ 1` is then a constant-time lookup.
    pub fn with_inverses(gens: impl IntoIterator<Item = G>) -> Self {
        let mut out: SmallVec<[G; 32]> = SmallVec::new();
        for g in gens {
            out.push(g);
            out.push(g.inv());
        }
        Self {
            gens: out,
            paired_inverses: true,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.gens.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.gens.is_empty()
    }

    #[inline]
    pub fn get(&self, i: usize) -> &G {
        &self.gens[i]
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (u8, &G)> {
        self.gens
            .iter()
            .enumerate()
            .map(|(i, g)| (i as u8, g))
    }

    /// Returns the index `j` such that `gens[i].op(&gens[j]) == identity`.
    /// O(1) when constructed via `with_inverses`; O(n) otherwise.
    pub fn inverse_index(&self, i: usize) -> Option<usize> {
        if self.paired_inverses {
            let j = i ^ 1;
            return if j < self.gens.len() { Some(j) } else { None };
        }
        let target = self.gens[i].inv();
        self.gens.iter().position(|g| *g == target)
    }

    /// Whether each generator's inverse is also stored in the set.
    #[inline]
    pub fn has_paired_inverses(&self) -> bool {
        self.paired_inverses
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cyclic::Cyclic;
    use crate::permutation::Permutation;
    use crate::{Magma, Monoid};

    #[test]
    fn new_stores_generators_verbatim() {
        let g = GeneratingSet::new([Cyclic::<5>::from_index(1), Cyclic::<5>::from_index(2)]);
        assert_eq!(g.len(), 2);
        assert!(!g.has_paired_inverses());
    }

    #[test]
    fn with_inverses_doubles_and_pairs() {
        let g = GeneratingSet::with_inverses([Cyclic::<5>::from_index(1)]);
        assert_eq!(g.len(), 2);
        assert!(g.has_paired_inverses());
        assert_eq!(*g.get(0), Cyclic::<5>::from_index(1));
        assert_eq!(*g.get(1), Cyclic::<5>::from_index(4)); // inverse of 1 mod 5 is 4
        assert_eq!(g.inverse_index(0), Some(1));
        assert_eq!(g.inverse_index(1), Some(0));
    }

    #[test]
    fn inverse_index_falls_back_to_linear_search() {
        // Build a set where inverses happen to be present but not paired.
        let g = GeneratingSet::new([
            Cyclic::<5>::from_index(1),
            Cyclic::<5>::from_index(2),
            Cyclic::<5>::from_index(4), // inverse of 1
            Cyclic::<5>::from_index(3), // inverse of 2
        ]);
        assert_eq!(g.inverse_index(0), Some(2));
        assert_eq!(g.inverse_index(1), Some(3));
    }

    #[test]
    fn cube_qtm_face_moves_have_paired_inverses() {
        // Tiny stand-in for the cube generating set: two non-trivial S_4
        // permutations. After with_inverses, length is 4 and pairing holds.
        let r = Permutation::<4>::cycle(&[0, 1, 2, 3]);
        let u = Permutation::<4>::transposition(0, 2);
        let g = GeneratingSet::with_inverses([r, u]);
        assert_eq!(g.len(), 4);
        for i in 0..g.len() {
            let j = g.inverse_index(i).unwrap();
            assert_eq!(
                g.get(i).op(g.get(j)),
                Permutation::<4>::identity(),
                "gens[{i}] · gens[{j}] should be identity",
            );
        }
    }
}
