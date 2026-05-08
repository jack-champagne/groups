//! [`Word`]: a sequence of generator indices, the universal word/algorithm
//! type produced by Schreier–Sims and the solver.
//!
//! `Word` is plain data — it does not know which group it applies to. Methods
//! that need group context (`apply`, `inv`, `reduce`) take the
//! [`GeneratingSet`] as an explicit argument. The puzzle layer wraps `Word` in
//! domain-specific types (e.g. `CubeAlgorithm(Word)`) and provides `Display`,
//! `parse`, etc.

use smallvec::SmallVec;

use crate::generators::GeneratingSet;
use crate::{Action, Group};

/// A sequence of generator indices.
///
/// Storage is `SmallVec<[u8; 32]>` — typical cube solutions are 20-50 moves,
/// so 32 inline slots cover the median without allocation; longer sequences
/// spill to heap.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Word {
    indices: SmallVec<[u8; 32]>,
}

impl Word {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_indices(indices: impl IntoIterator<Item = u8>) -> Self {
        Self {
            indices: indices.into_iter().collect(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.indices.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.indices.is_empty()
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = u8> + '_ {
        self.indices.iter().copied()
    }

    pub fn push(&mut self, gen: u8) {
        self.indices.push(gen);
    }

    pub fn extend(&mut self, other: &Word) {
        self.indices.extend(other.indices.iter().copied());
    }

    pub fn concat(mut self, other: &Word) -> Word {
        self.extend(other);
        self
    }

    /// Apply this word to a state under a generating set, left-to-right.
    pub fn apply<G, S>(&self, gens: &GeneratingSet<G>, state: &S) -> S
    where
        G: Group,
        S: Action<G>,
    {
        let mut s = *state;
        for &i in &self.indices {
            s = s.act(gens.get(i as usize));
        }
        s
    }

    /// Evaluate this word as a single group element.
    pub fn evaluate<G: Group>(&self, gens: &GeneratingSet<G>) -> G {
        let mut acc = G::identity();
        for &i in &self.indices {
            acc = acc.op(gens.get(i as usize));
        }
        acc
    }

    /// Inverse of this word, expressed as indices into the same generating
    /// set. Requires every generator to have its inverse present in the set.
    /// Panics otherwise.
    pub fn inv<G: Group>(&self, gens: &GeneratingSet<G>) -> Word {
        let mut out = SmallVec::with_capacity(self.indices.len());
        for &i in self.indices.iter().rev() {
            let j = gens
                .inverse_index(i as usize)
                .expect("Word::inv: generating set lacks an inverse for this index; \
                         construct via GeneratingSet::with_inverses");
            out.push(j as u8);
        }
        Word { indices: out }
    }

    /// Free reduction: remove adjacent `gᵢ gᵢ⁻¹` pairs to a fixed point.
    /// Requires the generating set to know each generator's inverse index.
    pub fn reduce<G: Group>(&mut self, gens: &GeneratingSet<G>) {
        let mut stack: SmallVec<[u8; 32]> = SmallVec::new();
        for &i in &self.indices {
            if let Some(&top) = stack.last() {
                if let Some(top_inv) = gens.inverse_index(top as usize) {
                    if top_inv as u8 == i {
                        stack.pop();
                        continue;
                    }
                }
            }
            stack.push(i);
        }
        self.indices = stack;
    }

    /// Inverse word for paired-inverse generating sets (those built via
    /// [`GeneratingSet::with_inverses`]). Reverses the index sequence and
    /// XOR-toggles the low bit of each — exploiting that paired inverses
    /// sit at consecutive even/odd indices.
    ///
    /// Cheaper than [`Word::inv`] (no per-index linear search) but requires
    /// the paired-inverse layout. Panics if any index is out of range; UB
    /// only in the sense that the resulting word is meaningful only
    /// against the same paired set.
    pub fn inv_paired(&self) -> Word {
        Word {
            indices: self.indices.iter().rev().map(|i| i ^ 1).collect(),
        }
    }
}

impl IntoIterator for Word {
    type Item = u8;
    type IntoIter = smallvec::IntoIter<[u8; 32]>;
    fn into_iter(self) -> Self::IntoIter {
        self.indices.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cyclic::Cyclic;
    use crate::permutation::Permutation;
    use crate::{Magma, Monoid};

    #[test]
    fn empty_word_is_identity_evaluation() {
        let g = GeneratingSet::with_inverses([Cyclic::<5>::from_index(1)]);
        let w = Word::new();
        assert_eq!(w.evaluate(&g), Cyclic::<5>::identity());
    }

    #[test]
    fn evaluate_composes_left_to_right() {
        let g = GeneratingSet::with_inverses([Cyclic::<7>::from_index(2)]);
        // Apply generator at index 0 three times: 2+2+2 = 6 mod 7
        let w = Word::from_indices([0, 0, 0]);
        assert_eq!(w.evaluate(&g), Cyclic::<7>::from_index(6));
    }

    #[test]
    fn inverse_of_word() {
        let g = GeneratingSet::with_inverses([
            Permutation::<4>::cycle(&[0, 1, 2, 3]),
            Permutation::<4>::transposition(0, 2),
        ]);
        let w = Word::from_indices([0, 2, 0]);
        let w_inv = w.inv(&g);
        let composed = w.evaluate(&g).op(&w_inv.evaluate(&g));
        assert_eq!(composed, Permutation::<4>::identity());
    }

    #[test]
    fn reduce_cancels_adjacent_inverses() {
        let g = GeneratingSet::with_inverses([
            Cyclic::<5>::from_index(1),
            Cyclic::<5>::from_index(2),
        ]);
        // gens: [g0, g0⁻¹, g1, g1⁻¹] (indices 0, 1, 2, 3)
        let mut w = Word::from_indices([0, 1, 2, 3, 0]); // [g0, g0⁻¹, g1, g1⁻¹, g0]
        w.reduce(&g);
        // After reduction: [g0]
        assert_eq!(w.iter().collect::<Vec<_>>(), vec![0u8]);
    }

    #[test]
    fn reduce_to_empty() {
        let g = GeneratingSet::with_inverses([Cyclic::<5>::from_index(1)]);
        let mut w = Word::from_indices([0, 1, 0, 1]);
        w.reduce(&g);
        assert!(w.is_empty());
    }

    #[test]
    fn apply_to_state() {
        let g = GeneratingSet::with_inverses([Permutation::<4>::cycle(&[0, 1, 2, 3])]);
        let state: [u16; 4] = [10, 20, 30, 40];
        // Apply generator twice: equivalent to applying its square
        let w = Word::from_indices([0, 0]);
        let result = w.apply(&g, &state);
        let twice = state.act(g.get(0)).act(g.get(0));
        assert_eq!(result, twice);
    }
}
