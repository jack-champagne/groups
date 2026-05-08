//! Partial states: the "fix these slots / wildcard those slots" headline
//! feature.
//!
//! A `PartialState` describes a *coset* of a pointwise stabilizer:
//! "every state matching this pattern, where some slots are pinned to a
//! specific value and others are wildcards."
//!
//! ## Implementation
//!
//! For state types that act on points `0..N` via a `PermutationLike` group,
//! the natural per-slot constraint is "the point that ends up at this slot
//! must equal a specific value." [`Bsgs::coset_member_word`] then asks
//! Schreier–Sims: does any group element take the start state to a state
//! satisfying the constraints?
//!
//! Mathematically, this is a coset query:
//! `{ g ∈ G | start.act(g) matches partial }`.
//! When the BSGS base is chosen to put constrained slots first, sift naturally
//! projects the search onto the constraint set.

use crate::bsgs::{Bsgs, PermutationLike};
use crate::Group;

/// Per-slot constraint.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Constraint {
    /// Slot value is irrelevant.
    Wildcard,
    /// Slot value must equal this point. Stored as a `u16` index into the
    /// `0..N` action set the BSGS lives over.
    MustEqual(u16),
}

/// A constraint pattern over the `0..N` action set of a `PermutationLike`
/// group.
///
/// `constraints[i] = MustEqual(v)` means "after applying the group element
/// to the start state, the value at slot `i` must equal `v`."
/// `constraints[i] = Wildcard` means "anything goes at slot `i`."
#[derive(Debug, Clone)]
pub struct PartialState<const N: usize> {
    pub constraints: [Constraint; N],
}

impl<const N: usize> PartialState<N> {
    /// All slots wildcard.
    pub fn any() -> Self {
        Self {
            constraints: [Constraint::Wildcard; N],
        }
    }

    /// All slots pinned to a specific full state. Equivalent to "must reach
    /// this exact state."
    pub fn pinned_to(state: &[u16; N]) -> Self {
        let mut constraints = [Constraint::Wildcard; N];
        for (i, &v) in state.iter().enumerate() {
            constraints[i] = Constraint::MustEqual(v);
        }
        Self { constraints }
    }

    /// Returns indices of constrained (non-wildcard) slots.
    pub fn constrained_indices(&self) -> impl Iterator<Item = u16> + '_ {
        self.constraints.iter().enumerate().filter_map(|(i, c)| match c {
            Constraint::MustEqual(_) => Some(i as u16),
            Constraint::Wildcard => None,
        })
    }

    /// Builder: pin a slot to a specific value.
    pub fn pin(mut self, slot: u16, value: u16) -> Self {
        self.constraints[slot as usize] = Constraint::MustEqual(value);
        self
    }

    /// Builder: free (wildcard) a slot.
    pub fn free(mut self, slot: u16) -> Self {
        self.constraints[slot as usize] = Constraint::Wildcard;
        self
    }

    /// `true` iff the start point's image under `g` satisfies the constraints,
    /// where the start point is implied by where `g` sends each slot.
    ///
    /// More precisely: for each slot `i`, we check that `g.apply_to(i) == v`
    /// where `v` is `MustEqual(v)`. Wildcard slots impose no constraint.
    pub fn matches<G, const M: usize>(&self, g: &G) -> bool
    where
        G: PermutationLike<M>,
    {
        debug_assert_eq!(M, N, "PartialState size must match the group's action size");
        for (i, c) in self.constraints.iter().enumerate() {
            if let Constraint::MustEqual(v) = c {
                if g.apply_to(i as u16) != *v {
                    return false;
                }
            }
        }
        true
    }
}

impl<G, const N: usize> Bsgs<G, N>
where
    G: PermutationLike<N>,
{
    /// Whether some element of `G` maps the identity to a state satisfying
    /// the partial-state constraints — i.e., does there exist `g ∈ G` such
    /// that `partial.matches(&g)`?
    ///
    /// Implementation: BFS over the Cayley graph filtered by the constraint
    /// pattern. For puzzle-scale this is feasible when the search depth is
    /// modest; for huge groups, prefer the coset-aware path that uses the
    /// stabilizer chain structure (post-v1).
    pub fn coset_member_exists(
        &self,
        gens: &crate::generators::GeneratingSet<G>,
        partial: &PartialState<N>,
    ) -> bool
    where
        G: std::hash::Hash,
    {
        self.coset_member_word(gens, partial).is_some()
    }

    /// Returns a word reaching a state matching `partial`, or `None` if no
    /// such state is reachable within the search budget.
    ///
    /// For coset queries that hit identity-matching constraints, the trivial
    /// word suffices.
    pub fn coset_member_word(
        &self,
        gens: &crate::generators::GeneratingSet<G>,
        partial: &PartialState<N>,
    ) -> Option<crate::word::Word>
    where
        G: std::hash::Hash,
    {
        use crate::word::Word;
        use crate::Monoid;
        use std::collections::HashMap;

        let id = G::identity();
        if partial.matches(&id) {
            return Some(Word::new());
        }

        // Bounded BFS over the Cayley graph filtered by membership in G
        // (every state we consider is reachable via the given gens, so this
        // is automatic) and the constraint pattern.
        let mut prev: HashMap<G, (G, u8)> = HashMap::new();
        let mut frontier: Vec<G> = vec![id];
        let max_depth: u32 = 30;
        for _ in 0..max_depth {
            let mut next: Vec<G> = Vec::new();
            for &cur in &frontier {
                for (i, gen) in gens.iter() {
                    let nxt = cur.op(gen);
                    if partial.matches(&nxt) {
                        let mut w_rev = vec![i];
                        let mut node = cur;
                        while node != id {
                            let (parent, edge) = prev[&node];
                            w_rev.push(edge);
                            node = parent;
                        }
                        w_rev.reverse();
                        return Some(Word::from_indices(w_rev));
                    }
                    if !prev.contains_key(&nxt) && nxt != id {
                        prev.insert(nxt, (cur, i));
                        next.push(nxt);
                    }
                }
            }
            if next.is_empty() {
                break;
            }
            frontier = next;
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generators::GeneratingSet;
    use crate::permutation::Permutation;
    use crate::schreier_sims::deterministic::deterministic;
    use crate::Monoid;

    #[test]
    fn pinned_to_self_is_identity_match() {
        let identity_state = [0u16, 1, 2, 3];
        let partial = PartialState::<4>::pinned_to(&identity_state);
        assert!(partial.matches(&Permutation::<4>::identity()));
    }

    #[test]
    fn pin_specific_slot() {
        // PartialState pinning slot 0 to 2: any g with g.apply_to(0) == 2.
        let partial = PartialState::<4>::any().pin(0, 2);
        let g = Permutation::<4>::cycle(&[0, 1, 2]);  // 0→1→2→0
        // g sends 0 to 1, not 2. Should not match.
        assert!(!partial.matches(&g));
        let h = Permutation::<4>::cycle(&[0, 2]);  // swaps 0 and 2
        assert!(partial.matches(&h));
    }

    #[test]
    fn coset_member_finds_specific_pin() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<4>::transposition(0, 1),
            Permutation::<4>::transposition(1, 2),
            Permutation::<4>::transposition(2, 3),
        ]);
        let bsgs = deterministic::<_, 4>(&gens, &[0, 1, 2]);
        // "Find a sequence of moves that puts 2 in slot 0."
        let partial = PartialState::<4>::any().pin(0, 2);
        let w = bsgs.coset_member_word(&gens, &partial).expect("should exist in S_4");
        let g = w.evaluate(&gens);
        assert_eq!(g.apply_to(0), 2);
    }

    #[test]
    fn coset_member_returns_none_for_unreachable() {
        // A group generated by a single 3-cycle: only even permutations of {0,1,2,3}
        // — well, only 3-cycles in fact. Slot 3 stays fixed at value 3. So pinning
        // slot 3 to value 0 should be unreachable.
        let gens = GeneratingSet::with_inverses([Permutation::<4>::cycle(&[0, 1, 2])]);
        let bsgs = deterministic::<_, 4>(&gens, &[0, 1, 2]);
        let partial = PartialState::<4>::any().pin(3, 0);
        assert!(bsgs.coset_member_word(&gens, &partial).is_none());
    }

    #[test]
    fn fix_some_slots_free_others() {
        // "Find moves that take 0 to 0 (stays fixed) but get 2 into slot 1."
        let gens = GeneratingSet::with_inverses([
            Permutation::<4>::transposition(0, 1),
            Permutation::<4>::transposition(1, 2),
            Permutation::<4>::transposition(2, 3),
        ]);
        let bsgs = deterministic::<_, 4>(&gens, &[0, 1, 2]);
        let partial = PartialState::<4>::any()
            .pin(0, 0) // slot 0 stays at value 0
            .pin(1, 2); // slot 1 becomes value 2
        let w = bsgs
            .coset_member_word(&gens, &partial)
            .expect("should exist");
        let g = w.evaluate(&gens);
        assert_eq!(g.apply_to(0), 0);
        assert_eq!(g.apply_to(1), 2);
    }
}
