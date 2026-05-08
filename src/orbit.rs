//! Orbit enumeration.
//!
//! BFS over the Cayley graph of `⟨gens⟩` rooted at `start`, returning every
//! reachable state with a shortest word producing it. Bounded by `max_size`
//! so callers can cap memory on large or unknown-size groups.
//!
//! Useful for:
//! - Building complete algorithm tables for small subgroups (e.g., the 3×3
//!   last-layer subgroup, |LL| = 62,208 — fits in <50 MB).
//! - Validating subgroup orders via "enumerate everything reachable, count."
//! - Discovering shortest-word representations for every coset of a
//!   small-index subgroup.

use std::collections::HashMap;

use crate::generators::GeneratingSet;
use crate::word::Word;
use crate::Group;

/// Map of every state reachable from `start` to a shortest word producing it.
#[derive(Debug, Clone)]
pub struct OrbitMap<G: Group + std::hash::Hash> {
    pub start: G,
    pub states: HashMap<G, Word>,
    /// `true` if BFS terminated naturally; `false` if the cap was hit.
    pub complete: bool,
}

impl<G: Group + std::hash::Hash> OrbitMap<G> {
    pub fn len(&self) -> usize {
        self.states.len()
    }

    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }

    /// Shortest word taking `start` to `target`, or `None` if `target` is
    /// not in the orbit (or wasn't visited before the cap).
    pub fn word_to(&self, target: &G) -> Option<&Word> {
        self.states.get(target)
    }
}

/// BFS-enumerate the orbit of `start` under `gens`, capping at `max_size`
/// states. Returns all visited states with their shortest words.
///
/// For small subgroups (e.g., LL at 62,208 states), call with a generous
/// cap (~100K). For large or unbounded explorations, set the cap to the
/// memory you can afford and inspect `result.complete` to see whether BFS
/// finished or hit the cap.
pub fn enumerate_orbit<G>(
    start: &G,
    gens: &GeneratingSet<G>,
    max_size: usize,
) -> OrbitMap<G>
where
    G: Group + std::hash::Hash,
{
    let mut states: HashMap<G, Word> = HashMap::new();
    states.insert(*start, Word::new());

    let mut frontier: Vec<G> = vec![*start];

    while !frontier.is_empty() {
        if states.len() >= max_size {
            return OrbitMap {
                start: *start,
                states,
                complete: false,
            };
        }
        let mut next: Vec<G> = Vec::new();
        for cur in &frontier {
            let cur_word = states[cur].clone();
            for (i, gen) in gens.iter() {
                let nxt = cur.op(gen);
                if !states.contains_key(&nxt) {
                    let mut w = cur_word.clone();
                    w.push(i);
                    states.insert(nxt, w);
                    next.push(nxt);
                    if states.len() >= max_size {
                        return OrbitMap {
                            start: *start,
                            states,
                            complete: false,
                        };
                    }
                }
            }
        }
        frontier = next;
    }
    OrbitMap {
        start: *start,
        states,
        complete: true,
    }
}

/// Enumerate the orbit of `start` under a list of `(G, Word)` pairs (gens
/// with face-move expansions). Returns every reachable state mapped to a
/// shortest *face-move* word, by concatenating the per-gen word at each
/// BFS step.
///
/// Use this when the gens were extracted via
/// [`crate::schreier_sims::deterministic_with_words::BsgsWithWords::stabilizer_generators_with_words`]
/// — each gen carries its face-move expansion, and the orbit map produced
/// here gives you face-move algorithms for every state in the subgroup
/// directly (no further translation step).
pub fn enumerate_orbit_translated<G>(
    start: &G,
    gens_with_words: &[(G, Word)],
    max_size: usize,
) -> OrbitMap<G>
where
    G: Group + std::hash::Hash,
{
    use std::collections::HashMap;

    let mut states: HashMap<G, Word> = HashMap::new();
    states.insert(*start, Word::new());

    let mut frontier: Vec<G> = vec![*start];

    while !frontier.is_empty() {
        if states.len() >= max_size {
            return OrbitMap {
                start: *start,
                states,
                complete: false,
            };
        }
        let mut next: Vec<G> = Vec::new();
        for cur in &frontier {
            let cur_word = states[cur].clone();
            for (g, w) in gens_with_words {
                let nxt = cur.op(g);
                if !states.contains_key(&nxt) {
                    let new_word = cur_word.clone().concat(w);
                    states.insert(nxt, new_word);
                    next.push(nxt);
                    if states.len() >= max_size {
                        return OrbitMap {
                            start: *start,
                            states,
                            complete: false,
                        };
                    }
                }
            }
        }
        frontier = next;
    }
    OrbitMap {
        start: *start,
        states,
        complete: true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cyclic::Cyclic;
    use crate::permutation::Permutation;
    use crate::Monoid;

    #[test]
    fn enumerate_cyclic_5() {
        let gens = GeneratingSet::with_inverses([Cyclic::<5>::from_index(1)]);
        let orbit = enumerate_orbit(&Cyclic::<5>::identity(), &gens, 100);
        assert!(orbit.complete);
        assert_eq!(orbit.len(), 5);
    }

    #[test]
    fn enumerate_s_4_via_adjacent_transpositions() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<4>::transposition(0, 1),
            Permutation::<4>::transposition(1, 2),
            Permutation::<4>::transposition(2, 3),
        ]);
        let orbit = enumerate_orbit(&Permutation::<4>::identity(), &gens, 100);
        assert!(orbit.complete);
        assert_eq!(orbit.len(), 24);
    }

    #[test]
    fn enumerate_a_4() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<4>::cycle(&[0, 1, 2]),
            Permutation::<4>::cycle(&[1, 2, 3]),
        ]);
        let orbit = enumerate_orbit(&Permutation::<4>::identity(), &gens, 100);
        assert!(orbit.complete);
        assert_eq!(orbit.len(), 12);
    }

    #[test]
    fn enumerate_with_cap_returns_partial() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<5>::transposition(0, 1),
            Permutation::<5>::cycle(&[0, 1, 2, 3, 4]),
        ]);
        let orbit = enumerate_orbit(&Permutation::<5>::identity(), &gens, 50);
        assert!(!orbit.complete);
        assert!(orbit.len() <= 50);
    }

    #[test]
    fn shortest_words_via_word_to() {
        let gens = GeneratingSet::with_inverses([Permutation::<4>::transposition(0, 1)]);
        let orbit = enumerate_orbit(&Permutation::<4>::identity(), &gens, 10);
        // (0 1) reachable in 1 step.
        let target = Permutation::<4>::transposition(0, 1);
        let w = orbit.word_to(&target).unwrap();
        assert_eq!(w.len(), 1);
    }
}
