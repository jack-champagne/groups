//! Solver: pluggable IDA* search over `(GeneratingSet, Heuristic, start,
//! goal-predicate)`.
//!
//! Optimal-word search lives outside the BSGS-based core. The two question
//! types serve different use cases:
//!
//! - "Is target reachable?" / "Give me *some* word A → B": BSGS-based,
//!   sub-millisecond, possibly long. See [`crate::bsgs`].
//! - "Give me a *short* / *optimal* word A → B": IDA* + admissible heuristic.
//!   This module.
//!
//! ## IDA* (Iterative Deepening A*)
//!
//! Korf 1985. At each iteration, runs a depth-first search bounded by an
//! `f`-cost threshold (`g + h`). On overflow, the threshold becomes the
//! minimum overshoot; iterate until a solution is found.
//!
//! Memory is `O(depth)` rather than `O(branching^depth)` like A*. Good fit
//! for puzzle search: shallow optimal-solution depth (cube god's number 20),
//! large branching (~12-18), tight admissible heuristics (corner+edge
//! pattern databases).

use smallvec::SmallVec;

use crate::generators::GeneratingSet;
use crate::word::Word;
use crate::{Action, Group};

/// Admissible distance estimator: returns a lower bound on the number of
/// generator applications needed to reach a goal from `state`.
pub trait Heuristic<G: Group, S: Action<G>> {
    fn estimate(&self, state: &S) -> u32;
}

/// Trivial heuristic that always estimates 0. Reduces IDA* to plain
/// iterative-deepening DFS — useful for small problems and as a baseline.
pub struct ZeroHeuristic;
impl<G: Group, S: Action<G>> Heuristic<G, S> for ZeroHeuristic {
    #[inline]
    fn estimate(&self, _state: &S) -> u32 {
        0
    }
}

/// Result of an IDA* search.
#[derive(Debug)]
pub struct SolveResult {
    pub word: Word,
    pub depth: u32,
    pub nodes_expanded: u64,
}

/// IDA* over a generic `(GeneratingSet, Heuristic, start, goal-predicate)`.
///
/// Returns a shortest word taking `start` to a state satisfying `is_goal`,
/// or `None` if no path within `max_depth` exists.
///
/// Generator-pruning: avoids generating `g · g⁻¹` immediately
/// (free-reduction prefix), which cuts the branching factor by ~1.
pub fn ida_star<G, S, H, F>(
    gens: &GeneratingSet<G>,
    heuristic: &H,
    start: &S,
    is_goal: F,
    max_depth: u32,
) -> Option<SolveResult>
where
    G: Group,
    S: Action<G>,
    H: Heuristic<G, S>,
    F: Fn(&S) -> bool,
{
    let mut threshold: u32 = heuristic.estimate(start);
    let mut nodes: u64 = 0;
    let mut path: SmallVec<[u8; 32]> = SmallVec::new();

    loop {
        if threshold > max_depth {
            return None;
        }

        let outcome = dfs(gens, heuristic, start, &is_goal, 0, threshold, &mut path, &mut nodes);
        match outcome {
            DfsOutcome::Found => {
                return Some(SolveResult {
                    word: Word::from_indices(path.into_iter()),
                    depth: threshold,
                    nodes_expanded: nodes,
                });
            }
            DfsOutcome::NextThreshold(t) => {
                threshold = t;
            }
            DfsOutcome::Exhausted => return None,
        }
    }
}

enum DfsOutcome {
    Found,
    NextThreshold(u32),
    Exhausted,
}

#[allow(clippy::too_many_arguments)]
fn dfs<G, S, H, F>(
    gens: &GeneratingSet<G>,
    heuristic: &H,
    state: &S,
    is_goal: &F,
    depth: u32,
    threshold: u32,
    path: &mut SmallVec<[u8; 32]>,
    nodes: &mut u64,
) -> DfsOutcome
where
    G: Group,
    S: Action<G>,
    H: Heuristic<G, S>,
    F: Fn(&S) -> bool,
{
    *nodes += 1;
    let f = depth + heuristic.estimate(state);
    if f > threshold {
        return DfsOutcome::NextThreshold(f);
    }
    if is_goal(state) {
        return DfsOutcome::Found;
    }

    let mut min_over: Option<u32> = None;
    let last_idx = path.last().copied();
    let inverse_of_last = last_idx.and_then(|i| gens.inverse_index(i as usize).map(|x| x as u8));

    for (i, gen) in gens.iter() {
        // Skip the immediate inverse of the last move (free reduction prefix).
        if Some(i) == inverse_of_last {
            continue;
        }
        let next_state = state.act(gen);
        path.push(i);
        let outcome = dfs(gens, heuristic, &next_state, is_goal, depth + 1, threshold, path, nodes);
        match outcome {
            DfsOutcome::Found => return DfsOutcome::Found,
            DfsOutcome::NextThreshold(t) => {
                min_over = Some(min_over.map_or(t, |m| m.min(t)));
            }
            DfsOutcome::Exhausted => {}
        }
        path.pop();
    }
    match min_over {
        Some(t) => DfsOutcome::NextThreshold(t),
        None => DfsOutcome::Exhausted,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::permutation::Permutation;
    use crate::Monoid;

    #[test]
    fn ida_star_finds_optimal_in_s4() {
        // Generate S_4 by adjacent transpositions, look for the 3-cycle (0 1 2)
        // as a goal state.
        let gens = GeneratingSet::with_inverses([
            Permutation::<4>::transposition(0, 1),
            Permutation::<4>::transposition(1, 2),
            Permutation::<4>::transposition(2, 3),
        ]);
        let target = Permutation::<4>::cycle(&[0, 1, 2]);
        let start = Permutation::<4>::identity();
        let result = ida_star(
            &gens,
            &ZeroHeuristic,
            &start,
            |g| *g == target,
            10,
        )
        .expect("path should exist");
        // Verify the word actually reaches the target.
        let g = result.word.evaluate(&gens);
        assert_eq!(g, target);
        // (0 1 2) decomposes as two adjacent transpositions, so the optimal
        // word length is 2.
        assert_eq!(result.word.len(), 2, "optimal length should be 2");
    }

    #[test]
    fn ida_star_handles_identity_goal() {
        let gens = GeneratingSet::with_inverses([Permutation::<4>::transposition(0, 1)]);
        let start = Permutation::<4>::identity();
        let result = ida_star(
            &gens,
            &ZeroHeuristic,
            &start,
            |g| *g == Permutation::<4>::identity(),
            5,
        )
        .expect("trivial path");
        assert_eq!(result.word.len(), 0);
    }

    #[test]
    fn ida_star_returns_none_when_unreachable() {
        // Subgroup ⟨(0 1 2)⟩: only 3-cycles and identity. The transposition
        // (0 1) is unreachable.
        let gens = GeneratingSet::with_inverses([Permutation::<4>::cycle(&[0, 1, 2])]);
        let start = Permutation::<4>::identity();
        let target = Permutation::<4>::transposition(0, 1);
        let result = ida_star(&gens, &ZeroHeuristic, &start, |g| *g == target, 8);
        assert!(result.is_none());
    }
}
