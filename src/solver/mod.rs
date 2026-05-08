//! Solver: pluggable search algorithms over `Action<G>` + `GeneratingSet<G>` +
//! a `Heuristic`.
//!
//! Optimal-word search (IDA* with pruning tables) intentionally lives outside
//! the BSGS-based core. The two question types serve different use cases:
//!
//! - "Is target reachable?" / "Give me *some* word A → B": BSGS-based,
//!   sub-millisecond, possibly-long words. See [`crate::bsgs`].
//! - "Give me a *short* / *optimal* word A → B": IDA* + admissible heuristic,
//!   tens of MB to GB of pruning tables, milliseconds to seconds. This module.
//!
//! The trait surface is fixed in v1 so consumers can plug in their own
//! heuristics. Implementation lands post-v1.

use crate::generators::GeneratingSet;
use crate::word::Word;
use crate::{Action, Group};

/// An admissible distance estimator: returns a lower bound on the number of
/// generator applications needed to take `state` to a goal.
///
/// "Admissible" means the estimate must never *over*estimate the true
/// distance — IDA* and other heuristic-search algorithms rely on this for
/// optimality.
pub trait Heuristic<G: Group, S: Action<G>> {
    /// Estimated minimum number of generator applications from `state` to a
    /// goal state.
    fn estimate(&self, state: &S) -> u32;
}

/// IDA* over a generic `(GeneratingSet, Heuristic, start, goal-predicate)`.
///
/// Returns a shortest word taking `start` to a state satisfying `is_goal`,
/// or `None` if no path within `max_depth` exists.
///
/// **Status**: stubbed. Consumers can implement `Heuristic` today; the search
/// implementation lands post-v1.
pub fn ida_star<G, S, H, F>(
    _gens: &GeneratingSet<G>,
    _heuristic: &H,
    _start: &S,
    _is_goal: F,
    _max_depth: u32,
) -> Option<Word>
where
    G: Group,
    S: Action<G>,
    H: Heuristic<G, S>,
    F: Fn(&S) -> bool,
{
    unimplemented!("IDA* — trait surface laid down, implementation post-v1")
}
