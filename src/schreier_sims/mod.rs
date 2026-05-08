//! Schreier–Sims algorithm variants.
//!
//! All variants build the same [`Bsgs`][crate::bsgs::Bsgs] output. The choice
//! affects construction time and probabilistic-failure semantics; query-time
//! cost (sift, membership, |G|) is identical across variants.
//!
//! Variants:
//!
//! - [`deterministic`] — [Sims 1970]. Provably correct, exhaustive on Schreier
//!   generators. Best when you need certainty.
//! - `monte_carlo` (TODO) — sift random products until convergence; small
//!   probability of incomplete chain.
//! - `las_vegas` (TODO) — Monte Carlo + a deterministic verification pass for
//!   correctness with certainty.
//!
//! [Sims 1970]: https://en.wikipedia.org/wiki/Schreier%E2%80%93Sims_algorithm

pub mod deterministic;
pub mod deterministic_with_words;
pub mod las_vegas;
pub mod monte_carlo;
