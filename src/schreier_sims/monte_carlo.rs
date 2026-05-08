//! Monte Carlo Schreier–Sims (TODO).
//!
//! Sift random products of generators; when sift fails, append the residue to
//! the appropriate stabilizer level. Faster than deterministic in expectation
//! but with a small probability of producing an incomplete chain.
//!
//! ## Status
//!
//! Not yet implemented. The deterministic variant (`super::deterministic`)
//! produces a `Bsgs<G, N>` that downstream code consumes verbatim — when this
//! variant lands, it will produce the same `Bsgs` shape, with all consumers
//! (sift, membership, word reconstruction) unchanged.

use crate::bsgs::{Bsgs, PermutationLike};
use crate::generators::GeneratingSet;

/// Build a BSGS from `gens` using random sift. Returns `Err` if convergence
/// fails to reach the required confidence.
pub fn monte_carlo<G, const N: usize>(
    _gens: &GeneratingSet<G>,
    _base_hint: &[u16],
    _confidence: f64,
) -> Result<Bsgs<G, N>, IncompleteChain>
where
    G: PermutationLike<N>,
{
    unimplemented!("Monte Carlo Schreier-Sims — see super::deterministic for v1")
}

/// Reported when Monte Carlo sift didn't converge to the required confidence
/// level. Consumers should retry with deterministic verification (Las Vegas)
/// or fall back to deterministic.
#[derive(Debug)]
pub struct IncompleteChain {
    pub samples_taken: usize,
    pub confidence_achieved: f64,
}
