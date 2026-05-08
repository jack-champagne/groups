//! Las Vegas Schreier–Sims (TODO).
//!
//! Run Monte Carlo, then verify by deterministically completing the chain
//! (i.e., running the deterministic Schreier-generator pass on the existing
//! BSGS to confirm every Schreier generator sifts to identity). Fast in
//! expectation, correct with certainty.
//!
//! ## Status
//!
//! Stubbed. When implemented, the verification pass reuses
//! `super::deterministic`'s Schreier-generator inner loop on the already-built
//! chain — the bulk of the code is shared.

use crate::bsgs::{Bsgs, PermutationLike};
use crate::generators::GeneratingSet;

pub fn las_vegas<G, const N: usize>(
    _gens: &GeneratingSet<G>,
    _base_hint: &[u16],
) -> Bsgs<G, N>
where
    G: PermutationLike<N>,
{
    unimplemented!("Las Vegas Schreier-Sims — see super::deterministic for v1")
}
