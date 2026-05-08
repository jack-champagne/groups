//! Monte Carlo Schreier–Sims.
//!
//! Sift random products of generators; when the residue is non-trivial, append
//! it to the appropriate stabilizer level. After enough random samples have
//! sifted to identity in a row, declare the chain "probably complete."
//!
//! Faster than deterministic in expectation but with a bounded probability of
//! producing an incomplete chain. Use [`super::las_vegas`] when you need
//! certainty.
//!
//! ## Probability bound
//!
//! After a chain has reached "true" completeness, every subsequent random sift
//! reduces to identity. If the chain is still missing some element of `G`,
//! the probability that a uniformly random product sifts to identity is at
//! most ½ (this is the standard random-Schreier bound — see Holt's Handbook
//! of CGT, §4.4). So `k` consecutive identity sifts give a failure
//! probability ≤ 2⁻ᵏ.
//!
//! With `confidence = 1 - 2⁻⁶⁴`, we need `k ≥ 64` consecutive identity sifts.

use rand::seq::IteratorRandom;
use rand::Rng;
use smallvec::SmallVec;

use crate::bsgs::{Bsgs, PermutationLike, StabilizerLevel};
use crate::generators::GeneratingSet;

/// Build a BSGS via random sifts.
///
/// `confidence`: target probability that the resulting chain is complete.
/// E.g., `1.0 - 2.0_f64.powi(-64)` for ~2⁻⁶⁴ failure probability.
pub fn monte_carlo<G, R, const N: usize>(
    gens: &GeneratingSet<G>,
    base_hint: &[u16],
    rng: &mut R,
    confidence: f64,
) -> Bsgs<G, N>
where
    G: PermutationLike<N>,
    R: Rng + ?Sized,
{
    // k = ceil(-log2(1 - confidence))
    let failure_prob = (1.0 - confidence).max(2f64.powi(-1023));
    let k_required = (-failure_prob.log2()).ceil() as u32;
    let k_required = k_required.max(16); // sane minimum

    let mut bsgs: Bsgs<G, N> = Bsgs::empty();
    bsgs.base = SmallVec::from_iter(base_hint.iter().copied());

    for &b in base_hint {
        bsgs.levels.push(StabilizerLevel::empty(b));
    }
    if bsgs.levels.is_empty() {
        if let Some(b) = first_moved_point::<G, N>(gens) {
            bsgs.base.push(b);
            bsgs.levels.push(StabilizerLevel::empty(b));
        } else {
            return bsgs;
        }
    }
    bsgs.levels[0].strong_gens = gens.iter().map(|(_, g)| *g).collect();

    // Build initial orbits with the seed strong gens.
    for i in 0..bsgs.levels.len() {
        extend_orbit(&mut bsgs, i);
    }

    let mut consecutive_clean: u32 = 0;
    while consecutive_clean < k_required {
        let g = random_product(gens, rng, 16);
        let residue = sift(&bsgs, &g);
        if let Some(h) = residue {
            // Find the deepest level the residue stabilizes; add it there.
            install_residue(&mut bsgs, h);
            consecutive_clean = 0;
        } else {
            consecutive_clean += 1;
        }
    }
    bsgs
}

fn first_moved_point<G, const N: usize>(gens: &GeneratingSet<G>) -> Option<u16>
where
    G: PermutationLike<N>,
{
    for (_, g) in gens.iter() {
        for i in 0..(N as u16) {
            if g.apply_to(i) != i {
                return Some(i);
            }
        }
    }
    None
}

fn random_product<G, R>(gens: &GeneratingSet<G>, rng: &mut R, length: usize) -> G
where
    G: crate::Group,
    R: Rng + ?Sized,
{
    // Monoid is reachable via Group supertrait
    let mut acc = G::identity();
    for _ in 0..length {
        if let Some((_, g)) = gens.iter().choose(rng) {
            acc = acc.op(g);
        }
    }
    acc
}

/// Sift `g` through the chain. Returns Some(residue) if g is not in the
/// (current) group; None if it sifts to identity.
fn sift<G, const N: usize>(bsgs: &Bsgs<G, N>, g: &G) -> Option<G>
where
    G: PermutationLike<N>,
{
    let mut h = *g;
    for level in &bsgs.levels {
        let j = h.apply_to(level.base_point);
        match &level.transversal[j as usize] {
            Some(u) => h = h.op(&u.inv()),
            None => return Some(h),
        }
    }
    // Monoid is reachable via Group supertrait
    if h == G::identity() {
        None
    } else {
        Some(h)
    }
}

/// Install a non-trivial sift residue at the appropriate level (the one whose
/// base it doesn't fix), extending the base if needed.
fn install_residue<G, const N: usize>(bsgs: &mut Bsgs<G, N>, residue: G)
where
    G: PermutationLike<N>,
{
    // Monoid is reachable via Group supertrait
    // Find the first level whose base_point is moved by residue.
    let target_level = bsgs
        .levels
        .iter()
        .position(|lvl| residue.apply_to(lvl.base_point) != lvl.base_point);
    let target_level = match target_level {
        Some(idx) => idx,
        None => {
            // Residue fixes every base point. Need to extend the base with a
            // new point.
            let new_base = (0..N as u16)
                .find(|&p| residue.apply_to(p) != p)
                .expect("non-identity residue fixes all points?");
            bsgs.base.push(new_base);
            bsgs.levels.push(StabilizerLevel::empty(new_base));
            bsgs.levels.len() - 1
        }
    };
    bsgs.levels[target_level].strong_gens.push(residue);
    // Re-extend orbits at this level and shallower (since deeper orbits are
    // unaffected, but shallower orbits gain the new generator from the union).
    for i in (0..=target_level).rev() {
        extend_orbit(bsgs, i);
    }
}

/// Compute the orbit of `bsgs.levels[i].base_point` under the union of strong
/// gens from levels `[i, end]`.
fn extend_orbit<G, const N: usize>(bsgs: &mut Bsgs<G, N>, level: usize)
where
    G: PermutationLike<N>,
{
    // Monoid is reachable via Group supertrait
    let base_point = bsgs.levels[level].base_point;
    let mut transversal: Vec<Option<G>> = (0..N).map(|_| None).collect();
    transversal[base_point as usize] = Some(G::identity());

    let mut strong_gens: Vec<G> = Vec::new();
    for lvl in &bsgs.levels[level..] {
        strong_gens.extend(lvl.strong_gens.iter().copied());
    }

    let mut frontier: Vec<u16> = vec![base_point];
    while let Some(beta) = frontier.pop() {
        let u_beta = transversal[beta as usize].expect("frontier point must have a rep");
        for s in &strong_gens {
            let img = s.apply_to(beta);
            if transversal[img as usize].is_none() {
                transversal[img as usize] = Some(u_beta.op(s));
                frontier.push(img);
            }
        }
    }
    bsgs.levels[level].transversal = transversal.into_boxed_slice();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::permutation::Permutation;
    use rand::SeedableRng;
    use rand::rngs::StdRng;

    #[test]
    fn s_5_via_monte_carlo() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<5>::transposition(0, 1),
            Permutation::<5>::transposition(1, 2),
            Permutation::<5>::transposition(2, 3),
            Permutation::<5>::transposition(3, 4),
        ]);
        let mut rng = StdRng::seed_from_u64(42);
        let confidence = 1.0 - 2f64.powi(-32);
        let bsgs = monte_carlo::<_, _, 5>(&gens, &[0, 1, 2, 3], &mut rng, confidence);
        assert_eq!(bsgs.order(), 120);
    }

    #[test]
    fn alternating_4_via_monte_carlo() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<4>::cycle(&[0, 1, 2]),
            Permutation::<4>::cycle(&[1, 2, 3]),
        ]);
        let mut rng = StdRng::seed_from_u64(123);
        let bsgs = monte_carlo::<_, _, 4>(&gens, &[0, 1, 2], &mut rng, 1.0 - 2f64.powi(-32));
        assert_eq!(bsgs.order(), 12);
    }

    #[test]
    fn agrees_with_deterministic() {
        use crate::schreier_sims::deterministic::deterministic;
        let gens = GeneratingSet::with_inverses([
            Permutation::<6>::transposition(0, 1),
            Permutation::<6>::transposition(1, 2),
            Permutation::<6>::cycle(&[0, 1, 2, 3, 4, 5]),
        ]);
        let det = deterministic::<_, 6>(&gens, &[0, 1, 2, 3, 4]);
        let mut rng = StdRng::seed_from_u64(0xfeed);
        let mc = monte_carlo::<_, _, 6>(&gens, &[0, 1, 2, 3, 4], &mut rng, 1.0 - 2f64.powi(-40));
        assert_eq!(det.order(), mc.order());
    }
}
