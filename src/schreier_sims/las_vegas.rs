//! Las Vegas Schreier–Sims.
//!
//! Run Monte Carlo to build a candidate chain, then run a deterministic
//! verification pass: for every transversal point and every strong generator,
//! compute the Schreier generator and confirm it sifts to identity. If any
//! Schreier generator's sift residue is non-trivial, install it and repeat.
//!
//! Fast in expectation, correct with certainty.

use rand::Rng;
use smallvec::SmallVec;

use crate::bsgs::{Bsgs, PermutationLike, StabilizerLevel};
use crate::generators::GeneratingSet;

/// Build a BSGS via Monte Carlo, then verify deterministically.
pub fn las_vegas<G, R, const N: usize>(
    gens: &GeneratingSet<G>,
    base_hint: &[u16],
    rng: &mut R,
) -> Bsgs<G, N>
where
    G: PermutationLike<N>,
    R: Rng + ?Sized,
{
    // Initial chain via Monte Carlo at moderate confidence — verification
    // will catch any incompleteness.
    let mut bsgs = super::monte_carlo::monte_carlo::<G, R, N>(
        gens,
        base_hint,
        rng,
        1.0 - 2f64.powi(-32),
    );

    // Deterministic verification: sift every Schreier generator at every
    // level. Any non-identity residue is appended and we loop.
    verify_and_complete::<G, N>(&mut bsgs);
    bsgs
}

fn verify_and_complete<G, const N: usize>(bsgs: &mut Bsgs<G, N>)
where
    G: PermutationLike<N>,
{
    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..bsgs.levels.len() {
            // Strong gens at level i = union over [i, end].
            let mut level_gens: Vec<G> = Vec::new();
            for lvl in &bsgs.levels[i..] {
                level_gens.extend(lvl.strong_gens.iter().copied());
            }
            let transversal = bsgs.levels[i].transversal.clone();

            for (beta, u_beta_opt) in transversal.iter().enumerate() {
                let Some(u_beta) = u_beta_opt else { continue };
                for s in &level_gens {
                    let beta_s = s.apply_to(beta as u16);
                    let Some(u_beta_s) = bsgs.levels[i].transversal[beta_s as usize] else {
                        // Orbit incomplete — extend and retry.
                        extend_orbit::<G, N>(bsgs, i);
                        changed = true;
                        continue;
                    };
                    let schreier = u_beta.op(s).op(&u_beta_s.inv());

                    // Sift through deeper levels.
                    let mut residue = schreier;
                    let mut sifted_to_level: Option<usize> = None;
                    for j in (i + 1)..bsgs.levels.len() {
                        let img = residue.apply_to(bsgs.levels[j].base_point);
                        match bsgs.levels[j].transversal[img as usize] {
                            Some(u) => residue = residue.op(&u.inv()),
                            None => {
                                sifted_to_level = Some(j);
                                break;
                            }
                        }
                    }
                    use crate::Monoid;
                    if residue == G::identity() {
                        continue;
                    }

                    let target = match sifted_to_level {
                        Some(j) => j,
                        None => {
                            let new_base = (0..N as u16)
                                .find(|&p| residue.apply_to(p) != p)
                                .expect("non-identity residue fixes all points?");
                            bsgs.base.push(new_base);
                            bsgs.levels.push(StabilizerLevel::empty(new_base));
                            bsgs.levels.len() - 1
                        }
                    };
                    bsgs.levels[target].strong_gens.push(residue);
                    extend_orbit::<G, N>(bsgs, target);
                    changed = true;
                }
            }
        }
    }
}

fn extend_orbit<G, const N: usize>(bsgs: &mut Bsgs<G, N>, level: usize)
where
    G: PermutationLike<N>,
{
    use crate::Monoid;
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

// SmallVec is used by the imported `Bsgs` type signature only; not directly
// referenced here.
#[allow(dead_code)]
fn _smallvec_marker() -> SmallVec<[u16; 1]> {
    SmallVec::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::permutation::Permutation;
    use rand::SeedableRng;
    use rand::rngs::StdRng;

    #[test]
    fn s_5_via_las_vegas() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<5>::transposition(0, 1),
            Permutation::<5>::transposition(1, 2),
            Permutation::<5>::transposition(2, 3),
            Permutation::<5>::transposition(3, 4),
        ]);
        let mut rng = StdRng::seed_from_u64(7);
        let bsgs = las_vegas::<_, _, 5>(&gens, &[0, 1, 2, 3], &mut rng);
        assert_eq!(bsgs.order(), 120);
    }

    #[test]
    fn alternating_4_via_las_vegas() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<4>::cycle(&[0, 1, 2]),
            Permutation::<4>::cycle(&[1, 2, 3]),
        ]);
        let mut rng = StdRng::seed_from_u64(99);
        let bsgs = las_vegas::<_, _, 4>(&gens, &[0, 1, 2], &mut rng);
        assert_eq!(bsgs.order(), 12);
    }

    #[test]
    fn agrees_with_deterministic() {
        use crate::schreier_sims::deterministic::deterministic;
        let gens = GeneratingSet::with_inverses([
            Permutation::<6>::transposition(0, 1),
            Permutation::<6>::cycle(&[0, 1, 2, 3, 4, 5]),
        ]);
        let det = deterministic::<_, 6>(&gens, &[0, 1, 2, 3, 4]);
        let mut rng = StdRng::seed_from_u64(11);
        let lv = las_vegas::<_, _, 6>(&gens, &[0, 1, 2, 3, 4], &mut rng);
        assert_eq!(det.order(), lv.order());
    }
}
