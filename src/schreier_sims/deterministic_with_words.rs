//! Schreier–Sims with word-history tracking.
//!
//! Identical to [`super::deterministic::deterministic`] structurally, but
//! every transversal element and every strong generator carries a [`Word`]
//! recording how it was built up from the *original* user-supplied
//! generators (specifically: indices into a paired-inverse `GeneratingSet`).
//!
//! Output is [`BsgsWithWords`], which augments [`Bsgs`] with parallel
//! word-history tables. Consumers can then call
//! [`BsgsWithWords::stabilizer_generators_with_words`] to extract a subgroup
//! generating set together with face-move expansions, or pass those into
//! [`crate::orbit::enumerate_orbit_translated`] to build a complete
//! face-move algorithm table for that subgroup.
//!
//! ## Note on construction
//!
//! Word tracking adds modest overhead per SS step (a few `SmallVec` clones
//! per orbit edge and per Schreier residue). Memory grows by `O(B · N)`
//! Words at level-0 base size; for puzzle scale (~20 base points × ~50
//! orbit points × ~32-byte SmallVec) that's ~32 KB. Negligible.

use smallvec::SmallVec;

use crate::bsgs::{Bsgs, PermutationLike, StabilizerLevel};
use crate::generators::GeneratingSet;
use crate::word::Word;
use crate::Magma;

/// `Bsgs` augmented with word-history tables. The tables are indexed
/// in parallel to the underlying `Bsgs.levels` and `Bsgs.levels[i].transversal`.
#[derive(Debug, Clone)]
pub struct BsgsWithWords<G: crate::Group, const N: usize> {
    pub bsgs: Bsgs<G, N>,
    /// `transversal_words[i][β] = Some(w)` iff `bsgs.levels[i].transversal[β]
    /// = Some(rep)` and `w` evaluates to `rep` under the original generating
    /// set. Words are in indices into the *paired-inverse* gen set passed to
    /// `deterministic_with_words` (i.e., the set returned by
    /// `GeneratingSet::with_inverses`).
    pub transversal_words: Vec<Box<[Option<Word>]>>,
    /// `strong_gen_words[i][k]` is the word for `bsgs.levels[i].strong_gens[k]`.
    pub strong_gen_words: Vec<Vec<Word>>,
}

impl<G, const N: usize> BsgsWithWords<G, N>
where
    G: PermutationLike<N>,
{
    /// Returns the strong generators of the level-`level` stabilizer
    /// subgroup, paired with their words in the original generators.
    pub fn stabilizer_generators_with_words(&self, level: usize) -> Vec<(G, Word)> {
        let mut out = Vec::new();
        let start = level.min(self.bsgs.levels.len());
        for (i, lvl) in self.bsgs.levels[start..].iter().enumerate() {
            let level_idx = start + i;
            let words = &self.strong_gen_words[level_idx];
            for (k, g) in lvl.strong_gens.iter().enumerate() {
                out.push((*g, words[k].clone()));
            }
        }
        out
    }

    pub fn order(&self) -> u128 {
        self.bsgs.order()
    }
}

/// Build a `BsgsWithWords` deterministically, tracking face-move word
/// histories throughout. The supplied `GeneratingSet` MUST have paired
/// inverses (i.e., constructed via `GeneratingSet::with_inverses`).
///
/// Panics in release builds if `gens.has_paired_inverses()` is false in
/// debug, on the basis that word inversion uses the `i ^ 1` shortcut that
/// only holds for the paired layout.
pub fn deterministic_with_words<G, const N: usize>(
    gens: &GeneratingSet<G>,
    base_hint: &[u16],
) -> BsgsWithWords<G, N>
where
    G: PermutationLike<N>,
{
    debug_assert!(
        gens.has_paired_inverses(),
        "deterministic_with_words requires paired inverses; \
         construct gens via GeneratingSet::with_inverses"
    );

    let mut bsgs: Bsgs<G, N> = Bsgs::empty();
    bsgs.base = SmallVec::from_iter(base_hint.iter().copied());
    let mut transversal_words: Vec<Box<[Option<Word>]>> = Vec::new();
    let mut strong_gen_words: Vec<Vec<Word>> = Vec::new();

    for &b in base_hint {
        bsgs.levels.push(StabilizerLevel::empty(b));
        let mut t: Vec<Option<Word>> = (0..N).map(|_| None).collect();
        t[b as usize] = Some(Word::new());
        transversal_words.push(t.into_boxed_slice());
        strong_gen_words.push(Vec::new());
    }

    if bsgs.levels.is_empty() {
        if let Some(b) = first_moved_point(gens) {
            bsgs.base.push(b);
            bsgs.levels.push(StabilizerLevel::empty(b));
            let mut t: Vec<Option<Word>> = (0..N).map(|_| None).collect();
            t[b as usize] = Some(Word::new());
            transversal_words.push(t.into_boxed_slice());
            strong_gen_words.push(Vec::new());
        } else {
            return BsgsWithWords {
                bsgs,
                transversal_words,
                strong_gen_words,
            };
        }
    }

    // Seed level-0 strong gens from the user's set.
    bsgs.levels[0].strong_gens = gens.iter().map(|(_, g)| *g).collect();
    strong_gen_words[0] = gens.iter().map(|(i, _)| Word::from_indices([i])).collect();

    let mut state = BsgsWithWords {
        bsgs,
        transversal_words,
        strong_gen_words,
    };

    // Build initial orbits.
    for i in 0..state.bsgs.levels.len() {
        extend_orbit(&mut state, i);
    }

    sift_schreier(&mut state);
    state
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

fn sift_schreier<G, const N: usize>(state: &mut BsgsWithWords<G, N>)
where
    G: PermutationLike<N>,
{
    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..state.bsgs.levels.len() {
            // Collect (s, w_s) pairs from levels [i, end].
            let mut union: Vec<(G, Word)> = Vec::new();
            for level_idx in i..state.bsgs.levels.len() {
                for (k, s) in state.bsgs.levels[level_idx].strong_gens.iter().enumerate() {
                    union.push((*s, state.strong_gen_words[level_idx][k].clone()));
                }
            }
            let transversal = state.bsgs.levels[i].transversal.clone();
            let transversal_words = state.transversal_words[i].clone();

            for beta in 0..N {
                let Some(u_beta) = transversal[beta] else { continue };
                let w_beta = transversal_words[beta].clone().unwrap();
                for (s, w_s) in &union {
                    let beta_s = s.apply_to(beta as u16);
                    let Some(u_beta_s) = state.bsgs.levels[i].transversal[beta_s as usize] else {
                        extend_orbit(state, i);
                        changed = true;
                        continue;
                    };
                    let w_beta_s = state.transversal_words[i][beta_s as usize]
                        .clone()
                        .expect("transversal_words populated together with transversal");

                    let schreier = u_beta.op(s).op(&u_beta_s.inv());
                    // Word: w_beta ++ w_s ++ inv(w_beta_s)
                    let schreier_word = w_beta
                        .clone()
                        .concat(w_s)
                        .concat(&w_beta_s.inv_paired());

                    // Sift through deeper levels.
                    let mut residue = schreier;
                    let mut residue_word = schreier_word;
                    let mut sifted_to_level: Option<usize> = None;
                    for j in (i + 1)..state.bsgs.levels.len() {
                        let img = residue.apply_to(state.bsgs.levels[j].base_point);
                        match state.bsgs.levels[j].transversal[img as usize] {
                            Some(u) => {
                                let u_word = state.transversal_words[j][img as usize]
                                    .clone()
                                    .expect("populated in lockstep with transversal");
                                residue = residue.op(&u.inv());
                                residue_word = residue_word.concat(&u_word.inv_paired());
                            }
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
                            state.bsgs.base.push(new_base);
                            state.bsgs.levels.push(StabilizerLevel::empty(new_base));
                            let mut t: Vec<Option<Word>> = (0..N).map(|_| None).collect();
                            t[new_base as usize] = Some(Word::new());
                            state.transversal_words.push(t.into_boxed_slice());
                            state.strong_gen_words.push(Vec::new());
                            state.bsgs.levels.len() - 1
                        }
                    };
                    state.bsgs.levels[target].strong_gens.push(residue);
                    state.strong_gen_words[target].push(residue_word);
                    extend_orbit(state, target);
                    changed = true;
                }
            }
        }
    }
}

fn extend_orbit<G, const N: usize>(state: &mut BsgsWithWords<G, N>, level: usize)
where
    G: PermutationLike<N>,
{
    use crate::Monoid;
    let base_point = state.bsgs.levels[level].base_point;
    let mut transversal: Vec<Option<G>> = (0..N).map(|_| None).collect();
    let mut twords: Vec<Option<Word>> = (0..N).map(|_| None).collect();
    transversal[base_point as usize] = Some(G::identity());
    twords[base_point as usize] = Some(Word::new());

    // Union strong gens from levels [level, end] paired with their words.
    let mut union: Vec<(G, Word)> = Vec::new();
    for lvl_idx in level..state.bsgs.levels.len() {
        for (k, s) in state.bsgs.levels[lvl_idx].strong_gens.iter().enumerate() {
            union.push((*s, state.strong_gen_words[lvl_idx][k].clone()));
        }
    }

    let mut frontier: Vec<u16> = vec![base_point];
    while let Some(beta) = frontier.pop() {
        let u_beta = transversal[beta as usize].expect("frontier point has rep");
        let w_beta = twords[beta as usize].clone().unwrap();
        for (s, w_s) in &union {
            let img = s.apply_to(beta);
            if transversal[img as usize].is_none() {
                transversal[img as usize] = Some(u_beta.op(s));
                twords[img as usize] = Some(w_beta.clone().concat(w_s));
                frontier.push(img);
            }
        }
    }
    state.bsgs.levels[level].transversal = transversal.into_boxed_slice();
    state.transversal_words[level] = twords.into_boxed_slice();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::permutation::Permutation;

    #[test]
    fn s_4_construction_with_words() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<4>::transposition(0, 1),
            Permutation::<4>::transposition(1, 2),
            Permutation::<4>::transposition(2, 3),
        ]);
        let state = deterministic_with_words::<_, 4>(&gens, &[0, 1, 2]);
        assert_eq!(state.order(), 24);

        // Strong gens at level 0: should include all 6 user gens (3 + inverses).
        // Strong gens at deeper levels: residues.
        // Each strong gen's word should evaluate (via the original gens) back
        // to the gen itself.
        for level_idx in 0..state.bsgs.levels.len() {
            for (k, g) in state.bsgs.levels[level_idx].strong_gens.iter().enumerate() {
                let w = &state.strong_gen_words[level_idx][k];
                let computed = w.evaluate(&gens);
                assert_eq!(
                    computed, *g,
                    "strong gen at level {level_idx} idx {k}: word doesn't reproduce gen"
                );
            }
        }
    }

    #[test]
    fn transversal_words_evaluate_correctly() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<4>::transposition(0, 1),
            Permutation::<4>::transposition(1, 2),
            Permutation::<4>::transposition(2, 3),
        ]);
        let state = deterministic_with_words::<_, 4>(&gens, &[0, 1, 2]);

        for level_idx in 0..state.bsgs.levels.len() {
            for orbit_pt in 0..4 {
                if let Some(u) = state.bsgs.levels[level_idx].transversal[orbit_pt] {
                    let w = state.transversal_words[level_idx][orbit_pt]
                        .as_ref()
                        .expect("populated alongside transversal");
                    let computed = w.evaluate(&gens);
                    assert_eq!(
                        computed, u,
                        "transversal word at level {level_idx} orbit_pt {orbit_pt}: \
                         word doesn't reproduce rep"
                    );
                }
            }
        }
    }

    #[test]
    fn extracted_subgroup_gens_have_valid_words() {
        let gens = GeneratingSet::with_inverses([
            Permutation::<5>::transposition(0, 1),
            Permutation::<5>::transposition(1, 2),
            Permutation::<5>::transposition(2, 3),
            Permutation::<5>::transposition(3, 4),
        ]);
        let state = deterministic_with_words::<_, 5>(&gens, &[0, 1, 2, 3]);
        assert_eq!(state.order(), 120);

        // Get level-2 stabilizer gens (subgroup fixing 0 and 1; should be S_3
        // on {2, 3, 4}, order 6).
        let sub = state.stabilizer_generators_with_words(2);
        for (g, w) in &sub {
            // The word should reproduce g.
            assert_eq!(w.evaluate(&gens), *g);
            // g should fix 0 and 1.
            use crate::bsgs::PermutationLike;
            assert_eq!(g.apply_to(0), 0, "level-2 gen should fix 0");
            assert_eq!(g.apply_to(1), 1, "level-2 gen should fix 1");
        }
    }
}
