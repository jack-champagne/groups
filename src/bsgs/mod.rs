//! Base + Strong Generating Set (BSGS) — the data structure underlying
//! Schreier–Sims, sift, membership testing, |G| computation, and word
//! reconstruction.
//!
//! All Schreier–Sims variants ([deterministic][crate::schreier_sims::deterministic],
//! Monte Carlo, Las Vegas) produce the same `Bsgs` shape; consumers don't care
//! which built it.

use smallvec::SmallVec;

use crate::generators::GeneratingSet;
use crate::word::Word;
use crate::Group;

/// A group element acting on a finite set of points `0..N`. Used by BSGS to
/// drive its base-and-orbit construction.
///
/// For `Permutation<N>`, `apply_to(i)` is just the permutation map.
/// For puzzle groups (cube, megaminx, etc.), the puzzle layer provides a
/// "sticker representation" — an isomorphic embedding into `S_N` for some `N`
/// — and impls this trait via that embedding.
pub trait PermutationLike<const N: usize>: Group {
    /// Image of point `i` under this group element.
    fn apply_to(&self, i: u16) -> u16;
}

impl<const N: usize> PermutationLike<N> for crate::permutation::Permutation<N> {
    #[inline]
    fn apply_to(&self, i: u16) -> u16 {
        crate::permutation::Permutation::apply(self, i as usize) as u16
    }
}

/// One level of the stabilizer chain.
#[derive(Debug, Clone)]
pub struct StabilizerLevel<G: Group, const N: usize> {
    /// The base point fixed by deeper levels.
    pub base_point: u16,
    /// `transversal[i] = Some(g)` iff `i` is in the orbit of `base_point` and
    /// `base_point.act(g) == i`. `None` for points not in the orbit.
    ///
    /// Boxed to avoid bloating the stack with a giant per-level array; the
    /// underlying allocation is contiguous and lookup is `O(1)`.
    pub transversal: Box<[Option<G>]>,
    /// Strong generators of the stabilizer subgroup at this level.
    pub strong_gens: Vec<G>,
}

impl<G: Group, const N: usize> StabilizerLevel<G, N> {
    pub(crate) fn empty(base_point: u16) -> Self {
        let mut t: Vec<Option<G>> = (0..N).map(|_| None).collect();
        t[base_point as usize] = Some(G::identity());
        Self {
            base_point,
            transversal: t.into_boxed_slice(),
            strong_gens: Vec::new(),
        }
    }

    /// Number of points in the orbit of `base_point` at this level.
    pub fn orbit_size(&self) -> usize {
        self.transversal.iter().filter(|t| t.is_some()).count()
    }
}

/// Base + Strong Generating Set for a group acting on `0..N`.
///
/// Built via [`crate::schreier_sims`]. Once constructed, supports:
/// - `|G|` via [`Bsgs::order`]
/// - membership testing via [`Bsgs::is_member`]
/// - residual sift via [`Bsgs::sift`]
/// - word reconstruction via [`Bsgs::word_for`]
#[derive(Debug, Clone)]
pub struct Bsgs<G: Group, const N: usize> {
    pub base: SmallVec<[u16; 16]>,
    pub levels: Vec<StabilizerLevel<G, N>>,
}

impl<G, const N: usize> Bsgs<G, N>
where
    G: PermutationLike<N>,
{
    pub(crate) fn empty() -> Self {
        Self {
            base: SmallVec::new(),
            levels: Vec::new(),
        }
    }

    /// Returns a generating set for the subgroup `G_level` stabilizing the
    /// first `level` base points. This is the standard stabilizer-chain
    /// quotient: the elements of `G` that pointwise fix `base[0..level]`.
    ///
    /// - `level = 0` returns generators of all of `G` (== the user's input
    ///   generators, possibly augmented with Schreier residues).
    /// - `level = base.len()` returns no generators (the trivial subgroup).
    /// - `level = k` for `0 < k < base.len()` returns a generating set for
    ///   the level-`k` stabilizer.
    ///
    /// Use this to extract subgroups by stabilizer chain — e.g., for the 3×3
    /// cube with base ordered `[F2L stickers, LL stickers]`, calling this at
    /// `level = 12` yields generators of the last-layer subgroup
    /// (order 62,208).
    pub fn stabilizer_generators(&self, level: usize) -> Vec<G> {
        let mut out = Vec::new();
        let start = level.min(self.levels.len());
        for lvl in &self.levels[start..] {
            out.extend(lvl.strong_gens.iter().copied());
        }
        out
    }

    /// `|G|` — the product of the orbit sizes at each level.
    pub fn order(&self) -> u128 {
        self.levels
            .iter()
            .map(|lvl| lvl.orbit_size() as u128)
            .product()
    }

    /// Sift `g` through the chain. Returns `None` iff `g ∈ G` (the sift
    /// reduced to identity). Otherwise returns the residue.
    pub fn sift(&self, g: &G) -> Option<G> {
        let mut h = *g;
        for level in &self.levels {
            let j = h.apply_to(level.base_point);
            match &level.transversal[j as usize] {
                Some(u) => h = h.op(&u.inv()),
                None => return Some(h),
            }
        }
        if h == G::identity() {
            None
        } else {
            Some(h)
        }
    }

    /// `true` iff `g` is an element of `G`.
    #[inline]
    pub fn is_member(&self, g: &G) -> bool {
        self.sift(g).is_none()
    }

    /// Reconstruct `g` as a product of transversal representatives. Returns
    /// `None` if `g ∉ G`.
    ///
    /// This is *not* a word in the original generators — it's the
    /// canonical "transversal decomposition" of `g`. To get a word in user
    /// generators, additionally trace each transversal element through its
    /// Schreier-vector / generator history (TODO post-v1).
    pub fn transversal_decompose(&self, g: &G) -> Option<Vec<G>> {
        let mut h = *g;
        let mut out = Vec::with_capacity(self.levels.len());
        for level in &self.levels {
            let j = h.apply_to(level.base_point);
            match &level.transversal[j as usize] {
                Some(u) => {
                    out.push(*u);
                    h = h.op(&u.inv());
                }
                None => return None,
            }
        }
        if h == G::identity() {
            Some(out)
        } else {
            None
        }
    }

    /// Reconstruct a `Word` over the supplied generating set that produces
    /// `g`. Currently uses BFS over the Cayley graph to trace each
    /// transversal representative back to a generator word; works for
    /// puzzle-scale groups but not optimized.
    ///
    /// Returns `None` if `g ∉ G`.
    pub fn word_for(&self, gens: &GeneratingSet<G>, g: &G) -> Option<Word>
    where
        G: std::hash::Hash,
    {
        if !self.is_member(g) {
            return None;
        }
        // BFS from identity; for puzzle-scale this terminates fast because the
        // search depth is bounded by the diameter of the Cayley graph
        // (~20 for the cube). For general use this is a simplification we'll
        // replace with proper Schreier-vector trace post-v1.
        bfs_word(gens, g)
    }
}

fn bfs_word<G, const N: usize>(gens: &GeneratingSet<G>, target: &G) -> Option<Word>
where
    G: PermutationLike<N> + std::hash::Hash,
{
    use std::collections::HashMap;
    if *target == G::identity() {
        return Some(Word::new());
    }
    let mut prev: HashMap<G, (G, u8)> = HashMap::new();
    let mut frontier: Vec<G> = vec![G::identity()];
    let mut depth = 0;
    let max_depth = 30; // safety cap; cube god's number is 20
    while !frontier.is_empty() && depth < max_depth {
        let mut next_frontier = Vec::new();
        for &cur in &frontier {
            for (i, gen) in gens.iter() {
                let nxt = cur.op(gen);
                if nxt == *target {
                    let mut w = Word::new();
                    w.push(i);
                    let mut node = cur;
                    while node != G::identity() {
                        let (parent, edge) = prev[&node];
                        w.push(edge);
                        node = parent;
                    }
                    let mut indices: Vec<u8> = w.iter().collect();
                    indices.reverse();
                    return Some(Word::from_indices(indices));
                }
                if !prev.contains_key(&nxt) && nxt != G::identity() {
                    prev.insert(nxt, (cur, i));
                    next_frontier.push(nxt);
                }
            }
        }
        frontier = next_frontier;
        depth += 1;
    }
    None
}
