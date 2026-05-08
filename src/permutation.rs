//! The symmetric group `S_N` of permutations on `{0, …, N-1}`.
//!
//! Composition is **left-to-right**: `(σ · τ).apply(i) = τ.apply(σ.apply(i))`,
//! reading `σ.op(&τ)` as "first σ, then τ." This matches the cubing convention
//! `R U` = "do R, then U."

use std::fmt::Display;

use rand::Rng;
use rand::seq::SliceRandom;

use crate::cyclic::InvariantViolated;
use crate::{Action, Enumerable, Group, Magma, Monoid, Semigroup};

/// An element of `S_N`. Storage is `[u16; N]` where `map[i] = j` means "this
/// permutation sends index `i` to index `j`."
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct Permutation<const N: usize> {
    map: [u16; N],
}

impl<const N: usize> Permutation<N> {
    /// Constructs from a raw map. **Panics** if `map` is not a valid
    /// permutation (i.e., not a bijection on `0..N` with values fitting in
    /// `u16`).
    ///
    /// Use [`Permutation::try_from_map`] for fallible construction.
    pub fn from_map(map: [u16; N]) -> Self {
        match Self::try_from_map(map) {
            Ok(p) => p,
            Err(e) => panic!("Permutation::<{N}>::from_map: {e}"),
        }
    }

    /// Fallible constructor. Returns `Err` if `map` is not a bijection on
    /// `0..N`.
    pub fn try_from_map(map: [u16; N]) -> Result<Self, InvariantViolated> {
        let n = N as u16;
        let mut seen = [false; N];
        for &v in &map {
            if (v as usize) >= N {
                return Err(InvariantViolated::OutOfRange {
                    got: v as usize,
                    max: n as usize,
                });
            }
            if seen[v as usize] {
                return Err(InvariantViolated::OutOfRange {
                    got: v as usize,
                    max: n as usize,
                });
            }
            seen[v as usize] = true;
        }
        Ok(Self { map })
    }

    /// Returns the index that `self` sends `i` to.
    #[inline]
    pub fn apply(&self, i: usize) -> usize {
        self.map[i] as usize
    }

    /// Borrows the underlying map.
    #[inline]
    pub fn as_map(&self) -> &[u16; N] {
        &self.map
    }

    /// Returns a uniformly random permutation using `thread_rng()`. Use
    /// [`Permutation::random_with`] for deterministic / seeded RNG.
    pub fn random() -> Self {
        Self::random_with(&mut rand::thread_rng())
    }

    /// Returns a uniformly random permutation via Fisher–Yates with the
    /// supplied RNG.
    pub fn random_with<R: Rng + ?Sized>(rng: &mut R) -> Self {
        let mut map = Self::identity_map();
        map.shuffle(rng);
        Self { map }
    }

    /// Returns a transposition `(i j)` — the permutation that swaps `i` and
    /// `j` and fixes everything else. **Panics** if `i` or `j` is out of
    /// range.
    pub fn transposition(i: usize, j: usize) -> Self {
        assert!(i < N && j < N, "transposition({i},{j}) out of range for N={N}");
        let mut map = Self::identity_map();
        map.swap(i, j);
        Self { map }
    }

    /// Returns a single-cycle permutation `(c_0 c_1 … c_{k-1})`: `c_0 → c_1 →
    /// … → c_{k-1} → c_0`. **Panics** if any index is out of range or
    /// duplicated.
    pub fn cycle(cycle: &[usize]) -> Self {
        let mut seen = [false; N];
        for &c in cycle {
            assert!(c < N, "cycle: index {c} out of range for N={N}");
            assert!(!seen[c], "cycle: index {c} repeated");
            seen[c] = true;
        }
        let mut map = Self::identity_map();
        if cycle.len() >= 2 {
            for w in cycle.windows(2) {
                map[w[0]] = w[1] as u16;
            }
            map[*cycle.last().unwrap()] = cycle[0] as u16;
        }
        Self { map }
    }

    /// Returns the parity of the permutation: `0` for even, `1` for odd.
    pub fn parity(&self) -> u8 {
        let mut visited = [false; N];
        let mut transpositions = 0u32;
        for i in 0..N {
            if visited[i] {
                continue;
            }
            let mut j = i;
            let mut cycle_len = 0u32;
            while !visited[j] {
                visited[j] = true;
                j = self.map[j] as usize;
                cycle_len += 1;
            }
            transpositions += cycle_len.saturating_sub(1);
        }
        (transpositions & 1) as u8
    }

    fn identity_map() -> [u16; N] {
        let mut m = [0u16; N];
        for i in 0..N {
            m[i] = i as u16;
        }
        m
    }
}

impl<const N: usize> Default for Permutation<N> {
    fn default() -> Self {
        Self::identity()
    }
}

impl<const N: usize> Magma for Permutation<N> {
    /// Composition. Convention: `σ.op(&τ).apply(i) == τ.apply(σ.apply(i))` —
    /// "first σ, then τ."
    #[inline]
    fn op(&self, other: &Self) -> Self {
        let mut map = [0u16; N];
        for i in 0..N {
            map[i] = other.map[self.map[i] as usize];
        }
        Self { map }
    }
}

impl<const N: usize> Semigroup for Permutation<N> {}

impl<const N: usize> Monoid for Permutation<N> {
    #[inline]
    fn identity() -> Self {
        Self {
            map: Self::identity_map(),
        }
    }
}

impl<const N: usize> Group for Permutation<N> {
    fn inv(&self) -> Self {
        let mut map = [0u16; N];
        for i in 0..N {
            map[self.map[i] as usize] = i as u16;
        }
        Self { map }
    }
}

/// `Permutation<N>` acts on `[u16; N]` by relabelling indices: the value at
/// position `i` is transported to position `σ(i)`.
///
/// This satisfies the right-action axiom matching our op convention:
/// `arr.act(&σ.op(&τ)) == arr.act(&σ).act(&τ)`.
impl<const N: usize> Action<Permutation<N>> for [u16; N] {
    #[inline]
    fn act(&self, g: &Permutation<N>) -> Self {
        let mut out = [0u16; N];
        for i in 0..N {
            out[g.map[i] as usize] = self[i];
        }
        out
    }
}

impl<const N: usize> Enumerable for Permutation<N> {
    /// Iterates all `N!` permutations in lexicographic order of their map.
    fn iter() -> impl Iterator<Item = Self> {
        LexPermIter::<N>::new()
    }

    fn order() -> u128 {
        let mut acc: u128 = 1;
        for i in 1..=N as u128 {
            acc = acc.checked_mul(i).expect("N! overflows u128");
        }
        acc
    }
}

/// Lex-order permutation iterator. Yields N! permutations exactly once.
struct LexPermIter<const N: usize> {
    next: Option<[u16; N]>,
}

impl<const N: usize> LexPermIter<N> {
    fn new() -> Self {
        let mut m = [0u16; N];
        for i in 0..N {
            m[i] = i as u16;
        }
        Self { next: Some(m) }
    }
}

impl<const N: usize> Iterator for LexPermIter<N> {
    type Item = Permutation<N>;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.next?;
        // Compute next lex permutation in place
        let next = lex_next(cur);
        self.next = next;
        Some(Permutation { map: cur })
    }
}

fn lex_next<const N: usize>(mut m: [u16; N]) -> Option<[u16; N]> {
    if N < 2 {
        return None;
    }
    // Find largest i with m[i] < m[i+1]
    let mut i = N - 2;
    loop {
        if m[i] < m[i + 1] {
            break;
        }
        if i == 0 {
            return None;
        }
        i -= 1;
    }
    // Find largest j > i with m[j] > m[i]
    let mut j = N - 1;
    while m[j] <= m[i] {
        j -= 1;
    }
    m.swap(i, j);
    m[i + 1..].reverse();
    Some(m)
}

impl<const N: usize> Display for Permutation<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (i, v) in self.map.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{v}")?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_acts_as_identity() {
        for p in Permutation::<4>::iter() {
            assert_eq!(Permutation::<4>::identity().op(&p), p);
            assert_eq!(p.op(&Permutation::<4>::identity()), p);
        }
    }

    #[test]
    fn associativity_s4() {
        for x in Permutation::<4>::iter() {
            for y in Permutation::<4>::iter() {
                for z in Permutation::<4>::iter() {
                    assert_eq!(x.op(&y).op(&z), x.op(&y.op(&z)));
                }
            }
        }
    }

    #[test]
    fn inverses_exist_s4() {
        for p in Permutation::<4>::iter() {
            assert_eq!(p.op(&p.inv()), Permutation::<4>::identity());
            assert_eq!(p.inv().op(&p), Permutation::<4>::identity());
        }
    }

    #[test]
    fn s4_is_not_abelian() {
        let mut found = false;
        for x in Permutation::<4>::iter() {
            for y in Permutation::<4>::iter() {
                if x.op(&y) != y.op(&x) {
                    found = true;
                }
            }
        }
        assert!(found);
    }

    #[test]
    fn order_n_factorial() {
        assert_eq!(Permutation::<0>::order(), 1);
        assert_eq!(Permutation::<1>::order(), 1);
        assert_eq!(Permutation::<2>::order(), 2);
        assert_eq!(Permutation::<3>::order(), 6);
        assert_eq!(Permutation::<4>::order(), 24);
        assert_eq!(Permutation::<5>::order(), 120);
        assert_eq!(Permutation::<6>::order(), 720);
    }

    #[test]
    fn iter_count_matches_order() {
        assert_eq!(Permutation::<5>::iter().count() as u128, 120);
    }

    #[test]
    fn iter_produces_distinct() {
        let v: Vec<_> = Permutation::<4>::iter().collect();
        for i in 0..v.len() {
            for j in (i + 1)..v.len() {
                assert_ne!(v[i], v[j]);
            }
        }
    }

    #[test]
    fn try_from_map_rejects_non_bijection() {
        assert!(Permutation::<4>::try_from_map([0, 1, 2, 3]).is_ok());
        assert!(Permutation::<4>::try_from_map([0, 0, 2, 3]).is_err());
        assert!(Permutation::<4>::try_from_map([0, 1, 2, 4]).is_err());
    }

    #[test]
    fn transposition_swaps_two() {
        let p = Permutation::<5>::transposition(1, 3);
        assert_eq!(p.apply(0), 0);
        assert_eq!(p.apply(1), 3);
        assert_eq!(p.apply(2), 2);
        assert_eq!(p.apply(3), 1);
        assert_eq!(p.apply(4), 4);
    }

    #[test]
    fn cycle_constructor() {
        let p = Permutation::<5>::cycle(&[0, 2, 4]);
        assert_eq!(p.apply(0), 2);
        assert_eq!(p.apply(2), 4);
        assert_eq!(p.apply(4), 0);
        assert_eq!(p.apply(1), 1);
        assert_eq!(p.apply(3), 3);
    }

    #[test]
    fn parity_identity_is_even() {
        assert_eq!(Permutation::<5>::identity().parity(), 0);
    }

    #[test]
    fn parity_transposition_is_odd() {
        assert_eq!(Permutation::<5>::transposition(0, 1).parity(), 1);
    }

    #[test]
    fn parity_three_cycle_is_even() {
        // A 3-cycle decomposes into 2 transpositions, so even.
        assert_eq!(Permutation::<5>::cycle(&[0, 1, 2]).parity(), 0);
    }

    #[test]
    fn parity_is_homomorphism() {
        for x in Permutation::<4>::iter() {
            for y in Permutation::<4>::iter() {
                assert_eq!(x.op(&y).parity(), x.parity() ^ y.parity());
            }
        }
    }

    #[test]
    fn op_convention_matches_apply_left_to_right() {
        // (σ · τ).apply(i) == τ.apply(σ.apply(i))
        let sigma = Permutation::<5>::cycle(&[0, 1, 2]); // 0→1→2→0
        let tau = Permutation::<5>::transposition(2, 4);
        let comp = sigma.op(&tau);
        for i in 0..5 {
            assert_eq!(comp.apply(i), tau.apply(sigma.apply(i)));
        }
    }

    #[test]
    fn action_on_index_array_is_right_action() {
        // arr.act(σ.op(&τ)) == arr.act(σ).act(&τ)
        let arr: [u16; 5] = [10, 20, 30, 40, 50];
        let sigma = Permutation::<5>::cycle(&[0, 1, 2]);
        let tau = Permutation::<5>::transposition(2, 4);
        assert_eq!(arr.act(&sigma.op(&tau)), arr.act(&sigma).act(&tau));
    }

    #[test]
    fn action_identity_is_identity() {
        let arr: [u16; 5] = [10, 20, 30, 40, 50];
        assert_eq!(arr.act(&Permutation::<5>::identity()), arr);
    }
}
