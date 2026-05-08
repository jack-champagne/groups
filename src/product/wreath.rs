//! Wreath product `G ≀ S_N`: the natural structure for *cubies + their slot
//! permutations*.
//!
//! An element is `(fibers, perm)` where:
//! - `fibers: [G; N]` — one element of `G` per slot (e.g., the orientation of
//!   each cubie, or any per-slot decoration that lives in `G`).
//! - `perm: Permutation<N>` — a permutation of the `N` slots.
//!
//! Composition: when you compose `(f₁, σ) · (f₂, τ)`, the permutation `σ`
//! reindexes the second element's fibers before pointwise combining:
//!
//! ```text
//! (f₁, σ) · (f₂, τ) = (f, σ · τ),  where  f[i] = f₁[i] · f₂[σ(i)]
//! ```
//!
//! Equivalently in semidirect-product form, this is `[G; N] ⋊ S_N` where
//! `S_N` acts on `[G; N]` by index-relabelling. We give it a dedicated type
//! (rather than a `SemidirectProduct` alias) because the inner loop benefits
//! from a hand-tuned implementation that avoids trait-method indirection.

use std::fmt::Display;

use crate::permutation::Permutation;
use crate::{Enumerable, Group, Magma, Monoid, Semigroup};

/// The wreath product `G ≀ S_N`. Stack-allocated, `Copy` if `G: Copy`.
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct WreathProduct<G: Copy + Eq, const N: usize> {
    pub fibers: [G; N],
    pub perm: Permutation<N>,
}

impl<G: Copy + Eq, const N: usize> WreathProduct<G, N> {
    #[inline]
    pub fn new(fibers: [G; N], perm: Permutation<N>) -> Self {
        Self { fibers, perm }
    }
}

impl<G: Magma, const N: usize> Magma for WreathProduct<G, N> {
    /// `(f₁, σ) · (f₂, τ)`: the new fiber at slot `i` is `f₁[i] · f₂[σ(i)]`,
    /// and the permutation is `σ · τ` (left-to-right convention).
    #[inline]
    fn op(&self, other: &Self) -> Self {
        let perm = self.perm.op(&other.perm);
        let mut fibers = self.fibers;
        let sigma_map = self.perm.as_map();
        for i in 0..N {
            let j = sigma_map[i] as usize;
            fibers[i] = self.fibers[i].op(&other.fibers[j]);
        }
        Self { fibers, perm }
    }
}

impl<G: Semigroup, const N: usize> Semigroup for WreathProduct<G, N> {}

impl<G: Monoid, const N: usize> Monoid for WreathProduct<G, N> {
    #[inline]
    fn identity() -> Self {
        Self {
            fibers: [G::identity(); N],
            perm: Permutation::<N>::identity(),
        }
    }
}

impl<G: Group, const N: usize> Group for WreathProduct<G, N> {
    /// `(f, σ)⁻¹ = (f', σ⁻¹)` where `f'[σ(i)] = f[i]⁻¹`, equivalently
    /// `f'[i] = f[σ⁻¹(i)]⁻¹`.
    #[inline]
    fn inv(&self) -> Self {
        let perm_inv = self.perm.inv();
        let mut fibers = [G::identity(); N];
        let perm_inv_map = perm_inv.as_map();
        for i in 0..N {
            let j = perm_inv_map[i] as usize;
            fibers[i] = self.fibers[j].inv();
        }
        Self {
            fibers,
            perm: perm_inv,
        }
    }
}

impl<G: Enumerable, const N: usize> Enumerable for WreathProduct<G, N> {
    fn iter() -> impl Iterator<Item = Self> {
        let fiber_choices: Vec<G> = G::iter().collect();
        all_fiber_arrays::<G, N>(fiber_choices).flat_map(|fibers| {
            Permutation::<N>::iter().map(move |perm| Self { fibers, perm })
        })
    }

    fn order() -> u128 {
        let mut acc: u128 = 1;
        for _ in 0..N {
            acc = acc.checked_mul(G::order()).expect("|G ≀ S_N| overflows u128");
        }
        acc.checked_mul(Permutation::<N>::order())
            .expect("|G ≀ S_N| overflows u128")
    }
}

/// Iterate over all `[G; N]` by exhaustive product of the per-slot choices.
fn all_fiber_arrays<G: Copy, const N: usize>(choices: Vec<G>) -> impl Iterator<Item = [G; N]> {
    let count = (choices.len() as u128).checked_pow(N as u32).unwrap_or(0);
    (0..count).map(move |mut idx| {
        let mut arr = [choices[0]; N];
        let base = choices.len() as u128;
        for i in 0..N {
            arr[i] = choices[(idx % base) as usize];
            idx /= base;
        }
        arr
    })
}

impl<G: Display + Copy + Eq, const N: usize> Display for WreathProduct<G, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(fibers=[")?;
        for (i, g) in self.fibers.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{g}")?;
        }
        write!(f, "], perm={})", self.perm)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cyclic::Cyclic;

    type C3WrS3 = WreathProduct<Cyclic<3>, 3>;

    #[test]
    fn order_is_g_to_n_times_n_factorial() {
        // |C₃ ≀ S₃| = 3³ · 3! = 27 · 6 = 162
        assert_eq!(C3WrS3::order(), 162);
        assert_eq!(C3WrS3::iter().count() as u128, 162);
    }

    #[test]
    fn associativity_small() {
        // 162³ ≈ 4.2M triples — too slow for an exhaustive test. Sample.
        use rand::Rng;
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xc0ffee);
        let elems: Vec<_> = C3WrS3::iter().collect();
        for _ in 0..2000 {
            let x = elems[rng.gen_range(0..elems.len())];
            let y = elems[rng.gen_range(0..elems.len())];
            let z = elems[rng.gen_range(0..elems.len())];
            assert_eq!(x.op(&y).op(&z), x.op(&y.op(&z)));
        }
    }

    #[test]
    fn inverses_exhaustive() {
        for x in C3WrS3::iter() {
            assert_eq!(x.op(&x.inv()), C3WrS3::identity());
            assert_eq!(x.inv().op(&x), C3WrS3::identity());
        }
    }

    #[test]
    fn cube_corner_subgroup_r4_is_identity() {
        // The action of cube move R on the 8 corners is:
        //   - permutation: cycle (1 2 6 5)  in slots {0..7}, leaving {0,3,4,7}
        //     fixed (using the standard URF/UFL/ULB/UBR/DFR/DLF/DBL/DRB labelling)
        //   - corner orientations: twist of (0,1,2,0,0,2,1,0) at the four moved
        //     slots in C₃.
        //
        // R⁴ = identity in the corner-only group. With a *direct* product this
        // would fail (the user's existing puzzle-cube code's bug). With wreath
        // product composition, it succeeds.

        // Use a synthetic test that mimics this structure on 4 slots, since the
        // full cube R is in the cube example. Here: cycle (0 1 2 3) on 4 slots
        // with twists (1, 2, 0, 0) — chosen so the twist sum mod 3 is 0.
        type W = WreathProduct<Cyclic<3>, 4>;
        let c = |i: usize| Cyclic::<3>::from_index(i);
        let move_r = W::new(
            [c(1), c(2), c(0), c(0)],
            Permutation::<4>::cycle(&[0, 1, 2, 3]),
        );
        let r2 = move_r.op(&move_r);
        let r3 = r2.op(&move_r);
        let r4 = r3.op(&move_r);
        assert_eq!(r4, W::identity(),
            "R⁴ should be identity in the wreath product (this is the bug \
             the user observed in puzzle-cube/src/main.rs)");
    }

    #[test]
    fn fibers_are_reindexed_by_left_perm() {
        // Direct verification of the wreath composition law:
        // (f₁, σ) · (f₂, τ) has fiber[i] = f₁[i] · f₂[σ(i)].
        type W = WreathProduct<Cyclic<5>, 3>;
        let f1 = [
            Cyclic::<5>::from_index(1),
            Cyclic::<5>::from_index(2),
            Cyclic::<5>::from_index(3),
        ];
        let f2 = [
            Cyclic::<5>::from_index(4),
            Cyclic::<5>::from_index(0),
            Cyclic::<5>::from_index(2),
        ];
        let sigma = Permutation::<3>::cycle(&[0, 1, 2]); // 0→1, 1→2, 2→0
        let tau = Permutation::<3>::transposition(0, 1);
        let a = W::new(f1, sigma);
        let b = W::new(f2, tau);
        let c = a.op(&b);
        // fiber[0] = f1[0] · f2[σ(0)] = f1[0] · f2[1] = 1 + 0 = 1 mod 5
        // fiber[1] = f1[1] · f2[σ(1)] = f1[1] · f2[2] = 2 + 2 = 4 mod 5
        // fiber[2] = f1[2] · f2[σ(2)] = f1[2] · f2[0] = 3 + 4 = 2 mod 5
        assert_eq!(c.fibers[0], Cyclic::<5>::from_index(1));
        assert_eq!(c.fibers[1], Cyclic::<5>::from_index(4));
        assert_eq!(c.fibers[2], Cyclic::<5>::from_index(2));
        assert_eq!(c.perm, sigma.op(&tau));
    }
}
