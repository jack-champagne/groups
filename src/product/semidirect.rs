//! Semidirect product `N ⋊ H`: pairs `(n, h)` where `H` acts on `N`.
//!
//! Composition: `(n₁, h₁) · (n₂, h₂) = (n₁ · φ_{h₁}(n₂), h₁ · h₂)`.
//!
//! Reuses the [`Action`] trait: `H` acts on `N` via `n.act(&h)`. Conventions
//! match the right-action contract documented on `Action`.

use std::fmt::Display;

use crate::{Action, Enumerable, Group, Magma, Monoid, Semigroup};

/// The semidirect product `N ⋊ H`, where `N: Action<H>` defines the action
/// `φ_h(n) = n.act(&h)`.
///
/// For a *direct* product (trivial action) you should use
/// [`crate::product::DirectProduct`] instead — it avoids the action evaluation
/// in the inner loop.
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct SemidirectProduct<N: Copy + Eq, H: Copy + Eq> {
    pub n: N,
    pub h: H,
}

impl<N, H> SemidirectProduct<N, H>
where
    N: Copy + Eq,
    H: Copy + Eq,
{
    #[inline]
    pub fn new(n: N, h: H) -> Self {
        Self { n, h }
    }
}

impl<N, H> Magma for SemidirectProduct<N, H>
where
    N: Magma + Action<H>,
    H: Magma + Monoid,
{
    /// `(n₁, h₁) · (n₂, h₂) = (n₁ · φ_{h₁}(n₂), h₁ · h₂)`
    /// where `φ_{h₁}(n₂) = n₂.act(&h₁)`.
    #[inline]
    fn op(&self, other: &Self) -> Self {
        Self {
            n: self.n.op(&other.n.act(&self.h)),
            h: self.h.op(&other.h),
        }
    }
}

impl<N, H> Semigroup for SemidirectProduct<N, H>
where
    N: Semigroup + Action<H>,
    H: Semigroup + Monoid,
{
}

impl<N, H> Monoid for SemidirectProduct<N, H>
where
    N: Monoid + Action<H>,
    H: Monoid,
{
    #[inline]
    fn identity() -> Self {
        Self {
            n: N::identity(),
            h: H::identity(),
        }
    }
}

impl<N, H> Group for SemidirectProduct<N, H>
where
    N: Group + Action<H>,
    H: Group,
{
    /// `(n, h)⁻¹ = (φ_{h⁻¹}(n⁻¹), h⁻¹)` — verifying with the op:
    /// `(n, h) · (φ_{h⁻¹}(n⁻¹), h⁻¹) = (n · φ_h(φ_{h⁻¹}(n⁻¹)), h · h⁻¹)
    ///                                = (n · n⁻¹, e) = (e, e)`.
    #[inline]
    fn inv(&self) -> Self {
        let h_inv = self.h.inv();
        Self {
            n: self.n.inv().act(&h_inv),
            h: h_inv,
        }
    }
}

impl<N, H> Enumerable for SemidirectProduct<N, H>
where
    N: Enumerable + Action<H>,
    H: Enumerable,
{
    fn iter() -> impl Iterator<Item = Self> {
        N::iter().flat_map(|n| H::iter().map(move |h| Self { n, h }))
    }

    fn order() -> u128 {
        N::order()
            .checked_mul(H::order())
            .expect("|N ⋊ H| overflows u128")
    }
}

impl<N, H> Display for SemidirectProduct<N, H>
where
    N: Display + Copy + Eq,
    H: Display + Copy + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(n={}, h={})", self.n, self.h)
    }
}
