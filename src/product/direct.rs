//! Direct product `A × B`: pairs `(a, b)` with componentwise composition.

use std::fmt::Display;

use crate::{Enumerable, Group, Magma, Monoid, Semigroup};

/// The direct product `A × B`. Composition is componentwise; the two factors
/// ignore each other entirely.
///
/// `(a₁, b₁) · (a₂, b₂) = (a₁·a₂, b₁·b₂)`.
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct DirectProduct<A: Copy + Eq, B: Copy + Eq>(pub A, pub B);

impl<A: Magma, B: Magma> Magma for DirectProduct<A, B> {
    #[inline]
    fn op(&self, other: &Self) -> Self {
        DirectProduct(self.0.op(&other.0), self.1.op(&other.1))
    }
}

impl<A: Semigroup, B: Semigroup> Semigroup for DirectProduct<A, B> {}

impl<A: Monoid, B: Monoid> Monoid for DirectProduct<A, B> {
    #[inline]
    fn identity() -> Self {
        DirectProduct(A::identity(), B::identity())
    }
}

impl<A: Group, B: Group> Group for DirectProduct<A, B> {
    #[inline]
    fn inv(&self) -> Self {
        DirectProduct(self.0.inv(), self.1.inv())
    }
}

impl<A: Enumerable, B: Enumerable> Enumerable for DirectProduct<A, B> {
    fn iter() -> impl Iterator<Item = Self> {
        A::iter().flat_map(|a| B::iter().map(move |b| DirectProduct(a, b)))
    }

    fn order() -> u128 {
        A::order()
            .checked_mul(B::order())
            .expect("|A × B| overflows u128")
    }
}

impl<A: Display + Copy + Eq, B: Display + Copy + Eq> Display for DirectProduct<A, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.0, self.1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cyclic::Cyclic;

    type C2xC3 = DirectProduct<Cyclic<2>, Cyclic<3>>;

    #[test]
    fn order_is_product() {
        assert_eq!(C2xC3::order(), 6);
        assert_eq!(C2xC3::iter().count() as u128, 6);
    }

    #[test]
    fn associativity() {
        for x in C2xC3::iter() {
            for y in C2xC3::iter() {
                for z in C2xC3::iter() {
                    assert_eq!(x.op(&y).op(&z), x.op(&y.op(&z)));
                }
            }
        }
    }

    #[test]
    fn inverses_exist() {
        for x in C2xC3::iter() {
            assert_eq!(x.op(&x.inv()), C2xC3::identity());
            assert_eq!(x.inv().op(&x), C2xC3::identity());
        }
    }

    #[test]
    fn componentwise_composition() {
        let a = DirectProduct(Cyclic::<4>::from_index(2), Cyclic::<5>::from_index(3));
        let b = DirectProduct(Cyclic::<4>::from_index(3), Cyclic::<5>::from_index(4));
        let c = a.op(&b);
        assert_eq!(c.0, Cyclic::<4>::from_index(1)); // (2+3) mod 4 = 1
        assert_eq!(c.1, Cyclic::<5>::from_index(2)); // (3+4) mod 5 = 2
    }
}
