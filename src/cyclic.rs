//! The cyclic group `Z/NZ` of order `N`, parameterized by const generic.

use std::fmt::Display;

use rand::Rng;

use crate::{Enumerable, Group, Magma, Monoid, Semigroup};

/// An element of the cyclic group `Z/NZ` of order `N`.
///
/// Storage is `u16` internally, so `N ≤ 65535`.
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct Cyclic<const N: usize> {
    elem: u16,
}

impl<const N: usize> Cyclic<N> {
    /// Constructs `Cyclic<N>` from an integer, panicking if `value >= N`.
    ///
    /// Use [`Cyclic::try_from_index`] for fallible construction from external
    /// input.
    pub fn from_index(value: usize) -> Self {
        assert!(
            value < N,
            "Cyclic::<{N}>::from_index({value}): value out of range"
        );
        Self { elem: value as u16 }
    }

    /// Fallible constructor for parsing/external-input paths.
    pub fn try_from_index(value: usize) -> Result<Self, InvariantViolated> {
        if value < N {
            Ok(Self { elem: value as u16 })
        } else {
            Err(InvariantViolated::OutOfRange { got: value, max: N })
        }
    }

    /// Returns the underlying index in `0..N`.
    #[inline]
    pub fn index(&self) -> usize {
        self.elem as usize
    }

    /// Returns a uniformly random element using `thread_rng()`. Use
    /// [`Cyclic::random_with`] for deterministic / seeded RNG.
    pub fn random() -> Self {
        Self::random_with(&mut rand::thread_rng())
    }

    /// Returns a uniformly random element using the provided RNG.
    pub fn random_with<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self {
            elem: rng.gen_range(0..N as u16),
        }
    }
}

impl<const N: usize> Default for Cyclic<N> {
    fn default() -> Self {
        Self::identity()
    }
}

impl<const N: usize> Magma for Cyclic<N> {
    #[inline]
    fn op(&self, other: &Self) -> Self {
        let n = N as u16;
        Self {
            elem: (self.elem + other.elem) % n,
        }
    }
}

impl<const N: usize> Semigroup for Cyclic<N> {}

impl<const N: usize> Monoid for Cyclic<N> {
    #[inline]
    fn identity() -> Self {
        Self { elem: 0 }
    }
}

impl<const N: usize> Group for Cyclic<N> {
    #[inline]
    fn inv(&self) -> Self {
        let n = N as u16;
        Self {
            elem: (n - self.elem) % n,
        }
    }
}

impl<const N: usize> Enumerable for Cyclic<N> {
    /// Iterates `0, 1, …, N-1`.
    fn iter() -> impl Iterator<Item = Self> {
        (0..N as u16).map(|elem| Self { elem })
    }

    fn order() -> u128 {
        N as u128
    }
}

impl<const N: usize> Display for Cyclic<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.elem)
    }
}

/// Errors returned by fallible constructors in this crate.
#[derive(Debug, PartialEq, Eq)]
pub enum InvariantViolated {
    OutOfRange { got: usize, max: usize },
}

impl Display for InvariantViolated {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfRange { got, max } => {
                write!(f, "value {got} is out of range (max exclusive {max})")
            }
        }
    }
}

impl std::error::Error for InvariantViolated {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_is_two_sided() {
        for x in Cyclic::<7>::iter() {
            assert_eq!(Cyclic::<7>::identity().op(&x), x);
            assert_eq!(x.op(&Cyclic::<7>::identity()), x);
        }
    }

    #[test]
    fn associativity() {
        for x in Cyclic::<5>::iter() {
            for y in Cyclic::<5>::iter() {
                for z in Cyclic::<5>::iter() {
                    assert_eq!(x.op(&y).op(&z), x.op(&y.op(&z)));
                }
            }
        }
    }

    #[test]
    fn inverses_exist() {
        for x in Cyclic::<7>::iter() {
            assert_eq!(x.op(&x.inv()), Cyclic::<7>::identity());
            assert_eq!(x.inv().op(&x), Cyclic::<7>::identity());
        }
    }

    #[test]
    fn closure() {
        let elems: Vec<_> = Cyclic::<5>::iter().collect();
        for x in Cyclic::<5>::iter() {
            for y in Cyclic::<5>::iter() {
                let z = x.op(&y);
                assert!(elems.contains(&z));
            }
        }
    }

    #[test]
    fn abelian() {
        for x in Cyclic::<6>::iter() {
            for y in Cyclic::<6>::iter() {
                assert_eq!(x.op(&y), y.op(&x));
            }
        }
    }

    #[test]
    fn order_matches_iter_count() {
        assert_eq!(Cyclic::<5>::order(), 5);
        assert_eq!(Cyclic::<5>::iter().count() as u128, Cyclic::<5>::order());
    }

    #[test]
    fn try_from_index_rejects_out_of_range() {
        assert!(Cyclic::<5>::try_from_index(5).is_err());
        assert!(Cyclic::<5>::try_from_index(0).is_ok());
    }

    #[test]
    #[should_panic]
    fn from_index_panics_on_out_of_range() {
        let _ = Cyclic::<5>::from_index(5);
    }

    #[test]
    fn op_assign_matches_op() {
        for x in Cyclic::<6>::iter() {
            for y in Cyclic::<6>::iter() {
                let mut a = x;
                a.op_assign(&y);
                assert_eq!(a, x.op(&y));
            }
        }
    }
}
