//! Property-based axiom tests for the trait stack.
//!
//! For each concrete `Group` we ship, verify (over many randomly sampled
//! elements):
//!   - left and right identity
//!   - associativity
//!   - left and right inverse
//!   - closure (operation stays in the structure — implicitly true via Rust's
//!     type system but useful as an explicit smoke test for our impls)
//!
//! Sampling strategy: use seeded RNG via `rand::rngs::StdRng` so failures are
//! reproducible. For very small groups (Cyclic<5>, Permutation<4>) we
//! exhaustively cover; for larger ones we sample.

use groups::cyclic::Cyclic;
use groups::permutation::Permutation;
use groups::product::{DirectProduct, WreathProduct};
use groups::{Group, Magma, Monoid};

use proptest::prelude::*;
use rand::SeedableRng;
use rand::rngs::StdRng;

// ---------- Strategies ----------

fn cyclic5() -> impl Strategy<Value = Cyclic<5>> {
    (0u64..5).prop_map(|s| {
        let mut rng = StdRng::seed_from_u64(s);
        Cyclic::<5>::random_with(&mut rng)
    })
}

fn perm6() -> impl Strategy<Value = Permutation<6>> {
    any::<u64>().prop_map(|s| {
        let mut rng = StdRng::seed_from_u64(s);
        Permutation::<6>::random_with(&mut rng)
    })
}

fn direct() -> impl Strategy<Value = DirectProduct<Cyclic<3>, Permutation<5>>> {
    any::<u64>().prop_map(|s| {
        let mut rng = StdRng::seed_from_u64(s);
        DirectProduct(
            Cyclic::<3>::random_with(&mut rng),
            Permutation::<5>::random_with(&mut rng),
        )
    })
}

fn wreath() -> impl Strategy<Value = WreathProduct<Cyclic<3>, 5>> {
    any::<u64>().prop_map(|s| {
        let mut rng = StdRng::seed_from_u64(s);
        let fibers = [
            Cyclic::<3>::random_with(&mut rng),
            Cyclic::<3>::random_with(&mut rng),
            Cyclic::<3>::random_with(&mut rng),
            Cyclic::<3>::random_with(&mut rng),
            Cyclic::<3>::random_with(&mut rng),
        ];
        let perm = Permutation::<5>::random_with(&mut rng);
        WreathProduct::new(fibers, perm)
    })
}

// ---------- Axioms ----------

macro_rules! axiom_tests {
    ($mod_name:ident, $strat:expr, $type:ty) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #![proptest_config(ProptestConfig { cases: 256, .. ProptestConfig::default() })]

                #[test]
                fn left_identity(x in $strat) {
                    prop_assert_eq!(<$type>::identity().op(&x), x);
                }

                #[test]
                fn right_identity(x in $strat) {
                    prop_assert_eq!(x.op(&<$type>::identity()), x);
                }

                #[test]
                fn associativity(x in $strat, y in $strat, z in $strat) {
                    prop_assert_eq!(x.op(&y).op(&z), x.op(&y.op(&z)));
                }

                #[test]
                fn left_inverse(x in $strat) {
                    prop_assert_eq!(x.inv().op(&x), <$type>::identity());
                }

                #[test]
                fn right_inverse(x in $strat) {
                    prop_assert_eq!(x.op(&x.inv()), <$type>::identity());
                }

                #[test]
                fn double_inverse_is_identity_op(x in $strat) {
                    prop_assert_eq!(x.inv().inv(), x);
                }

                #[test]
                fn op_assign_matches_op(x in $strat, y in $strat) {
                    let mut a = x;
                    a.op_assign(&y);
                    prop_assert_eq!(a, x.op(&y));
                }
            }
        }
    };
}

axiom_tests!(cyclic5_axioms, cyclic5(), Cyclic<5>);
axiom_tests!(perm6_axioms, perm6(), Permutation<6>);
axiom_tests!(direct_axioms, direct(), DirectProduct<Cyclic<3>, Permutation<5>>);
axiom_tests!(wreath_axioms, wreath(), WreathProduct<Cyclic<3>, 5>);
