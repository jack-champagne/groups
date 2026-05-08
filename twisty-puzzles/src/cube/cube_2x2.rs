//! 2×2 Pocket Cube.
//!
//! Group structure: `WreathProduct<Cyclic<3>, 8>` — 8 corner cubies, each
//! with a 3-fold orientation, permuted under `S₈`.
//!
//! `|⟨R, U, F⟩| = 7! · 3⁶ = 3,674,160`. R, U, F never touch the DBL corner,
//! which is therefore implicitly fixed — this is the standard published
//! value for the 2×2 cube group.

use groups::cyclic::Cyclic;
use groups::permutation::Permutation;
use groups::product::WreathProduct;
use groups::Monoid;

pub type Cube2x2State = WreathProduct<Cyclic<3>, 8>;
pub const N_STICKERS: usize = 24;
pub type Cube2x2StickerPerm = Permutation<N_STICKERS>;

#[inline]
fn t(x: usize) -> Cyclic<3> {
    Cyclic::<3>::from_index(x)
}

pub fn r() -> Cube2x2State {
    let mut fibers = [t(0); 8];
    fibers[0] = t(2);
    fibers[3] = t(1);
    fibers[4] = t(1);
    fibers[7] = t(2);
    Cube2x2State::new(fibers, Permutation::<8>::cycle(&[0, 4, 7, 3]))
}

pub fn u() -> Cube2x2State {
    Cube2x2State::new([t(0); 8], Permutation::<8>::cycle(&[0, 1, 2, 3]))
}

pub fn f() -> Cube2x2State {
    let mut fibers = [t(0); 8];
    fibers[0] = t(1);
    fibers[1] = t(2);
    fibers[4] = t(2);
    fibers[5] = t(1);
    Cube2x2State::new(fibers, Permutation::<8>::cycle(&[0, 4, 5, 1]))
}

pub fn l() -> Cube2x2State {
    let mut fibers = [t(0); 8];
    fibers[1] = t(1);
    fibers[2] = t(2);
    fibers[5] = t(2);
    fibers[6] = t(1);
    Cube2x2State::new(fibers, Permutation::<8>::cycle(&[1, 5, 6, 2]))
}

pub fn d() -> Cube2x2State {
    Cube2x2State::new([t(0); 8], Permutation::<8>::cycle(&[4, 7, 6, 5]))
}

pub fn b() -> Cube2x2State {
    let mut fibers = [t(0); 8];
    fibers[2] = t(1);
    fibers[3] = t(2);
    fibers[6] = t(2);
    fibers[7] = t(1);
    Cube2x2State::new(fibers, Permutation::<8>::cycle(&[3, 7, 6, 2]))
}

pub fn face_moves() -> [Cube2x2State; 6] {
    [r(), l(), u(), d(), f(), b()]
}

/// Faithful permutation representation of a 2×2 state as a permutation of
/// 24 corner stickers.
///
/// `apply_to(3i+k) = 3·σ(i) + (k + τ_i) mod 3`
///
/// Verified to be a homomorphism in tests.
pub fn to_sticker_perm(state: &Cube2x2State) -> Cube2x2StickerPerm {
    let mut map = [0u16; N_STICKERS];
    for i in 0..8 {
        let new_slot = state.perm.apply(i) as u16;
        let twist = state.fibers[i].index() as u16;
        for k in 0..3u16 {
            let dst = 3 * new_slot + ((k + twist) % 3);
            map[(3 * i as u16 + k) as usize] = dst;
        }
    }
    Permutation::from_map(map)
}

/// Convenience: sticker permutations for each face move.
pub fn face_move_sticker_perms() -> [Cube2x2StickerPerm; 6] {
    let m = face_moves();
    [
        to_sticker_perm(&m[0]),
        to_sticker_perm(&m[1]),
        to_sticker_perm(&m[2]),
        to_sticker_perm(&m[3]),
        to_sticker_perm(&m[4]),
        to_sticker_perm(&m[5]),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use groups::generators::GeneratingSet;
    use groups::schreier_sims::deterministic::deterministic;
    use groups::{Group, Magma};

    #[test]
    fn r_pow_4_is_identity() {
        let r = r();
        assert_eq!(r.op(&r).op(&r).op(&r), Cube2x2State::identity());
    }

    #[test]
    fn sexy_pow_6_is_identity() {
        let r = r();
        let u = u();
        let sexy = r.op(&u).op(&r.inv()).op(&u.inv());
        let sexy6 = (0..6).fold(Cube2x2State::identity(), |acc, _| acc.op(&sexy));
        assert_eq!(sexy6, Cube2x2State::identity());
    }

    #[test]
    fn sticker_perm_homomorphism() {
        use rand::SeedableRng;
        use rand::seq::SliceRandom;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x2222);
        let moves = face_moves();
        for _ in 0..30 {
            let mut g = Cube2x2State::identity();
            for _ in 0..(rand::Rng::gen_range(&mut rng, 0..15)) {
                g = g.op(moves.choose(&mut rng).unwrap());
            }
            let mut h = Cube2x2State::identity();
            for _ in 0..(rand::Rng::gen_range(&mut rng, 0..15)) {
                h = h.op(moves.choose(&mut rng).unwrap());
            }
            let prod = g.op(&h);
            let p_g = to_sticker_perm(&g);
            let p_h = to_sticker_perm(&h);
            let p_prod = to_sticker_perm(&prod);
            assert_eq!(p_prod, p_g.op(&p_h));
        }
    }

    #[test]
    fn corner_group_order_via_schreier_sims() {
        // |⟨R, U, F⟩| = 7! · 3⁶ = 3,674,160. The DBL corner is implicitly
        // fixed since R, U, F don't touch it.
        let r_sp = to_sticker_perm(&r());
        let u_sp = to_sticker_perm(&u());
        let f_sp = to_sticker_perm(&f());
        let gens = GeneratingSet::with_inverses([r_sp, u_sp, f_sp]);
        let base: Vec<u16> = (0..8).map(|i| 3 * i).collect();
        let bsgs = deterministic::<_, N_STICKERS>(&gens, &base);
        assert_eq!(bsgs.order(), 3_674_160);
    }
}
