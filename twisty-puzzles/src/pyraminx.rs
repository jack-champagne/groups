//! Pyraminx — tetrahedral puzzle.
//!
//! Group structure (no tips): `DirectProduct<WreathProduct<Cyclic<3>, 4>,
//! WreathProduct<Cyclic<2>, 6>>` — 4 corner cubies (twist only, no
//! permutation) × 6 edges (permuted with `C_2` orientation).
//!
//! Published value: `|G_pyraminx (no tips)| = 933,120 = 81 · 360 · 32`
//! (corner twists × A_6 edge perms × edge orientations).
//! With tips: `× 3⁴ = 75,582,720`.

use groups::cyclic::Cyclic;
use groups::permutation::Permutation;
use groups::product::{DirectProduct, WreathProduct};
use groups::Monoid;

pub type CornerGroup = WreathProduct<Cyclic<3>, 4>;
pub type EdgeGroup = WreathProduct<Cyclic<2>, 6>;
pub type PyraminxState = DirectProduct<CornerGroup, EdgeGroup>;

/// Stickers: 4 corners × 3 + 6 edges × 2 = 24.
pub const N_STICKERS: usize = 24;
pub type PyraminxStickerPerm = Permutation<N_STICKERS>;

#[inline]
fn t(x: usize) -> Cyclic<3> {
    Cyclic::<3>::from_index(x)
}

#[inline]
fn e(x: usize) -> Cyclic<2> {
    Cyclic::<2>::from_index(x)
}

/// Edge flip helper: build a fiber array with 1s at the given slots.
fn edge_flips(slots: &[usize]) -> [Cyclic<2>; 6] {
    let mut f = [e(0); 6];
    for &s in slots {
        f[s] = e(1);
    }
    f
}

/// U: twists corner 0 (top); 3-cycles edges (0, 1, 2). Flips two of the
/// cycled edges (per pyraminx geometry: a 120° face rotation flips two of
/// the three edges around its vertex). The choice of which two is forced
/// by the convention `m³ = identity`.
pub fn u() -> PyraminxState {
    let mut cf = [t(0); 4];
    cf[0] = t(1);
    DirectProduct(
        CornerGroup::new(cf, Permutation::<4>::identity()),
        EdgeGroup::new(edge_flips(&[1, 2]), Permutation::<6>::cycle(&[0, 1, 2])),
    )
}

pub fn l() -> PyraminxState {
    let mut cf = [t(0); 4];
    cf[1] = t(1);
    DirectProduct(
        CornerGroup::new(cf, Permutation::<4>::identity()),
        EdgeGroup::new(edge_flips(&[3, 5]), Permutation::<6>::cycle(&[1, 3, 5])),
    )
}

pub fn r() -> PyraminxState {
    let mut cf = [t(0); 4];
    cf[2] = t(1);
    DirectProduct(
        CornerGroup::new(cf, Permutation::<4>::identity()),
        EdgeGroup::new(edge_flips(&[4, 5]), Permutation::<6>::cycle(&[2, 4, 5])),
    )
}

pub fn back() -> PyraminxState {
    let mut cf = [t(0); 4];
    cf[3] = t(1);
    DirectProduct(
        CornerGroup::new(cf, Permutation::<4>::identity()),
        EdgeGroup::new(edge_flips(&[3, 4]), Permutation::<6>::cycle(&[0, 3, 4])),
    )
}

pub fn face_moves() -> [PyraminxState; 4] {
    [u(), l(), r(), back()]
}

pub fn to_sticker_perm(state: &PyraminxState) -> PyraminxStickerPerm {
    let DirectProduct(corners, edges) = state;
    let mut map = [0u16; N_STICKERS];
    for i in 0..4 {
        let new_slot = corners.perm.apply(i) as u16;
        let twist = corners.fibers[i].index() as u16;
        for k in 0..3u16 {
            map[(3 * i as u16 + k) as usize] = 3 * new_slot + ((k + twist) % 3);
        }
    }
    for j in 0..6 {
        let new_slot = edges.perm.apply(j) as u16;
        let flip = edges.fibers[j].index() as u16;
        for k in 0..2u16 {
            map[(12 + 2 * j as u16 + k) as usize] = 12 + 2 * new_slot + ((k + flip) % 2);
        }
    }
    Permutation::from_map(map)
}

pub fn face_move_sticker_perms() -> [PyraminxStickerPerm; 4] {
    let m = face_moves();
    [
        to_sticker_perm(&m[0]),
        to_sticker_perm(&m[1]),
        to_sticker_perm(&m[2]),
        to_sticker_perm(&m[3]),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use groups::generators::GeneratingSet;
    use groups::schreier_sims::deterministic::deterministic;
    use groups::{Group, Magma};

    #[test]
    fn each_face_move_has_order_3() {
        for (name, m) in [("U", u()), ("L", l()), ("R", r()), ("B", back())] {
            let m3 = m.op(&m).op(&m);
            assert_eq!(m3, PyraminxState::identity(), "{name}^3 must be identity");
        }
    }

    #[test]
    fn sticker_perm_homomorphism() {
        use rand::SeedableRng;
        use rand::seq::SliceRandom;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xfeed);
        let moves = face_moves();
        for _ in 0..30 {
            let mut g = PyraminxState::identity();
            for _ in 0..(rand::Rng::gen_range(&mut rng, 0..15)) {
                g = g.op(moves.choose(&mut rng).unwrap());
            }
            let mut h = PyraminxState::identity();
            for _ in 0..(rand::Rng::gen_range(&mut rng, 0..15)) {
                h = h.op(moves.choose(&mut rng).unwrap());
            }
            assert_eq!(to_sticker_perm(&g.op(&h)), to_sticker_perm(&g).op(&to_sticker_perm(&h)));
        }
    }

    #[test]
    fn pyraminx_group_order_via_schreier_sims() {
        let gens = GeneratingSet::with_inverses(face_move_sticker_perms());
        let base: Vec<u16> = vec![0, 3, 6, 9, 12, 14, 16, 18, 20, 22];
        let bsgs = deterministic::<_, N_STICKERS>(&gens, &base);
        assert_eq!(bsgs.order(), 933_120);
    }
}
