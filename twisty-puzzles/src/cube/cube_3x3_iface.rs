//! Puzzle-level interface for the 3×3: cube notation moves, algorithms,
//! pinning queries (`CubeQuery`), word reconstruction, and orbit queries.
//!
//! This sits on top of [`super::cube_3x3`] (the algebraic core) and the
//! [`groups::bsgs`] machinery, exposing them in cube-native vocabulary so
//! callers don't have to think in sticker indices.

use std::fmt;

use groups::bsgs::Bsgs;
use groups::generators::GeneratingSet;
use groups::partial_state::{Constraint, PartialState};
use groups::permutation::Permutation;
use groups::schreier_sims::deterministic::deterministic;
use groups::word::Word;
use groups::{Magma, Monoid};

use super::cube_3x3::{
    self as core, Cube3x3State, Cube3x3StickerPerm, N_STICKERS,
};

// ============ Move and Algorithm ============

/// Quarter-turn-metric (QTM) face moves with face notation. Each `Move` is
/// a single primitive turn; `R2` and similar compositions are represented
/// as multiple `Move`s in an [`Algorithm`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Move {
    R, Rp,
    L, Lp,
    U, Up,
    D, Dp,
    F, Fp,
    B, Bp,
}

impl Move {
    /// All twelve QTM moves, in the canonical order used by `face_qtm_set`.
    pub const ALL: [Move; 12] = [
        Move::R, Move::Rp, Move::L, Move::Lp, Move::U, Move::Up,
        Move::D, Move::Dp, Move::F, Move::Fp, Move::B, Move::Bp,
    ];

    /// The 3×3 group element that this move represents.
    pub fn to_state(&self) -> Cube3x3State {
        match self {
            Move::R => core::r(),
            Move::Rp => groups::Group::inv(&core::r()),
            Move::L => core::l(),
            Move::Lp => groups::Group::inv(&core::l()),
            Move::U => core::u(),
            Move::Up => groups::Group::inv(&core::u()),
            Move::D => core::d(),
            Move::Dp => groups::Group::inv(&core::d()),
            Move::F => core::f(),
            Move::Fp => groups::Group::inv(&core::f()),
            Move::B => core::b(),
            Move::Bp => groups::Group::inv(&core::b()),
        }
    }

    pub fn inverse(&self) -> Move {
        match self {
            Move::R => Move::Rp, Move::Rp => Move::R,
            Move::L => Move::Lp, Move::Lp => Move::L,
            Move::U => Move::Up, Move::Up => Move::U,
            Move::D => Move::Dp, Move::Dp => Move::D,
            Move::F => Move::Fp, Move::Fp => Move::F,
            Move::B => Move::Bp, Move::Bp => Move::B,
        }
    }
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Move::R => "R", Move::Rp => "R'",
            Move::L => "L", Move::Lp => "L'",
            Move::U => "U", Move::Up => "U'",
            Move::D => "D", Move::Dp => "D'",
            Move::F => "F", Move::Fp => "F'",
            Move::B => "B", Move::Bp => "B'",
        };
        f.write_str(s)
    }
}

/// A sequence of QTM face moves with cube-notation `Display`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Algorithm(pub Vec<Move>);

impl Algorithm {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn from_moves(moves: impl IntoIterator<Item = Move>) -> Self {
        Self(moves.into_iter().collect())
    }

    /// Apply this algorithm to a state, left-to-right (the first move is
    /// applied first, matching cube-reader convention `R U F` = "do R, then U,
    /// then F").
    pub fn apply_to(&self, state: &Cube3x3State) -> Cube3x3State {
        self.0
            .iter()
            .fold(*state, |acc, m| acc.op(&m.to_state()))
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The reverse-and-invert of this algorithm.
    pub fn inverse(&self) -> Algorithm {
        Algorithm(self.0.iter().rev().map(|m| m.inverse()).collect())
    }
}

impl fmt::Display for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, m) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(" ")?;
            }
            write!(f, "{m}")?;
        }
        Ok(())
    }
}

/// A canonical QTM `GeneratingSet` over the 48 sticker permutation. The
/// invariant assumed by [`word_to_algorithm`] is that index `2i` is move
/// `Move::ALL[i]`'s sticker perm and index `2i + 1` is its inverse — which
/// is exactly what `with_inverses` produces from the `Move::ALL` list.
fn qtm_sticker_gens() -> GeneratingSet<Cube3x3StickerPerm> {
    let pairs: Vec<Cube3x3StickerPerm> = [
        Move::R, Move::L, Move::U, Move::D, Move::F, Move::B,
    ]
    .iter()
    .map(|m| core::to_sticker_perm(&m.to_state()))
    .collect();
    GeneratingSet::with_inverses(pairs)
}

/// Translate a [`Word`] of generator indices (as emitted by
/// [`Bsgs::coset_member_word`] over [`qtm_sticker_gens`]) into a cube-notation
/// [`Algorithm`].
pub fn word_to_algorithm(word: &Word) -> Algorithm {
    // qtm_sticker_gens uses with_inverses on [R, L, U, D, F, B], so the
    // 12 indices map to: 0=R, 1=R', 2=L, 3=L', 4=U, 5=U', 6=D, 7=D',
    // 8=F, 9=F', 10=B, 11=B'. The order matches Move::ALL above.
    let moves: Vec<Move> = word.iter().map(|i| Move::ALL[i as usize]).collect();
    Algorithm(moves)
}

// ============ Pinning queries ============

/// Per-corner constraint: pin to a target slot with a target twist.
#[derive(Debug, Copy, Clone)]
pub struct CornerPin {
    /// Slot to constrain. Valid range 0..8.
    pub slot: u8,
    /// Required cubie position after the move (i.e., this slot must contain
    /// the cubie that started at `slot_target`).
    pub slot_target: u8,
    /// Required twist of the cubie now at `slot`. Valid range 0..3.
    pub twist: u8,
}

/// Per-edge constraint.
#[derive(Debug, Copy, Clone)]
pub struct EdgePin {
    pub slot: u8,
    pub slot_target: u8,
    pub flip: u8,
}

/// Builder for pinning queries on the 3×3.
///
/// Slots not mentioned via `pin_*` are wildcards (any cubie may be there
/// in any orientation). Use this to pose questions like *"what moves take
/// the corner currently at slot 0 to slot 4 with twist 1, while leaving
/// edges 0 and 1 fixed in place?"*
#[derive(Debug, Clone, Default)]
pub struct CubeQuery {
    pub corner_pins: Vec<CornerPin>,
    pub edge_pins: Vec<EdgePin>,
}

impl CubeQuery {
    pub fn new() -> Self {
        Self::default()
    }

    /// Pin a corner cubie in its solved position and orientation.
    pub fn pin_corner_solved(mut self, slot: u8) -> Self {
        self.corner_pins.push(CornerPin {
            slot,
            slot_target: slot,
            twist: 0,
        });
        self
    }

    /// Pin a corner: "the cubie that was originally at `slot_target` must
    /// end up at `slot` with the given `twist`."
    pub fn pin_corner_at(mut self, slot: u8, slot_target: u8, twist: u8) -> Self {
        assert!(slot < 8 && slot_target < 8 && twist < 3);
        self.corner_pins.push(CornerPin { slot, slot_target, twist });
        self
    }

    pub fn pin_edge_solved(mut self, slot: u8) -> Self {
        self.edge_pins.push(EdgePin {
            slot,
            slot_target: slot,
            flip: 0,
        });
        self
    }

    pub fn pin_edge_at(mut self, slot: u8, slot_target: u8, flip: u8) -> Self {
        assert!(slot < 12 && slot_target < 12 && flip < 2);
        self.edge_pins.push(EdgePin { slot, slot_target, flip });
        self
    }

    /// Render the query as a sticker-level [`PartialState`] over the 48
    /// stickers.
    ///
    /// For each corner pin (slot, slot_target, twist), the three corner
    /// stickers `3·slot+k` for k ∈ {0,1,2} are required to equal
    /// `3·slot_target + ((k - twist) mod 3)` — i.e., applying a move with
    /// permutation σ and twist τ that takes cubie `slot_target` to slot
    /// `slot` with twist `twist` means `apply_to(3·slot_target + (k-twist) mod 3)
    /// = 3·slot + k` for those stickers, equivalently
    /// `apply_to(...) ≈ inverse-direction equation` which simplifies to
    /// the formula above.
    pub fn to_sticker_partial(&self) -> PartialState<N_STICKERS> {
        let mut constraints = [Constraint::Wildcard; N_STICKERS];

        for p in &self.corner_pins {
            // We want: after applying g, the cubie at slot p.slot is the
            // one that started at p.slot_target with the given twist. In
            // sticker terms with our formula
            //   apply_to(3i+k) = 3·σ(i) + (k + τ_i) mod 3,
            // we want the sticker at source position 3·p.slot_target + k₀
            // (where k₀ is the original sticker index 0..2) to land at
            // sticker 3·p.slot + ((k₀ + p.twist) mod 3). Inverting:
            //   apply_to(3·p.slot_target + k₀) = 3·p.slot + ((k₀ + p.twist) mod 3)
            for k0 in 0u16..3 {
                let src = 3 * p.slot_target as u16 + k0;
                let dst = 3 * p.slot as u16 + ((k0 + p.twist as u16) % 3);
                constraints[src as usize] = Constraint::MustEqual(dst);
            }
        }

        for p in &self.edge_pins {
            for k0 in 0u16..2 {
                let src = 24 + 2 * p.slot_target as u16 + k0;
                let dst = 24 + 2 * p.slot as u16 + ((k0 + p.flip as u16) % 2);
                constraints[src as usize] = Constraint::MustEqual(dst);
            }
        }

        PartialState { constraints }
    }
}

// ============ Solver entry points ============

/// Cached BSGS for the standard QTM 3×3 generating set.
///
/// Construction takes ~15ms; cache as needed.
pub struct CubeBsgs {
    pub bsgs: Bsgs<Cube3x3StickerPerm, N_STICKERS>,
    pub gens: GeneratingSet<Cube3x3StickerPerm>,
}

impl CubeBsgs {
    /// Build the full QTM 3×3 BSGS. ~15ms construction time.
    pub fn build_qtm() -> Self {
        let gens = qtm_sticker_gens();
        let base: Vec<u16> = vec![
            0, 3, 6, 9, 12, 15, 18, 21, // one corner sticker per corner
            24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, // one edge sticker per edge
        ];
        let bsgs = deterministic::<_, N_STICKERS>(&gens, &base);
        Self { bsgs, gens }
    }

    /// `|G|`, which for QTM 3×3 should be `43,252,003,274,489,856,000`.
    pub fn order(&self) -> u128 {
        self.bsgs.order()
    }

    /// Whether the given state is in the cube group (always true if `state`
    /// was built from face moves, but useful for state-from-image inputs).
    pub fn is_solvable(&self, state: &Cube3x3State) -> bool {
        let perm = core::to_sticker_perm(state);
        self.bsgs.is_member(&perm)
    }
}

/// Find an [`Algorithm`] taking `start` to a state matching `query`.
///
/// Returns `None` if no such state is reachable within the search budget
/// (currently bounded BFS to depth 30 — covers all 3×3 states under God's
/// Number 20 for QTM).
pub fn find_algorithm(
    cube_bsgs: &CubeBsgs,
    start: &Cube3x3State,
    query: &CubeQuery,
) -> Option<Algorithm> {
    // We want g such that start.op(&g) matches query.
    // Equivalently, g must match the partial state shifted by start.inv():
    // for each constrained source sticker s, the target value v becomes
    // (start.inv())·(v lifted) — translating each constraint's target
    // value through the sticker permutation of start.inv().
    let start_perm = core::to_sticker_perm(start);
    let start_inv = groups::Group::inv(&start_perm);
    let raw_partial = query.to_sticker_partial();

    let mut shifted = [Constraint::Wildcard; N_STICKERS];
    for (i, c) in raw_partial.constraints.iter().enumerate() {
        if let Constraint::MustEqual(v) = c {
            // We want apply_to(start)(i) = v_original, equivalently
            // apply_to(g)(i) = start_inv(v_original) — i.e., the constraint
            // on g is that its sticker at index i equals start_inv(v).
            use groups::bsgs::PermutationLike;
            let new_v = start_inv.apply_to(*v);
            shifted[i] = Constraint::MustEqual(new_v);
        }
    }
    let partial: PartialState<N_STICKERS> = PartialState { constraints: shifted };

    let word = cube_bsgs.bsgs.coset_member_word(&cube_bsgs.gens, &partial)?;
    Some(word_to_algorithm(&word))
}

/// Like [`find_algorithm`] but with a configurable BFS depth bound. Lower
/// bounds let callers bail out fast on hard constraint sets.
pub fn find_algorithm_max_depth(
    cube_bsgs: &CubeBsgs,
    start: &Cube3x3State,
    query: &CubeQuery,
    max_depth: u32,
) -> Option<Algorithm> {
    let start_perm = core::to_sticker_perm(start);
    let start_inv = groups::Group::inv(&start_perm);
    let raw_partial = query.to_sticker_partial();

    let mut shifted = [Constraint::Wildcard; N_STICKERS];
    for (i, c) in raw_partial.constraints.iter().enumerate() {
        if let Constraint::MustEqual(v) = c {
            use groups::bsgs::PermutationLike;
            let new_v = start_inv.apply_to(*v);
            shifted[i] = Constraint::MustEqual(new_v);
        }
    }
    let partial: PartialState<N_STICKERS> = PartialState { constraints: shifted };

    let word = cube_bsgs
        .bsgs
        .coset_member_word_max_depth(&cube_bsgs.gens, &partial, max_depth)?;
    Some(word_to_algorithm(&word))
}

/// Where can the cubie at corner slot `slot` end up under the QTM face-move
/// group? Returns the orbit as a list of slots reachable from `slot`.
pub fn corner_orbit(cube_bsgs: &CubeBsgs, slot: u8) -> Vec<u8> {
    use groups::bsgs::PermutationLike;
    // The orbit of corner sticker 3*slot under all generators.
    let mut visited = vec![false; N_STICKERS];
    let mut frontier = vec![3 * slot as u16];
    visited[3 * slot as usize] = true;
    while let Some(p) = frontier.pop() {
        for (_, g) in cube_bsgs.gens.iter() {
            let q = g.apply_to(p);
            if !visited[q as usize] {
                visited[q as usize] = true;
                frontier.push(q);
            }
        }
    }
    // Convert sticker indices back to corner slots.
    (0..8u8)
        .filter(|s| visited[3 * (*s) as usize])
        .collect()
}

/// Where can the cubie at edge slot `slot` end up?
pub fn edge_orbit(cube_bsgs: &CubeBsgs, slot: u8) -> Vec<u8> {
    use groups::bsgs::PermutationLike;
    let start = 24 + 2 * slot as u16;
    let mut visited = vec![false; N_STICKERS];
    let mut frontier = vec![start];
    visited[start as usize] = true;
    while let Some(p) = frontier.pop() {
        for (_, g) in cube_bsgs.gens.iter() {
            let q = g.apply_to(p);
            if !visited[q as usize] {
                visited[q as usize] = true;
                frontier.push(q);
            }
        }
    }
    (0..12u8)
        .filter(|s| visited[24 + 2 * (*s) as usize])
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use groups::Group;

    #[test]
    fn move_state_round_trip() {
        for m in Move::ALL {
            assert_eq!(m.to_state(), m.to_state(), "move state should be deterministic");
            assert_eq!(
                m.to_state().op(&m.inverse().to_state()),
                Cube3x3State::identity(),
                "{m} · {m}.inverse() must be identity",
                m = m,
            );
        }
    }

    #[test]
    fn algorithm_display() {
        let alg = Algorithm::from_moves([Move::R, Move::U, Move::Rp, Move::Up]);
        assert_eq!(format!("{alg}"), "R U R' U'");
    }

    #[test]
    fn algorithm_apply_matches_op_chain() {
        let alg = Algorithm::from_moves([Move::R, Move::U, Move::F]);
        let direct = core::r().op(&core::u()).op(&core::f());
        assert_eq!(alg.apply_to(&Cube3x3State::identity()), direct);
    }

    #[test]
    fn algorithm_inverse() {
        let alg = Algorithm::from_moves([Move::R, Move::U, Move::F]);
        let inv = alg.inverse();
        assert_eq!(format!("{inv}"), "F' U' R'");
        let composed = inv.apply_to(&alg.apply_to(&Cube3x3State::identity()));
        assert_eq!(composed, Cube3x3State::identity());
    }

    #[test]
    fn corner_orbit_under_qtm_is_all_8_slots() {
        let cube = CubeBsgs::build_qtm();
        let orbit = corner_orbit(&cube, 0);
        assert_eq!(orbit.len(), 8, "S_8 acts transitively on corners under QTM");
    }

    #[test]
    fn edge_orbit_under_qtm_is_all_12_slots() {
        let cube = CubeBsgs::build_qtm();
        let orbit = edge_orbit(&cube, 0);
        assert_eq!(orbit.len(), 12, "S_12 acts transitively on edges under QTM");
    }

    #[test]
    fn find_algorithm_for_solved_query_from_solved_state() {
        // Asking for "leave URF in place" from the solved cube should give
        // an empty algorithm (or a short loop).
        let cube = CubeBsgs::build_qtm();
        let query = CubeQuery::new().pin_corner_solved(0);
        let alg = find_algorithm(&cube, &Cube3x3State::identity(), &query).unwrap();
        // Apply it; the URF stickers should still be in place.
        let result = alg.apply_to(&Cube3x3State::identity());
        let perm = core::to_sticker_perm(&result);
        use groups::bsgs::PermutationLike;
        // After apply, sticker 0 (URF top) should still be at sticker 0.
        assert_eq!(perm.apply_to(0), 0);
        assert_eq!(perm.apply_to(1), 1);
        assert_eq!(perm.apply_to(2), 2);
    }

    #[test]
    fn find_algorithm_to_specific_corner_slot() {
        // From solved, find moves that put corner-0-cubie into slot-4
        // with twist 0.
        let cube = CubeBsgs::build_qtm();
        let query = CubeQuery::new().pin_corner_at(4, 0, 0);
        let alg = find_algorithm(&cube, &Cube3x3State::identity(), &query).unwrap();
        let result = alg.apply_to(&Cube3x3State::identity());
        let perm = core::to_sticker_perm(&result);
        use groups::bsgs::PermutationLike;
        // Cubie originally at slot 0 (stickers 0,1,2) should now be at slot
        // 4 with twist 0 (stickers 12,13,14 with k unchanged).
        assert_eq!(perm.apply_to(0), 12);
        assert_eq!(perm.apply_to(1), 13);
        assert_eq!(perm.apply_to(2), 14);
    }

    #[test]
    fn find_algorithm_solving_a_small_scramble() {
        // Apply a 3-move scramble, then ask the solver for moves that
        // "fix UFR (corner 0)" — verify the result actually does fix it.
        let cube = CubeBsgs::build_qtm();
        let scramble = Algorithm::from_moves([Move::R, Move::U, Move::Fp]);
        let scrambled = scramble.apply_to(&Cube3x3State::identity());
        let query = CubeQuery::new().pin_corner_solved(0);
        let alg = find_algorithm(&cube, &scrambled, &query).unwrap();
        let result = alg.apply_to(&scrambled);
        let perm = core::to_sticker_perm(&result);
        use groups::bsgs::PermutationLike;
        assert_eq!(perm.apply_to(0), 0);
    }
}
