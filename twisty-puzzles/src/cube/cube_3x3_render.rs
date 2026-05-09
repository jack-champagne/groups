//! ASCII / Unicode renderer for the 3×3 cube state.
//!
//! Unfolds the cube into a "+" layout and prints each face as a 3×3 grid
//! of colored squares. Verified by `solved_state_renders_uniformly` test —
//! the solved cube prints with each face uniformly colored.

use super::cube_3x3 as core;

/// One of the six face colors.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Face {
    U, D, F, B, L, R,
}

impl Face {
    /// Single-letter face label (U/D/F/B/L/R).
    pub fn letter(self) -> char {
        match self {
            Face::U => 'U', Face::D => 'D',
            Face::F => 'F', Face::B => 'B',
            Face::L => 'L', Face::R => 'R',
        }
    }

    /// Standard cube color glyph using Unicode color blocks.
    pub fn color_block(self) -> &'static str {
        match self {
            Face::U => "⬜", // White
            Face::D => "🟨", // Yellow
            Face::F => "🟩", // Green
            Face::B => "🟦", // Blue
            Face::L => "🟧", // Orange
            Face::R => "🟥", // Red
        }
    }
}

/// `HOME_FACE[i]` is the face that sticker `i` belongs to in the solved
/// state. Convention:
/// - Corner stickers `3i+0` are on the cubie's U/D-axis face.
/// - Corner stickers `3i+1` and `3i+2` are on the other two faces, ordered
///   "clockwise around the corner looking from outside."
/// - Edge stickers `2j+0` are on the U/D-axis face (for U/D edges) or the
///   F/B-axis face (for slice edges); `2j+1` is the other.
pub const HOME_FACE: [Face; 48] = [
    // Corner 0 URF: U, F, R
    Face::U, Face::F, Face::R,
    // Corner 1 UFL: U, L, F
    Face::U, Face::L, Face::F,
    // Corner 2 ULB: U, B, L
    Face::U, Face::B, Face::L,
    // Corner 3 UBR: U, R, B
    Face::U, Face::R, Face::B,
    // Corner 4 DFR: D, R, F
    Face::D, Face::R, Face::F,
    // Corner 5 DLF: D, F, L
    Face::D, Face::F, Face::L,
    // Corner 6 DBL: D, L, B
    Face::D, Face::L, Face::B,
    // Corner 7 DRB: D, B, R
    Face::D, Face::B, Face::R,
    // Edge 0 UF: U, F
    Face::U, Face::F,
    // Edge 1 UL: U, L
    Face::U, Face::L,
    // Edge 2 UB: U, B
    Face::U, Face::B,
    // Edge 3 UR: U, R
    Face::U, Face::R,
    // Edge 4 FR: F, R
    Face::F, Face::R,
    // Edge 5 FL: F, L
    Face::F, Face::L,
    // Edge 6 BL: B, L
    Face::B, Face::L,
    // Edge 7 BR: B, R
    Face::B, Face::R,
    // Edge 8 DF: D, F
    Face::D, Face::F,
    // Edge 9 DL: D, L
    Face::D, Face::L,
    // Edge 10 DB: D, B
    Face::D, Face::B,
    // Edge 11 DR: D, R
    Face::D, Face::R,
];

/// 8 visible cells per face (centers are fixed and shown as the face's home
/// color; this array tracks the sticker positions whose colors change).
/// Order is row-major: TL, TM, TR, ML, MR, BL, BM, BR.
pub const U_LAYOUT: [u16; 8] = [
    6, 28, 9,    // ULB-U, UB-U, UBR-U
    26, 30,      // UL-U, UR-U
    3, 24, 0,    // UFL-U, UF-U, URF-U
];

pub const D_LAYOUT: [u16; 8] = [
    15, 40, 12,  // DLF-D, DF-D, DFR-D
    42, 46,      // DL-D, DR-D
    18, 44, 21,  // DBL-D, DB-D, DRB-D
];

pub const F_LAYOUT: [u16; 8] = [
    5, 25, 1,    // UFL-F, UF-F, URF-F
    34, 32,      // FL-F, FR-F
    16, 41, 14,  // DLF-F, DF-F, DFR-F
];

pub const R_LAYOUT: [u16; 8] = [
    2, 31, 10,   // URF-R, UR-R, UBR-R
    33, 39,      // FR-R, BR-R
    13, 47, 23,  // DFR-R, DR-R, DRB-R
];

pub const L_LAYOUT: [u16; 8] = [
    8, 27, 4,    // ULB-L, UL-L, UFL-L
    37, 35,      // BL-L, FL-L
    19, 43, 17,  // DBL-L, DL-L, DLF-L
];

pub const B_LAYOUT: [u16; 8] = [
    11, 29, 7,   // UBR-B, UB-B, ULB-B
    38, 36,      // BR-B, BL-B
    22, 45, 20,  // DRB-B, DB-B, DBL-B
];

/// Returns the face whose color is shown at position `p` in cube state `σ`.
///
/// The sticker currently at position `p` is the one whose original position
/// is `σ⁻¹(p)`; its color is its home face.
pub fn face_at_position(state: &core::Cube3x3State, p: u16) -> Face {
    use groups::Group;
    let sigma = core::to_sticker_perm(state);
    let sigma_inv = sigma.inv();
    let sticker_id = groups::bsgs::PermutationLike::apply_to(&sigma_inv, p);
    HOME_FACE[sticker_id as usize]
}

/// Render the 3×3 cube state as an unfolded "+" layout using Unicode color
/// blocks. Each face is a 3×3 grid; the cube is laid out as
///
/// ```text
///         U U U
///         U U U
///         U U U
/// L L L  F F F  R R R  B B B
/// L L L  F F F  R R R  B B B
/// L L L  F F F  R R R  B B B
///         D D D
///         D D D
///         D D D
/// ```
pub fn render(state: &core::Cube3x3State) -> String {
    let face_grid = |face: Face, layout: &[u16; 8]| -> [Face; 9] {
        let mut g = [face; 9];
        // Cell positions in the grid, row-major: 0=TL 1=TM 2=TR 3=ML 4=CC 5=MR 6=BL 7=BM 8=BR
        // layout entries map to: TL TM TR ML MR BL BM BR (skipping CC).
        let cells = [0, 1, 2, 3, 5, 6, 7, 8];
        for (i, &cell) in cells.iter().enumerate() {
            g[cell] = face_at_position(state, layout[i]);
        }
        g[4] = face; // center is fixed
        g
    };

    let u = face_grid(Face::U, &U_LAYOUT);
    let d = face_grid(Face::D, &D_LAYOUT);
    let f = face_grid(Face::F, &F_LAYOUT);
    let b = face_grid(Face::B, &B_LAYOUT);
    let l = face_grid(Face::L, &L_LAYOUT);
    let r = face_grid(Face::R, &R_LAYOUT);

    let row = |g: &[Face; 9], r: usize| -> String {
        format!(
            "{}{}{}",
            g[3 * r].color_block(),
            g[3 * r + 1].color_block(),
            g[3 * r + 2].color_block()
        )
    };

    let mut out = String::new();
    // Top: U face
    for r_idx in 0..3 {
        out.push_str("      ");
        out.push_str(&row(&u, r_idx));
        out.push('\n');
    }
    // Middle: L F R B
    for r_idx in 0..3 {
        out.push_str(&row(&l, r_idx));
        out.push_str(&row(&f, r_idx));
        out.push_str(&row(&r, r_idx));
        out.push_str(&row(&b, r_idx));
        out.push('\n');
    }
    // Bottom: D face
    for r_idx in 0..3 {
        out.push_str("      ");
        out.push_str(&row(&d, r_idx));
        out.push('\n');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cube::cube_3x3_iface::{Algorithm, Move};
    use groups::Monoid;

    #[test]
    fn solved_state_renders_uniformly() {
        // Every cell of each face should show that face's color in the solved
        // state.
        let solved = core::Cube3x3State::identity();
        for (face, layout) in [
            (Face::U, &U_LAYOUT),
            (Face::D, &D_LAYOUT),
            (Face::F, &F_LAYOUT),
            (Face::R, &R_LAYOUT),
            (Face::L, &L_LAYOUT),
            (Face::B, &B_LAYOUT),
        ] {
            for &p in layout.iter() {
                let actual = face_at_position(&solved, p);
                assert_eq!(
                    actual,
                    face,
                    "solved state cell at face {face:?} position {p} \
                     showed {actual:?} instead",
                );
            }
        }
    }

    #[test]
    fn rendering_changes_after_a_move() {
        let solved = core::Cube3x3State::identity();
        let alg = Algorithm::from_moves([Move::R]);
        let after = alg.apply_to(&solved);
        let r1 = render(&solved);
        let r2 = render(&after);
        assert_ne!(r1, r2);
    }

    #[test]
    fn home_face_count_is_balanced() {
        // 8 stickers per face × 6 faces = 48.
        let mut counts = [0u32; 6];
        for f in HOME_FACE.iter() {
            let idx = match f {
                Face::U => 0, Face::D => 1, Face::F => 2,
                Face::B => 3, Face::L => 4, Face::R => 5,
            };
            counts[idx] += 1;
        }
        for (i, c) in counts.iter().enumerate() {
            assert_eq!(*c, 8, "face {i} has {c} stickers, expected 8");
        }
    }
}
