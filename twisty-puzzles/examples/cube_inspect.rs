//! Inspect a cube state's algebraic invariants: cycle structure, twist sums,
//! parity. Pass an algorithm; the example shows what the resulting state
//! "is" mathematically.
//!
//! Examples:
//! ```
//! cargo run -p twisty-puzzles --example cube_inspect -- "R U R' U'"
//! cargo run -p twisty-puzzles --example cube_inspect -- "R U2 R' U' R U' R'"     # Sune
//! cargo run -p twisty-puzzles --example cube_inspect -- "R U R' F' R U R' U' R' F R2 U' R'"   # T-perm
//! ```

use groups::Monoid;
use twisty_puzzles::cube::cube_3x3 as core;
use twisty_puzzles::cube::cube_3x3_iface::{Algorithm, Move};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let alg_str = args.join(" ");
    let alg = parse_algorithm(&alg_str);
    let solved = core::Cube3x3State::identity();
    let state = alg.apply_to(&solved);

    println!("=== Cube state inspector ===");
    println!("Algorithm: {alg}  ({} moves QTM)\n", alg.len());

    let groups::product::DirectProduct(corners, edges) = state;

    println!("Corner permutation:");
    let corner_cycles = perm_cycles_to_strings(&corners.perm.as_map(), CORNER_NAMES);
    if corner_cycles.is_empty() {
        println!("  identity (all corners in place)");
    } else {
        for c in &corner_cycles {
            println!("  ({c})");
        }
    }
    print_corner_orientations(&corners);

    println!("\nEdge permutation:");
    let edge_cycles = perm_cycles_to_strings(&edges.perm.as_map(), EDGE_NAMES);
    if edge_cycles.is_empty() {
        println!("  identity (all edges in place)");
    } else {
        for c in &edge_cycles {
            println!("  ({c})");
        }
    }
    print_edge_orientations(&edges);

    println!("\nObservable invariants for this state:");
    let twist_sum: u32 = (0..8).map(|i| corners.fibers[i].index() as u32).sum::<u32>() % 3;
    let flip_sum: u32 = (0..12).map(|j| edges.fibers[j].index() as u32).sum::<u32>() % 2;
    let cp = corners.perm.parity();
    let ep = edges.perm.parity();
    println!("  Corner twist sum mod 3:  {twist_sum}");
    println!("  Edge flip sum mod 2:     {flip_sum}");
    println!("  Corner perm parity:      {cp}");
    println!("  Edge perm parity:        {ep}");

    // For algorithm-derived states these are forced (twist=0, flip=0,
    // cp == ep) by construction. Worth showing for understanding the
    // structure, but not a validity check — every algorithm output is
    // automatically valid.
}

const CORNER_NAMES: [&str; 8] = ["URF", "UFL", "ULB", "UBR", "DFR", "DLF", "DBL", "DRB"];
const EDGE_NAMES: [&str; 12] = [
    "UF", "UL", "UB", "UR", "FR", "FL", "BL", "BR", "DF", "DL", "DB", "DR",
];

fn perm_cycles_to_strings<const N: usize>(map: &[u16; N], names: [&str; N]) -> Vec<String>
where
    [&'static str; N]: Sized,
{
    let mut visited = [false; N];
    let mut out = Vec::new();
    for i in 0..N {
        if visited[i] || map[i] as usize == i {
            // Skip fixed points and already-visited.
            visited[i] = true;
            continue;
        }
        let mut cycle = Vec::new();
        let mut j = i;
        while !visited[j] {
            visited[j] = true;
            cycle.push(names[j]);
            j = map[j] as usize;
        }
        if cycle.len() >= 2 {
            out.push(cycle.join(" → "));
        }
    }
    out
}

fn print_corner_orientations(c: &core::CornerGroup) {
    let twisted: Vec<(usize, u8)> = (0..8)
        .filter_map(|i| {
            let t = c.fibers[i].index() as u8;
            if t == 0 {
                None
            } else {
                Some((i, t))
            }
        })
        .collect();
    if twisted.is_empty() {
        println!("  All corner orientations 0.");
    } else {
        let s: Vec<String> = twisted
            .iter()
            .map(|(i, t)| format!("{}: +{t}", CORNER_NAMES[*i]))
            .collect();
        println!("  Twists: {}", s.join(", "));
    }
}

fn print_edge_orientations(e: &core::EdgeGroup) {
    let flipped: Vec<usize> = (0..12)
        .filter(|&j| e.fibers[j].index() == 1)
        .collect();
    if flipped.is_empty() {
        println!("  All edge orientations 0 (no flips).");
    } else {
        let s: Vec<String> = flipped.iter().map(|j| EDGE_NAMES[*j].to_string()).collect();
        println!("  Flipped: {}", s.join(", "));
    }
}

fn parse_algorithm(s: &str) -> Algorithm {
    let mut moves = Vec::new();
    for token in s.split_whitespace() {
        if token.is_empty() {
            continue;
        }
        let (face_char, suffix) = token.split_at(1);
        let primary = match face_char {
            "R" => Move::R, "L" => Move::L, "U" => Move::U,
            "D" => Move::D, "F" => Move::F, "B" => Move::B,
            _ => {
                eprintln!("unrecognized face: {token}");
                continue;
            }
        };
        match suffix {
            "" => moves.push(primary),
            "'" => moves.push(primary.inverse()),
            "2" => {
                moves.push(primary);
                moves.push(primary);
            }
            other => eprintln!("unrecognized suffix on {token}: {other:?}"),
        }
    }
    Algorithm(moves)
}
