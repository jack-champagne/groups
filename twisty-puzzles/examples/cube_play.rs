//! Apply an algorithm to a solved cube and render before/after.
//!
//! Pass an algorithm as a single argument in Singmaster-ish notation, e.g.
//!
//! ```
//! cargo run --release -p twisty-puzzles --example cube_play -- "R U R' U'"
//! cargo run --release -p twisty-puzzles --example cube_play -- "R U R' F' R U R' U' R' F R2 U' R'"   # T-perm
//! cargo run --release -p twisty-puzzles --example cube_play -- "R U2 R' U' R U' R'"                  # Sune
//! ```
//!
//! With no argument, prints the solved cube.

use groups::Monoid;
use twisty_puzzles::cube::cube_3x3 as core;
use twisty_puzzles::cube::cube_3x3_iface::{Algorithm, Move};
use twisty_puzzles::cube::cube_3x3_render::render;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let alg_str = args.join(" ");
    let alg = parse_algorithm(&alg_str);

    let solved = core::Cube3x3State::identity();

    println!("=== solved ===");
    print!("{}", render(&solved));

    if alg.is_empty() {
        println!("\n(No algorithm provided. Pass one as the first argument,\n \
                  e.g. \"R U R' U'\" for the sexy move.)");
        return;
    }

    println!("\n=== applied: {alg} ===");
    let after = alg.apply_to(&solved);
    print!("{}", render(&after));

    // Quick stats.
    println!("\nAlgorithm: {alg}");
    println!("Length:    {} moves (QTM)", alg.len());
    println!(
        "Inverse:   {}",
        alg.inverse()
    );
}

fn parse_algorithm(s: &str) -> Algorithm {
    let mut moves = Vec::new();
    for token in s.split_whitespace() {
        if token.is_empty() {
            continue;
        }
        let (face_char, suffix) = token.split_at(1);
        let primary = match face_char {
            "R" => Move::R,
            "L" => Move::L,
            "U" => Move::U,
            "D" => Move::D,
            "F" => Move::F,
            "B" => Move::B,
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
            other => {
                eprintln!("unrecognized suffix on {token}: {other:?}");
            }
        }
    }
    Algorithm(moves)
}
