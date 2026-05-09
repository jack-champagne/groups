# groups + twisty-puzzles

A Rust workspace for **computational group theory targeted at twisty
puzzles**. Two crates:

- **`groups`** — pure abstract algebra: trait stack (`Magma → Semigroup →
  Monoid → Group`), `Action`, `Cyclic<N>`, `Permutation<N>`,
  `DirectProduct`, `SemidirectProduct`, `WreathProduct`, generating sets,
  words, partial states, BSGS, all three Schreier-Sims variants
  (deterministic, Monte Carlo, Las Vegas), orbit enumeration, IDA*.

- **`twisty-puzzles`** — models of WCA-recognized puzzles built on
  `groups`: 2×2, 3×3, Pyraminx, Skewb, plus stubs for 4×4–7×7, Megaminx,
  Square-1, and Clock.

## Quickstart — fun things to run locally

All examples in the workspace can be run via cargo. **Use `--release` for
performance-sensitive demos.**

### See the cube

```bash
cargo run --release -p twisty-puzzles --example cube_play -- "R U R' U'"
```

Renders the solved cube and the cube after applying the *sexy move*
using Unicode color blocks.

### Inspect a cube state's algebra

```bash
cargo run --release -p twisty-puzzles --example cube_inspect -- "R U R' F' R U R' U' R' F R2 U' R'"
```

Prints the corner/edge cycle decomposition, twist sums, parity, and
invariant checks for the resulting state. Useful for understanding what
any given algorithm "does" mathematically.

### Pinning queries — the headline use case

```bash
cargo run --release -p twisty-puzzles --example cube_3x3_queries
```

Builds the BSGS for the cube, validates `|G| = 43,252,003,274,489,856,000`,
then runs constraint-based queries: "find moves that put URF in slot 4",
"pin URF + UBR + UF in place", "what slots can corner 0 reach under just
R, U?". All sub-millisecond after the ~15 ms BSGS construction.

### Solve and progressive pinning

```bash
cargo run --release -p twisty-puzzles --example cube_3x3_solve
```

Applies a 4-move scramble, then solves it two ways: (1) end-to-end via
full-state pin and `find_algorithm`, (2) progressively pinning cubies
one at a time. Demonstrates how partial-state machinery enables
incremental solving.

### Solve-time benchmark

```bash
cargo run --release -p twisty-puzzles --example cube_3x3_solve_bench
```

Measures `find_algorithm` solve time across scramble depths 1–6.
Honest about where plain BFS hits the wall (~depth 6, ~750 ms). Hitting
random-scramble depth 17–20 needs Thistlethwaite, Kociemba, or Korf with
pattern databases.

### Last-layer subgroup exploration

```bash
cargo run --release -p twisty-puzzles --example cube_3x3_last_layer
```

Builds the BSGS with an F2L-first base ordering, extracts the LL
stabilizer's 12 generators (~7 ms), and enumerates all **62,208** LL
states with shortest-word maps in ~200 ms. Validates `|LL| = 4! · 3³ ·
4! · 2³ / 2`.

### Word-tracked SS on the 2×2

```bash
cargo run --release -p twisty-puzzles --example cube_2x2_word_demo
```

Builds the 2×2 BSGS while tracking face-move word histories for every
strong generator and transversal element. Validates the
`enumerate_orbit_translated` pipeline that produces actual face-move
algorithms (in Singmaster notation) for every state in a chosen
subgroup.

### The cube via wreath products

```bash
cargo run --example cube3_corners
```

(In the `groups` crate root.) Demonstrates the wreath-product
composition fix: `R⁴ = identity`, `(R U R' U')⁶ = identity`,
twist-sum-mod-3 invariant. Things the user's existing direct-product
representation in `puzzle-cube/main.rs` cannot exhibit.

## Tests + benchmarks

```bash
# Full test suite (groups + twisty-puzzles + proptest)
cargo test --workspace

# Microbenchmarks
cargo bench --workspace
```

The benchmark suite measures: `Permutation::op`, `WreathProduct::op`,
deterministic Schreier-Sims construction across `S_n` for n=4..8, BSGS
sift, and per-puzzle SS validation.

Headline numbers (release):
- `Permutation<48>::op`: 35 ns
- `WreathProduct<C₃,8>::op` (cube corners): 11.5 ns
- BSGS sift on `S_8`: 112 ns
- Schreier-Sims chain build for full 3×3 cube: ~15 ms
- 2×2 chain build with word tracking: ~2 ms

## Repo layout

```
groups/
├── src/
│   ├── lib.rs                          # trait stack
│   ├── cyclic.rs                       # Cyclic<N>
│   ├── permutation.rs                  # Permutation<N>
│   ├── product/                        # DirectProduct, SemidirectProduct, WreathProduct
│   ├── generators.rs                   # GeneratingSet
│   ├── word.rs                         # Word
│   ├── partial_state.rs                # PartialState + coset queries
│   ├── bsgs/                           # BSGS, sift, membership, |G|
│   ├── schreier_sims/                  # deterministic + monte_carlo + las_vegas + with_words
│   ├── orbit.rs                        # enumerate_orbit + enumerate_orbit_translated
│   └── solver/                         # IDA*, Heuristic trait
├── examples/
│   └── cube3_corners.rs
├── benches/
└── tests/

twisty-puzzles/
├── src/
│   ├── lib.rs
│   ├── cube/
│   │   ├── cube_2x2.rs
│   │   ├── cube_3x3.rs
│   │   ├── cube_3x3_iface.rs           # Move, Algorithm, CubeQuery, find_algorithm
│   │   ├── cube_3x3_render.rs          # Unicode renderer
│   │   └── cube_n.rs                   # 4×4–7×7 (doc stub)
│   ├── pyraminx.rs
│   ├── skewb.rs
│   ├── megaminx.rs                     # type stub
│   ├── square_one.rs                   # doc-only (semigroup)
│   └── clock.rs                        # doc-only (not a permutation puzzle)
├── examples/
│   ├── cube_play.rs                    # render before/after applying an algorithm
│   ├── cube_inspect.rs                 # show cycle decomposition + invariants
│   ├── cube_3x3_queries.rs             # pinning + orbits
│   ├── cube_3x3_solve.rs               # scramble + solve + progressive pinning
│   ├── cube_3x3_solve_bench.rs         # solve-time benchmark
│   ├── cube_3x3_last_layer.rs          # LL stabilizer enumeration
│   └── cube_2x2_word_demo.rs           # word-tracked SS demo
└── benches/
```

## Status

**Library:** complete for puzzle-shaped CGT — all major algorithms
implemented, ~130 tests passing.

**Puzzles:** 2×2, 3×3, Pyraminx, Skewb fully modeled with SS-validated
`|G|`. The 3×3 has the full puzzle-level interface (Move, Algorithm,
CubeQuery, find_algorithm, orbit queries, ASCII rendering).

**Followups (post-v1):** Thistlethwaite/Kociemba/Korf for fast random-
scramble solving, NxN cube generalization (4×4–7×7), full Megaminx
model, Square-1 (semigroup, needs state-conditional moves), Clock
(abelian — needs Smith normal form, not Schreier-Sims).
