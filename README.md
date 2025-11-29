# proofs-square-circle-overlap

Formal verification in Rocq (formerly Coq) of the overlap area between a circle
and a square, both centered at the origin. The project provides a complete
case-by-case analysis covering all possible configurations from full overlap
to zero overlap, together with reference implementations in Haskell and Python.

## Problem statement

Given a circle of radius R centered at the origin and a square with side length
2s also centered at the origin, compute the area of their intersection. The
solution requires careful geometric decomposition based on the relationship
between R and s.

## Goal: integrating over all circle centers

If the objective is to integrate the overlap area over every possible circle
center z in the plane, define A(z) = ∫ 1_S(u) · 1_C(u−z) du (a convolution).
Swapping the integrals yields

∫ A(z) dz = ∫ 1_S(u) (∫ 1_C(u−z) dz) du = (area of C) · (area of S)
          = (πR²) · (4s²).

Thus, over all of ℝ² the total integral is just the product of the two areas,
so the eight positional cases collapse. If circle centers are restricted to a
bounded window instead, integrate this same convolution only over that window.

## Case decomposition

The image `Rough/Area of overlap between circle and square - 2D (Tidy Working).png`
illustrates the eight distinct cases that arise:

1. **Full circle contained** (s >> R): Overlap area = πR²
2. **Circle extends beyond top/bottom** (moderate s):
   Area = πR² - sector(y) + triangle(y)
3. **Circle extends beyond top and right** (smaller s):
   Area = πR² - sector(x) + triangle1(x) - sector2(y) + triangle2(y)
4. **Complex asymmetric case** (s ≈ R):
   Uses double integral formula involving arcsin and algebraic terms
5. **Circle extends beyond bottom** (different moderate s):
   Area = sector(y) - triangle(y)
6. **Circle mostly outside, lower configuration**:
   Area = πR² - LowerRightAreaLikeD(x,y) - LeftSegment(x)
7. **Circle mostly outside, upper-right configuration**:
   Area = UpperRightSector(x,y) - UpperTriangle(x,y) - RightTriangle(x,y)
8. **No overlap** (s << R or circle too small): Overlap area = 0

Each case employs a combination of circular sectors, triangular corrections,
and in the most general scenario a double integral over the overlapping domain.

## Repository layout

- `Rocq/` – the formal development
  - `SquareCircleOverlap.v`: definitions of geometric primitives (sectors,
    triangles, segment areas), the case analysis, and the main area formula
  - `_CoqProject`: logical load paths (`-Q . SquareCircleOverlap`) and file list
- `Haskell/` – informal reference implementation that mirrors the case analysis
  for numerical experimentation in GHCi
- `Python/` – quick-running sanity checks that empirically validate the formulas
  against numerical integration
- `Rough/` – working diagrams and visual aids, including the comprehensive
  8-case illustration

## Building the Rocq proofs

```bash
cd Rocq
coq_makefile -f _CoqProject -o Makefile
make                    # compiles all .v files
make clean              # remove artifacts
```

The project targets Rocq 8.20+ (Coq 8.20+). All files live under the
`SquareCircleOverlap` namespace as configured in `_CoqProject`.

## Haskell quick start

```bash
cd Haskell
ghci SquareCircleOverlap.hs
Prelude> overlapArea 1.0 1.5   -- circle radius 1.0, square half-side 1.5
```

This implementation is not formally verified but is useful for exploring the
geometric formulas and generating visualizations.

## Python sanity checks

The scripts in `Python/` provide numerical integration baselines:

```bash
cd Python
python3 test_overlap_cases.py
python3 validate_formulas.py
```

They compare the analytic formulas against Monte Carlo and quadrature methods
to ensure correctness before formalizing in Rocq.

## Current status

- `Rocq/SquareCircleOverlap.v` is under active development
- Case analysis structure is defined based on the 8-case decomposition
- Formal proofs of area formulas are in progress
- Haskell and Python reference implementations match the diagram specification

To work on the development interactively, use your preferred Rocq/Coq IDE
(CoqIDE, VS Code + VsCoq, Proof General), reload
`Rocq/SquareCircleOverlap.v`, and re-run `make` after edits to ensure the
project compiles.
