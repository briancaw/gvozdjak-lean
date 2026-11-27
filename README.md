# gvozdjak-lean

A Lean 4 proof of Gvozdjak's 2004 conjecture on graceful labelings of paths with
prescribed end labels.

**Status.** The theorem `Gvozdjak.gvozdjak` in `Gvozdjak/Main.lean` compiles with no
`sorry`, and depends only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); the build checks this on every push. No human mathematician has reviewed
the project yet. What Lean guarantees is that the statement in `Gvozdjak/Statement.lean`
is proved; whether that statement is a faithful rendering of the conjecture is for a
reader to judge, and that file is about forty lines long.

## The statement

A graceful labeling of the path with `n` edges is an ordering of `0, 1, ..., n`
whose `n` consecutive absolute differences are `1, 2, ..., n` in some order.
For `n >= 1`, one exists starting at `a` and ending at `b` if and only if

1. `b - a` has the same parity as `n(n+1)/2`,
2. `0 < |b - a| <= (n+1)/2`,
3. `n/2 <= a + b <= 3n/2`.

(`n = 0` is excluded: the one-vertex path has `a = b = 0`, which condition 2 forbids.)

## Layout

| File | Content |
| --- | --- |
| `Statement.lean` | Definitions and the statement. Read this first. |
| `Basic.lean` | `Spec`: a labeling described by its ends and its label and difference counts; concatenation, reversal, translation, reflection. |
| `Layers.lean` | Alpha-labeled paths with every admissible pair of ends, in every position. |
| `Moves.lean` | The fifteen moves: wrapping up to three layers around a smaller graceful path. Generated. |
| `Small.lean` | Explicit labelings for all 3,311 admissible triples with `n <= 41`, `a < b`, checked in the kernel. Generated. |
| `Reduction00.lean` ... `Reduction31.lean`, `Reduction.lean` | For `n >= 42`, explicit parameters showing that one of the moves applies, by residue class of `(n mod 4, a mod 2)`. Generated. |
| `Necessity.lean` | The three conditions are necessary. |
| `Main.lean` | The theorem, and the axiom check. |
| `BaseCases.lean` | The 39 labelings from the paper's appendix (not needed by the proof). |

The generated files are produced by the Python scripts in `scripts/`. The integer set
library isl is used there only to *find* formulas and case splits; every step is
re-checked by Lean, so the scripts are not part of the trusted base.

## Building

Core Lean only, no Mathlib: `lake build` (Lean 4.33.1; about 25 minutes, mostly linear
arithmetic).

## Acknowledgement

The construction, the formalization and the scripts were produced with substantial
assistance from Claude, an AI model made by Anthropic.
