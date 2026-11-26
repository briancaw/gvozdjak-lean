# gvozdjak-lean

Work in progress: a Lean 4 formalization of a claimed proof of Gvozdjak's 2004
conjecture on graceful labelings of paths with prescribed end labels.

**Status: nothing is proved here yet.** The repository currently contains only the
formal statement (`Gvozdjak/Statement.lean`); the main theorem is marked `sorry`.
The underlying paper proof is computer-assisted and has not been checked by a
combinatorialist.

## The statement

A graceful labeling of the path with `n` edges is an ordering of `0, 1, ..., n`
whose `n` consecutive absolute differences are `1, 2, ..., n` in some order.
The conjecture: for `n >= 1`, one exists starting at `a` and ending at `b`
if and only if

1. `b - a` has the same parity as `n(n+1)/2`,
2. `0 < |b - a| <= (n+1)/2`,
3. `n/2 <= a + b <= 3n/2`.

## Plan

1. Statement and the explicit base-case labelings.
2. Onion lemma (wrapping stretched alpha-labeled layers around a core) and existence of layers.
3. Necessity of the three conditions.
4. The reduction theorem, with explicit parameters for each of the fifteen moves.

The project uses core Lean only (no Mathlib). Build with `lake build`.
