/-
Gvozdjak's conjecture on graceful labelings of paths with prescribed end labels.

STATUS: statement only. This file has NOT been compiled yet.
It uses core Lean only (no Mathlib), so that the final proof has no dependencies.
-/

namespace Gvozdjak

/-- `|x - y|` on natural numbers. -/
def adiff (x y : Nat) : Nat := (x - y) + (y - x)

/-- The consecutive absolute differences of a sequence. -/
def diffs : List Nat → List Nat
  | x :: y :: t => adiff x y :: diffs (y :: t)
  | _ => []

/-- `p` is an `(a, b; n)`-graceful labeling of the path with `n` edges:
it starts at `a`, ends at `b`, uses each of `0, …, n` exactly once,
and its `n` consecutive differences are `1, …, n` in some order. -/
def IsGraceful (a b n : Nat) (p : List Nat) : Prop :=
  p.head? = some a ∧
  p.getLast? = some b ∧
  p.Perm (List.range (n + 1)) ∧
  (diffs p).Perm (List.range' 1 n)

/-- Gvozdjak's conditions (C1)–(C3), with denominators cleared.
* (C1) `b - a ≡ n(n+1)/2 (mod 2)`
* (C2) `0 < |b - a| ≤ (n+1)/2`
* (C3) `n/2 ≤ a + b ≤ 3n/2` -/
def Admissible (a b n : Nat) : Prop :=
  a ≤ n ∧ b ≤ n ∧
  (a + b + n * (n + 1) / 2) % 2 = 0 ∧
  a ≠ b ∧ 2 * adiff a b ≤ n + 1 ∧
  n ≤ 2 * (a + b) ∧ 2 * (a + b) ≤ 3 * n

/-- Sanity check from the paper's example: `0, 4, 1, 3, 2` is `(0, 2; 4)`-graceful. -/
example : IsGraceful 0 2 4 [0, 4, 1, 3, 2] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

/-- **Gvozdjak's conjecture.** For `n ≥ 1`, an `(a, b; n)`-graceful labeling exists
if and only if `(a, b; n)` is admissible.  (`n = 0` is excluded: the one-vertex path
has `a = b = 0`, which (C2) forbids.) -/
theorem gvozdjak (a b n : Nat) (hn : 1 ≤ n) :
    (∃ p, IsGraceful a b n p) ↔ Admissible a b n := by
  sorry

end Gvozdjak
