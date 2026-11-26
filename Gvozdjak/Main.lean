/-
Gvozdjak's conjecture: the main theorem.
-/
import Gvozdjak.Small
import Gvozdjak.Reduction
import Gvozdjak.Necessity

namespace Gvozdjak

theorem admissible_symm {a b n : Nat} (h : Admissible a b n) : Admissible b a n := by
  unfold Admissible adiff at *
  omega

theorem isGraceful_reverse {a b n : Nat} {p : List Nat} (h : IsGraceful a b n p) :
    IsGraceful b a n p.reverse :=
  isGraceful_iff_spec.mpr (isGraceful_iff_spec.mp h).reverse

/-- Sufficiency, by strong induction on `n`: small cases are explicit, and for `n ≥ 42` one of
the fifteen moves reduces `(a, b; n)` to a smaller admissible triple. -/
theorem sufficiency (n : Nat) : ∀ a b, Admissible a b n → ∃ p, IsGraceful a b n p := by
  refine Nat.strongRecOn n ?_
  intro n ih
  have key : ∀ a b, a < b → Admissible a b n → ∃ p, IsGraceful a b n p := by
    intro a b hab h
    by_cases hn : n ≤ 41
    · exact small hn hab h
    · exact red_sound (reduction n a b (by omega) hab (admissible_iff_admL.mp h))
        (fun N s e hN hadm => ih N hN s e (admissible_iff_admL.mpr hadm))
  intro a b h
  rcases Nat.lt_or_ge a b with hab | hab
  · exact key a b hab h
  · have hne : a ≠ b := h.2.2.2.1
    obtain ⟨p, hp⟩ := key b a (by omega) (admissible_symm h)
    exact ⟨p.reverse, isGraceful_reverse hp⟩

/-- **Gvozdjak's conjecture.** For `n ≥ 1`, an `(a, b; n)`-graceful labeling of the path with
`n` edges exists if and only if `(a, b; n)` is admissible. -/
theorem gvozdjak : GvozdjakConjecture := by
  intro a b n hn
  exact ⟨fun ⟨_, hp⟩ => necessity hn hp, sufficiency n a b⟩

end Gvozdjak

#print axioms Gvozdjak.gvozdjak
