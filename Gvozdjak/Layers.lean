/-
Lemma A: layers exist.

A layer is an α-labeled path placed in arbitrary position: its low labels fill an interval
starting at `lo`, its high labels fill an interval starting at `hi`, and its differences fill
the interval that this placement forces.  Stating the lemma for every position at once makes
"stretching" a layer implicit, so no separate stretching lemma is needed.

Shapes (κ ≥ 0, 0 ≤ A ≤ κ):
* `O κ A`  : κ+1 low and κ+1 high labels, from low index `A` to high index `A`;
* `EL κ A` : κ+1 low and κ high labels, from low index `A` to low index `κ - A`;
* `EH κ A` : κ low and κ+1 high labels, from high index `A` to high index `κ - A`.
-/
import Gvozdjak.Basic

namespace Gvozdjak

abbrev HasO (κ A lo hi : Nat) : Prop :=
  ∃ p, Spec (lo + A) (hi + A) (fun x => ind lo (κ + 1) x + ind hi (κ + 1) x)
    (ind (hi - lo - κ) (2 * κ + 1)) p

abbrev HasEL (κ A lo hi : Nat) : Prop :=
  ∃ p, Spec (lo + A) (lo + κ - A) (fun x => ind lo (κ + 1) x + ind hi κ x)
    (ind (hi - lo - κ) (2 * κ)) p

abbrev HasEH (κ A lo hi : Nat) : Prop :=
  ∃ p, Spec (hi + A) (hi + κ - A) (fun x => ind lo κ x + ind hi (κ + 1) x)
    (ind (hi - lo - κ + 1) (2 * κ)) p

def LayersAt (κ : Nat) : Prop :=
  (∀ A lo hi, A ≤ κ → lo + κ + 1 ≤ hi → HasO κ A lo hi) ∧
  (∀ A lo hi, 1 ≤ κ → A ≤ κ → 2 * A ≠ κ → lo + κ + 1 ≤ hi → HasEL κ A lo hi) ∧
  (∀ A lo hi, 1 ≤ κ → A ≤ κ → 2 * A ≠ κ → lo + κ ≤ hi → HasEH κ A lo hi)

set_option maxHeartbeats 0 in
theorem layersAt (κ : Nat) : LayersAt κ := by
  refine Nat.strongRecOn κ ?_
  intro κ ih
  -- `EL κ A` for `2A < κ`
  have elS : ∀ A lo hi, 1 ≤ κ → 2 * A < κ → lo + κ + 1 ≤ hi → HasEL κ A lo hi := by
    intro A lo hi hk hA hh
    by_cases h1 : κ = 1
    · subst h1
      have hA0 : A = 0 := by omega
      subst hA0
      refine ⟨[lo, hi, lo + 1], rfl, rfl, ?_, ?_⟩
      · intro x
        simp only [List.count_cons, List.count_nil, beq_iff_eq, ite_eq_ind_one, ind]
        omega
      · intro d
        simp only [diffs_cons_cons, diffs_singleton, List.count_cons, List.count_nil,
          beq_iff_eq, ite_eq_ind_one, ind, adiff]
        omega
    · by_cases h3 : κ = 3 * A + 1
      · obtain ⟨pX, hX⟩ := (ih (A + 1) (by omega)).1 A lo (hi + (2 * A - 1))
          (by omega) (by omega)
        obtain ⟨pY, hY⟩ := (ih (2 * A - 1) (by omega)).2.1 A (lo + (A + 1) + 1) hi
          (by omega) (by omega) (by omega) (by omega)
        exact ⟨_, (hX.append hY).congr (by omega) (by omega)
          (fun x => by simp only [ind]; omega) (fun d => by simp only [ind, adiff]; omega)⟩
      · obtain ⟨pX, hX⟩ := (ih A (by omega)).1 A lo (hi + (κ - 1 - A))
          (by omega) (by omega)
        obtain ⟨pY, hY⟩ := (ih (κ - 1 - A) (by omega)).2.1 A (lo + A + 1) hi
          (by omega) (by omega) (by omega) (by omega)
        exact ⟨_, (hX.append hY).congr (by omega) (by omega)
          (fun x => by simp only [ind]; omega) (fun d => by simp only [ind, adiff]; omega)⟩
  -- `EL κ A` in general, by reversal
  have elAll : ∀ A lo hi, 1 ≤ κ → A ≤ κ → 2 * A ≠ κ → lo + κ + 1 ≤ hi → HasEL κ A lo hi := by
    intro A lo hi hk hA hne hh
    by_cases hs : 2 * A < κ
    · exact elS A lo hi hk hs hh
    · obtain ⟨p, hp⟩ := elS (κ - A) lo hi hk (by omega) hh
      exact ⟨_, hp.reverse.congr (by omega) (by omega) (fun _ => rfl) (fun _ => rfl)⟩
  -- `EH κ A`, by reflecting `EL κ (κ - A)`
  have eh : ∀ A lo hi, 1 ≤ κ → A ≤ κ → 2 * A ≠ κ → lo + κ ≤ hi → HasEH κ A lo hi := by
    intro A lo hi hk hA hne hh
    obtain ⟨p, hp⟩ := elAll (κ - A) lo (hi + 1) hk (by omega) (by omega) (by omega)
    refine ⟨_, (hp.reflect (lo + hi + κ) ?_).congr (by omega) (by omega) ?_ ?_⟩
    · intro y hy
      simp only [ind] at hy
      omega
    · intro x
      try dsimp only
      split <;> simp only [ind] <;> omega
    · intro d
      simp only [ind]
      omega
  -- `O κ A` for `2A ≤ κ`
  have oS : ∀ A lo hi, 2 * A ≤ κ → lo + κ + 1 ≤ hi → HasO κ A lo hi := by
    intro A lo hi hA hh
    by_cases h0 : κ = 0
    · subst h0
      have hA0 : A = 0 := by omega
      subst hA0
      refine ⟨[lo, hi], rfl, rfl, ?_, ?_⟩
      · intro x
        simp only [List.count_cons, List.count_nil, beq_iff_eq, ite_eq_ind_one, ind]
        omega
      · intro d
        simp only [diffs_cons_cons, diffs_singleton, List.count_cons, List.count_nil,
          beq_iff_eq, ite_eq_ind_one, ind, adiff]
        omega
    · by_cases h2 : 2 * A = κ
      · obtain ⟨pX, hX⟩ := (ih A (by omega)).2.1 A lo (hi + A + 1)
          (by omega) (by omega) (by omega) (by omega)
        obtain ⟨pY, hY⟩ := (ih A (by omega)).2.2 A (lo + A + 1) hi
          (by omega) (by omega) (by omega) (by omega)
        exact ⟨_, (hX.append hY.reverse).congr (by omega) (by omega)
          (fun x => by simp only [ind]; omega) (fun d => by simp only [ind, adiff]; omega)⟩
      · obtain ⟨pX, hX⟩ := (ih (κ / 2) (by omega)).1 A lo (hi + (κ - 1) / 2 + 1)
          (by omega) (by omega)
        obtain ⟨pY, hY⟩ := (ih ((κ - 1) / 2) (by omega)).1 A (lo + κ / 2 + 1) hi
          (by omega) (by omega)
        exact ⟨_, (hX.append hY).congr (by omega) (by omega)
          (fun x => by simp only [ind]; omega) (fun d => by simp only [ind, adiff]; omega)⟩
  -- `O κ A` in general, by reflecting and reversing `O κ (κ - A)`
  have oAll : ∀ A lo hi, A ≤ κ → lo + κ + 1 ≤ hi → HasO κ A lo hi := by
    intro A lo hi hA hh
    by_cases hs : 2 * A ≤ κ
    · exact oS A lo hi hs hh
    · obtain ⟨p, hp⟩ := oS (κ - A) lo hi (by omega) hh
      refine ⟨_, (hp.reflect (lo + hi + κ) ?_).reverse.congr (by omega) (by omega) ?_ ?_⟩
      · intro y hy
        simp only [ind] at hy
        omega
      · intro x
        try dsimp only
        split <;> simp only [ind] <;> omega
      · intro d
        rfl
  exact ⟨oAll, elAll, eh⟩

theorem hasO {κ A lo hi : Nat} (h1 : A ≤ κ) (h2 : lo + κ + 1 ≤ hi) : HasO κ A lo hi :=
  (layersAt κ).1 A lo hi h1 h2

theorem hasEL {κ A lo hi : Nat} (h0 : 1 ≤ κ) (h1 : A ≤ κ) (h2 : 2 * A ≠ κ)
    (h3 : lo + κ + 1 ≤ hi) : HasEL κ A lo hi :=
  (layersAt κ).2.1 A lo hi h0 h1 h2 h3

theorem hasEH {κ A lo hi : Nat} (h0 : 1 ≤ κ) (h1 : A ≤ κ) (h2 : 2 * A ≠ κ)
    (h3 : lo + κ ≤ hi) : HasEH κ A lo hi :=
  (layersAt κ).2.2 A lo hi h0 h1 h2 h3

end Gvozdjak
