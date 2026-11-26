/-
Basic machinery.

A labeling is described by a `Spec`: its first and last label, how often each label occurs,
and how often each difference occurs.  Gracefulness, α-labeled layers in arbitrary position,
and partially assembled onions are all instances of `Spec`, and concatenating two pieces
is a single lemma (`Spec.append`).  All later arithmetic is linear and is discharged by `omega`.
-/
import Gvozdjak.Statement

namespace Gvozdjak

/-- Indicator of the interval `[s, s + k)`, written with `min`/`max` so that `omega`
can reason about it. -/
def ind (s k x : Nat) : Nat := min (x + 1) (s + k) - max x s

theorem ite_eq_ind (s k x : Nat) : (if s ≤ x ∧ x < s + k then 1 else 0) = ind s k x := by
  unfold ind; split <;> omega

theorem ite_eq_ind_one (w d : Nat) : (if w = d then 1 else 0) = ind w 1 d := by
  unfold ind; split <;> omega

theorem ite_lt_eq_ind (n x : Nat) : (if x < n then 1 else 0) = ind 0 n x := by
  unfold ind; split <;> omega

theorem adiff_comm (x y : Nat) : adiff x y = adiff y x := by
  unfold adiff; omega

@[simp] theorem diffs_nil : diffs [] = [] := rfl
@[simp] theorem diffs_singleton (x : Nat) : diffs [x] = [] := rfl
@[simp] theorem diffs_cons_cons (x y : Nat) (t : List Nat) :
    diffs (x :: y :: t) = adiff x y :: diffs (y :: t) := rfl

/-- Differences of a concatenation: the two blocks of differences plus the joining edge. -/
theorem diffs_append_cons {v u : Nat} :
    ∀ (p q : List Nat), p.getLast? = some v →
      diffs (p ++ u :: q) = diffs p ++ adiff v u :: diffs (u :: q)
  | [], q, h => by simp at h
  | [x], q, h => by
      have hx : x = v := by simpa using h
      subst hx
      rfl
  | x :: y :: p', q, h => by
      have h' : (y :: p').getLast? = some v := by
        rw [List.getLast?_cons_cons] at h; exact h
      have ih := @diffs_append_cons v u (y :: p') q h'
      show adiff x y :: diffs ((y :: p') ++ u :: q) = _
      rw [ih]
      rfl

theorem diffs_reverse : ∀ p : List Nat, diffs p.reverse = (diffs p).reverse
  | [] => rfl
  | [x] => rfl
  | x :: y :: t => by
      have ih := diffs_reverse (y :: t)
      have hl : (y :: t).reverse.getLast? = some y := by simp
      rw [List.reverse_cons, diffs_append_cons _ _ hl, ih, diffs_cons_cons, List.reverse_cons,
        adiff_comm y x]
      rfl

theorem count_map_add (lo x : Nat) :
    ∀ p : List Nat, (p.map (lo + ·)).count x = if lo ≤ x then p.count (x - lo) else 0
  | [] => by simp
  | y :: t => by
      simp only [List.map_cons, List.count_cons, count_map_add lo x t, beq_iff_eq]
      (repeat' split) <;> omega

theorem diffs_map_add (lo : Nat) : ∀ p : List Nat, diffs (p.map (lo + ·)) = diffs p
  | [] => rfl
  | [x] => rfl
  | x :: y :: t => by
      have ih := diffs_map_add lo (y :: t)
      have e : adiff (lo + x) (lo + y) = adiff x y := by unfold adiff; omega
      show adiff (lo + x) (lo + y) :: diffs ((y :: t).map (lo + ·)) = adiff x y :: diffs (y :: t)
      rw [ih, e]

theorem count_map_sub (c x : Nat) :
    ∀ p : List Nat, (∀ y, y ∈ p → y ≤ c) →
      (p.map (c - ·)).count x = if x ≤ c then p.count (c - x) else 0
  | [], _ => by simp
  | y :: t, h => by
      have hy : y ≤ c := h y (by simp)
      have ih := count_map_sub c x t (fun z hz => h z (by simp [hz]))
      simp only [List.map_cons, List.count_cons, ih, beq_iff_eq]
      (repeat' split) <;> omega

theorem diffs_map_sub (c : Nat) :
    ∀ p : List Nat, (∀ y, y ∈ p → y ≤ c) → diffs (p.map (c - ·)) = diffs p
  | [], _ => rfl
  | [x], _ => rfl
  | x :: y :: t, h => by
      have hx : x ≤ c := h x (by simp)
      have hy : y ≤ c := h y (by simp)
      have ih := diffs_map_sub c (y :: t) (fun z hz => h z (by simp [hz]))
      have e : adiff (c - x) (c - y) = adiff x y := by unfold adiff; omega
      show adiff (c - x) (c - y) :: diffs ((y :: t).map (c - ·)) = adiff x y :: diffs (y :: t)
      rw [ih, e]

/-- `p` starts at `u`, ends at `v`, contains each label `x` exactly `cv x` times and has
each difference `d` exactly `cd d` times. -/
structure Spec (u v : Nat) (cv cd : Nat → Nat) (p : List Nat) : Prop where
  hd : p.head? = some u
  lt : p.getLast? = some v
  cnt : ∀ x, p.count x = cv x
  dcnt : ∀ d, (diffs p).count d = cd d

namespace Spec

theorem congr {u v u' v' : Nat} {cv cd cv' cd' : Nat → Nat} {p : List Nat}
    (h : Spec u v cv cd p) (hu : u = u') (hv : v = v')
    (hcv : ∀ x, cv x = cv' x) (hcd : ∀ d, cd d = cd' d) : Spec u' v' cv' cd' p :=
  ⟨hu ▸ h.hd, hv ▸ h.lt, fun x => (h.cnt x).trans (hcv x), fun d => (h.dcnt d).trans (hcd d)⟩

/-- Concatenation: counts add, and the joining edge contributes one difference. -/
theorem append {u v u' v' : Nat} {cv cd cv' cd' : Nat → Nat} {p q : List Nat}
    (h1 : Spec u v cv cd p) (h2 : Spec u' v' cv' cd' q) :
    Spec u v' (fun x => cv x + cv' x)
      (fun d => cd d + cd' d + ind (adiff v u') 1 d) (p ++ q) := by
  obtain ⟨q', rfl⟩ := List.head?_eq_some_iff.mp h2.hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.head?_append, h1.hd]; rfl
  · rw [List.getLast?_append, h2.lt]; rfl
  · intro x
    rw [List.count_append, h1.cnt, h2.cnt]
  · intro d
    have e2 := h2.dcnt d
    rw [diffs_append_cons _ _ h1.lt, List.count_append, List.count_cons, h1.dcnt, e2]
    simp only [beq_iff_eq, ite_eq_ind_one]
    omega

theorem reverse {u v : Nat} {cv cd : Nat → Nat} {p : List Nat}
    (h : Spec u v cv cd p) : Spec v u cv cd p.reverse := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.head?_reverse]; exact h.lt
  · rw [List.getLast?_reverse]; exact h.hd
  · intro x; rw [List.count_reverse]; exact h.cnt x
  · intro d; rw [diffs_reverse, List.count_reverse]; exact h.dcnt d

/-- Translate every label by `lo`. -/
theorem shift {u v : Nat} {cv cd : Nat → Nat} {p : List Nat}
    (h : Spec u v cv cd p) (lo : Nat) :
    Spec (lo + u) (lo + v) (fun x => if lo ≤ x then cv (x - lo) else 0) cd (p.map (lo + ·)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.head?_map, h.hd]; rfl
  · rw [List.getLast?_map, h.lt]; rfl
  · intro x; rw [count_map_add, h.cnt]
  · intro d; rw [diffs_map_add]; exact h.dcnt d

/-- Reflect every label in `c`. -/
theorem reflect {u v : Nat} {cv cd : Nat → Nat} {p : List Nat}
    (h : Spec u v cv cd p) (c : Nat) (hb : ∀ y, 0 < cv y → y ≤ c) :
    Spec (c - u) (c - v) (fun x => if x ≤ c then cv (c - x) else 0) cd (p.map (c - ·)) := by
  have hmem : ∀ y, y ∈ p → y ≤ c := fun y hy =>
    hb y (by rw [← h.cnt y]; exact List.count_pos_iff.mpr hy)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.head?_map, h.hd]; rfl
  · rw [List.getLast?_map, h.lt]; rfl
  · intro x; rw [count_map_sub c x p hmem, h.cnt]
  · intro d; rw [diffs_map_sub c p hmem]; exact h.dcnt d

/-- A single vertex. -/
theorem single (x : Nat) : Spec x x (ind x 1) (fun _ => 0) [x] := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro y
    simp only [List.count_cons, List.count_nil, beq_iff_eq, ite_eq_ind_one]
    omega
  · intro d; rfl

end Spec

/-- Gracefulness is the `Spec` with labels `0..n` and differences `1..n`, each once. -/
theorem isGraceful_iff_spec {a b n : Nat} {p : List Nat} :
    IsGraceful a b n p ↔ Spec a b (ind 0 (n + 1)) (ind 1 n) p := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, ?_, ?_⟩
    · intro x
      rw [h3.count_eq x, List.count_range, ite_lt_eq_ind]
    · intro d
      rw [h4.count_eq d, List.count_range_1', ite_eq_ind]
  · intro h
    refine ⟨h.hd, h.lt, ?_, ?_⟩
    · refine List.perm_iff_count.mpr (fun x => ?_)
      rw [h.cnt x, List.count_range, ite_lt_eq_ind]
    · refine List.perm_iff_count.mpr (fun d => ?_)
      rw [h.dcnt d, List.count_range_1', ite_eq_ind]

end Gvozdjak
