/-
The theorem in textbook form.

`Statement.lean` phrases the conjecture with lists and natural-number arithmetic.  This file
restates it the way a combinatorialist would write it and derives that form from
`Gvozdjak.gvozdjak`:

* a labeling is a function `f : Fin (n + 1) → ℕ` with values in `0..n`, injective, with
  `f 0 = a`, `f n = b`, and injective edge differences `|f (i+1) - f i|` lying in `1..n`;
* the three conditions are written over the integers, with signed subtraction and without the
  redundant bounds `a ≤ n`, `b ≤ n` (`admissibleInt_bounds` shows they follow).

This file was written during an independent audit of the repository and is not used by the
main proof.
-/
import Gvozdjak.Main

def AdmissibleInt (a b n : Int) : Prop :=
  ((b - a) - ((n * (n + 1)) / 2)) % 2 = 0 ∧
  0 < (b - a).natAbs ∧
  2 * (b - a).natAbs ≤ n + 1 ∧
  n ≤ 2 * (a + b) ∧
  2 * (a + b) ≤ 3 * n

def IsGracefulFin (a b n : Nat) (f : Fin (n + 1) → Nat) : Prop :=
  f ⟨0, by omega⟩ = a ∧
  f ⟨n, by omega⟩ = b ∧
  (∀ i, f i ≤ n) ∧
  (∀ i j, f i = f j → i = j) ∧
  (∀ i : Fin n,
    1 ≤ Int.natAbs ((f ⟨i.val + 1, by omega⟩ : Int) - (f ⟨i.val, by omega⟩ : Int)) ∧
    Int.natAbs ((f ⟨i.val + 1, by omega⟩ : Int) - (f ⟨i.val, by omega⟩ : Int)) ≤ n) ∧
  (∀ i j : Fin n,
    Int.natAbs ((f ⟨i.val + 1, by omega⟩ : Int) - (f ⟨i.val, by omega⟩ : Int)) =
    Int.natAbs ((f ⟨j.val + 1, by omega⟩ : Int) - (f ⟨j.val, by omega⟩ : Int)) → i = j)

theorem admissible_iff_int (a b n : Nat) (hn : 1 ≤ n) :
    Gvozdjak.Admissible a b n ↔ AdmissibleInt (a : Int) (b : Int) (n : Int) := by
  unfold Gvozdjak.Admissible Gvozdjak.adiff AdmissibleInt
  have hmul : ((n * (n + 1) : Nat) : Int) = (n : Int) * ((n : Int) + 1) := by
    simp [Int.natCast_mul, Int.natCast_add]
  have hcast : ((n * (n + 1) / 2 : Nat) : Int) = ((n : Int) * ((n : Int) + 1)) / 2 := by
    rw [← hmul]; exact Int.natCast_ediv (n * (n + 1)) 2
  omega

theorem diffs_length (p : List Nat) (h : 1 ≤ p.length) : (Gvozdjak.diffs p).length = p.length - 1 := by
  match p with
  | [] => simp at h
  | [_] => simp [Gvozdjak.diffs]
  | x :: y :: t =>
    simp only [Gvozdjak.diffs, List.length_cons]
    have ih := diffs_length (y :: t) (by simp)
    simp only [List.length_cons] at ih; omega

theorem diffs_getElem (p : List Nat) (i : Nat) (hi : i + 1 < p.length) :
    (Gvozdjak.diffs p)[i]'(by rw [diffs_length p (by omega)]; omega) =
    Int.natAbs ((p[i + 1]'hi : Int) - (p[i]'(by omega) : Int)) := by
  match p, i with
  | [], _ => simp at hi
  | [_], _ => simp at hi
  | x :: y :: t, 0 =>
    simp only [Gvozdjak.diffs, List.getElem_cons_zero, List.getElem_cons_succ, Gvozdjak.adiff]; omega
  | x :: y :: t, i + 1 =>
    simp only [Gvozdjak.diffs, List.getElem_cons_succ]
    exact diffs_getElem (y :: t) i (by simpa using hi)

theorem nodup_subset_length_le : ∀ {l₁ l₂ : List Nat}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l₂ := hsub a (by simp)
    have hsub' : ∀ x ∈ t, x ∈ l₂.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun h => hnd.1 (by subst h; exact hx))).mpr (hsub x (by simp [hx]))
    have ih := nodup_subset_length_le hnd.2 hsub'
    have her : (l₂.erase a).length = l₂.length - 1 := List.length_erase_of_mem ha
    have hpos : 0 < l₂.length := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

theorem perm_of_nodup_subset_length {l₁ l₂ : List Nat}
    (hnd1 : l₁.Nodup) (hnd2 : l₂.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂) (hlen : l₁.length = l₂.length) :
    l₁.Perm l₂ := by
  refine (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr fun x => ⟨hsub x, fun hx2 => ?_⟩
  exact Classical.byContradiction fun hnot => by
    have hsub' : ∀ y ∈ l₁, y ∈ l₂.erase x := fun y hy =>
      (List.mem_erase_of_ne (fun heq => hnot (by subst heq; exact hy))).mpr (hsub y hy)
    have hle := nodup_subset_length_le hnd1 hsub'
    have her := List.length_erase_of_mem hx2
    have hpos := List.length_pos_of_mem hx2
    omega

theorem nodup_iff_inj_getElem (l : List Nat) :
    l.Nodup ↔ ∀ i j (hi : i < l.length) (hj : j < l.length), l[i]'hi = l[j]'hj → i = j := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.nodup_cons, ih]
    constructor
    · rintro ⟨hx, ht⟩ i j hi hj heq
      cases i <;> cases j
      · rfl
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact False.elim (hx (heq ▸ List.getElem_mem _))
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact False.elim (hx (heq.symm ▸ List.getElem_mem _))
      · simp only [List.getElem_cons_succ] at heq
        exact congrArg Nat.succ (ht _ _ (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)
    · intro h
      refine ⟨?_, ?_⟩
      · intro hx
        rw [List.mem_iff_getElem] at hx
        rcases hx with ⟨j, hj, heq⟩
        have := h 0 (j + 1) (by simp) (by simpa using Nat.succ_lt_succ hj) (by simpa using heq.symm)
        omega
      · intro i j hi hj heq
        have := h (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj) (by simpa using heq)
        omega

theorem isGraceful_iff_fin (a b n : Nat) :
    (∃ p, Gvozdjak.IsGraceful a b n p) ↔ (∃ f : Fin (n + 1) → Nat, IsGracefulFin a b n f) := by
  constructor
  · rintro ⟨p, hhd, hlt, hperm, hdperm⟩
    have hlen : p.length = n + 1 := by rw [hperm.length_eq, List.length_range]
    have hdlen : (Gvozdjak.diffs p).length = n := by rw [hdperm.length_eq, List.length_range']
    let f : Fin (n + 1) → Nat := fun i => p[i.val]'(by omega)
    refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [f]
      have h0 : p.head? = some (p[0]'(by omega)) := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      rw [h0] at hhd; exact Option.some.inj hhd
    · simp only [f]
      have hl : p.getLast? = some (p[n]'(by omega)) := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
        congr 1; congr 1; omega
      rw [hl] at hlt; exact Option.some.inj hlt
    · intro i
      have hmem : f i ∈ List.range (n + 1) := hperm.subset (List.getElem_mem _)
      have := List.mem_range.mp hmem; omega
    · intro i j hij
      have hnd : p.Nodup := hperm.nodup_iff.mpr List.nodup_range
      exact Fin.ext ((nodup_iff_inj_getElem p).mp hnd i.val j.val (by omega) (by omega) hij)
    · intro i
      have hmem : (Gvozdjak.diffs p)[i.val]'(by omega) ∈ List.range' 1 n := hdperm.subset (List.getElem_mem _)
      rw [diffs_getElem p i.val (by omega)] at hmem
      rcases List.mem_range'.mp hmem with ⟨k, hk, heq⟩
      simp only [f]; omega
    · intro i j hij
      have hnd : (Gvozdjak.diffs p).Nodup := hdperm.nodup_iff.mpr (List.nodup_range' (h := by omega))
      have heq : (Gvozdjak.diffs p)[i.val]'(by omega) = (Gvozdjak.diffs p)[j.val]'(by omega) := by
        rw [diffs_getElem p i.val (by omega), diffs_getElem p j.val (by omega)]; exact hij
      exact Fin.ext ((nodup_iff_inj_getElem _).mp hnd i.val j.val (by omega) (by omega) heq)
  · rintro ⟨f, hf0, hfn, hfb, hfinj, hdb, hdinj⟩
    let p : List Nat := List.ofFn f
    have hlen : p.length = n + 1 := List.length_ofFn
    refine ⟨p, ?_, ?_, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      simp only [p, List.getElem_ofFn]; exact congrArg some hf0
    · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      have hidx : p.length - 1 = n := by omega
      simp only [p, List.getElem_ofFn]; congr 1
      have : (⟨p.length - 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext hidx
      rw [this]; exact hfn
    · apply perm_of_nodup_subset_length
      · rw [nodup_iff_inj_getElem]
        intro i j hi hj heq; simp only [p, List.getElem_ofFn] at heq
        exact congrArg Fin.val (hfinj ⟨i, by omega⟩ ⟨j, by omega⟩ heq)
      · exact List.nodup_range
      · intro x hx; rw [List.mem_iff_getElem] at hx; rcases hx with ⟨i, hi, rfl⟩
        simp only [p, List.getElem_ofFn]
        exact List.mem_range.mpr (Nat.lt_succ_of_le (hfb ⟨i, by omega⟩))
      · rw [hlen, List.length_range]
    · apply perm_of_nodup_subset_length
      · rw [nodup_iff_inj_getElem]
        intro i j hi hj heq
        have hdl : (Gvozdjak.diffs p).length = n := by rw [diffs_length p (by omega)]; omega
        rw [diffs_getElem p i (by omega), diffs_getElem p j (by omega)] at heq
        simp only [p, List.getElem_ofFn] at heq
        exact congrArg Fin.val (hdinj ⟨i, by omega⟩ ⟨j, by omega⟩ heq)
      · exact List.nodup_range' (h := by omega)
      · intro d hd; rw [List.mem_iff_getElem] at hd; rcases hd with ⟨i, hi, rfl⟩
        have hdl : (Gvozdjak.diffs p).length = n := by rw [diffs_length p (by omega)]; omega
        rw [diffs_getElem p i (by omega)]; simp only [p, List.getElem_ofFn]
        have hb := hdb ⟨i, by omega⟩; dsimp only at hb
        rw [List.mem_range']
        exact ⟨Int.natAbs ((f ⟨i + 1, by omega⟩ : Int) - (f ⟨i, by omega⟩ : Int)) - 1, by omega, by omega⟩
      · rw [diffs_length p (by omega), hlen, List.length_range']; omega

theorem gvozdjak_textbook (a b n : Nat) (hn : 1 ≤ n) :
    (∃ f : Fin (n + 1) → Nat, IsGracefulFin a b n f) ↔ AdmissibleInt (a : Int) (b : Int) (n : Int) := by
  rw [← isGraceful_iff_fin, ← admissible_iff_int a b n hn]
  exact Gvozdjak.gvozdjak a b n hn

theorem admissibleInt_bounds (a b n : Int) (hn : 1 ≤ n) (h : AdmissibleInt a b n) :
    0 ≤ a ∧ a ≤ n ∧ 0 ≤ b ∧ b ≤ n := by
  unfold AdmissibleInt at h
  omega

/-- info: 'gvozdjak_textbook' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gvozdjak_textbook
