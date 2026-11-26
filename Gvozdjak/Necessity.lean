/-
Necessity: a graceful labeling of the path with `n ≥ 1` edges from `a` to `b` forces (C1)–(C3).

(C1) is a parity count.  For (C2) and (C3), fix a "centre" `c` and give label `v` the weight
`|2v - c|`.  Every edge `{x, y}` satisfies `2|x - y| ≤ |2x - c| + |2y - c|`; summing over the
path, in which the two end labels are used once and all others twice, bounds
`|2a - c| + |2b - c|` by `2·Σ_v |2v - c| - n(n+1)`.  The three centres `n`, `n + 1`, `n - 1`
give (C2) and the two halves of (C3).
-/
import Gvozdjak.Basic

namespace Gvozdjak

theorem perm_sum {l₁ l₂ : List Nat} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.sum_cons, ih]
  | swap x y l => simp only [List.sum_cons]; omega
  | trans _ _ ih1 ih2 => omega

/-- `2·(s + (s+1) + … + (s+k-1)) + k = k(2s + k)`. -/
theorem two_sum_range' : ∀ k s : Nat, 2 * (List.range' s k).sum + k = k * (2 * s + k)
  | 0, s => by simp
  | k + 1, s => by
      have ih := two_sum_range' k (s + 1)
      rw [List.range'_succ, List.sum_cons]
      have e1 : (k + 1) * (2 * s + (k + 1)) = k * (2 * s) + k * k + k + 2 * s + k + 1 := by
        simp only [Nat.add_mul, Nat.mul_add]; omega
      have e2 : k * (2 * (s + 1) + k) = k * (2 * s) + k * 2 + k * k := by
        simp only [Nat.mul_add]
      omega

theorem two_sum_range'_one (n : Nat) : 2 * (List.range' 1 n).sum = n * (n + 1) := by
  have h := two_sum_range' n 1
  have e : n * (2 * 1 + n) = n * (n + 1) + n := by
    simp only [Nat.mul_add]; omega
  omega

/-- Parity: the two ends and the sum of the differences have even total. -/
theorem parity_ends : ∀ (p : List Nat) (u v : Nat), p.head? = some u → p.getLast? = some v →
    (u + v + (diffs p).sum) % 2 = 0
  | [], _, _, h, _ => by simp at h
  | [x], u, v, h1, h2 => by
      have e1 : x = u := by simpa using h1
      have e2 : x = v := by simpa using h2
      subst e1; subst e2
      simp only [diffs_singleton, List.sum_nil]
      omega
  | x :: y :: t, u, v, h1, h2 => by
      have e1 : x = u := by simpa using h1
      subst e1
      have h2' : (y :: t).getLast? = some v := by
        rw [List.getLast?_cons_cons] at h2; exact h2
      have ih := parity_ends (y :: t) y v rfl h2'
      simp only [diffs_cons_cons, List.sum_cons, adiff]
      omega

/-- The weighted edge count. -/
theorem weighted (c : Nat) : ∀ (p : List Nat) (u v : Nat), p.head? = some u → p.getLast? = some v →
    2 * (diffs p).sum + adiff (2 * u) c + adiff (2 * v) c ≤
      2 * (p.map (fun w => adiff (2 * w) c)).sum
  | [], _, _, h, _ => by simp at h
  | [x], u, v, h1, h2 => by
      have e1 : x = u := by simpa using h1
      have e2 : x = v := by simpa using h2
      subst e1; subst e2
      simp only [diffs_singleton, List.sum_nil, List.map_cons, List.map_nil, List.sum_cons]
      omega
  | x :: y :: t, u, v, h1, h2 => by
      have e1 : x = u := by simpa using h1
      subst e1
      have h2' : (y :: t).getLast? = some v := by
        rw [List.getLast?_cons_cons] at h2; exact h2
      have ih := weighted c (y :: t) y v rfl h2'
      simp only [diffs_cons_cons, List.sum_cons, List.map_cons] at ih ⊢
      simp only [adiff] at ih ⊢
      omega

/-- `Σ_{v=0}^{n} |2v - c|`. -/
def wsum (n c : Nat) : Nat := ((List.range (n + 1)).map (fun w => adiff (2 * w) c)).sum

theorem wsum_step (n c : Nat) :
    wsum (n + 2) (c + 2) = wsum n c + (c + 2) + adiff (2 * (n + 2)) (c + 2) := by
  unfold wsum
  have e : List.range (n + 2 + 1) = 0 :: ((List.range (n + 1)).map Nat.succ ++ [n + 2]) := by
    rw [List.range_succ_eq_map, List.range_succ, List.map_append]
    rfl
  have hf : ((fun w => adiff (2 * w) (c + 2)) ∘ Nat.succ) = fun w => adiff (2 * w) c := by
    funext w
    simp only [Function.comp, adiff]
    omega
  rw [e, List.map_cons, List.sum_cons, List.map_append, List.sum_append_nat, List.map_map, hf,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [adiff]
  omega

theorem wsum_succ : ∀ n : Nat, 2 * wsum n (n + 1) ≤ n * (n + 1) + n + 2
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      have ih := wsum_succ n
      have st : wsum (n + 2) (n + 2 + 1) =
          wsum n (n + 1) + (n + 1 + 2) + adiff (2 * (n + 2)) (n + 1 + 2) := wsum_step n (n + 1)
      have e : (n + 2) * (n + 2 + 1) = n * (n + 1) + 4 * n + 6 := by
        simp only [Nat.add_mul, Nat.mul_add]; omega
      rw [st, e]
      simp only [adiff]
      omega

theorem wsum_self : ∀ n : Nat, 2 * wsum n n ≤ n * (n + 1) + n + 1
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      have ih := wsum_self n
      have st := wsum_step n n
      have e : (n + 2) * (n + 2 + 1) = n * (n + 1) + 4 * n + 6 := by
        simp only [Nat.add_mul, Nat.mul_add]; omega
      rw [st, e]
      simp only [adiff]
      omega

theorem wsum_pred_aux : ∀ m : Nat, 2 * wsum (m + 1) m ≤ (m + 1) * (m + 1 + 1) + (m + 1) + 2
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
      have ih := wsum_pred_aux m
      have st : wsum (m + 2 + 1) (m + 2) =
          wsum (m + 1) m + (m + 2) + adiff (2 * (m + 1 + 2)) (m + 2) := wsum_step (m + 1) m
      have e : (m + 2 + 1) * (m + 2 + 1 + 1) = (m + 1) * (m + 1 + 1) + 4 * m + 10 := by
        simp only [Nat.add_mul, Nat.mul_add]; omega
      rw [st, e]
      simp only [adiff]
      omega

theorem wsum_pred (n : Nat) (hn : 1 ≤ n) : 2 * wsum n (n - 1) ≤ n * (n + 1) + n + 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact wsum_pred_aux m

/-- The two end labels of a path on at least two distinct-count vertices differ. -/
theorem ends_ne {a b n : Nat} {p : List Nat} (hn : 1 ≤ n)
    (hs : Spec a b (ind 0 (n + 1)) (ind 1 n) p) (hl : p.length = n + 1) : a ≠ b := by
  intro hab
  subst hab
  have hc := hs.cnt a
  have hle : ind 0 (n + 1) a ≤ 1 := by unfold ind; omega
  match p, hs.hd, hs.lt, hl, hc with
  | [], h, _, _, _ => simp at h
  | [x], _, _, hl, _ => simp at hl; omega
  | x :: y :: t, h1, h2, _, hc =>
      have e1 : x = a := by simpa using h1
      subst e1
      have h2' : (y :: t).getLast? = some x := by
        rw [List.getLast?_cons_cons] at h2; exact h2
      have hm : x ∈ y :: t := List.mem_of_getLast? h2'
      have hp : 0 < (y :: t).count x := List.count_pos_iff.mpr hm
      rw [List.count_cons_self] at hc
      omega

theorem necessity {a b n : Nat} {p : List Nat} (hn : 1 ≤ n) (h : IsGraceful a b n p) :
    Admissible a b n := by
  have hs := isGraceful_iff_spec.mp h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hl : p.length = n + 1 := by rw [h3.length_eq, List.length_range]
  have hne : a ≠ b := ends_ne hn hs hl
  -- the end labels lie in `0..n`
  have ha : a ≤ n := by
    obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp h1
    have hc := hs.cnt a
    rw [List.count_cons_self] at hc
    unfold ind at hc
    omega
  have hb : b ≤ n := by
    obtain ⟨t, rfl⟩ := List.getLast?_eq_some_iff.mp h2
    have hc := hs.cnt b
    rw [List.count_append, List.count_singleton_self] at hc
    unfold ind at hc
    omega
  -- the differences sum to `n(n+1)/2`
  have hT : 2 * (diffs p).sum = n * (n + 1) := by
    rw [perm_sum h4]; exact two_sum_range'_one n
  have hpar := parity_ends p a b h1 h2
  -- the three weighted counts
  have hw : ∀ c, 2 * (diffs p).sum + adiff (2 * a) c + adiff (2 * b) c ≤ 2 * wsum n c := by
    intro c
    have := weighted c p a b h1 h2
    have e : (p.map (fun w => adiff (2 * w) c)).sum = wsum n c := perm_sum (h3.map _)
    omega
  have i1 := hw (n + 1)
  have i2 := hw (n - 1)
  have i3 := hw n
  have b1 := wsum_succ n
  have b2 := wsum_pred n hn
  have b3 := wsum_self n
  simp only [adiff] at i1 i2 i3
  have hdiv : n * (n + 1) / 2 = (diffs p).sum := by omega
  unfold Admissible adiff
  rw [hdiv]
  refine ⟨ha, hb, ?_, hne, ?_, ?_, ?_⟩ <;> omega

end Gvozdjak
