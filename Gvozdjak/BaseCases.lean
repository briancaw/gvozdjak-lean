/-
The 39 base cases: admissible triples with `n ≤ 41` and `a < b` that are not produced
by one of the fifteen moves, each with an explicit graceful labeling checked by `decide`.
Generated from the appendix of the paper.
-/
import Gvozdjak.Statement

namespace Gvozdjak

theorem base_1_0_1 : IsGraceful 0 1 1 [0, 1] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_2_0_1 : IsGraceful 0 1 2 [0, 2, 1] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_2_1_2 : IsGraceful 1 2 2 [1, 0, 2] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_3_0_2 : IsGraceful 0 2 3 [0, 3, 1, 2] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_3_1_3 : IsGraceful 1 3 3 [1, 2, 0, 3] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_6_1_4 : IsGraceful 1 4 6 [1, 5, 0, 6, 3, 2, 4] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_6_2_3 : IsGraceful 2 3 6 [2, 6, 0, 5, 4, 1, 3] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_6_2_5 : IsGraceful 2 5 6 [2, 4, 3, 0, 6, 1, 5] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_6_3_4 : IsGraceful 3 4 6 [3, 6, 0, 5, 1, 2, 4] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_7_1_5 : IsGraceful 1 5 7 [1, 6, 0, 7, 3, 4, 2, 5] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_7_2_6 : IsGraceful 2 6 7 [2, 5, 3, 4, 0, 7, 1, 6] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_8_2_4 : IsGraceful 2 4 8 [2, 6, 1, 7, 0, 8, 5, 3, 4] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_8_4_6 : IsGraceful 4 6 8 [4, 7, 0, 8, 2, 3, 5, 1, 6] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_9_3_4 : IsGraceful 3 4 9 [3, 6, 5, 9, 0, 8, 1, 7, 2, 4] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_9_4_5 : IsGraceful 4 5 9 [4, 6, 3, 2, 7, 1, 8, 0, 9, 5] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_9_5_6 : IsGraceful 5 6 9 [5, 9, 0, 8, 1, 7, 2, 4, 3, 6] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_10_4_5 : IsGraceful 4 5 10 [4, 3, 6, 10, 0, 9, 1, 8, 2, 7, 5] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_13_4_9 : IsGraceful 4 9 13 [4, 8, 3, 10, 2, 11, 1, 12, 0, 13, 7, 5, 6, 9] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_13_5_6 : IsGraceful 5 6 13 [5, 9, 3, 10, 2, 11, 1, 12, 0, 13, 8, 7, 4, 6] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_13_5_8 : IsGraceful 5 8 13 [5, 6, 3, 10, 2, 11, 1, 12, 0, 13, 7, 9, 4, 8] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_14_4_5 : IsGraceful 4 5 14 [4, 9, 7, 6, 10, 3, 11, 2, 12, 1, 13, 0, 14, 8, 5] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_14_6_7 : IsGraceful 6 7 14 [6, 5, 8, 4, 10, 3, 11, 2, 12, 1, 13, 0, 14, 9, 7] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_14_7_8 : IsGraceful 7 8 14 [7, 5, 6, 9, 14, 0, 13, 1, 12, 2, 11, 3, 10, 4, 8] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_14_9_10 : IsGraceful 9 10 14 [9, 3, 11, 2, 12, 1, 13, 0, 14, 7, 4, 8, 6, 5, 10] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_15_6_10 : IsGraceful 6 10 15 [6, 7, 9, 15, 0, 14, 1, 13, 2, 12, 3, 11, 4, 8, 5, 10] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_16_6_10 : IsGraceful 6 10 16 [6, 11, 8, 7, 5, 9, 16, 0, 15, 1, 14, 2, 13, 3, 12, 4, 10] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_17_5_6 : IsGraceful 5 6 17 [5, 11, 8, 9, 7, 12, 4, 13, 3, 14, 2, 15, 1, 16, 0, 17, 10, 6] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_18_5_6 : IsGraceful 5 6 18 [5, 12, 9, 8, 10, 18, 0, 17, 1, 16, 2, 15, 3, 14, 4, 13, 7, 11, 6] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_18_5_8 : IsGraceful 5 8 18 [5, 13, 4, 14, 3, 15, 2, 16, 1, 17, 0, 18, 11, 7, 12, 6, 9, 10, 8] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_18_10_13 : IsGraceful 10 13 18 [10, 7, 8, 6, 11, 5, 12, 4, 14, 3, 15, 2, 16, 1, 17, 0, 18, 9, 13] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_21_6_7 : IsGraceful 6 7 21 [6, 14, 10, 11, 9, 12, 21, 0, 20, 1, 19, 2, 18, 3, 17, 4, 16, 5, 15, 8, 13, 7] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_21_9_10 : IsGraceful 9 10 21 [9, 8, 11, 13, 21, 0, 20, 1, 19, 2, 18, 3, 17, 4, 16, 5, 15, 6, 12, 7, 14, 10] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_21_11_12 : IsGraceful 11 12 21 [11, 7, 14, 9, 8, 10, 13, 21, 0, 20, 1, 19, 2, 18, 3, 17, 4, 16, 5, 15, 6, 12] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_22_7_8 : IsGraceful 7 8 22 [7, 14, 6, 16, 5, 17, 4, 18, 3, 19, 2, 20, 1, 21, 0, 22, 13, 11, 10, 15, 9, 12, 8] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_23_8_16 : IsGraceful 8 16 23 [8, 14, 7, 15, 6, 17, 5, 18, 4, 19, 3, 20, 2, 21, 1, 22, 0, 23, 13, 9, 12, 10, 11, 16] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_28_8_10 : IsGraceful 8 10 28 [8, 19, 9, 18, 14, 13, 15, 12, 20, 7, 21, 6, 22, 5, 23, 4, 24, 3, 25, 2, 26, 1, 27, 0, 28, 16, 11, 17, 10] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_30_9_10 : IsGraceful 9 10 30 [9, 20, 8, 22, 7, 23, 6, 24, 5, 25, 4, 26, 3, 27, 2, 28, 1, 29, 0, 30, 17, 13, 18, 12, 15, 16, 14, 21, 11, 19, 10] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_33_10_11 : IsGraceful 10 11 33 [10, 22, 9, 24, 8, 25, 7, 26, 6, 27, 5, 28, 4, 29, 3, 30, 2, 31, 1, 32, 0, 33, 19, 14, 20, 13, 17, 16, 18, 15, 23, 12, 21, 11] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

theorem base_41_12_27 : IsGraceful 12 27 41 [12, 28, 11, 30, 10, 31, 9, 32, 8, 33, 7, 34, 6, 35, 5, 36, 4, 37, 3, 38, 2, 39, 1, 40, 0, 41, 23, 16, 24, 15, 25, 19, 20, 22, 17, 21, 18, 29, 14, 26, 13, 27] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

end Gvozdjak
