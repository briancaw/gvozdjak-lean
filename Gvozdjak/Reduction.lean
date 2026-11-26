/-
The reduction theorem: every admissible triple with `n ≥ 42` and `a < b` reduces, by one of the
fifteen moves, to a smaller admissible triple.  The eight residue classes are proved in the
generated files `Reduction00` … `Reduction31`.
-/
import Gvozdjak.Reduction00
import Gvozdjak.Reduction01
import Gvozdjak.Reduction10
import Gvozdjak.Reduction11
import Gvozdjak.Reduction20
import Gvozdjak.Reduction21
import Gvozdjak.Reduction30
import Gvozdjak.Reduction31

namespace Gvozdjak

theorem reduction (n a b : Nat) (h42 : 42 ≤ n) (hab : a < b) (hadm : AdmL a b n) : Red n a b := by
  have hpar : ((n % 4 = 0 ∨ n % 4 = 3) ∧ (a + b) % 2 = 0) ∨
      ((n % 4 = 1 ∨ n % 4 = 2) ∧ (a + b) % 2 = 1) := by
    unfold AdmL at hadm; omega
  obtain h | h | h | h : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  · obtain g | g : a % 2 = 0 ∨ a % 2 = 1 := by omega
    · exact cover00 n a b (n / 4) (a / 2) (b / 2) (by omega) (by omega) (by omega) h42 hab hadm
    · exact cover01 n a b (n / 4) (a / 2) (b / 2) (by omega) (by omega) (by omega) h42 hab hadm
  · obtain g | g : a % 2 = 0 ∨ a % 2 = 1 := by omega
    · exact cover10 n a b (n / 4) (a / 2) (b / 2) (by omega) (by omega) (by omega) h42 hab hadm
    · exact cover11 n a b (n / 4) (a / 2) (b / 2) (by omega) (by omega) (by omega) h42 hab hadm
  · obtain g | g : a % 2 = 0 ∨ a % 2 = 1 := by omega
    · exact cover20 n a b (n / 4) (a / 2) (b / 2) (by omega) (by omega) (by omega) h42 hab hadm
    · exact cover21 n a b (n / 4) (a / 2) (b / 2) (by omega) (by omega) (by omega) h42 hab hadm
  · obtain g | g : a % 2 = 0 ∨ a % 2 = 1 := by omega
    · exact cover30 n a b (n / 4) (a / 2) (b / 2) (by omega) (by omega) (by omega) h42 hab hadm
    · exact cover31 n a b (n / 4) (a / 2) (b / 2) (by omega) (by omega) (by omega) h42 hab hadm

end Gvozdjak
