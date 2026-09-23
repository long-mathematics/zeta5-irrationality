import Zeta5.Arithmetic.Normalization
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

namespace Zeta5

open Polynomial

theorem muX_natDegree_le (R : RationalDomain) : (muX R).natDegree ≤ 1 := by
  unfold muX
  apply natDegree_add_le_of_degree_le
  · simp
  · unfold Finsupp.sum
    apply natDegree_sum_le_of_forall_le
    intro j hj
    apply (natDegree_C_mul_le _ _).trans
    unfold poleMoment
    apply natDegree_add_le_of_degree_le
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · apply (natDegree_C_mul_le _ _).trans
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · exact natDegree_X_le
        · rw [natDegree_C]; decide
      · rw [natDegree_C]; decide
    · rw [natDegree_C]; decide

/-- The matrix is affine in precisely the source variable `X`. -/
theorem GK_affine (n : ℕ) :
    GK n = (X : ℚ[X]) • (GK n).map (fun P ↦ C (P.coeff 1)) +
      (GK n).map (fun P ↦ C (P.coeff 0)) := by
  funext i j
  change muX (entryDomain n (i.val + j.val)) =
    X * C ((muX (entryDomain n (i.val + j.val))).coeff 1) +
      C ((muX (entryDomain n (i.val + j.val))).coeff 0)
  rw [mul_comm X]
  exact eq_X_add_C_of_natDegree_le_one (muX_natDegree_le _)

/-- Upper degree bound; the exact leading coefficient remains a separate target. -/
theorem deltaK_natDegree_le (n : ℕ) : (deltaK n).natDegree ≤ h n := by
  unfold deltaK
  rw [GK_affine]
  simpa [Matrix.map_map, Function.comp_def] using
    natDegree_det_X_add_C_le ((GK n).map (fun P ↦ P.coeff 1))
      ((GK n).map (fun P ↦ P.coeff 0))

theorem FK_natDegree_le (n : ℕ) : (FK n).natDegree ≤ h n := by
  exact (natDegree_C_mul_le _ _).trans (deltaK_natDegree_le n)

theorem QKM_natDegree_le (n M : ℕ) : (QKM n M).natDegree ≤ h n := by
  exact (natDegree_C_mul_le _ _).trans (FK_natDegree_le n)

end Zeta5
