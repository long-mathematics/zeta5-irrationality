import Zeta5.Certificate.InnerSum
import Zeta5.Certificate.WeightedAffineIntegral

/-! Appendix B.1: exact integration of the original inner limiting function.
The partition and all branch proofs are kernel checked. -/

namespace Zeta5.Certificate

open MeasureTheory Set

private theorem inner_piece_integrable (i : ℕ) (hi : i < 143) :
    IntervalIntegrable innerIntegrand volume (innerEndpoint i) (innerEndpoint (i + 1)) := by
  apply (weighted_affine_integrable (innerSlope i) (innerIntercept i)
    (innerEndpoint i) (innerEndpoint (i + 1))
    (innerEndpoint_pos i (by omega)) (innerEndpoint_increasing i hi).le).congr_uIoo
  rw [uIoo_of_le (innerEndpoint_increasing i hi).le]
  intro x hx
  simp only [innerIntegrand, inner_branches i hi x hx]

theorem inner_piece_integral (i : ℕ) (hi : i < 143) :
    (∫ x in innerEndpoint i..innerEndpoint (i + 1), innerIntegrand x) =
      innerSlope i * (1 / innerEndpoint i - 1 / innerEndpoint (i + 1)) +
        innerIntercept i / 2 * (1 / innerEndpoint i ^ 2 - 1 / innerEndpoint (i + 1) ^ 2) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le
    (g := fun x ↦ (innerIntercept i + innerSlope i * x) / x ^ 3)
    (innerEndpoint_increasing i hi).le
    (fun x hx ↦ by simp only [innerIntegrand, inner_branches i hi x hx])]
  exact weighted_affine_integral _ _ _ _ (innerEndpoint_pos i (by omega))
    (innerEndpoint_increasing i hi).le

/-- The source integral of `R(x) / x³` on `[3,20]`, obtained from all 143
branches of the actual `Gamma` integral and scalar term. -/
theorem inner_integral :
    (∫ x in (3 : ℝ)..20, innerIntegrand x) =
      322437603634266857629 / 7535670527041937280000 := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := innerIntegrand) (a := innerEndpoint) (n := 143) inner_piece_integrable
  change (∫ x in innerEndpoint 0..innerEndpoint 143, innerIntegrand x) = _
  rw [← hsum]
  trans ∑ i ∈ Finset.range 143,
    (innerSlope i * (1 / innerEndpoint i - 1 / innerEndpoint (i + 1)) +
      innerIntercept i / 2 * (1 / innerEndpoint i ^ 2 - 1 / innerEndpoint (i + 1) ^ 2))
  · apply Finset.sum_congr rfl
    intro i hi
    exact inner_piece_integral i (Finset.mem_range.mp hi)
  · exact inner_exact_sum

end Zeta5.Certificate
