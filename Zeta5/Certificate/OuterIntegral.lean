import Zeta5.Certificate.Margins
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Appendix B.2: the source outer integrand, with the multiplicative
indicator implemented by the stated piecewise definition. -/

namespace Zeta5.Certificate

open MeasureTheory Set

noncomputable def outerR0 (y : ℝ) : ℝ :=
  if 1 / 3 < y ∧ y < 1 / 2 then
    8 - 9 * y - 8 * (3 / 40) - 5 * min (3 / 40) (1 - 2 * y) -
      5 * max 0 (1 + 3 / 40 - 3 * y)
  else if 1 / 2 < y ∧ y < 1 then
    7 * (1 - y) - 6 * min (3 / 40) (1 - y) -
      6 * max 0 (1 + 3 / 40 - 2 * y) + max 0 (1 + 4 * (3 / 40) - 2 * y)
  else 0

noncomputable def outerCorrection (y : ℝ) : ℝ :=
  if 1 / 3 < y ∧ y < 1 / 2 then
    max 0 (1 + 4 * (3 / 40) - 3 * y - max 0 (1 + 3 / 40 - 3 * y))
  else 0

noncomputable def outerIntegrand (y : ℝ) : ℝ :=
  outerR0 y - outerCorrection y - 2 * (37 / 40) * (⌊1 / y⌋ : ℤ) +
    ∑ j ∈ Finset.range 5, max 0 (2 * (37 / 40) - ((j : ℝ) + 1) * y)

private theorem floor_recip (y : ℝ) (k : ℤ) (hy : 0 < y)
    (hlo : (k : ℝ) * y ≤ 1) (hhi : 1 < ((k : ℝ) + 1) * y) :
    ⌊1 / y⌋ = k := by
  apply Int.floor_eq_iff.mpr
  exact ⟨(le_div_iff₀ hy).mpr hlo, (div_lt_iff₀ hy).mpr hhi⟩

theorem outer_branch_0 (y : ℝ) (hl : (1/3 : ℝ) < y) (hr : y < (43/120 : ℝ)) :
    outerIntegrand y = (279/40 : ℝ) + (-9 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (2 : ℤ) := floor_recip y 2 (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  have ha : 1 / 3 < y ∧ y < 1 / 2 := ⟨by linarith, by linarith⟩
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_left ha]
  norm_num [Finset.sum_range_succ]
  simp only [min_def, max_def]
  repeat' (split <;> try linarith)

theorem outer_branch_1 (y : ℝ) (hl : (43/120 : ℝ) < y) (hr : y < (37/100 : ℝ)) :
    outerIntegrand y = (451/40 : ℝ) + (-21 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (2 : ℤ) := floor_recip y 2 (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  have ha : 1 / 3 < y ∧ y < 1 / 2 := ⟨by linarith, by linarith⟩
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_left ha]
  norm_num [Finset.sum_range_succ]
  simp only [min_def, max_def]
  repeat' (split <;> try linarith)

theorem outer_branch_2 (y : ℝ) (hl : (37/100 : ℝ) < y) (hr : y < (13/30 : ℝ)) :
    outerIntegrand y = (377/40 : ℝ) + (-16 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (2 : ℤ) := floor_recip y 2 (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  have ha : 1 / 3 < y ∧ y < 1 / 2 := ⟨by linarith, by linarith⟩
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_left ha]
  norm_num [Finset.sum_range_succ]
  simp only [min_def, max_def]
  repeat' (split <;> try linarith)

theorem outer_branch_3 (y : ℝ) (hl : (13/30 : ℝ) < y) (hr : y < (37/80 : ℝ)) :
    outerIntegrand y = (429/40 : ℝ) + (-19 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (2 : ℤ) := floor_recip y 2 (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  have ha : 1 / 3 < y ∧ y < 1 / 2 := ⟨by linarith, by linarith⟩
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_left ha]
  norm_num [Finset.sum_range_succ]
  simp only [min_def, max_def]
  repeat' (split <;> try linarith)

theorem outer_branch_4 (y : ℝ) (hl : (37/80 : ℝ) < y) (hr : y < (1/2 : ℝ)) :
    outerIntegrand y = (17/4 : ℝ) + (-5 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (2 : ℤ) := floor_recip y 2 (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  have ha : 1 / 3 < y ∧ y < 1 / 2 := ⟨by linarith, by linarith⟩
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_left ha]
  norm_num [Finset.sum_range_succ]
  simp only [min_def, max_def]
  repeat' (split <;> try linarith)

theorem outer_branch_5 (y : ℝ) (hl : (1/2 : ℝ) < y) (hr : y < (43/80 : ℝ)) :
    outerIntegrand y = (51/10 : ℝ) + (-3 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (1 : ℤ) := floor_recip y 1 (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  have ha : ¬ (1 / 3 < y ∧ y < 1 / 2) := by rintro ⟨_, h⟩; linarith
  have hb : 1 / 2 < y ∧ y < 1 := ⟨by linarith, by linarith⟩
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_right ha, ite_eq_left hb]
  norm_num [Finset.sum_range_succ]
  simp only [min_def, max_def]
  repeat' (split <;> try linarith)

theorem outer_branch_6 (y : ℝ) (hl : (43/80 : ℝ) < y) (hr : y < (37/60 : ℝ)) :
    outerIntegrand y = (231/20 : ℝ) + (-15 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (1 : ℤ) := floor_recip y 1 (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  have ha : ¬ (1 / 3 < y ∧ y < 1 / 2) := by rintro ⟨_, h⟩; linarith
  have hb : 1 / 2 < y ∧ y < 1 := ⟨by linarith, by linarith⟩
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_right ha, ite_eq_left hb]
  norm_num [Finset.sum_range_succ]
  simp only [min_def, max_def]
  repeat' (split <;> try linarith)

theorem outer_branch_7 (y : ℝ) (hl : (37/60 : ℝ) < y) (hr : y < (13/20 : ℝ)) :
    outerIntegrand y = (97/10 : ℝ) + (-12 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (1 : ℤ) := floor_recip y 1 (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  have ha : ¬ (1 / 3 < y ∧ y < 1 / 2) := by rintro ⟨_, h⟩; linarith
  have hb : 1 / 2 < y ∧ y < 1 := ⟨by linarith, by linarith⟩
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_right ha, ite_eq_left hb]
  norm_num [Finset.sum_range_succ]
  simp only [min_def, max_def]
  repeat' (split <;> try linarith)

theorem outer_branch_8 (y : ℝ) (hl : (13/20 : ℝ) < y) (hr : y < (37/40 : ℝ)) :
    outerIntegrand y = (42/5 : ℝ) + (-10 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (1 : ℤ) := floor_recip y 1 (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  have ha : ¬ (1 / 3 < y ∧ y < 1 / 2) := by rintro ⟨_, h⟩; linarith
  have hb : 1 / 2 < y ∧ y < 1 := ⟨by linarith, by linarith⟩
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_right ha, ite_eq_left hb]
  norm_num [Finset.sum_range_succ]
  simp only [min_def, max_def]
  repeat' (split <;> try linarith)

theorem outer_branch_9 (y : ℝ) (hl : (37/40 : ℝ) < y) (hr : y < (1 : ℝ)) :
    outerIntegrand y = (1 : ℝ) + (-2 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (1 : ℤ) := floor_recip y 1 (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  have ha : ¬ (1 / 3 < y ∧ y < 1 / 2) := by rintro ⟨_, h⟩; linarith
  have hb : 1 / 2 < y ∧ y < 1 := ⟨by linarith, by linarith⟩
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_right ha, ite_eq_left hb]
  norm_num [Finset.sum_range_succ]
  simp only [min_def, max_def]
  repeat' (split <;> try linarith)

theorem outer_branch_10 (y : ℝ) (hl : (1 : ℝ) < y) (hr : y < (37/20 : ℝ)) :
    outerIntegrand y = (37/20 : ℝ) + (-1 : ℝ) * y := by
  have hf : ⌊1 / y⌋ = (0 : ℤ) := floor_recip y 0 (by linarith) (by norm_num) (by norm_num; linarith)
  have ha : ¬ (1 / 3 < y ∧ y < 1 / 2) := by rintro ⟨_, h⟩; linarith
  have hb : ¬ (1 / 2 < y ∧ y < 1) := by rintro ⟨_, h⟩; linarith
  simp only [outerIntegrand, hf, outerR0, outerCorrection, ite_eq_right ha, ite_eq_right hb]
  norm_num [Finset.sum_range_succ]
  simp only [max_def]
  repeat' (split <;> try linarith)

/-- Ordered source partition, with a harmless default outside `0..11`. -/
noncomputable def outerEndpoint : ℕ → ℝ
  | 0 => 1/3
  | 1 => 43/120
  | 2 => 37/100
  | 3 => 13/30
  | 4 => 37/80
  | 5 => 1/2
  | 6 => 43/80
  | 7 => 37/60
  | 8 => 13/20
  | 9 => 37/40
  | 10 => 1
  | 11 => 37 / 20
  | _ => 0

noncomputable def outerIntercept : ℕ → ℝ
  | 0 => 279/40
  | 1 => 451/40
  | 2 => 377/40
  | 3 => 429/40
  | 4 => 17/4
  | 5 => 51/10
  | 6 => 231/20
  | 7 => 97/10
  | 8 => 42/5
  | 9 => 1
  | 10 => 37/20
  | _ => 0

noncomputable def outerSlope : ℕ → ℝ
  | 0 => -9
  | 1 => -21
  | 2 => -16
  | 3 => -19
  | 4 => -5
  | 5 => -3
  | 6 => -15
  | 7 => -12
  | 8 => -10
  | 9 => -2
  | 10 => -1
  | _ => 0

private theorem outerEndpoint_increasing (i : ℕ) (hi : i < 11) :
    outerEndpoint i < outerEndpoint (i + 1) := by
  interval_cases i <;> norm_num [outerEndpoint]

theorem outer_branches (i : ℕ) (hi : i < 11) (y : ℝ)
    (hy : y ∈ Ioo (outerEndpoint i) (outerEndpoint (i + 1))) :
    outerIntegrand y = outerIntercept i + outerSlope i * y := by
  interval_cases i <;> simp only [outerEndpoint, outerIntercept, outerSlope] at *
  · exact outer_branch_0 y hy.1 hy.2
  · exact outer_branch_1 y hy.1 hy.2
  · exact outer_branch_2 y hy.1 hy.2
  · exact outer_branch_3 y hy.1 hy.2
  · exact outer_branch_4 y hy.1 hy.2
  · exact outer_branch_5 y hy.1 hy.2
  · exact outer_branch_6 y hy.1 hy.2
  · exact outer_branch_7 y hy.1 hy.2
  · exact outer_branch_8 y hy.1 hy.2
  · exact outer_branch_9 y hy.1 hy.2
  · exact outer_branch_10 y hy.1 hy.2

private theorem outer_piece_integrable (i : ℕ) (hi : i < 11) :
    IntervalIntegrable outerIntegrand volume (outerEndpoint i) (outerEndpoint (i + 1)) := by
  have hc : Continuous (fun y : ℝ ↦ outerIntercept i + outerSlope i * y) := by fun_prop
  apply (hc.intervalIntegrable _ _).congr_uIoo
  rw [uIoo_of_le (outerEndpoint_increasing i hi).le]
  intro y hy
  exact (outer_branches i hi y hy).symm

private theorem integral_affine (a b c d : ℝ) :
    (∫ y in a..b, c + d * y) = c * (b - a) + d * (b ^ 2 - a ^ 2) / 2 := by
  rw [intervalIntegral.integral_add
    (show IntervalIntegrable (fun _ : ℝ ↦ c) volume a b from continuous_const.intervalIntegrable a b)
    (show IntervalIntegrable (fun y : ℝ ↦ d * y) volume a b from
      (continuous_const.mul continuous_id).intervalIntegrable a b)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id]
  simp only [smul_eq_mul]
  ring

theorem outer_piece_integral (i : ℕ) (hi : i < 11) :
    (∫ y in outerEndpoint i..outerEndpoint (i + 1), outerIntegrand y) =
      outerIntercept i * (outerEndpoint (i + 1) - outerEndpoint i) +
        outerSlope i * (outerEndpoint (i + 1) ^ 2 - outerEndpoint i ^ 2) / 2 := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (outerEndpoint_increasing i hi).le
    (fun y hy ↦ outer_branches i hi y hy)]
  exact integral_affine _ _ _ _

/-- Exact integral of the original outer expression over the entire source range,
including `(1, 2λ)`. Branch values at the finite endpoints are discarded only
using null-singleton interval-integral congruence. -/
theorem outer_integral :
    (∫ y in (1 / 3 : ℝ)..(37 / 20 : ℝ), outerIntegrand y) = 127751 / 96000 := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := outerIntegrand) (a := outerEndpoint) (n := 11) outer_piece_integrable
  change (∫ y in outerEndpoint 0..outerEndpoint 11, outerIntegrand y) = _
  rw [← hsum]
  trans ∑ i ∈ Finset.range 11,
    (outerIntercept i * (outerEndpoint (i + 1) - outerEndpoint i) +
      outerSlope i * (outerEndpoint (i + 1) ^ 2 - outerEndpoint i ^ 2) / 2)
  · apply Finset.sum_congr rfl
    intro i hi
    exact outer_piece_integral i (Finset.mem_range.mp hi)
  · norm_num [Finset.sum_range_succ, outerEndpoint, outerIntercept, outerSlope]

end Zeta5.Certificate
