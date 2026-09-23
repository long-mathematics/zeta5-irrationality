import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace Zeta5.Certificate

open MeasureTheory Set
open scoped Interval

private theorem weighted_affine_eq (x a b : ℝ) (hx : x ≠ 0) :
    (b + a * x) / x ^ 3 = a * x ^ (-2 : ℤ) + b * x ^ (-3 : ℤ) := by
  norm_num [zpow_neg]
  field_simp
  ring

private theorem zero_not_uIcc {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    (0 : ℝ) ∉ [[l, r]] := by
  rw [uIcc_of_le hlr]
  intro hz
  exact (not_le_of_gt hl) hz.1

theorem weighted_affine_integrable (a b l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) :
    IntervalIntegrable (fun x : ℝ ↦ (b + a * x) / x ^ 3) volume l r := by
  have h₂ := intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := -2)
    (Or.inr (zero_not_uIcc hl hlr))
  have h₃ := intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := -3)
    (Or.inr (zero_not_uIcc hl hlr))
  apply ((h₂.const_mul a).add (h₃.const_mul b)).congr_uIoo
  rw [uIoo_of_le hlr]
  intro x hx
  exact (weighted_affine_eq x a b (ne_of_gt (lt_trans hl hx.1))).symm

theorem weighted_affine_integral (a b l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) :
    (∫ x in l..r, (b + a * x) / x ^ 3) =
      a * (1 / l - 1 / r) + b / 2 * (1 / l ^ 2 - 1 / r ^ 2) := by
  have hz := zero_not_uIcc hl hlr
  have h₂ := intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := -2) (Or.inr hz)
  have h₃ := intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := -3) (Or.inr hz)
  rw [intervalIntegral.integral_congr_Ioo_of_le hlr
    (fun x hx ↦ weighted_affine_eq x a b (ne_of_gt (lt_trans hl hx.1))),
    intervalIntegral.integral_add (h₂.const_mul a) (h₃.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_zpow (n := -2) (Or.inr ⟨by norm_num, hz⟩),
    integral_zpow (n := -3) (Or.inr ⟨by norm_num, hz⟩)]
  norm_num [zpow_neg]
  ring

end Zeta5.Certificate
