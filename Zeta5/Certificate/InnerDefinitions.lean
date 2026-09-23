import Zeta5.Certificate.Margins
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! The original inner limiting function of (5.4)–(5.6), before any
piecewise expansion. The finite branch proofs integrate its actual floor
expression in the auxiliary variable. -/

namespace Zeta5.Certificate

open MeasureTheory Set

noncomputable def innerEll (x z : ℝ) : ℝ :=
  (⌊x - z⌋ : ℤ) + (⌊x + z⌋ : ℤ) + 1

noncomputable def innerB (x z : ℝ) : ℝ := 3 * innerEll ((3 / 40) * x) z
noncomputable def innerT (x : ℝ) : ℝ := (⌊2 * (23 / 20) * x⌋ : ℤ)
noncomputable def innerS (x : ℝ) : ℝ := (23 / 20) * x - innerT x / 2
noncomputable def innerQ (x : ℝ) : ℝ := (⌊2 * x⌋ : ℤ)
noncomputable def innerNplus (x : ℝ) : ℝ := (2 * x - innerQ x) / 2
noncomputable def innerGammaIntegrand (x z : ℝ) : ℝ :=
  (innerT x - innerB x z) * (innerT x + innerB x z - innerEll x z - 5)
noncomputable def innerGamma (x : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..(1 / 2), innerGammaIntegrand x z) +
    innerS x * (2 * innerT x - innerQ x - 5) + max 0 (innerS x - innerNplus x)
noncomputable def innerJ (u : ℝ) : ℝ :=
  let m : ℝ := (⌊2 * u⌋ : ℤ)
  m * u - m * (m + 1) / 4
noncomputable def innerScalar (x : ℝ) : ℝ :=
  2 * (37 / 40) * x * (⌊x⌋ : ℤ) -
    12 * (37 / 40) * x * (⌊(3 / 40) * x⌋ : ℤ) - 2 * innerJ ((37 / 40) * x)
noncomputable def innerR (x : ℝ) : ℝ := -innerGamma x - innerScalar x
noncomputable def innerIntegrand (x : ℝ) : ℝ := innerR x / x ^ 3

theorem intervalIntegrable_of_eq_const_Ioo {f : ℝ → ℝ} {l r c : ℝ}
    (hlr : l ≤ r) (hf : ∀ z ∈ Ioo l r, f z = c) :
    IntervalIntegrable f volume l r := by
  apply (continuous_const.intervalIntegrable l r :
    IntervalIntegrable (fun _ : ℝ ↦ c) volume l r).congr_uIoo
  rw [uIoo_of_le hlr]
  intro z hz
  exact (hf z hz).symm

/-- A checked three-strip integral; the open-strip hypotheses ignore only
finitely many endpoints, whose Lebesgue measure is zero. -/
theorem integral_three_strips (f : ℝ → ℝ) (a b c₀ c₁ c₂ : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2)
    (h₀ : ∀ z ∈ Ioo 0 a, f z = c₀)
    (h₁ : ∀ z ∈ Ioo a b, f z = c₁)
    (h₂ : ∀ z ∈ Ioo b (1 / 2), f z = c₂) :
    (∫ z in (0 : ℝ)..(1 / 2), f z) = a * c₀ + (b - a) * c₁ + (1 / 2 - b) * c₂ := by
  have hi₀ := intervalIntegrable_of_eq_const_Ioo ha h₀
  have hi₁ := intervalIntegrable_of_eq_const_Ioo hab h₁
  have hi₂ := intervalIntegrable_of_eq_const_Ioo hb h₂
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi₀.trans hi₁) hi₂,
    ← intervalIntegral.integral_add_adjacent_intervals hi₀ hi₁]
  rw [intervalIntegral.integral_congr_Ioo_of_le ha h₀,
    intervalIntegral.integral_congr_Ioo_of_le hab h₁,
    intervalIntegral.integral_congr_Ioo_of_le hb h₂]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

end Zeta5.Certificate
