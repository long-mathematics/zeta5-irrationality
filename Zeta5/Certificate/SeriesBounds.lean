import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! The finite-series remainder bounds used by the Appendix A checker.
The source uses 64 logarithm terms and 80 arctangent terms. -/

namespace Zeta5.Certificate

open Finset Filter Set
open scoped Topology

noncomputable def atanPartial (x : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range m, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1)

/-- The source's symmetric 80-term remainder bound, valid on a slightly
larger interval than the reduced checker domain `[0,1/2]`. -/
theorem atan_eighty_remainder (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    |Real.arctan x - atanPartial x 80| ≤ x ^ 161 / 161 := by
  let f : ℕ → ℝ := fun k ↦ x ^ (2 * k + 1) / (2 * k + 1)
  have hanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro k
    dsimp [f]
    apply div_le_div₀ (by positivity) ?_ (by positivity) (by norm_num)
    exact pow_le_pow_of_le_one hx₀ hx₁.le (by omega)
  have hsum := (Real.hasSum_arctan (x := x) (by simpa [Real.norm_eq_abs, abs_of_nonneg hx₀])).tendsto_sum_nat
  have hsum' : Tendsto (fun n ↦ ∑ k ∈ range n, (-1 : ℝ) ^ k * f k)
      atTop (𝓝 (Real.arctan x)) := by
    simpa only [f, mul_div_assoc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hsum
  have hlo := hanti.alternating_series_le_tendsto hsum' 40
  have hhi := hanti.tendsto_le_alternating_series hsum' 40
  norm_num only [show 2 * 40 = 80 by rfl, show 2 * 40 + 1 = 81 by rfl] at hlo hhi
  rw [sum_range_succ] at hhi
  simp only [f, ← mul_div_assoc] at hlo hhi
  change atanPartial x 80 ≤ Real.arctan x at hlo
  have hup : Real.arctan x ≤ atanPartial x 80 + x ^ 161 / 161 := by
    change Real.arctan x ≤ atanPartial x 80 + (-1 : ℝ) ^ 80 * x ^ (2 * 80 + 1) / (2 * 80 + 1) at hhi
    norm_num only [show (-1 : ℝ) ^ 80 = 1 by norm_num, one_mul] at hhi
    exact hhi
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

noncomputable def logPartial (z : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range m, z ^ (2 * k + 1) / (2 * k + 1)

/-- The sharper geometric-tail bound used in the source, with its factor
`129` retained in the denominator. -/
theorem log_sixty_four_remainder (z : ℝ) (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    0 ≤ Real.log ((1 + z) / (1 - z)) - 2 * logPartial z 64 ∧
    Real.log ((1 + z) / (1 - z)) - 2 * logPartial z 64 ≤
      2 * z ^ 129 / (129 * (1 - z ^ 2)) := by
  have hden : 0 < 1 - z ^ 2 := by nlinarith
  have hlo := Real.sum_range_le_log_div hz₀ hz₁ 64
  have hlo' : 0 ≤ Real.log ((1 + z) / (1 - z)) - 2 * logPartial z 64 := by
    dsimp [logPartial]
    linarith
  refine ⟨hlo', ?_⟩
  let F : ℝ → ℝ := fun t ↦
    1 / 2 * Real.log ((1 + t) / (1 - t)) - logPartial t 64
  let G : ℝ → ℝ := fun t ↦ t ^ 129 / (129 * (1 - z ^ 2)) - F t
  let G' : ℝ → ℝ := fun t ↦ t ^ 128 / (1 - z ^ 2) - (t ^ 2) ^ 64 / (1 - t ^ 2)
  have hder : ∀ t ∈ Icc 0 z, HasDerivAt G (G' t) t := by
    intro t ht
    have hF : HasDerivAt F ((t ^ 2) ^ 64 / (1 - t ^ 2)) t :=
      Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range 64
        (by linarith [ht.1]) (by linarith [ht.2])
    have hP : HasDerivAt (fun t : ℝ ↦ t ^ 129 / (129 * (1 - z ^ 2)))
        (t ^ 128 / (1 - z ^ 2)) t := by
      convert (hasDerivAt_pow 129 t).div_const (129 * (1 - z ^ 2)) using 1
      field_simp
      ring
    exact hP.sub hF
  have hmono : MonotoneOn G (Icc 0 z) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 z)
      (fun t ht ↦ (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hder t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Icc 0 z := interior_subset ht
    have hs : t ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ ht'.1 ht'.2 2
    dsimp [G']
    rw [sub_nonneg]
    norm_num only [← pow_mul]
    exact div_le_div_of_nonneg_left (by positivity) hden (by linarith)
  have hG := hmono ⟨le_rfl, hz₀⟩ ⟨hz₀, le_rfl⟩ hz₀
  have hG₀ : G 0 = 0 := by simp [G, F, logPartial]
  rw [hG₀] at hG
  dsimp [G, F] at hG
  rw [mul_div_assoc]
  linarith

/-- The exact Machin identity used to enclose pi in the source checker. -/
theorem machin_identity :
    Real.pi = 16 * Real.arctan (1 / 5 : ℝ) - 4 * Real.arctan (1 / 239 : ℝ) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  simp only [one_div] at *
  linarith

/-- The checker half-angle reduction, with its range verified. -/
theorem atan_half_angle (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    let t := x / (1 + Real.sqrt (1 + x ^ 2))
    0 ≤ t ∧ t ≤ 1 / 2 ∧ Real.arctan x = 2 * Real.arctan t := by
  let s := Real.sqrt (1 + x ^ 2)
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  have hs₂ : s ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs₁ : 1 ≤ s := by nlinarith
  have hd : 0 < 1 + s := by linarith
  let t := x / (1 + s)
  have ht₀ : 0 ≤ t := div_nonneg hx₀ hd.le
  have ht₁ : t ≤ 1 / 2 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  change 0 ≤ t ∧ t ≤ 1 / 2 ∧ _
  refine ⟨ht₀, ht₁, ?_⟩
  have htt : t * t < 1 := by nlinarith
  have hrel : t * (1 + s) = x := div_mul_cancel₀ x hd.ne'
  have halg : (t + t) / (1 - t * t) = x := by
    apply (div_eq_iff (by linarith : 1 - t * t ≠ 0)).mpr
    have hsx := congrArg (fun y : ℝ ↦ t * y) hs₂
    have htx := congrArg (fun y : ℝ ↦ t * y) hrel
    nlinarith [sq_nonneg (t * s - x)]
  have ha := Real.arctan_add htt
  rw [halg] at ha
  linarith

end Zeta5.Certificate
