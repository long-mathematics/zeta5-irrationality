import Mathlib.Algebra.Polynomial.DenomsClearable
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The elementary final contradiction, independent of the determinant construction. -/

namespace Zeta5

open Polynomial

/-- Positive integer-polynomial values with linear degree and quadratic exponential
decay force irrationality. All three estimates are required only eventually. -/
theorem irrational_of_integer_polynomials (x d c : ℝ) (hc : 0 < c)
    (P : ℕ → ℤ[X]) (n₀ : ℕ)
    (hdegree : ∀ n ≥ n₀, ((P n).natDegree : ℝ) ≤ d * n)
    (hpos : ∀ n ≥ n₀, 0 < (P n).eval₂ (Int.castRingHom ℝ) x)
    (hsmall : ∀ n ≥ n₀,
      (P n).eval₂ (Int.castRingHom ℝ) x < Real.exp (-c * (n : ℝ) ^ 2)) :
    Irrational x := by
  rintro ⟨q, rfl⟩
  have hb : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hb1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  obtain ⟨n, hn⟩ := exists_nat_gt (max (n₀ : ℝ) (max 0 (d * Real.log q.den / c)))
  have hn₀ : n₀ ≤ n := by exact_mod_cast (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn))
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnc : d * Real.log q.den < c * n := by
    have := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    exact (div_lt_iff₀ hc).mp this |>.trans_eq (mul_comm _ _)
  have hlog : 0 ≤ Real.log (q.den : ℝ) := Real.log_nonneg hb1
  have hexponent : ((P n).natDegree : ℝ) * Real.log q.den - c * (n : ℝ) ^ 2 < 0 := by
    have hdeg := mul_le_mul_of_nonneg_right (hdegree n hn₀) hlog
    have hstrict := mul_lt_mul_of_pos_right hnc hnpos
    nlinarith
  have hrat : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
  have hlower := one_le_pow_mul_abs_eval_div (K := ℝ) (f := P n)
    (a := q.num) (b := (q.den : ℤ)) (by exact_mod_cast q.den_pos)
    (by simpa [eval_map, ← hrat] using (ne_of_gt (hpos n hn₀)))
  have hlower' : (1 : ℝ) ≤ (q.den : ℝ) ^ (P n).natDegree *
      (P n).eval₂ (Int.castRingHom ℝ) (q : ℝ) := by
    simpa [eval_map, ← hrat, abs_of_pos (hpos n hn₀)] using hlower
  have hupper := mul_lt_mul_of_pos_left (hsmall n hn₀)
    (pow_pos hb (P n).natDegree)
  have hpow : (q.den : ℝ) ^ (P n).natDegree =
      Real.exp (((P n).natDegree : ℝ) * Real.log q.den) := by
    rw [Real.exp_nat_mul, Real.exp_log hb]
  rw [hpow, ← Real.exp_add] at hupper
  have hlt : Real.exp (((P n).natDegree : ℝ) * Real.log q.den +
      -c * (n : ℝ) ^ 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [hpow] at hlower'
  linarith

end Zeta5
