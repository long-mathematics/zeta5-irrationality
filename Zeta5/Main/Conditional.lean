import Zeta5.Construction.Degree
import Zeta5.Main.IntegerPolynomialCriterion

namespace Zeta5

open Polynomial

/-- An explicitly conditional endpoint for the *actual* source polynomial.
The missing integrality, positivity, and decay estimates are all visible
arguments. This theorem does not assert that any of those arguments exists. -/
theorem irrational_of_inputs (n₀ : ℕ)
    (hintegral : ∀ n ≥ n₀, ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) = QKM n 200)
    (hpos : ∀ n ≥ n₀, 0 < (QKM n 200).eval₂ (Rat.castHom ℝ) zetaFive)
    (hsmall : ∀ n ≥ n₀, (QKM n 200).eval₂ (Rat.castHom ℝ) zetaFive <
      Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2)) :
    Irrational zetaFive := by
  classical
  let P : ℕ → ℤ[X] := fun n ↦ if hn : n₀ ≤ n then (hintegral n hn).choose else 0
  have hmap (n : ℕ) (hn : n₀ ≤ n) : (P n).map (Int.castRingHom ℚ) = QKM n 200 := by
    simpa only [P, dite_eq_left hn] using (hintegral n hn).choose_spec
  have heval (n : ℕ) (hn : n₀ ≤ n) :
      (P n).eval₂ (Int.castRingHom ℝ) zetaFive =
        (QKM n 200).eval₂ (Rat.castHom ℝ) zetaFive := by
    rw [← hmap n hn, eval₂_map]
    rfl
  apply irrational_of_integer_polynomials zetaFive 37 (139 / 5) (by norm_num) P n₀
  · intro n hn
    have hdeg : (P n).natDegree = (QKM n 200).natDegree := by
      rw [← hmap n hn, natDegree_map_eq_of_injective (Int.cast_injective)]
    rw [hdeg]
    exact_mod_cast QKM_natDegree_le n 200
  · intro n hn
    rw [heval n hn]
    exact hpos n hn
  · intro n hn
    rw [heval n hn]
    exact hsmall n hn

end Zeta5
