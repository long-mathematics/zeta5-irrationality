import Zeta5.Construction.Functional
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.PSeries

namespace Zeta5

open Polynomial

/-- The paper's integer parameters, avoiding divisions on natural numbers. -/
def parameters (n : ℕ) : ℕ × ℕ × ℕ := (40 * n, 3 * n, 37 * n)

abbrev K (n : ℕ) : ℕ := 40 * n
abbrev N (n : ℕ) : ℕ := 3 * n
abbrev h (n : ℕ) : ℕ := 37 * n

/-- The real series whose irrationality is the primary endpoint. -/
noncomputable def zetaFive : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5

theorem zetaFive_summable : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 5) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 5))

/-- `D_m(t) = ∏_{1 ≤ j ≤ m} (t+j²)`. -/
noncomputable def D (m : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range m, (X + C (((j : ℚ) + 1) ^ 2))

/-- The uncancelled denominator, with exactly `h n` distinct allowed poles. -/
noncomputable def tailD (n : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.Ico (N n) (K n), (X + C (((j : ℚ) + 1) ^ 2))

/-- Polynomial numerator after cancelling the common factor `D_N`. -/
noncomputable def entryNumerator (n e : ℕ) : ℚ[X] := D (N n) ^ 5 * X ^ e

/-- Ordinary monic division and the simple-pole residue formula. -/
noncomputable def entryDomain (n e : ℕ) : RationalDomain :=
  (entryNumerator n e / tailD n,
    ∑ j ∈ Finset.Ico (N n) (K n), Finsupp.single j
      ((entryNumerator n e).eval (-((j : ℚ) + 1) ^ 2) /
        (tailD n).derivative.eval (-((j : ℚ) + 1) ^ 2)))

/-- The source Hankel matrix of affine polynomials. -/
noncomputable def GK (n : ℕ) : Matrix (Fin (h n)) (Fin (h n)) ℚ[X] :=
  fun i j ↦ muX (entryDomain n (i.val + j.val))

/-- The source determinant. -/
noncomputable def deltaK (n : ℕ) : ℚ[X] := (GK n).det

/-- The positive factorial scalar, used for positive `n`. -/
def scalarSK (n : ℕ) : ℚ :=
  ((K n).factorial : ℚ) ^ (2 * h n) * 4 ^ (h n - 1) /
    (((N n).factorial : ℚ) ^ (12 * h n) *
      ∏ i ∈ Finset.Ico 1 (h n), (((2 * i).factorial : ℚ) ^ 2))

/-- The rational polynomial `S_K Δ_K`. -/
noncomputable def FK (n : ℕ) : ℚ[X] := C (scalarSK n) * deltaK n

end Zeta5
