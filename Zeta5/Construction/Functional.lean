import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finsupp.Basic

/-! The partial-fraction coordinates of the source's rational vector space.
The label `j : ℕ` represents the permitted simple pole `-(j+1)^2`.
There is intentionally no multiplication operation on this domain. -/

namespace Zeta5

open Polynomial

/-- Polynomial part and finitely many simple principal parts. -/
abbrev RationalDomain := ℚ[X] × (ℕ →₀ ℚ)

/-- The finite fifth-order harmonic number, including `harmonicFive 0 = 0`. -/
def harmonicFive (j : ℕ) : ℚ := ∑ v ∈ Finset.range j, 1 / ((v : ℚ) + 1) ^ 5

/-- The polynomial moments, with Mathlib's convention `bernoulli 1 = -1/2`. -/
def polynomialMoment (e : ℕ) : ℚ :=
  (-1) ^ e * bernoulli (2 * e + 2) * (2 * e + 3) * (2 * e + 4) * (2 * e + 5) / 24

/-- Value at the simple pole with positive label `j+1`. -/
noncomputable def poleMoment (j : ℕ) : ℚ[X] :=
  C (((j : ℚ) + 1) ^ 4) * (X - C (harmonicFive (j + 1))) - C (1 / 4) +
    C (1 / (2 * ((j : ℚ) + 1)))

/-- The actual affine functional in equations (2.2)–(2.3), in unique
partial-fraction coordinates. -/
noncomputable def muX (R : RationalDomain) : ℚ[X] :=
  C (R.1.sum fun e a ↦ a * polynomialMoment e) +
    R.2.sum (fun j a ↦ C a * poleMoment j)

end Zeta5
