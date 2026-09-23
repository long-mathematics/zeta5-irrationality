# Pinned and inspected toolchain

- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- Mathlib's own `lean-toolchain` agrees with the project pin.
- All transitive package revisions remain pinned in `lake-manifest.json`.

Verified locally on 23 September 2026. `lake exe cache get` retrieved the
available compiled dependencies; missing artifacts were built from their
pinned sources. `lake build` checks the library as a default target. The
executable is a separate smoke test and does not link all of Mathlib.

## Inspected and used interfaces

- `Polynomial.one_le_pow_mul_abs_eval_div` in
  `Mathlib/Algebra/Polynomial/DenomsClearable.lean`: for an integer polynomial,
  positive integer denominator, and nonzero evaluation, the denominator to
  the natural degree times the absolute evaluation is at least one.
- `zeta_eq_tsum_one_div_nat_add_one_cpow` in
  `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`: the shifted complex series
  equals Riemann zeta when the real part of the argument exceeds one.
- `Real.summable_one_div_nat_pow` in `Mathlib/Analysis/PSeries.lean`:
  summability holds precisely for natural exponent greater than one.
- `Polynomial.natDegree_det_X_add_C_le` in
  `Mathlib/LinearAlgebra/Matrix/Polynomial.lean`: the determinant of an affine
  polynomial matrix has degree at most its dimension.
- `bernoulli` in `Mathlib/NumberTheory/Bernoulli.lean` uses `B₁ = -1/2`.
- Interval-integral congruence on open intervals and adjacent-interval
  summation in `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
  handle the finite branch endpoints and partition assembly.
- `integral_id` and `integral_zpow` in
  `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean` provide the affine
  and inverse-power integral formulas with their domain hypotheses.
- `Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range` and
  `Real.sum_range_le_log_div` in `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean`
  support the project's sharper 64-term logarithm remainder proof.
- `Real.hasSum_arctan` in
  `Mathlib/Analysis/SpecialFunctions/Complex/Arctan.lean`, together with the
  even/odd partial-sum bounds in `Mathlib/Analysis/SpecificLimits/Normed.lean`,
  supplies the source's 80-term arctangent remainder.
- `Real.arctan_add`, `Real.arctan_inv_of_pos`, and
  `Real.four_mul_arctan_inv_5_sub_arctan_inv_239` in
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean` give the
  checked argument reductions and exact Machin identity.

## Further interfaces located, not yet discharged

- `Bernoulli.vonStaudt_clausen` and
  `Bernoulli.padicValRat_bernoulli` exist in the pinned Bernoulli module.
  Their exact statements have been read. The full local bounds and their
  connection to the project functional remain to be proved and audited.
- `riemannZeta_two_mul_nat` in
  `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean` gives the even-value
  formula. The project moment identity remains unproved.
- The local search of L-series modules found no Hermite integral interface.
- Searches of number-theory modules found Chebyshev estimates and divergence
  of prime counting, but not the required `θ(T)/T → 1` theorem. This is a
  library search result, not a mathematical obstruction or an assumption.

The external-input ledger stays pending until the exact needed interface has
been proved or fully instantiated and audited.
