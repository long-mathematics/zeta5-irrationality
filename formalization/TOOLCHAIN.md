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
