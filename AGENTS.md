# Autonomous formalization instructions

## Objective and current state

Formalize the mathematical development in
`paper/zeta5_formalization_draft.tex`, based on the attributed manuscript of
Aabir Fauzan dated 17 September 2026. The primary unconditional endpoint is
irrationality of the real series `sum_{n>=0} 1/(n+1)^5`, with a bridge to the
intended Riemann-zeta value. The approximation exponent 260 and height bounds
are optional secondary endpoints.

This package contains a compiled mathematical draft and executed finite
Python certificates. It contains **no completed or tested Lean proofs**.
`formalization/declarations.csv` records pending targets. Do not describe
Python certificate success, an implication from assumptions, or a clean build
of a conditional scaffold as a formalization of irrationality.

## First actions

1. Read the complete mathematical draft, REPAIRS.md, the declaration ledger,
   and the external-input ledger. Read the local completed-domain proof before
   choosing a Tate-algebra representation.
2. Run `python3 certificates/verify.py`. It must reproduce all finite checks.
3. Select a compatible Lean/Mathlib toolchain based on actual available
   versions, pin exact revisions, and record them. Do not guess declaration
   names or claim that a library theorem exists without inspecting its type.
4. Create local modules following the planned paths in the ledger, or record
   a justified equivalent organization. Preserve stable public target names.
5. Establish the generic rational-polynomial contradiction and an explicitly
   conditional end-to-end theorem early. The conditional theorem must retain
   all missing inputs in its type.

## Proof and statement discipline

- Definitions must represent the actual polynomials, functional, prime
  exponents, and measure in the draft. Do not replace the construction with
  arbitrary objects whose properties already contain the desired conclusion.
- Parameterize by n with K=40*n, N=3*n, h=37*n. Be explicit about all coercions.
- The rational-function domain has polynomial parts and simple specified
  poles only. It is not closed under arbitrary multiplication.
- A far pole is evaluated by its convergent analytic expansion, not by an
  invented harmonic-index convention. The distribution identity applies to
  all integer poles, even when d(r)>=p. Only the local integrality lemma
  requires small harmonic indices for its near poles.
- The target of local infinite sums has fixed polynomial degree. Do not
  assume the whole polynomial ring is complete in its Gauss norm.
- State coefficientwise Gauss-valuation bounds, including the constant
  coefficient. Preserve both quotient and residue contributions.
- Keep p=2,3,5 in the small-prime proof. Keep the v_p(24) loss.
- Preserve signed normalization exponents. Use integer powers of positive
  rational primes, not truncated natural exponents.
- Prove CRT unimodularity, source-by-source row comparisons, and the rank of
  the polynomial correction over Q_p. Rank modulo p is insufficient.
- Preserve the nonpositive-weight hypothesis of the rank-correction lemma.
  Do not apply it to the inner weights, which may be positive.
- Equation (5.9) of the original paper has a MULTIPLICATIVE indicator.
  The draft's piecewise version is correct. The prior suggested deletion of
  an additive indicator was a reading error, not a source erratum.
- Fix M before taking limits. K>=200*M^2 is admissibility only. The decay
  theorem still has an existential threshold.
- For the logarithmic-energy lemma, prove the diagonal is null under the
  total variation product measure. A real-valued kernel using Real.log 0
  without this hypothesis is not the source lemma. For collisions in the
  configuration estimate use the zero Vandermonde product directly.
- Track the positivity/nonzero premises of every division, logarithm,
  determinant factorization, and matrix inverse.

## Certificates

The JSON data and verifier use exact integers/Fractions and outward-rounded
192-bit dyadic intervals. No floating-point comparison is an acceptance test.
The verifier checks all 684 potential cells, 143 symbolic inner pieces, 11
outer pieces, and the numerical constants. Its result is not a Lean proof.

Prove a sound interval checker and exact polynomial branch checker in Lean,
then replay finite witnesses or equivalent computations. Prove domain and
branch conditions, partition coverage, and strict margins. It is acceptable
to generate witnesses externally; do not trust an external Boolean oracle.
Prefer a kernel-checkable certificate path. Do not silently add compiler or
native-evaluation trust. Record the exact axiom dependencies of certificate
lemmas and the endpoint; use proof-producing arithmetic, kernel reduction,
or checked witnesses for the final certificate milestone.

Do not recalculate the source constants with a different measure or improved
zero-class weights unless the new variant is separately proved and tracked.
First formalize the unchanged construction.

## Infrastructure and progress

Standard theorems such as von Staudt--Clausen, the Hermite integral, and the
PNT may initially be explicit parameters in a conditional development. Find
actual library theorems or prove precise interfaces; do not introduce axioms
or hide their statements inside an opaque assumption.

Work incrementally, running targeted builds after each lemma and the full
build at milestones. Update the declaration ledger with the exact Lean name,
module, proof status, remaining inputs, and verification command. Count only
proved mathematical targets, not helper declarations, when reporting coverage.

When a library gap is found, state the exact needed theorem and continue
through independent modules. When a mathematical obstruction is found,
record the exact statement, hypotheses, and a minimal counterexample or
missing implication in BLOCKERS.md. Attempt a repair, but do not weaken a
public statement without a documented mathematical change and review.

## Completion audit

The primary target is complete only after:

- A clean pinned-toolchain build from source.
- No `sorry`/`admit` in endpoint dependencies and no project-owned axioms.
- Every provisional input instantiated by a proved or audited imported theorem.
- `#print axioms` output saved for the main theorem and every public endpoint.
- The intended zeta-series definition and its bridge independently checked.
- Kernel-checkable finite certificates attached to the actual construction.
- Optional consequences clearly separated in status reports.

Preserve original authorship and distinguish this working edition from an
author-approved revision. Do not assign a license to the reconstructed
manuscript, publish a repository, or change public attribution without
explicit authorization. If work is placed in an authorized Git repository,
use a feature branch, reviewable commits, tests, and the existing PR/CI policy.
