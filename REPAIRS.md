# Editorial decisions and proof expansions

## Source and attribution

- Source: Aabir Fauzan, *ζ(5) is irrational*, 17 September 2026, 32 pages.
- Uploaded PDF SHA-256:
  `a42c05ccc46b9a7c36428913453c4617202c59109713ba20f464ab9ec640d0da`.
- This LaTeX is a reconstruction and expanded formalization working edition,
  not the author's original source and not an author-approved revision.
- It was prepared for Christopher D. Long; the original mathematical claims
  remain attributed to Fauzan. No additional mathematical coauthor has been
  assigned to the original paper.

## Corrections to earlier audit commentary

### Original equation (5.9) is not erroneous

The actual PDF typesets

    d(y) = (1+4α-3y-(1+α-3y)_+)_+ * 1_(1/3,1/2)(y).

The positive-part subscript was previously misread as an addition sign.
There is no additive indicator. The draft preserves the formula, written
piecewise. The integral 9/640 and outer total 127751/96000 are unchanged.

### Admissibility is not the decay threshold

K>=200*M^2 is the explicit domain condition for the normalizer. For K=40*n
and M=200 it becomes n>=200000, but that does not prove the asserted decay
for every n from 200000 onward. The corrected quantifiers are: there exists
n0>=200000 such that the decay holds for all n>=n0. For M=100000 the
admissibility threshold is n>=50,000,000,000; its eventual decay threshold
may also be larger. No effective threshold is claimed.

## Expanded mathematical arguments

1. The rational functional's vector-space domain and coefficientwise scalar
   extensions are explicit; repeated poles are excluded unless separately
   supported.
2. Restricted series and a finite principal-part direct sum replace an
   unspecified completed domain. Injectivity in the localization proves
   uniqueness. A coefficient formula proves bounded division.
3. Local infinite evaluations take values in Q_p + Q_p Y, a fixed
   finite-dimensional complete space, rather than implicitly treating the
   whole polynomial ring as complete.
4. The integral-extension lemma includes convergence, the degree restriction
   on U0, the one-power loss on analytic terms, and closedness of integral
   coefficients.
5. The far-pole series and compatibility of expansion order are proved with
   an explicit near/far convention.
6. Reflection and difference are extended to the completed domain, with
   regularity at zero required only where it is actually needed.
7. Distribution is proved first on polynomials and 1/x, then by an explicit
   positive-pole recurrence and reflection for negative poles. No restriction
   d(r)<p is imposed on the original poles of the distribution theorem.
8. The small-prime root counting and inverse-product estimate are expanded,
   including the neighborhoods of every integer pole and p=2,3,5.
9. The inner basis has a full source-versus-row comparison table and all four
   extra-allocation cases. The zero source and degree conditions are explicit.
10. The outer polynomial correction is shown to have small rank over Q_p,
    not merely modulo p. Divided differences and class counts are expanded.
11. The weighted prime-sum interface is separated from the PNT and the
    fixed-cutoff quantifier order is explicit.
12. The logarithmic-energy proof includes integrability and a formalization
    warning about the totalized value of Real.log at zero. Collisions are
    handled by a zero Vandermonde product, not a false real log inequality.
13. All scaling powers and the retained integrable tail in the real bound
    are displayed separately.
14. The optional approximation/height branch is separated from irrationality.

## Independent computation performed for this edition

`python3 certificates/verify.py` passed:

- Positive masses, total mass 37/40, nesting, and all interval-length bounds.
- The minimizing-point bracket and the sign needed by the Vstar estimate.
- All 684 cells of the source partition, including exact coverage checks.
- The energy and Cstar enclosures and the real quadratic coefficient.
- The optional tight kappa enclosure.
- All 143 inner pieces: every branch certified and full rational polynomial
  coefficients computed, including an independent comparison of the original
  Gamma integral with the F/Q expansion.
- All 17 unit-interval totals and the exact full inner integral.
- All 11 outer affine pieces and the exact full outer integral.
- The tail-at-20 rational arithmetic and both positive final margins.
- The two rational constant identities in the approximation argument.

The finite elementary-function computation uses 192-bit outward-rounded
integer intervals (the source specifies 144-bit square-root brackets), with
unchanged logarithm/arctangent truncation lengths 64 and 80. No mathematical
constant is improved or changed.

The largest accepted upper endpoint for B(l,r) occurs in cell (30,6,26) and
is approximately -6.64500268921558832385. This is a certified cell upper
bound, not the true supremum of the potential. The exact interval is in the
JSON report. Numerical printing is not used to accept an inequality.

These are exact Python computations, not Lean/kernel certificates. Infinite
functional identities, analytic arguments, and asymptotic estimates remain
mathematical proof obligations for the Lean project.

## User-supplied audit evidence, not rerun here

The user supplied Claude's reports of exact determinant and valuation tests
for K=40,80,120,160; truncated p-adic distribution tests at p=7,11; small-scale
inner-basis mechanism tests; large-scale outer bookkeeping comparisons; and
floating-point potential/prime-sum checks. Those reports state that no fatal
break was found and explicitly do not claim certification. They are not
assumed correct as proof premises and are not described as computations
performed by this working edition.

## Deliberately unchanged

The determinant, scalar normalization, signed prime exponents, original
zero-class weights (-2,0), comparison measure, final decay constants, and
exponent 260 are retained. The earlier audit's suggested optimization of
zero-class weights is not folded into the baseline. The author's speculative
further-work discussion and historical introduction are not needed for the
formal proof and are not reconstructed as new research claims.
