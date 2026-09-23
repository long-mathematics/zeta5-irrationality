# Formalization status

## Primary endpoint

Target:

```lean
Zeta5.zeta_five_irrational
```

Status: **not yet formalized**.

Planned mathematical declarations: **49 total**, of which **45** are required
for the main irrationality theorem and **4** belong only to the optional
rational-approximation/height branch.

Current unconditional proved target count: **6 / 49**. In addition, **1**
explicitly conditional target is proved and **9** construction definitions
compile. These categories are reported separately; definitions and the
conditional endpoint are not proofs of irrationality.

The six unconditional targets are:

- `Zeta5.irrational_of_integer_polynomials`;
- `Zeta5.zetaFive_eq_riemannZeta`;
- `Zeta5.Certificate.final_rational_margins`;
- `Zeta5.Certificate.outer_integral`;
- `Zeta5.Certificate.inner_integral`;
- `Zeta5.Certificate.interval_soundness`.

The actual `GK`, `deltaK`, `scalarSK`, `FK`, signed `normalizationFactor`, and
`QKM` are defined. The functional uses polynomial and finite simple-pole
coordinates. Proofs of the rational-function embedding and the entry
partial-fraction identity remain outstanding; no correspondence theorem is
claimed for those definitions yet.

The degree upper bound `QKM_natDegree_le` is proved, so the conditional theorem
`irrational_of_inputs` has exactly three remaining estimates as arguments:
eventual integrality, positivity, and quadratic exponential decay of the
actual `QKM n 200`. The exact-degree target, including its nonzero leading
coefficient formula, remains partial. Helper results do not increase the
49-target coverage count.

The final margins are checked from the unchanged rational constants with
proof-producing `norm_num`. The outer integral is proved from the actual
piecewise expression: Lean checks all 11 affine branches, their ordered
partition, integrability, and
the exact integral sum. Values at partition endpoints are handled through
null-singleton interval-integral congruence.

The inner integral is proved from the original `Gamma` integral and scalar
term. Lean checks all 143 branches, including the auxiliary floor-function
integrals on three strips, then integrates and sums the resulting expressions.
The script `scripts/generate_inner_branches.py` generates proof scripts;
its candidate values are checked on the entire open domains by Lean. It is
not a trusted oracle.

Interval-certificate soundness is proved, including exact arithmetic checks,
the source logarithm and arctangent remainders, and their range reductions.
The proof-carrying certificate design and its equivalence to the source
checker contract are documented in
[`formalization/CERTIFICATES.md`](formalization/CERTIFICATES.md). The specific
energy/norm and potential-cell witnesses remain pending.

## Latest verification

- `lake build` passed with the original pinned Lean and Mathlib revisions.
- All 6 repository audit tests passed; the source audit found no proof
  placeholders or project-owned axioms.
- The Python verifier reproduced all 684 potential cells, 143 inner pieces,
  11 outer pieces, and the numerical constants.
- The public foundation audit is in
  [`formalization/audits/foundations.txt`](formalization/audits/foundations.txt),
  reproducible with `lake env lean formalization/AuditFoundations.lean`.
  Its declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
  No native-evaluation axiom occurs in any of these certificate proofs.
- [`formalization/TOOLCHAIN.md`](formalization/TOOLCHAIN.md) records exact
  inspected library interfaces and outstanding library searches.

There is no declaration `Zeta5.zeta_five_irrational` yet and no endpoint axiom
audit to report. The unconditional completion criteria below remain unmet.

The source-of-truth declaration inventory is
[`formalization/declarations.csv`](formalization/declarations.csv). Update that
ledger whenever a target is proved, replaced by a precisely equivalent theorem,
or split into justified subtargets.

## Completion criteria

The headline theorem may be described as formally verified only after all of
the following hold:

- `lake build` succeeds from the pinned toolchain and manifest.
- No endpoint dependency contains `sorry` or `admit`.
- There are no project-owned `axiom` declarations.
- Every provisional external input has been instantiated by a proved local
  theorem or a specifically audited imported theorem.
- The exact zeta-series definition and its bridge to the intended Riemann-zeta
  value have been checked independently.
- The finite potential and prime-sum certificates are replayed by a sound
  Lean checker or equivalent proof-producing arithmetic.
- `#print axioms Zeta5.zeta_five_irrational` is recorded and reviewed.
- The transitive dependencies of the endpoint have been audited for statement
  correspondence with the mathematical draft.

A conditional theorem is useful during development but does not satisfy these
criteria.

## Planned stages

| Stage | Scope | Targets | Status |
|---|---|---:|---|
| 1 | Definitions, determinant degree, generic contradiction, conditional bridge | 13 | 9 definitions; 2 unconditional proofs; 1 conditional proof; exact degree partial |
| 2 | Kernel-checkable finite certificates | 6 | rational margins, both integrals, interval soundness proved; 2 pending |
| 3 | Completed local rational functional and distribution | 7 | pending |
| 4 | Inner/outer determinant valuation estimates | 6 | pending |
| 5 | Normalization and prime-sum asymptotics | 4 | pending |
| 6 | Positive moments, logarithmic energy, real determinant bound | 7 | pending |
| 7 | Polynomial estimates and irrationality | 2 | pending |
| 8 | Optional exponent-260/height branch | 4 | deferred |

The autonomous agent should keep independent modules moving when one stage is
blocked by library infrastructure.

## External inputs to discharge

The initial interface ledger identifies Bernoulli identities,
von Staudt--Clausen, Euler's even-zeta formula, a Hermite/Hurwitz-zeta integral,
the prime number theorem, p-adic completeness infrastructure, and real-analysis
infrastructure. Legendre-polynomial input is optional and only needed for the
exponent-260 branch.

See [`formalization/external_inputs.csv`](formalization/external_inputs.csv).

## Known mathematical audit status

Multiple adversarial audits and exact/floating-point diagnostic computations
have found no fatal gap. Those audits are evidence for prioritizing
formalization, not substitutes for it. The formalization must independently
resolve every proof obligation.
