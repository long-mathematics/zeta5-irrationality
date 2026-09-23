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

Current proved target count: **0 / 49**.

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
| 1 | Definitions, determinant degree, generic contradiction, conditional bridge | 13 | pending |
| 2 | Kernel-checkable finite certificates | 6 | pending |
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
