# Dependency graph

The declaration CSV now records three unconditional proofs, one conditional
endpoint, nine definitions, and a partial degree target. The finite potential
and integral certificates still have only Python verification; the final
rational margins have separate Lean proofs. The graph below is the planned
mathematical dependency graph, not a generated inventory of Lean code.
The generic `EXT_REAL_ANALYSIS` interface must be split into actual imported
or proved declarations as implementation proceeds; it is not permission to
introduce an omnibus axiom.

## Main proof

```text
Definitions ──> actual GK, DeltaK, SK, FK, QKM
    │                      │
    │                      ├─> degree h
    │                      └─> positive moment representation ─> positivity
    │
    ├─> integer-valued polynomials ─> small-prime determinant bound ─┐
    │                                                             │
    ├─> restricted series / principal parts                        │
    │     ├─> integral extension                                   │
    │     └─> reflection + difference ─> distribution               │
    │                └─> inner CRT weights ─> inner valuation ──────┤
    │                                                             ├─> integrality
    └─> polynomial correction + field rank                         │
          └─> outer CRT weights ─> outer valuation ────────────────┘

inner counts + scalar valuations ─> uniform inner limit ─┐
outer counts + scalar valuations ─> uniform outer limit ─┤
PNT ─> weighted prime sums ──────────────────────────────┤
exact inner/outer integrals + periodic tail ─────────────┴─> log m / K² <= AM

interval soundness + rational data ─> comparison measure certificate ─┐
Gaussian kernel ─> zero-mass energy ─> circle regularization ──────────┤
positive moments ─> determinant integral ─────────────────────────────┤
confinement + scaling + factorial cancellation ──────────────────────┴─> log F / K² <= U

integrality + degree + positivity + both growth bounds + exact margins
   └─> integer polynomials with positive exp(-c n²) values
         └─> elementary rational-evaluation contradiction
               └─> Irrational zetaFive
                     + bridge to the intended Riemann-zeta value
```

The implementation may reuse a generic conditional theorem early. That
conditional theorem is a distinct declaration (`irrational_of_inputs`). Its
hypotheses remain visible, and it does not count as the unconditional endpoint.

## Optional branch

```text
positive moments + residue coefficient matrix + Legendre exterior bound
 + certified kappa < 6933/500
   └─> relative matrix norm
         ├─> M=100000 decay + positivity under perturbation ─> exponent 260
         └─> coefficient height < exp(13 K²)

integrality + positive rational content ─> primitive normalization bounds
```

## Critical statement reviews

1. The functional has only simple allowed poles, with coefficientwise scalar extension.
2. Gauss valuations cover every polynomial coefficient, not a selected residue or specialization.
3. The local distribution parameter is `Y=p^5 X + Cp` with the sign shown in the paper.
4. The correction has rank over the field, not only over a residue field.
5. All signs in the normalizing prime product are preserved.
6. The fixed cutoff precedes every asymptotic limit.
7. The logarithmic kernel has a proved null diagonal; Lean's totalized log at zero cannot replace this condition.
8. All exact certificate bounds are connected to the actual rational data and the actual external field.
9. The final theorem refers to the real zeta series, not an arbitrary real satisfying assumptions.
