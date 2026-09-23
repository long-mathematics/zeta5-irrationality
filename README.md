# ζ(5) Irrationality — Lean Formalization

This repository is an autonomous Lean formalization project for the proof in
Aabir Fauzan, **“ζ(5) is irrational”** (17 September 2026).

The mathematical source claims the first proof that the individual value
`ζ(5)` is irrational. Because of the significance of that claim, this
repository is organized around reproducibility, explicit dependency tracking,
exact finite certificates, and a kernel-level audit of the eventual Lean
endpoint.

## Current status

**Formalization status: 3 / 49 planned targets proved unconditionally;
1 conditional theorem and 9 construction definitions implemented.**

No Lean proof of irrationality is claimed yet. The repository currently
contains a pinned Lean/Mathlib project, an expanded formalization-oriented
working edition of the paper, exact finite certificate verification, a
49-target declaration ledger, an external-input ledger, and CI/integrity
checks. The first checked proofs establish the generic integer-polynomial
criterion, the real-series/Riemann-zeta bridge, and the final rational margins.
The conditional endpoint still requires integrality, positivity, and decay
for the actual source polynomial. The primary endpoint is:

```lean
Zeta5.zeta_five_irrational
```

The endpoint counts as complete only when it builds without `sorry`, `admit`,
or project-owned axioms, every provisional input has been discharged, and
`#print axioms Zeta5.zeta_five_irrational` has been audited.

See [`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md) for the live status and
[`AGENTS.md`](AGENTS.md) for the autonomous formalization protocol.

## Mathematical source and working edition

- [Read the compiled working edition (PDF, 41 pages)](paper/zeta5_formalization_draft.pdf)
- [Expanded LaTeX working edition](paper/zeta5_formalization_draft.tex)
- Rebuild the PDF locally with `make pdf` (requires LaTeX and `latexmk`)
- [Repair and audit-provenance log](REPAIRS.md)
- [Formalization dependency graph](formalization/dependency_graph.md)
- [Declaration ledger](formalization/declarations.csv)
- [External-input ledger](formalization/external_inputs.csv)

The LaTeX source in this repository is a reconstructed and expanded working
edition prepared for formalization. It is **not** Fauzan's original LaTeX and
is **not** an author-approved revision. The underlying mathematical claims
remain attributed to Aabir Fauzan.

The compiled PDF is the working edition used for this ongoing Lean
formalization attempt. It presents the mathematical argument and proof
obligations; it is not evidence that the Lean irrationality theorem has been
completed. See the [live formalization status](FORMALIZATION_STATUS.md).

The working edition records two important clarifications established during
audit:

1. Original equation (5.9) contains a **multiplicative** indicator; an earlier
   audit misread the positive-part notation as an additive indicator. The
   working edition preserves the source formula.
2. `K ≥ 200 M²` is an admissibility condition for the normalizer, not an
   effective threshold for the eventual decay assertion.

## Exact finite verification

The finite numerical certificates are independently reproducible with the
Python standard library only:

```sh
python3 certificates/verify.py
```

The checked package covers all 684 cells of the potential certificate, all
143 symbolic inner pieces, all 11 outer affine pieces, the exact rational
integrals, energy/scalar constants, and the final rational margins. Acceptance
uses exact rational arithmetic and outward-rounded dyadic interval arithmetic,
not floating-point comparisons.

These computations support the source proof but are **not** themselves a Lean
proof. The formalization must replay them through a sound kernel-checkable
certificate path.

## Lean build

The project follows the `long-mathematics` Lean conventions and pins both Lean
and Mathlib.

```sh
lake build
python3 -B -m unittest discover -s scripts -p 'test_*.py'
python3 -B scripts/audit_lean.py
```

Convenience targets:

```sh
make lean
make audit
make verify
make pdf
make check
```

The optional rational-approximation exponent `260` and coefficient-height
results are deliberately secondary. The autonomous project should first close
and audit the unconditional irrationality theorem.

## Repository integrity policy

- Formalize the actual determinant construction; do not replace it with an
  abstract assumption encoding the desired conclusion.
- Conditional scaffolds are allowed only when every missing hypothesis remains
  explicit in the theorem type and status ledger.
- Do not weaken a public target to make Lean accept it.
- Do not introduce project-owned axioms.
- A clean build is not sufficient: statement correspondence and transitive
  axiom/dependency audits are required.
- Mathematical discrepancies go in `BLOCKERS.md` with a precise statement and
  attempted repair.

## Provenance

The reconstructed working edition records the SHA-256 of the user-supplied
source PDF as

```text
a42c05ccc46b9a7c36428913453c4617202c59109713ba20f464ab9ec640d0da
```

The repository does not treat the supplied human/AI audits or finite
experiments as proof premises.

## Licensing

Repository code and infrastructure are distributed under the existing
[MIT License](LICENSE). The reconstructed working edition in `paper/` remains
explicitly attributed to Aabir Fauzan as the author of the underlying
mathematical manuscript; this repository does not represent the reconstruction
as Fauzan's original source or as an author-approved revision.
