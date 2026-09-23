# Kernel-checkable finite certificates

The certificate framework uses proof-carrying interval witnesses. It does not
execute Python inside Lean or trust an externally returned Boolean.

## Interval representation and acceptance

`Zeta5.Certificate.RationalInterval` stores exact rational endpoints.
`RationalInterval.dyadic lo hi` embeds the source's integer endpoints with
exact denominator `2^192`. This permits the existing outward-rounded Python
implementation to generate candidates without making its rounding code part
of the trusted proof.

Each arithmetic operation has a Boolean acceptance rule consisting of exact
rational inequalities. The rule checks the proposed endpoints, rather than
recomputing the choice of rounded endpoints:

- addition and negation check the respective endpoint inequalities;
- multiplication checks all four endpoint products;
- reciprocal checks that the input excludes zero and reverses its endpoints,
  for both positive and negative intervals;
- square root checks nonnegativity and squared endpoint inequalities.

Each rule has a Lean theorem proving real enclosure from accepted inputs.
Powers, subtraction, and division are compositions of these operations.

## Elementary functions

The framework proves the original 64-term logarithm remainder, including the
factor `129` in its denominator, and the original 80-term arctangent remainder.
It also proves the half-angle reduction with its range conditions and uses
Mathlib's exact Machin identity for pi. Signed binary logarithm scaling and
monotonic endpoint evaluation have checked interfaces.

`Enclosure x I` is a finite certificate indexed by its actual real expression
`x` and proposed interval `I`. Elementary-function constructors require
certificates for the exact polynomial and remainder expressions in the
source formulas. Unrelated numerical bounds cannot satisfy those types.
Every numerical acceptance condition must itself have a kernel-checked
proof that the corresponding exact Boolean check equals `true`.

`Zeta5.Certificate.interval_soundness` proves by induction on this certificate
that `x` belongs to `I`. There is no constructor accepting an arbitrary
assertion of the desired enclosure. Lean's ordinary equality transport can
be used to connect algebraically equal expressions, with a checked equality
proof. Candidate witnesses can be generated outside Lean; acceptance and
soundness remain inside its kernel. Use proof-producing arithmetic or kernel
reduction for the Boolean checks, never native evaluation.

This is an equivalent proof-producing certificate path for the draft's
interval-checker contract. The general interval representation is broader
than dyadics, while the supplied source witness embedding retains exactly
192 bits and the original mathematical constants.

The potential-cell and energy/norm targets remain pending until their
specific witnesses have been constructed and connected to the actual source
expressions. Proving the checker alone does not prove those bounds.

## Arithmetic integrals

The outer-integral proof checks all 11 affine branches of the actual source
expression and integrates them over their complete ordered partition.
The inner-integral proof checks all 143 branches of the original Gamma
integral and scalar term, including the auxiliary three-strip integrals.
The generator `scripts/generate_inner_branches.py` chooses candidate floor
values and strips, but Lean proves their inequalities over the whole open
domain. The exact integral sum is then proved in Lean.

Finite endpoints are handled by interval-integral congruence on open
intervals, justified by null singleton sets. No integral value is inferred
from sampled points or from Python's success.
