import Zeta5.Certificate.ElementaryIntervals

/-! Proof-carrying interval certificates for Appendix A.

A certificate contains exact rational endpoint checks and recursively checked
certificates for its operands. `dyadic` embeds the source's 192-bit integer
witnesses exactly. The witness generator may choose rounded endpoints, but
no choice is accepted without its rational inequalities being proved in Lean.

The polynomial and remainder operands of elementary-function rules are
indexed by their actual real expressions. Thus an unrelated enclosed value
cannot be substituted for a series or its remainder. -/

namespace Zeta5.Certificate

open RationalInterval

set_option maxRecDepth 4096

/-- A closed calculus of checked enclosures. There is no constructor accepting
an arbitrary assertion that the desired value lies in its claimed interval. -/
inductive Enclosure : ℝ → RationalInterval → Type
  | rational (q : ℚ) (I : RationalInterval) (h : checkRat I q = true) : Enclosure (q : ℝ) I
  | add {x y : ℝ} {A B : RationalInterval} (a : Enclosure x A) (b : Enclosure y B)
      (C : RationalInterval) (h : checkAdd A B C = true) : Enclosure (x + y) C
  | neg {x : ℝ} {A : RationalInterval} (a : Enclosure x A) (C : RationalInterval)
      (h : checkNeg A C = true) : Enclosure (-x) C
  | mul {x y : ℝ} {A B : RationalInterval} (a : Enclosure x A) (b : Enclosure y B)
      (C : RationalInterval) (h : checkMul A B C = true) : Enclosure (x * y) C
  | inv {x : ℝ} {A : RationalInterval} (a : Enclosure x A) (C : RationalInterval)
      (h : checkInv A C = true) : Enclosure (1 / x) C
  | sqrt {x : ℝ} {A : RationalInterval} (a : Enclosure x A) (C : RationalInterval)
      (h : checkSqrt A C = true) : Enclosure (Real.sqrt x) C
  | logReduced {x : ℝ} {A P R : RationalInterval} (a : Enclosure x A)
      (p : Enclosure (logPartial ((x - 1) / (x + 1)) 64) P)
      (r : Enclosure (2 * ((x - 1) / (x + 1)) ^ 129 /
        (129 * (1 - ((x - 1) / (x + 1)) ^ 2))) R)
      (C : RationalInterval) (h : checkLogReduced A P R C = true) : Enclosure (Real.log x) C
  | atanReduced {x : ℝ} {A P R : RationalInterval} (a : Enclosure x A)
      (p : Enclosure (atanPartial x 80) P) (r : Enclosure (x ^ 161 / 161) R)
      (C : RationalInterval) (h : checkAtanReduced A P R C = true) : Enclosure (Real.arctan x) C
  | logMonotone {x : ℝ} {A L U : RationalInterval} (a : Enclosure x A)
      (l : Enclosure (Real.log A.lo) L) (u : Enclosure (Real.log A.hi) U)
      (C : RationalInterval) (hd : checkLogDomain A = true)
      (h : checkMonotone L U C = true) : Enclosure (Real.log x) C
  | atanMonotone {x : ℝ} {A L U : RationalInterval} (a : Enclosure x A)
      (l : Enclosure (Real.arctan A.lo) L) (u : Enclosure (Real.arctan A.hi) U)
      (C : RationalInterval) (h : checkMonotone L U C = true) : Enclosure (Real.arctan x) C
  | logScale (q : ℚ) (e : ℤ) (r : ℚ) {C : RationalInterval}
      (p : Enclosure ((e : ℝ) * Real.log 2 + Real.log (r : ℝ)) C)
      (h : checkLogScale q e r = true) : Enclosure (Real.log (q : ℝ)) C
  | halfAngle {x : ℝ} {A C : RationalInterval} (a : Enclosure x A)
      (p : Enclosure (2 * Real.arctan (x / (1 + Real.sqrt (1 + x ^ 2)))) C)
      (h : checkHalfAngleDomain A = true) : Enclosure (Real.arctan x) C
  | atanReciprocal {x : ℝ} {A C : RationalInterval} (a : Enclosure x A)
      (p : Enclosure (Real.pi / 2 - Real.arctan (1 / x)) C)
      (h : checkLogDomain A = true) : Enclosure (Real.arctan x) C
  | pi {C : RationalInterval}
      (p : Enclosure (16 * Real.arctan (1 / 5 : ℝ) - 4 * Real.arctan (1 / 239 : ℝ)) C) :
      Enclosure Real.pi C

/-- Soundness of every accepted interval certificate. Acceptance consists of
kernel-checked constructors and exact Boolean endpoint checks; no external
Boolean oracle or native evaluation is a premise. -/
theorem interval_soundness {x : ℝ} {I : RationalInterval} (c : Enclosure x I) : I.Contains x := by
  induction c with
  | rational q I h => exact checkRat_sound I q h
  | add a b C h ha hb => exact checkAdd_sound ha hb h
  | neg a C h ha => exact checkNeg_sound ha h
  | mul a b C h ha hb => exact checkMul_sound ha hb h
  | inv a C h ha => exact checkInv_sound ha h
  | sqrt a C h ha => exact checkSqrt_sound ha h
  | logReduced a p r C h ha hp hr => exact checkLogReduced_sound ha hp hr h
  | atanReduced a p r C h ha hp hr => exact checkAtanReduced_sound ha hp hr h
  | logMonotone a l u C hd h ha hl hu => exact checkLogMonotone_sound ha hl hu hd h
  | atanMonotone a l u C h ha hl hu => exact checkAtanMonotone_sound ha hl hu h
  | logScale q e r p h hp => exact checkLogScale_sound q e r hp h
  | halfAngle a p h ha hp => exact checkHalfAngle_sound ha hp h
  | atanReciprocal a p h ha hp => exact checkAtanReciprocal_sound ha hp h
  | pi p hp => simpa only [machin_identity] using hp

end Zeta5.Certificate
