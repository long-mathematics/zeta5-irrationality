import Zeta5.Construction.Definitions
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Fold
import Mathlib.Tactic

/-! The unchanged signed prime normalization from Sections 4–5.
Definitions are total; all source estimates require `Admissible n M`.
All half-integer weights are represented by twice their value in `ℤ`. -/

namespace Zeta5

open Polynomial

def Admissible (n M : ℕ) : Prop := 0 < n ∧ 40 ≤ M ∧ 200 * M ^ 2 ≤ K n

/-- The number of labels in an ordinary square class. -/
def classCount (A p a : ℕ) : ℕ :=
  ((Finset.Icc 1 A).filter fun j ↦ j % p = a % p ∨ j % p = (p - a) % p).card

def ordinaryClasses (p : ℕ) : Finset ℕ := Finset.Icc 1 ((p - 1) / 2)
def zeroBlockSize (M : ℕ) : ℕ := 4 * M + 10
def innerBudget (n M p : ℕ) : ℕ := h n - zeroBlockSize M + 3 * (N n - N n / p)
def innerBaseline (n M p : ℕ) : ℕ := innerBudget n M p / ((p - 1) / 2)
def innerExtras (n M p : ℕ) : ℕ := innerBudget n M p % ((p - 1) / 2)

/-- Position in the order of decreasing class count, then increasing label. -/
def classPosition (n p a : ℕ) : ℕ :=
  ((ordinaryClasses p).filter fun b ↦
    classCount (K n) p a < classCount (K n) p b ∨
      (classCount (K n) p a = classCount (K n) p b ∧ b < a)).card

def extraRow (n M p a : ℕ) : ℕ :=
  if classPosition n p a < innerExtras n M p then 1 else 0

def innerBlockSize (n M p a : ℕ) : ℕ :=
  innerBaseline n M p - 3 * classCount (N n) p a + extraRow n M p a

def innerOrdinaryWeightTwice (n p a i : ℕ) : ℤ :=
  2 * (i : ℤ) + 6 * (classCount (N n) p a : ℤ) - (classCount (K n) p a : ℤ) - 4

def innerZeroWeightTwice (n M p i : ℕ) : ℤ :=
  (ordinaryClasses p).fold min
    (4 * (i : ℤ) + 12 * (N n / p : ℕ) - 2 * (K n / p : ℕ) + 1)
    (fun a ↦ 2 * ((innerBaseline n M p : ℤ) + extraRow n M p a) -
      (classCount (K n) p a : ℤ) - 4)

def gammaInner (n M p : ℕ) : ℤ :=
  (∑ i ∈ Finset.range (zeroBlockSize M), innerZeroWeightTwice n M p i) +
    ∑ a ∈ ordinaryClasses p,
      ∑ i ∈ Finset.range (innerBlockSize n M p a), innerOrdinaryWeightTwice n p a i

def outerRankBound (n p : ℕ) : ℤ := max 0 ((K n : ℤ) + 4 * N n - 2 * p + 2)
def outerRemainder (n p : ℕ) : ℕ := K n % p
def outerOverlap (n p : ℕ) : ℤ := max 0 ((N n : ℤ) + outerRemainder n p - p + 1)
def outerRemovedCount (n p : ℕ) : ℤ :=
  (min (N n) (outerRemainder n p) : ℕ) + outerOverlap n p

/-- Includes the source convention `γ_out = 0` when `p > K`. -/
def gammaOuter (n p : ℕ) : ℤ :=
  if K n < p then 0
  else if K n < 2 * p then
    -7 * ((K n : ℤ) - p) + 6 * outerRemovedCount n p - 1 -
      min (outerRankBound n p) ((p : ℤ) - 1 - N n + outerOverlap n p)
  else
    -7 * ((K n : ℤ) - p) + 3 + 12 * N n + 5 * outerRemovedCount n p -
      min (outerRankBound n p) ((p : ℤ) + outerOverlap n p)

/-- Signed lower bound, including the `v_p(24)` loss at small primes. -/
def primeLowerBound (n M p : ℕ) : ℤ :=
  if p * M ≤ K n then
    -6 * (h n : ℤ) * Nat.log p (5 * K n) - (h n : ℤ) * padicValNat p 24
  else if 3 * p ≤ K n then
    padicValRat p (scalarSK n) + gammaInner n M p
  else padicValRat p (scalarSK n) + gammaOuter n p

/-- Exact prime product with integer powers; no truncation of positive bounds. -/
def normalizationFactor (n M : ℕ) : ℚ :=
  ∏ p ∈ (Finset.Icc 1 (2 * h n)).filter Nat.Prime, (p : ℚ) ^ (-primeLowerBound n M p)

/-- The actual normalized polynomial; integrality is a separate theorem. -/
noncomputable def QKM (n M : ℕ) : ℚ[X] := C (normalizationFactor n M) * FK n

theorem normalizationFactor_pos (n M : ℕ) : 0 < normalizationFactor n M := by
  apply Finset.prod_pos
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2
  exact zpow_pos (by exact_mod_cast hp'.pos) _

end Zeta5
