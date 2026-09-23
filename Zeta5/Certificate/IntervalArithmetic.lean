import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Exact endpoint checks for outward-rounded rational intervals.
Dyadic source witnesses are represented exactly as rationals with denominator
`2^192`. Each Boolean acceptance rule has a real-enclosure theorem. -/

namespace Zeta5.Certificate

structure RationalInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

namespace RationalInterval

def dyadic (lo hi : ℤ) : RationalInterval := ⟨lo / (2 ^ 192), hi / (2 ^ 192)⟩
def Contains (I : RationalInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

def checkRat (I : RationalInterval) (q : ℚ) : Bool := decide (I.lo ≤ q ∧ q ≤ I.hi)
def checkAdd (A B C : RationalInterval) : Bool :=
  decide (C.lo ≤ A.lo + B.lo ∧ A.hi + B.hi ≤ C.hi)
def checkNeg (A C : RationalInterval) : Bool := decide (C.lo ≤ -A.hi ∧ -A.lo ≤ C.hi)
def checkMul (A B C : RationalInterval) : Bool :=
  decide (C.lo ≤ A.lo * B.lo ∧ C.lo ≤ A.lo * B.hi ∧
    C.lo ≤ A.hi * B.lo ∧ C.lo ≤ A.hi * B.hi ∧
    A.lo * B.lo ≤ C.hi ∧ A.lo * B.hi ≤ C.hi ∧
    A.hi * B.lo ≤ C.hi ∧ A.hi * B.hi ≤ C.hi)
def checkInv (A C : RationalInterval) : Bool :=
  decide ((0 < A.lo ∨ A.hi < 0) ∧ C.lo ≤ 1 / A.hi ∧ 1 / A.lo ≤ C.hi)
def checkSqrt (A C : RationalInterval) : Bool :=
  decide (0 ≤ A.lo ∧ 0 ≤ C.lo ∧ 0 ≤ C.hi ∧ C.lo ^ 2 ≤ A.lo ∧ A.hi ≤ C.hi ^ 2)

theorem checkRat_sound (I : RationalInterval) (q : ℚ) (h : I.checkRat q = true) :
    I.Contains (q : ℝ) := by
  have h' : I.lo ≤ q ∧ q ≤ I.hi := of_decide_eq_true h
  change (I.lo : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ I.hi
  exact_mod_cast h'

theorem checkAdd_sound {A B C : RationalInterval} {x y : ℝ}
    (hx : A.Contains x) (hy : B.Contains y) (h : checkAdd A B C = true) :
    C.Contains (x + y) := by
  have h' : C.lo ≤ A.lo + B.lo ∧ A.hi + B.hi ≤ C.hi := of_decide_eq_true h
  have hl : (C.lo : ℝ) ≤ A.lo + B.lo := by exact_mod_cast h'.1
  have hu : (A.hi : ℝ) + B.hi ≤ C.hi := by exact_mod_cast h'.2
  exact ⟨hl.trans (add_le_add hx.1 hy.1), (add_le_add hx.2 hy.2).trans hu⟩

theorem checkNeg_sound {A C : RationalInterval} {x : ℝ}
    (hx : A.Contains x) (h : checkNeg A C = true) : C.Contains (-x) := by
  have h' : C.lo ≤ -A.hi ∧ -A.lo ≤ C.hi := of_decide_eq_true h
  have hl : (C.lo : ℝ) ≤ -(A.hi : ℝ) := by exact_mod_cast h'.1
  have hu : -(A.lo : ℝ) ≤ C.hi := by exact_mod_cast h'.2
  exact ⟨hl.trans (neg_le_neg hx.2), (neg_le_neg hx.1).trans hu⟩

private theorem rectangle_lower {a b c d l x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (h₀ : l ≤ a * c) (h₁ : l ≤ a * d) (h₂ : l ≤ b * c) (h₃ : l ≤ b * d) :
    l ≤ x * y := by
  by_cases hy₀ : 0 ≤ y
  · have hxy := mul_le_mul_of_nonneg_right hx.1 hy₀
    by_cases ha : 0 ≤ a
    · exact (h₀.trans (mul_le_mul_of_nonneg_left hy.1 ha)).trans hxy
    · exact (h₁.trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge ha))).trans hxy
  · have hxy := mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy₀)
    by_cases hb : 0 ≤ b
    · exact (h₂.trans (mul_le_mul_of_nonneg_left hy.1 hb)).trans hxy
    · exact (h₃.trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hb))).trans hxy

theorem checkMul_sound {A B C : RationalInterval} {x y : ℝ}
    (hx : A.Contains x) (hy : B.Contains y) (h : checkMul A B C = true) :
    C.Contains (x * y) := by
  have h' : C.lo ≤ A.lo * B.lo ∧ C.lo ≤ A.lo * B.hi ∧
    C.lo ≤ A.hi * B.lo ∧ C.lo ≤ A.hi * B.hi ∧
    A.lo * B.lo ≤ C.hi ∧ A.lo * B.hi ≤ C.hi ∧
    A.hi * B.lo ≤ C.hi ∧ A.hi * B.hi ≤ C.hi := of_decide_eq_true h
  have hr : (C.lo : ℝ) ≤ A.lo * B.lo ∧ (C.lo : ℝ) ≤ A.lo * B.hi ∧
    (C.lo : ℝ) ≤ A.hi * B.lo ∧ (C.lo : ℝ) ≤ A.hi * B.hi ∧
    (A.lo : ℝ) * B.lo ≤ C.hi ∧ (A.lo : ℝ) * B.hi ≤ C.hi ∧
    (A.hi : ℝ) * B.lo ≤ C.hi ∧ (A.hi : ℝ) * B.hi ≤ C.hi := by exact_mod_cast h'
  rcases hr with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  refine ⟨rectangle_lower hx hy h₀ h₁ h₂ h₃, ?_⟩
  have hn := rectangle_lower ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩ hy
    (by nlinarith : -(C.hi : ℝ) ≤ -(A.hi : ℝ) * B.lo)
    (by nlinarith : -(C.hi : ℝ) ≤ -(A.hi : ℝ) * B.hi)
    (by nlinarith : -(C.hi : ℝ) ≤ -(A.lo : ℝ) * B.lo)
    (by nlinarith : -(C.hi : ℝ) ≤ -(A.lo : ℝ) * B.hi)
  nlinarith

theorem checkInv_sound {A C : RationalInterval} {x : ℝ}
    (hx : A.Contains x) (h : checkInv A C = true) : C.Contains (1 / x) := by
  have h' : (0 < A.lo ∨ A.hi < 0) ∧ C.lo ≤ 1 / A.hi ∧ 1 / A.lo ≤ C.hi :=
    of_decide_eq_true h
  have hl : (C.lo : ℝ) ≤ 1 / (A.hi : ℝ) := by exact_mod_cast h'.2.1
  have hu : 1 / (A.lo : ℝ) ≤ C.hi := by exact_mod_cast h'.2.2
  rcases h'.1 with hp | hn
  · have hp' : (0 : ℝ) < A.lo := by exact_mod_cast hp
    exact ⟨hl.trans (one_div_le_one_div_of_le (hp'.trans_le hx.1) hx.2),
      (one_div_le_one_div_of_le hp' hx.1).trans hu⟩
  · have hn' : (A.hi : ℝ) < 0 := by exact_mod_cast hn
    exact ⟨hl.trans (one_div_le_one_div_of_neg_of_le hn' hx.2),
      (one_div_le_one_div_of_neg_of_le (hx.2.trans_lt hn') hx.1).trans hu⟩

theorem checkSqrt_sound {A C : RationalInterval} {x : ℝ}
    (hx : A.Contains x) (h : checkSqrt A C = true) : C.Contains (Real.sqrt x) := by
  have h' : 0 ≤ A.lo ∧ 0 ≤ C.lo ∧ 0 ≤ C.hi ∧ C.lo ^ 2 ≤ A.lo ∧ A.hi ≤ C.hi ^ 2 :=
    of_decide_eq_true h
  have hr : (0 : ℝ) ≤ A.lo ∧ (0 : ℝ) ≤ C.lo ∧ (0 : ℝ) ≤ C.hi ∧
    (C.lo : ℝ) ^ 2 ≤ A.lo ∧ (A.hi : ℝ) ≤ (C.hi : ℝ) ^ 2 := by exact_mod_cast h'
  rcases hr with ⟨ha, hc, hd, hl, hu⟩
  have hsq := Real.sq_sqrt (ha.trans hx.1)
  have hpos := Real.sqrt_nonneg x
  constructor <;> nlinarith [hx.1, hx.2]

end RationalInterval
end Zeta5.Certificate
