import Zeta5.Certificate.IntervalArithmetic
import Zeta5.Certificate.SeriesBounds

/-! Elementary-function acceptance rules. The polynomial and remainder
premises are themselves real-enclosure obligations, discharged by the
arithmetic interval rules when replaying a finite witness. -/

namespace Zeta5.Certificate
namespace RationalInterval

def checkLogReduced (A P R C : RationalInterval) : Bool :=
  decide (1 ≤ A.lo ∧ A.hi ≤ 2 ∧ C.lo ≤ 2 * P.lo ∧ 2 * P.hi + R.hi ≤ C.hi)
def checkAtanReduced (A P R C : RationalInterval) : Bool :=
  decide (0 ≤ A.lo ∧ A.hi ≤ 1 / 2 ∧ C.lo ≤ P.lo - R.hi ∧ P.hi + R.hi ≤ C.hi)

theorem checkLogReduced_sound {A P R C : RationalInterval} {x : ℝ}
    (hx : A.Contains x)
    (hp : P.Contains (logPartial ((x - 1) / (x + 1)) 64))
    (hr : R.Contains (2 * ((x - 1) / (x + 1)) ^ 129 /
      (129 * (1 - ((x - 1) / (x + 1)) ^ 2))))
    (h : checkLogReduced A P R C = true) : C.Contains (Real.log x) := by
  have h' : 1 ≤ A.lo ∧ A.hi ≤ 2 ∧ C.lo ≤ 2 * P.lo ∧ 2 * P.hi + R.hi ≤ C.hi :=
    of_decide_eq_true h
  have hc : (1 : ℝ) ≤ A.lo ∧ (A.hi : ℝ) ≤ 2 ∧
    (C.lo : ℝ) ≤ 2 * (P.lo : ℝ) ∧ 2 * (P.hi : ℝ) + R.hi ≤ C.hi := by
    exact_mod_cast h'
  have hx₁ : 1 ≤ x := hc.1.trans hx.1
  have hx₂ : x ≤ 2 := hx.2.trans hc.2.1
  let z := (x - 1) / (x + 1)
  have hd : 0 < x + 1 := by linarith
  have hz₀ : 0 ≤ z := div_nonneg (by linarith) hd.le
  have hz₁ : z < 1 := (div_lt_iff₀ hd).mpr (by linarith)
  have heq : (1 + z) / (1 - z) = x := by
    dsimp [z]
    field_simp
    ring
  have he := log_sixty_four_remainder z hz₀ hz₁
  rw [heq] at he
  change (P.lo : ℝ) ≤ logPartial z 64 ∧ logPartial z 64 ≤ P.hi at hp
  change (R.lo : ℝ) ≤ 2 * z ^ 129 / (129 * (1 - z ^ 2)) ∧
    2 * z ^ 129 / (129 * (1 - z ^ 2)) ≤ R.hi at hr
  constructor <;> linarith [hc.2.2.1, hc.2.2.2, hp.1, hp.2, hr.2, he.1, he.2]

theorem checkAtanReduced_sound {A P R C : RationalInterval} {x : ℝ}
    (hx : A.Contains x) (hp : P.Contains (atanPartial x 80))
    (hr : R.Contains (x ^ 161 / 161)) (h : checkAtanReduced A P R C = true) :
    C.Contains (Real.arctan x) := by
  have h' : 0 ≤ A.lo ∧ A.hi ≤ 1 / 2 ∧ C.lo ≤ P.lo - R.hi ∧ P.hi + R.hi ≤ C.hi :=
    of_decide_eq_true h
  have hc : (0 : ℝ) ≤ A.lo ∧ (A.hi : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) ∧
    (C.lo : ℝ) ≤ (P.lo : ℝ) - R.hi ∧ (P.hi : ℝ) + R.hi ≤ C.hi := by exact_mod_cast h'
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
  have he := abs_le.mp (atan_eighty_remainder x (hc.1.trans hx.1) (by linarith [hx.2, hc.2.1]))
  constructor <;> linarith [hc.2.2.1, hc.2.2.2, hp.1, hp.2, hr.2, he.1, he.2]

def checkMonotone (L U C : RationalInterval) : Bool := decide (C.lo ≤ L.lo ∧ U.hi ≤ C.hi)
def checkLogDomain (A : RationalInterval) : Bool := decide (0 < A.lo)
def checkHalfAngleDomain (A : RationalInterval) : Bool := decide (0 ≤ A.lo ∧ A.hi ≤ 1)
def checkLogScale (q : ℚ) (e : ℤ) (r : ℚ) : Bool := decide (q = 2 ^ e * r ∧ 0 < r)

theorem checkMonotone_sound {A L U C : RationalInterval} {x : ℝ} {f : ℝ → ℝ}
    (hx : A.Contains x) (hl : L.Contains (f A.lo)) (hu : U.Contains (f A.hi))
    (hmono : MonotoneOn f (Set.Icc (A.lo : ℝ) A.hi)) (h : checkMonotone L U C = true) :
    C.Contains (f x) := by
  have h' : C.lo ≤ L.lo ∧ U.hi ≤ C.hi := of_decide_eq_true h
  have hc : (C.lo : ℝ) ≤ L.lo ∧ (U.hi : ℝ) ≤ C.hi := by exact_mod_cast h'
  exact ⟨hc.1.trans (hl.1.trans (hmono ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1)),
    ((hmono hx ⟨hx.1.trans hx.2, le_rfl⟩ hx.2).trans hu.2).trans hc.2⟩

theorem checkLogMonotone_sound {A L U C : RationalInterval} {x : ℝ}
    (hx : A.Contains x) (hl : L.Contains (Real.log A.lo)) (hu : U.Contains (Real.log A.hi))
    (hd : checkLogDomain A = true) (h : checkMonotone L U C = true) : C.Contains (Real.log x) := by
  have h' : 0 < A.lo := of_decide_eq_true hd
  have ha : (0 : ℝ) < A.lo := by exact_mod_cast h'
  apply checkMonotone_sound hx hl hu ?_ h
  intro a ham b hbm hab
  exact (Real.log_le_log_iff (ha.trans_le ham.1) (ha.trans_le hbm.1)).mpr hab

theorem checkAtanMonotone_sound {A L U C : RationalInterval} {x : ℝ}
    (hx : A.Contains x) (hl : L.Contains (Real.arctan A.lo))
    (hu : U.Contains (Real.arctan A.hi)) (h : checkMonotone L U C = true) :
    C.Contains (Real.arctan x) :=
  checkMonotone_sound hx hl hu (fun _ _ _ _ hab ↦ Real.arctan_le_arctan_iff.mpr hab) h

theorem checkLogScale_sound {C : RationalInterval} (q : ℚ) (e : ℤ) (r : ℚ)
    (hp : C.Contains ((e : ℝ) * Real.log 2 + Real.log (r : ℝ)))
    (h : checkLogScale q e r = true) : C.Contains (Real.log (q : ℝ)) := by
  have h' : q = 2 ^ e * r ∧ 0 < r := of_decide_eq_true h
  have he : (q : ℝ) = (2 : ℝ) ^ e * (r : ℝ) := by
    have he₀ := congrArg (fun a : ℚ ↦ (a : ℝ)) h'.1
    push_cast at he₀
    exact he₀
  have hr : (0 : ℝ) < r := by exact_mod_cast h'.2
  rw [he, Real.log_mul (zpow_ne_zero e (by norm_num)) hr.ne', Real.log_zpow]
  exact hp

theorem checkHalfAngle_sound {A C : RationalInterval} {x : ℝ}
    (hx : A.Contains x)
    (hp : C.Contains (2 * Real.arctan (x / (1 + Real.sqrt (1 + x ^ 2)))))
    (h : checkHalfAngleDomain A = true) : C.Contains (Real.arctan x) := by
  have h' : 0 ≤ A.lo ∧ A.hi ≤ 1 := of_decide_eq_true h
  have hc : (0 : ℝ) ≤ A.lo ∧ (A.hi : ℝ) ≤ 1 := by exact_mod_cast h'
  rw [(atan_half_angle x (hc.1.trans hx.1) (hx.2.trans hc.2)).2.2]
  exact hp

theorem checkAtanReciprocal_sound {A C : RationalInterval} {x : ℝ}
    (hx : A.Contains x) (hp : C.Contains (Real.pi / 2 - Real.arctan (1 / x)))
    (h : checkLogDomain A = true) : C.Contains (Real.arctan x) := by
  have h' : 0 < A.lo := of_decide_eq_true h
  have hc : (0 : ℝ) < A.lo := by exact_mod_cast h'
  have he := Real.arctan_inv_of_pos (hc.trans_le hx.1)
  have he' : Real.pi / 2 - Real.arctan (1 / x) = Real.arctan x := by
    simpa only [one_div] using (sub_eq_iff_eq_add.mpr (by linarith :
      Real.pi / 2 = Real.arctan x + Real.arctan x⁻¹))
  rwa [he'] at hp

end RationalInterval
end Zeta5.Certificate
