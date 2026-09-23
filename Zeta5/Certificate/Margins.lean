import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-! Exact final arithmetic from Appendix B.3. `norm_num` produces kernel-checked
proof terms; the Python verifier is not a premise of these declarations.
The analytic estimates that use these constants remain separate obligations. -/

namespace Zeta5.Certificate

def innerIntegralValue : ℚ := 322437603634266857629 / 7535670527041937280000
def outerIntegralValue : ℚ := 127751 / 96000
def tailUpperAtTwenty : ℚ := -2689 / 48000
def aStar : ℚ := 9928298118277006344769 / 7535670527041937280000
def aBound (M : ℚ) : ℚ :=
  aStar + 7 * (37 / 40) / M - (2923 / 240 - 1 / 4) / M ^ 2 + 32 / M ^ 3
def realBound : ℚ := -2733991 / 2000000

theorem aStar_identity :
    aStar = outerIntegralValue + innerIntegralValue + tailUpperAtTwenty := by
  norm_num [aStar, outerIntegralValue, innerIntegralValue, tailUpperAtTwenty]

/-- Both exact identities and their strict signs, without an external oracle. -/
theorem final_rational_margins :
    -1600 * (aBound 200 + realBound) - 139 / 5 =
      3089837638249482469 / 58872425992515135000 ∧
    0 < -1600 * (aBound 200 + realBound) - 139 / 5 ∧
    -1600 * (aBound 100000 + realBound) - 7907 / 100 =
      29873543950273155160680943 / 3679526624532195937500000000 ∧
    0 < -1600 * (aBound 100000 + realBound) - 7907 / 100 := by
  norm_num [aBound, aStar, realBound]

end Zeta5.Certificate
