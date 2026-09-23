import Zeta5.Construction.Definitions
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

namespace Zeta5

/-- The intended real series agrees with the analytic Riemann zeta value.
The equality in `ℂ` also certifies that this value is real. -/
theorem zetaFive_eq_riemannZeta : (zetaFive : ℂ) = riemannZeta 5 := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num : 1 < (5 : ℂ).re)]
  rw [zetaFive, Complex.ofReal_tsum]
  congr 1
  funext n
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_natCast]
  norm_cast

end Zeta5
