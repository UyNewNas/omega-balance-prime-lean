import OmegaBalance.F3PadicLogCompositionFinite
import Mathlib.RingTheory.PowerSeries.Trunc

namespace OmegaBalance

open Filter Topology

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem hasSum_f3PadicLog_all_coeff {z : ℚ_[3]} (hz : ‖z‖ < 1) :
    HasSum
      (fun d : ℕ =>
        PowerSeries.coeff d (PowerSeries.log ℚ_[3]) * z ^ d)
      (f3PadicLogOnePlus z) := by
  rw [← hasSum_nat_add_iff' 1]
  simpa [PowerSeries.coeff_log] using
    (hasSum_f3PadicLog_powerSeries_coeff hz)

theorem f3PadicLogTrunc_eval_eq_sum_range
    (z : ℚ_[3]) (N : ℕ) :
    (PowerSeries.trunc N (PowerSeries.log ℚ_[3])).eval z =
      ∑ d ∈ Finset.range N,
        PowerSeries.coeff d (PowerSeries.log ℚ_[3]) * z ^ d := by
  simpa using
    (PowerSeries.eval₂_trunc_eq_sum_range
      (R := ℚ_[3]) z (RingHom.id ℚ_[3]) N (PowerSeries.log ℚ_[3]))

theorem tendsto_f3PadicLogTrunc_eval {z : ℚ_[3]} (hz : ‖z‖ < 1) :
    Tendsto
      (fun N : ℕ => (PowerSeries.trunc N (PowerSeries.log ℚ_[3])).eval z)
      atTop (𝓝 (f3PadicLogOnePlus z)) := by
  simpa only [f3PadicLogTrunc_eval_eq_sum_range] using
    (hasSum_f3PadicLog_all_coeff hz).tendsto_sum_nat

theorem f3PadicLogTrunc_comp_eval_one
    (x y : ℚ_[3]) (N : ℕ) :
    ((PowerSeries.trunc N (PowerSeries.log ℚ_[3])).comp
        (f3PadicLogMulPolynomial x y)).eval 1 =
      (PowerSeries.trunc N (PowerSeries.log ℚ_[3])).eval
        (x + y + x * y) := by
  rw [Polynomial.eval_comp, f3PadicLogMulPolynomial_eval_one]

theorem tendsto_f3PadicLogTrunc_product_eval
    {x y : ℚ_[3]} (hxy : ‖x + y + x * y‖ < 1) :
    Tendsto
      (fun N : ℕ =>
        ((PowerSeries.trunc N (PowerSeries.log ℚ_[3])).comp
          (f3PadicLogMulPolynomial x y)).eval 1)
      atTop (𝓝 (f3PadicLogOnePlus (x + y + x * y))) := by
  simpa only [f3PadicLogTrunc_comp_eval_one] using
    (tendsto_f3PadicLogTrunc_eval hxy)

end OmegaBalance
