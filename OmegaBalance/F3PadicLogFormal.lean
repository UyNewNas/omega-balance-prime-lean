import OmegaBalance.F3PadicLogIsometry
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Formal-coefficient bridge for the genuine 3-adic F₃ logarithm

The pinned mathlib power-series evaluator requires an `IsLinearTopology`
instance on the target. The usual topology on `ℚ_[3]` does not provide that
instance, so this module does not identify the analytic sum with
`PowerSeries.eval₂`.

Instead it records a topology-free coefficient bridge: the project logarithm
is the convergent sum of the coefficients of mathlib's formal
`PowerSeries.log`; the pinned exponential is recorded as its coefficient
tsum without asserting convergence outside its p-adic radius.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem f3PadicLogTerm_eq_powerSeries_coeff (x : ℚ_[3]) (k : ℕ) :
    f3PadicLogTerm x k =
      PowerSeries.coeff (k + 1) (PowerSeries.log ℚ_[3]) * x ^ (k + 1) := by
  simp [f3PadicLogTerm, PowerSeries.coeff_log, pow_add, div_eq_mul_inv]
  ring

theorem hasSum_f3PadicLog_powerSeries_coeff {x : ℚ_[3]} (hx : ‖x‖ < 1) :
    HasSum
      (fun k : ℕ =>
        PowerSeries.coeff (k + 1) (PowerSeries.log ℚ_[3]) * x ^ (k + 1))
      (f3PadicLogOnePlus x) := by
  rw [f3PadicLogOnePlus]
  simpa only [← f3PadicLogTerm_eq_powerSeries_coeff] using
    (summable_f3PadicLogTerm hx).hasSum

theorem f3PadicExp_eq_tsum_powerSeries_coeff (x : ℚ_[3]) :
    NormedSpace.exp x =
      ∑' k : ℕ, PowerSeries.coeff k (PowerSeries.exp ℚ_[3]) * x ^ k := by
  rw [NormedSpace.exp_eq_tsum ℚ]
  apply tsum_congr
  intro k
  simp [PowerSeries.coeff_exp, Algebra.smul_def]

theorem f3PadicFormal_exp_subst_log :
    (PowerSeries.exp ℚ_[3]).subst (PowerSeries.log ℚ_[3]) =
      1 + PowerSeries.X := by
  exact PowerSeries.subst_exp_log ℚ_[3]

theorem f3PadicFormal_log_subst_exp_sub_one :
    (PowerSeries.log ℚ_[3]).subst (PowerSeries.exp ℚ_[3] - 1) =
      PowerSeries.X := by
  exact PowerSeries.subst_log_exp_sub_one ℚ_[3]

end OmegaBalance
