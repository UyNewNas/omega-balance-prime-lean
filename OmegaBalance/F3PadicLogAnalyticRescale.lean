import OmegaBalance.F3PadicLogFormalMul

/-!
# Analytic specialization of rescaled formal logarithms

This module is the first analytic specialization layer for the formal LOG-1
product law.  It avoids the unavailable `IsLinearTopology ℚ_[3] ℚ_[3]`
instance: rescaling by `x * X` is handled coefficientwise, and the already
proved genuine p-adic logarithm summability identifies the coefficient sum.

The remaining LOG-1 gap is only the nonlinear left-hand specialization:
identifying the coefficient sum of
`log.subst (x*X + y*X + (x*X)*(y*X))` with
`f3PadicLogOnePlus (x + y + x*y)`.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Coefficients of the formal logarithm after the linear rescaling
`X ↦ xX` are the original logarithm coefficients multiplied by `x^n`. -/
theorem f3PadicFormal_log_smul_X_coeff (x : ℚ_[3]) (n : ℕ) :
    PowerSeries.coeff n
        ((PowerSeries.log ℚ_[3]).subst (x • PowerSeries.X)) =
      x ^ n * PowerSeries.coeff n (PowerSeries.log ℚ_[3]) := by
  rw [← PowerSeries.rescale_eq_subst x (PowerSeries.log ℚ_[3])]
  exact PowerSeries.coeff_rescale (PowerSeries.log ℚ_[3]) x n

/-- The project logarithm term is exactly the corresponding positive-degree
coefficient of the linearly rescaled formal logarithm. -/
theorem f3PadicLogTerm_eq_formal_rescale_coeff (x : ℚ_[3]) (k : ℕ) :
    f3PadicLogTerm x k =
      PowerSeries.coeff (k + 1)
        ((PowerSeries.log ℚ_[3]).subst (x • PowerSeries.X)) := by
  calc
    f3PadicLogTerm x k =
        PowerSeries.coeff (k + 1) (PowerSeries.log ℚ_[3]) * x ^ (k + 1) :=
      f3PadicLogTerm_eq_powerSeries_coeff x k
    _ = x ^ (k + 1) *
        PowerSeries.coeff (k + 1) (PowerSeries.log ℚ_[3]) := by
      rw [mul_comm]
    _ = PowerSeries.coeff (k + 1)
        ((PowerSeries.log ℚ_[3]).subst (x • PowerSeries.X)) :=
      (f3PadicFormal_log_smul_X_coeff x (k + 1)).symm

/-- On the open p-adic unit ball, summing the positive-degree coefficients of
the rescaled formal logarithm gives the genuine analytic logarithm series. -/
theorem hasSum_f3PadicFormal_log_rescale_coeff {x : ℚ_[3]} (hx : ‖x‖ < 1) :
    HasSum
      (fun k : ℕ =>
        PowerSeries.coeff (k + 1)
          ((PowerSeries.log ℚ_[3]).subst (x • PowerSeries.X)))
      (f3PadicLogOnePlus x) := by
  simpa only [f3PadicFormal_log_smul_X_coeff, mul_comm] using
    hasSum_f3PadicLog_powerSeries_coeff hx

/-- Formal LOG-1 product law specialized to the two linear series `xX` and
`yX`. -/
theorem f3PadicFormal_log_mul_rescaled (x y : ℚ_[3]) :
    (PowerSeries.log ℚ_[3]).subst
        (x • PowerSeries.X + y • PowerSeries.X +
          (x • PowerSeries.X) * (y • PowerSeries.X)) =
      (PowerSeries.log ℚ_[3]).subst (x • PowerSeries.X) +
        (PowerSeries.log ℚ_[3]).subst (y • PowerSeries.X) := by
  simpa using
    f3PadicFormal_log_mul
      (x • (PowerSeries.X : PowerSeries ℚ_[3]))
      (y • (PowerSeries.X : PowerSeries ℚ_[3]))
      (by simp) (by simp)

/-- The coefficient sum of the formal product-law left side is already
identified with the sum of the two genuine analytic logarithms.  This closes
the right-hand analytic specialization without any fake power-series
evaluation map on `ℚ_[3]`. -/
theorem hasSum_f3PadicFormal_log_product_coeff
    {x y : ℚ_[3]} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum
      (fun k : ℕ =>
        PowerSeries.coeff (k + 1)
          ((PowerSeries.log ℚ_[3]).subst
            (x • PowerSeries.X + y • PowerSeries.X +
              (x • PowerSeries.X) * (y • PowerSeries.X))))
      (f3PadicLogOnePlus x + f3PadicLogOnePlus y) := by
  rw [f3PadicFormal_log_mul_rescaled x y]
  simpa only [map_add] using
    (hasSum_f3PadicFormal_log_rescale_coeff hx).add
      (hasSum_f3PadicFormal_log_rescale_coeff hy)

/-- Actual F₃ inputs satisfy the hypotheses of the rescaled analytic
specialization.  The sole remaining bridge is to identify the nonlinear
formal coefficient sum with the analytic logarithm at the product
displacement. -/
theorem hasSum_f3PadicFormal_log_product_delta_coeff
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    HasSum
      (fun k : ℕ =>
        PowerSeries.coeff (k + 1)
          ((PowerSeries.log ℚ_[3]).subst
            (f3PadicDelta m • PowerSeries.X +
              f3PadicDelta n • PowerSeries.X +
              (f3PadicDelta m • PowerSeries.X) *
                (f3PadicDelta n • PowerSeries.X))))
      (f3PadicLog m + f3PadicLog n) := by
  simpa [f3PadicLog] using
    hasSum_f3PadicFormal_log_product_coeff
      (f3PadicDelta_norm_lt_one hm hm3)
      (f3PadicDelta_norm_lt_one hn hn3)

end OmegaBalance
