import OmegaBalance.F3PadicLogCompositionGauss

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- A coarse but uniform bound for the positive-degree coefficients of the
formal logarithm over ℚ_[3].  It is deliberately expressed with the same
polynomial factor that already occurs in the analytic majorant for
`f3PadicLogTerm`. -/
theorem norm_powerSeries_log_coeff_succ_le (k : ℕ) :
    ‖PowerSeries.coeff (k + 1) (PowerSeries.log ℚ_[3])‖
      ≤ ((k + 1 : ℕ) : ℝ) := by
  have h := norm_f3PadicLogTerm_le (1 : ℚ_[3]) k
  rw [f3PadicLogTerm_eq_powerSeries_coeff] at h
  simpa using h

/-- Pointwise majorant for the double-series matrix occurring when the formal
logarithm is composed with
`xX + yX + xyX²`.  The Gauss-norm estimate contributes the geometric
`(1/3)^(k+1)` decay; the logarithm coefficient contributes only the
linear factor `k+1`. -/
theorem norm_f3PadicLogCompositionTerm_le
    {x y : ℚ_[3]}
    (hx : ‖x‖ ≤ (1 / 3 : ℝ)) (hy : ‖y‖ ≤ (1 / 3 : ℝ))
    (k n : ℕ) :
    ‖PowerSeries.coeff (k + 1) (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ (k + 1)).coeff n‖
      ≤ ((k + 1 : ℕ) : ℝ) * (1 / 3 : ℝ) ^ (k + 1) := by
  rw [norm_mul]
  exact mul_le_mul
    (norm_powerSeries_log_coeff_succ_le k)
    (norm_f3PadicLogMulPolynomial_pow_coeff_le hx hy (k + 1) n)
    (norm_nonneg _)
    (by positivity)

end OmegaBalance
