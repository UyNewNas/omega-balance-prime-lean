import OmegaBalance.F3PadicLogCompositionGauss

/-!
# Scalar majorants for the final 3-adic logarithm composition interchange

The formal substitution coefficient at outer degree `d` contains the product
of the logarithm coefficient and a coefficient of the `d`-th power of the
quadratic product increment.  This file supplies the pointwise real majorants
needed for the eventual double-series/Fubini step.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The norm of the degree-`d` coefficient of the formal logarithm is at
most `d`.  This deliberately uses the already-verified project bound on
the 3-adic norm of inverse natural-number casts. -/
theorem norm_f3PadicFormalLog_coeff_le (d : ℕ) :
    ‖PowerSeries.coeff d (PowerSeries.log ℚ_[3])‖ ≤ (d : ℝ) := by
  cases d with
  | zero =>
      simp
  | succ k =>
      calc
        ‖PowerSeries.coeff (k + 1) (PowerSeries.log ℚ_[3])‖ =
            ‖f3PadicLogTerm (1 : ℚ_[3]) k‖ := by
              have h := f3PadicLogTerm_eq_powerSeries_coeff (1 : ℚ_[3]) k
              simpa using congrArg norm h.symm
        _ ≤ (((k + 1 : ℕ) : ℝ) * ‖(1 : ℚ_[3])‖ ^ (k + 1)) :=
          norm_f3PadicLogTerm_le (1 : ℚ_[3]) k
        _ = ((k + 1 : ℕ) : ℝ) := by simp

/-- Combining the logarithm-coefficient bound with the nonarchimedean Gauss
bound gives a separable majorant for every coefficient in the formal
composition double series. -/
theorem norm_f3PadicFormalLog_coeff_mul_pow_coeff_le
    {x y : ℚ_[3]}
    (hx : ‖x‖ ≤ (1 / 3 : ℝ)) (hy : ‖y‖ ≤ (1 / 3 : ℝ))
    (d n : ℕ) :
    ‖PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ d).coeff n‖
      ≤ (d : ℝ) * (1 / 3 : ℝ) ^ d := by
  rw [norm_mul]
  exact mul_le_mul
    (norm_f3PadicFormalLog_coeff_le d)
    (norm_f3PadicLogMulPolynomial_pow_coeff_le hx hy d n)
    (norm_nonneg _)
    (by positivity)

end OmegaBalance
