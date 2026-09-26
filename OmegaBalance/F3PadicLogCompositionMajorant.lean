import OmegaBalance.F3PadicLogCompositionGauss
import Mathlib.Algebra.Polynomial.Degree.Support

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

/-- The quadratic substitution polynomial has degree at most two, uniformly
in its coefficients. -/
theorem f3PadicLogMulPolynomial_natDegree_le_two (x y : ℚ_[3]) :
    (f3PadicLogMulPolynomial x y).natDegree ≤ 2 := by
  unfold f3PadicLogMulPolynomial
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · simpa using Polynomial.natDegree_C_mul_X_pow_le x 1
    · simpa using Polynomial.natDegree_C_mul_X_pow_le y 1
  · exact Polynomial.natDegree_C_mul_X_pow_le (x * y) 2

/-- Consequently the d-th power of the substitution polynomial has degree
at most 2d. -/
theorem f3PadicLogMulPolynomial_pow_natDegree_le
    (x y : ℚ_[3]) (d : ℕ) :
    (f3PadicLogMulPolynomial x y ^ d).natDegree ≤ 2 * d := by
  calc
    (f3PadicLogMulPolynomial x y ^ d).natDegree
        ≤ d * (f3PadicLogMulPolynomial x y).natDegree :=
      Polynomial.natDegree_pow_le
    _ ≤ d * 2 := Nat.mul_le_mul_left d
      (f3PadicLogMulPolynomial_natDegree_le_two x y)
    _ = 2 * d := by omega

/-- Only the first 2d+1 coefficient indices can occur in the d-th power. -/
theorem f3PadicLogMulPolynomial_pow_support_subset_range
    (x y : ℚ_[3]) (d : ℕ) :
    (f3PadicLogMulPolynomial x y ^ d).support ⊆
      Finset.range (2 * d + 1) := by
  exact Polynomial.supp_subset_range <|
    (f3PadicLogMulPolynomial_pow_natDegree_le x y d).trans_lt
      (Nat.lt_succ_self (2 * d))

/-- The d-th power therefore has at most 2d+1 nonzero coefficients. -/
theorem f3PadicLogMulPolynomial_pow_support_card_le
    (x y : ℚ_[3]) (d : ℕ) :
    (f3PadicLogMulPolynomial x y ^ d).support.card ≤ 2 * d + 1 := by
  calc
    (f3PadicLogMulPolynomial x y ^ d).support.card
        ≤ (Finset.range (2 * d + 1)).card :=
      Finset.card_le_card
        (f3PadicLogMulPolynomial_pow_support_subset_range x y d)
    _ = 2 * d + 1 := by simp

end OmegaBalance
