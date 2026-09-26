import OmegaBalance.F3PadicLogCompositionGauss
import Mathlib.Tactic.ComputeDegree

/-!
# Scalar majorants for the final 3-adic logarithm composition interchange

The formal substitution coefficient at outer degree `d` contains the product
of the logarithm coefficient and a coefficient of the `d`-th power of the
quadratic product increment. This file supplies the pointwise real majorants
needed for the eventual double-series/Fubini step.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

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

theorem f3PadicLogMulPolynomial_natDegree_le_two (x y : ℚ_[3]) :
    (f3PadicLogMulPolynomial x y).natDegree ≤ 2 := by
  unfold f3PadicLogMulPolynomial
  compute_degree

theorem f3PadicLogMulPolynomial_pow_natDegree_le
    (x y : ℚ_[3]) (d : ℕ) :
    (f3PadicLogMulPolynomial x y ^ d).natDegree ≤ 2 * d := by
  have h :=
    Polynomial.natDegree_pow_le_of_le d
      (f3PadicLogMulPolynomial_natDegree_le_two x y)
  simpa [Nat.mul_comm] using h

theorem f3PadicLogMulPolynomial_pow_coeff_eq_zero_of_two_mul_lt
    (x y : ℚ_[3]) {d n : ℕ} (h : 2 * d < n) :
    (f3PadicLogMulPolynomial x y ^ d).coeff n = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (f3PadicLogMulPolynomial_pow_natDegree_le x y d) h)

theorem f3PadicLogMulPolynomial_pow_support_subset_range
    (x y : ℚ_[3]) (d : ℕ) :
    (f3PadicLogMulPolynomial x y ^ d).support ⊆ Finset.range (2 * d + 1) := by
  intro n hn
  rw [Finset.mem_range]
  by_contra hnot
  have hlt : 2 * d < n := by omega
  exact (Polynomial.mem_support_iff.mp hn)
    (f3PadicLogMulPolynomial_pow_coeff_eq_zero_of_two_mul_lt x y hlt)

end OmegaBalance
