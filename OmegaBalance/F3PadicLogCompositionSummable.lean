import OmegaBalance.F3PadicLogCompositionMajorant
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- For each fixed outer logarithm degree, the coefficient row of the
nonlinear substitution has finite support and is therefore summable after
taking norms. -/
theorem summable_norm_f3PadicLogCompositionRow
    (x y : ℚ_[3]) (k : ℕ) :
    Summable (fun n : ℕ =>
      ‖PowerSeries.coeff (k + 1) (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ (k + 1)).coeff n‖) := by
  apply summable_of_ne_finset_zero
    (s := (f3PadicLogMulPolynomial x y ^ (k + 1)).support)
  intro n hn
  have hc :
      (f3PadicLogMulPolynomial x y ^ (k + 1)).coeff n = 0 := by
    simpa [Polynomial.mem_support_iff] using hn
  simp [hc]

/-- The full ℓ¹ mass of one outer row is bounded by its support size times
the uniform Gauss majorant. -/
theorem tsum_norm_f3PadicLogCompositionRow_le
    {x y : ℚ_[3]}
    (hx : ‖x‖ ≤ (1 / 3 : ℝ)) (hy : ‖y‖ ≤ (1 / 3 : ℝ))
    (k : ℕ) :
    (∑' n : ℕ,
      ‖PowerSeries.coeff (k + 1) (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ (k + 1)).coeff n‖)
      ≤ (((2 * (k + 1) + 1 : ℕ) : ℝ) *
          (((k + 1 : ℕ) : ℝ) * (1 / 3 : ℝ) ^ (k + 1))) := by
  rw [tsum_eq_sum
    (s := (f3PadicLogMulPolynomial x y ^ (k + 1)).support)
    (fun n hn => by
      have hc :
          (f3PadicLogMulPolynomial x y ^ (k + 1)).coeff n = 0 := by
        simpa [Polynomial.mem_support_iff] using hn
      simp [hc])]
  calc
    (∑ n ∈ (f3PadicLogMulPolynomial x y ^ (k + 1)).support,
      ‖PowerSeries.coeff (k + 1) (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ (k + 1)).coeff n‖)
        ≤ (f3PadicLogMulPolynomial x y ^ (k + 1)).support.card •
            (((k + 1 : ℕ) : ℝ) * (1 / 3 : ℝ) ^ (k + 1)) := by
          exact Finset.sum_le_card_nsmul _ _ _ fun n _ =>
            norm_f3PadicLogCompositionTerm_le hx hy k n
    _ = (((f3PadicLogMulPolynomial x y ^ (k + 1)).support.card : ℕ) : ℝ) *
          (((k + 1 : ℕ) : ℝ) * (1 / 3 : ℝ) ^ (k + 1)) := by
          simp [nsmul_eq_mul]
    _ ≤ (((2 * (k + 1) + 1 : ℕ) : ℝ) *
          (((k + 1 : ℕ) : ℝ) * (1 / 3 : ℝ) ^ (k + 1))) := by
          gcongr
          exact_mod_cast
            f3PadicLogMulPolynomial_pow_support_card_le x y (k + 1)

/-- The row majorants form a convergent real series.  This is the quantitative
input needed for the final norm-summability/Fubini step. -/
theorem summable_f3PadicLogCompositionRowMajorant :
    Summable (fun k : ℕ =>
      (((2 * (k + 1) + 1 : ℕ) : ℝ) *
        (((k + 1 : ℕ) : ℝ) * (1 / 3 : ℝ) ^ (k + 1)))) := by
  have hr : ‖(1 / 3 : ℝ)‖ < 1 := by norm_num
  have h2 :
      Summable (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 3 : ℝ) ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one
        (R := ℝ) 2 (r := (1 / 3 : ℝ)) hr)
  have h1 :
      Summable (fun n : ℕ => (n : ℝ) * (1 / 3 : ℝ) ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one
        (R := ℝ) 1 (r := (1 / 3 : ℝ)) hr)
  have h2s :
      Summable (fun k : ℕ =>
        ((k + 1 : ℕ) : ℝ) ^ 2 * (1 / 3 : ℝ) ^ (k + 1)) := by
    simpa [Function.comp_def] using h2.comp_injective Nat.succ_injective
  have h1s :
      Summable (fun k : ℕ =>
        ((k + 1 : ℕ) : ℝ) * (1 / 3 : ℝ) ^ (k + 1)) := by
    simpa [Function.comp_def] using h1.comp_injective Nat.succ_injective
  have h := (h2s.mul_left (2 : ℝ)).add h1s
  convert h using 1
  funext k
  push_cast
  ring

end OmegaBalance
