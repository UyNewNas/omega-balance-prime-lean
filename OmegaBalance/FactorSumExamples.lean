import OmegaBalance.FactorSumStructure
import OmegaBalance.FactorSumFamily

/-! Kernel-checked examples. No external probable-prime results are assumed. -/

namespace OmegaBalance

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem sumFamily_prime_values_five : SumFamilyPrimeValues 5 := by
  norm_num [SumFamilyPrimeValues, sumFamilyU, sumFamilyV, sumFamilyQ,
    sumFamilyR, sumFamilyCenter]

theorem sumBalanced_3615811 : IsPrimeFactorSumBalancedPrime 3615811 := by
  simpa [sumFamilyCenter] using sumFamily_five_primes sumFamily_prime_values_five

theorem sumBalanced_3615811_profile : omegaSum 3615811 = 9 ∧ omegaDiff 3615811 = -1 := by
  constructor
  · simpa [sumFamilyCenter] using sumFamily_omegaSum_eq_nine sumFamily_prime_values_five
  · simpa [sumFamilyCenter] using sumFamily_omegaDiff_eq_neg_one sumFamily_prime_values_five

/-- A five-level example, not asserted to be the smallest such prime. -/
theorem doubleBalanced_870404071 : IsDoubleBalancedPrime 870404071 5 := by
  apply doubleBalanced_five_of_shape (by norm_num)
  refine ⟨5, 1493, 19433, 9619, 11311, ?_, Or.inl ⟨by norm_num, by norm_num⟩, by norm_num⟩
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem doubleBalanced_748465063 : IsDoubleBalancedPrime 748465063 5 := by
  apply doubleBalanced_five_of_shape (by norm_num)
  refine ⟨19, 269, 24407, 4673, 20021, ?_, Or.inl ⟨by norm_num, by norm_num⟩, by norm_num⟩
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- The least attainable count level is exactly five. -/
theorem doubleBalanced_minimum_level :
    (∃ p : ℕ, IsDoubleBalancedPrime p 5) ∧
      ∀ p k : ℕ, IsDoubleBalancedPrime p k → 5 ≤ k := by
  exact ⟨⟨870404071, doubleBalanced_870404071⟩,
    fun _ _ h => doubleBalanced_level_ge_five h⟩

theorem sumBalanced_11 : IsPrimeFactorSumBalancedPrime 11 := by
  have hs2 := primeFactorSum_prime Nat.prime_two
  have hs1 := primeFactorSum_one
  have h := primeFactorSum_cofactor_construction
    (A := 1) (B := 2) (q := 5) (r := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega) (by norm_num)
  exact h

theorem sumBalanced_17 : IsPrimeFactorSumBalancedPrime 17 := by
  have hs4 : primeFactorSum 4 = 4 := by
    simpa using primeFactorSum_prime_pow Nat.prime_two 2
  have hs3 := primeFactorSum_prime Nat.prime_three
  have h := primeFactorSum_cofactor_construction
    (A := 4) (B := 3) (q := 2) (r := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega) (by norm_num)
  exact h

theorem sumBalanced_31 : IsPrimeFactorSumBalancedPrime 31 := by
  have hs8 : primeFactorSum 8 = 6 := by
    simpa using primeFactorSum_prime_pow Nat.prime_two 3
  have hs3 := primeFactorSum_prime Nat.prime_three
  have h := primeFactorSum_cofactor_construction
    (A := 3) (B := 8) (q := 5) (r := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega) (by norm_num)
  exact h

end OmegaBalance
