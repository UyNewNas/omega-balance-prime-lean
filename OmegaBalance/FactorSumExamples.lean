import OmegaBalance.FactorSumStructure
import OmegaBalance.FactorSumFamily
import OmegaBalance.FactorSumLucasCertificates

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

/-- Exact kernel-checked factor-sum and Ω profile of the level-five witness. -/
theorem doubleBalanced_870404071_profile :
    primeFactorSum (870404071 - 1) = 20936 ∧
    primeFactorSum (870404071 + 1) = 20936 ∧
    bigOmega (870404071 - 1) = 5 ∧
    bigOmega (870404071 + 1) = 5 := by
  have hLpr : ∀ z ∈ [2, 3, 5, 1493, 19433], z.Prime := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hRpr : ∀ z ∈ [2, 2, 2, 9619, 11311], z.Prime := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hLe : [2, 3, 5, 1493, 19433].prod = 870404071 - 1 := by norm_num
  have hRe : [2, 2, 2, 9619, 11311].prod = 870404071 + 1 := by norm_num
  have hLS := primeFactorSum_of_factors hLe hLpr
  have hRS := primeFactorSum_of_factors hRe hRpr
  have hLO := bigOmega_of_factors hLe hLpr
  have hRO := bigOmega_of_factors hRe hRpr
  norm_num at hLS hRS hLO hRO
  exact ⟨hLS, hRS, hLO, hRO⟩

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


/-- All five family values at `t=41529` are kernel-certified prime. -/
theorem sumFamily_prime_values_41529 : SumFamilyPrimeValues 41529 := by
  refine ⟨by norm_num [sumFamilyU], by norm_num [sumFamilyV], ?_, ?_, ?_⟩
  · simpa [sumFamilyQ] using prime_672626441909
  · simpa [sumFamilyR] using prime_672625902031
  · simpa [sumFamilyCenter] using prime_1676030389155588931

theorem sumBalanced_1676030389155588931 :
    IsPrimeFactorSumBalancedPrime 1676030389155588931 := by
  simpa [sumFamilyCenter] using sumFamily_five_primes sumFamily_prime_values_41529

theorem sumBalanced_1676030389155588931_profile :
    omegaSum 1676030389155588931 = 9 ∧ omegaDiff 1676030389155588931 = -1 := by
  constructor
  · simpa [sumFamilyCenter] using
      sumFamily_omegaSum_eq_nine sumFamily_prime_values_41529
  · simpa [sumFamilyCenter] using
      sumFamily_omegaDiff_eq_neg_one sumFamily_prime_values_41529

/-- All five family values at `t=48465` are kernel-certified prime. -/
theorem sumFamily_prime_values_48465 : SumFamilyPrimeValues 48465 := by
  refine ⟨by norm_num [sumFamilyU], by norm_num [sumFamilyV], ?_, ?_, ?_⟩
  · simpa [sumFamilyQ] using prime_916065462437
  · simpa [sumFamilyR] using prime_916064832391
  · simpa [sumFamilyCenter] using prime_2663854240184425411

theorem sumBalanced_2663854240184425411 :
    IsPrimeFactorSumBalancedPrime 2663854240184425411 := by
  simpa [sumFamilyCenter] using sumFamily_five_primes sumFamily_prime_values_48465

theorem sumBalanced_2663854240184425411_profile :
    omegaSum 2663854240184425411 = 9 ∧ omegaDiff 2663854240184425411 = -1 := by
  constructor
  · simpa [sumFamilyCenter] using
      sumFamily_omegaSum_eq_nine sumFamily_prime_values_48465
  · simpa [sumFamilyCenter] using
      sumFamily_omegaDiff_eq_neg_one sumFamily_prime_values_48465

end OmegaBalance
