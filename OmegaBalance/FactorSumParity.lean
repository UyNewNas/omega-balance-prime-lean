import OmegaBalance.FactorSumArithmetic

/-!
# Two-adic restrictions for simultaneous sum/count balance

These are necessary conditions only.  They keep the sum statistic and the
multiplicity count statistic separate, and make the parity consequence used
in the third research round available as a public Lean interface.
-/

namespace OmegaBalance

/-- In a double-balanced prime, one neighbor has `v₂ = 1`; the other has an
odd `v₂` at least three.  The disjunction records which side is which. -/
theorem doubleBalanced_two_adic_profile {p k : ℕ} (h : IsDoubleBalancedPrime p k) :
    (valuation 2 (p - 1) = 1 ∧
      3 ≤ valuation 2 (p + 1) ∧ valuation 2 (p + 1) % 2 = 1) ∨
    (valuation 2 (p + 1) = 1 ∧
      3 ≤ valuation 2 (p - 1) ∧ valuation 2 (p - 1) % 2 = 1) := by
  have hp2 : 2 < p := by
    have hp := h.1.two_le
    by_contra! hn
    have he : p = 2 := by omega
    have hs := h.2.1
    simp [IsPrimeFactorSumBalanced, he, primeFactorSum_prime Nat.prime_three] at hs
  have hpL : p - 1 ≠ 0 := by omega
  have hpR : p + 1 ≠ 0 := by omega
  have hsum := h.2.1
  unfold IsPrimeFactorSumBalanced at hsum
  have hparL := primeFactorSum_parity (p - 1)
  have hparR := primeFactorSum_parity (p + 1)
  rw [h.2.2.1] at hparL
  rw [h.2.2.2] at hparR
  have hvpar : valuation 2 (p - 1) % 2 = valuation 2 (p + 1) % 2 := by
    omega
  rcases doubleBalanced_mod_eight h with hm | hm
  · right
    have hlo : valuation 2 (p + 1) = 1 := by
      apply valuation_eq_of_pow_dvd Nat.prime_two hpR
      · norm_num
        apply Nat.dvd_iff_mod_eq_zero.mpr
        omega
      · norm_num
        intro hd
        have hz := Nat.mod_eq_zero_of_dvd hd
        omega
    have hhi : 3 ≤ valuation 2 (p - 1) := by
      unfold valuation
      apply (Nat.prime_two.pow_dvd_iff_le_factorization hpL).mp
      norm_num
      apply Nat.dvd_iff_mod_eq_zero.mpr
      omega
    exact ⟨hlo, hhi, by omega⟩
  · left
    have hlo : valuation 2 (p - 1) = 1 := by
      apply valuation_eq_of_pow_dvd Nat.prime_two hpL
      · norm_num
        apply Nat.dvd_iff_mod_eq_zero.mpr
        omega
      · norm_num
        intro hd
        have hz := Nat.mod_eq_zero_of_dvd hd
        omega
    have hhi : 3 ≤ valuation 2 (p + 1) := by
      unfold valuation
      apply (Nat.prime_two.pow_dvd_iff_le_factorization hpR).mp
      norm_num
      apply Nat.dvd_iff_mod_eq_zero.mpr
      omega
    exact ⟨hlo, hhi, by omega⟩

/-- The common prime-factor sum has parity `k-1`: equivalently, adding one to
that sum gives the parity of the common multiplicity count `k`. -/
theorem doubleBalanced_common_sum_parity {p k : ℕ} (h : IsDoubleBalancedPrime p k) :
    (primeFactorSum (p - 1) + 1) % 2 = k % 2 ∧
      (primeFactorSum (p + 1) + 1) % 2 = k % 2 := by
  have hprof := doubleBalanced_two_adic_profile h
  have hparL := primeFactorSum_parity (p - 1)
  have hparR := primeFactorSum_parity (p + 1)
  rw [h.2.2.1] at hparL
  rw [h.2.2.2] at hparR
  rcases hprof with hl | hr
  · omega
  · omega

end OmegaBalance
