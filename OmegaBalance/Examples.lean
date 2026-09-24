import OmegaBalance.F3

/-! Kernel-checked regression tests, including the exceptional pair and failed converses. -/

namespace OmegaBalance

@[simp] theorem v3_two : v3 2 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
@[simp] theorem v3_three : v3 3 = 1 := by simpa using v3_pow_three 1
@[simp] theorem v3_four : v3 4 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
@[simp] theorem v3_eight : v3 8 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
@[simp] theorem v3_fourteen : v3 14 = 0 := v3_eq_zero_of_not_dvd (by norm_num)

@[simp] theorem v3_six : v3 6 = 1 := by
  change v3 (2 * 3) = 1
  rw [v3_mul (by norm_num) (by norm_num), v3_two, v3_three]

@[simp] theorem v3_twelve : v3 12 = 1 := by
  change v3 (4 * 3) = 1
  rw [v3_mul (by norm_num) (by norm_num), v3_four, v3_three]

/-- The first example in the problem statement. -/
@[simp] theorem v3_eighteen : v3 18 = 2 := by
  change v3 (2 * 3 ^ 2) = 2
  rw [v3_mul (by norm_num) (by norm_num), v3_two, v3_pow_three]

/-- The second example in the problem statement. -/
@[simp] theorem v3_twenty_seven : v3 27 = 3 := by
  simpa using v3_pow_three 3

/-- The third example in the problem statement. -/
@[simp] theorem v3_twenty : v3 20 = 0 := v3_eq_zero_of_not_dvd (by norm_num)

@[simp] theorem f3_three : f3 3 = 0 := by
  norm_num [f3, neighborDiff]

@[simp] theorem f3_five : f3 5 = 1 := by
  norm_num [f3, neighborDiff]

@[simp] theorem f3_seven : f3 7 = -1 := by
  norm_num [f3, neighborDiff]

@[simp] theorem f3_thirteen : f3 13 = -1 := by
  norm_num [f3, neighborDiff]

theorem twin_five_seven_example :
    f3 7 = -f3 5 ∧ f3 5 ≠ 0 ∧ f3 7 ≠ 0 := by
  exact f3_twin (p := 5) (by decide) (by decide) (by decide)

theorem twin_seventeen_nineteen_example : f3 17 = 2 ∧ f3 19 = -2 := by
  have h := f3_twin_values (p := 17) (by decide) (by decide) (by decide)
  norm_num at h
  exact ⟨h.1, h.2⟩

/-- The `p > 3` hypothesis cannot be dropped: `(3,5)` is a twin pair. -/
theorem exceptional_twin_three : IsTwinPrime 3 ∧ f3 5 ≠ -f3 3 := by
  refine ⟨by decide, ?_⟩
  norm_num

@[simp] theorem bigOmega_four : bigOmega 4 = 2 := by
  simpa using bigOmega_prime_pow Nat.prime_two 2

@[simp] theorem bigOmega_six : bigOmega 6 = 2 := by
  change bigOmega (2 * 3) = 2
  rw [bigOmega_mul (by norm_num) (by norm_num),
    bigOmega_prime Nat.prime_two, bigOmega_prime Nat.prime_three]

@[simp] theorem bigOmega_eight : bigOmega 8 = 3 := by
  simpa using bigOmega_prime_pow Nat.prime_two 3

theorem five_isOmegaBalancedPrime : IsOmegaBalancedPrime 5 := by
  refine ⟨by decide, ?_⟩
  norm_num [IsOmegaBalanced]

/-- F₃ symmetry is NOT a symmetry theorem for the full Ω difference. -/
theorem omegaDiff_twin_five_seven : omegaDiff 5 = 0 ∧ omegaDiff 7 = 1 := by
  norm_num [omegaDiff, neighborDiff]

/-- Opposite nonzero F₃ values do not characterize twin primes. -/
theorem opposite_f3_not_sufficient_for_twins :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 3 < p ∧ p < q ∧
      f3 q = -f3 p ∧ f3 p ≠ 0 ∧ q ≠ p + 2 := by
  refine ⟨5, 13, by decide, by decide, ?_⟩
  norm_num

end OmegaBalance
