import OmegaBalance.F3PrimeDensityExact

namespace OmegaBalance

/-- Exact positive F₃ level as a nested power-of-three residue condition,
including the two small primes. -/
theorem f3_prime_eq_pos_level_iff_mod_exact
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    f3 p = (k : ℤ) ↔
      p % (3 ^ k) = 3 ^ k - 1 ∧
        p % (3 ^ (k + 1)) ≠ 3 ^ (k + 1) - 1 := by
  by_cases h3 : 3 < p
  · exact f3_prime_eq_pos_level_iff_mod_exact_above_three hp h3 hk
  · have hp2 : 2 ≤ p := hp.two_le
    have hp3 : p ≤ 3 := by omega
    have hp23 : p = 2 ∨ p = 3 := by omega
    rcases hp23 with rfl | rfl
    · have hlow := mod_pow_three_eq_sub_one_iff_dvd_add_one (j := k) (n := 2)
      have hhigh := mod_pow_three_eq_sub_one_iff_dvd_add_one (j := k + 1) (n := 2)
      simp only [hlow, hhigh]
      norm_num
      rw [← v3_eq_iff_pow_three_dvd_not_succ (n := 3) (k := k) (by norm_num),
          f3_two, v3_three]
      norm_cast
    · have hlow := mod_pow_three_eq_sub_one_iff_dvd_add_one (j := k) (n := 3)
      have hhigh := mod_pow_three_eq_sub_one_iff_dvd_add_one (j := k + 1) (n := 3)
      simp only [hlow, hhigh]
      norm_num
      rw [← v3_eq_iff_pow_three_dvd_not_succ (n := 4) (k := k) (by norm_num),
          f3_three, v3_four]
      norm_cast

/-- Exact negative F₃ level as a nested power-of-three residue condition,
including the two small primes. -/
theorem f3_prime_eq_neg_level_iff_mod_exact
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    f3 p = -(k : ℤ) ↔
      p % (3 ^ k) = 1 ∧
        p % (3 ^ (k + 1)) ≠ 1 := by
  by_cases h3 : 3 < p
  · exact f3_prime_eq_neg_level_iff_mod_exact_above_three hp h3 hk
  · have hp2 : 2 ≤ p := hp.two_le
    have hp3 : p ≤ 3 := by omega
    have hp23 : p = 2 ∨ p = 3 := by omega
    rcases hp23 with rfl | rfl
    · have hlow := mod_pow_three_eq_one_iff_dvd_sub_one k 2 hk (by norm_num)
      have hhigh := mod_pow_three_eq_one_iff_dvd_sub_one (k + 1) 2 (by omega) (by norm_num)
      simp only [hlow, hhigh]
      norm_num
      rw [← v3_eq_iff_pow_three_dvd_not_succ (n := 1) (k := k) (by norm_num),
          f3_two, v3_one]
      omega
    · have hlow := mod_pow_three_eq_one_iff_dvd_sub_one k 3 hk (by norm_num)
      have hhigh := mod_pow_three_eq_one_iff_dvd_sub_one (k + 1) 3 (by omega) (by norm_num)
      simp only [hlow, hhigh]
      norm_num
      rw [← v3_eq_iff_pow_three_dvd_not_succ (n := 2) (k := k) (by norm_num),
          f3_three, v3_two]
      omega

end OmegaBalance
