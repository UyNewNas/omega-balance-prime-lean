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
      have hhigh_ne :
          2 % (3 ^ (k + 1)) ≠ 3 ^ (k + 1) - 1 ↔
            ¬ 3 ^ (k + 1) ∣ 2 + 1 :=
        not_congr hhigh
      rw [hlow, hhigh_ne]
      norm_num
      have hv3 : v3 3 = 1 := by simpa using v3_pow_three 1
      rw [← v3_eq_iff_pow_three_dvd_not_succ (n := 3) (k := k) (by norm_num),
          hv3]
      norm_cast
    · have hlow := mod_pow_three_eq_sub_one_iff_dvd_add_one (j := k) (n := 3)
      have hhigh := mod_pow_three_eq_sub_one_iff_dvd_add_one (j := k + 1) (n := 3)
      have hhigh_ne :
          3 % (3 ^ (k + 1)) ≠ 3 ^ (k + 1) - 1 ↔
            ¬ 3 ^ (k + 1) ∣ 3 + 1 :=
        not_congr hhigh
      rw [hlow, hhigh_ne]
      norm_num
      rw [← v3_eq_iff_pow_three_dvd_not_succ (n := 4) (k := k) (by norm_num)]
      have hv4 : v3 4 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      have hv2 : v3 2 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      unfold f3 neighborDiff
      simp [hv4, hv2]
      omega

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
      have hhigh_ne :
          2 % (3 ^ (k + 1)) ≠ 1 ↔ ¬ 3 ^ (k + 1) ∣ 2 - 1 :=
        not_congr hhigh
      rw [hlow, hhigh_ne]
      norm_num
      omega
    · have hlow := mod_pow_three_eq_one_iff_dvd_sub_one k 3 hk (by norm_num)
      have hhigh := mod_pow_three_eq_one_iff_dvd_sub_one (k + 1) 3 (by omega) (by norm_num)
      have hhigh_ne :
          3 % (3 ^ (k + 1)) ≠ 1 ↔ ¬ 3 ^ (k + 1) ∣ 3 - 1 :=
        not_congr hhigh
      rw [hlow, hhigh_ne]
      norm_num
      rw [← v3_eq_iff_pow_three_dvd_not_succ (n := 2) (k := k) (by norm_num)]
      have hv4 : v3 4 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      have hv2 : v3 2 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      unfold f3 neighborDiff
      simp [hv4, hv2]
      omega

end OmegaBalance
