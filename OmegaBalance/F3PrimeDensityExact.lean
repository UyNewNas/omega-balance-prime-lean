import OmegaBalance.F3PrimeDensityResidueLimits
import OmegaBalance.F3CorrelationPeriod
import OmegaBalance.F3Extension

namespace OmegaBalance

@[simp] lemma f3_two : f3 2 = 1 := by
  have h := (f3_of_mod_three_two (n := 2) (by omega) (by norm_num)).1
  rw [h]
  simpa using v3_pow_three 1

lemma mod_pow_three_eq_sub_one_iff_dvd_add_one (j n : ℕ) :
    n % (3 ^ j) = 3 ^ j - 1 ↔ 3 ^ j ∣ n + 1 := by
  have hpos : 0 < (3 : ℕ) ^ j := by positivity
  have hlt : 3 ^ j - 1 < (3 : ℕ) ^ j := by omega
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hlt] using
    (modEq_pow_three_sub_one_iff_dvd_add_one (j := j) (n := n))

lemma mod_pow_three_eq_one_iff_dvd_sub_one
    (j n : ℕ) (hj : 0 < j) (hn : 1 ≤ n) :
    n % (3 ^ j) = 1 ↔ 3 ^ j ∣ n - 1 := by
  have hdiv : 3 ∣ (3 : ℕ) ^ j := dvd_pow_self 3 hj.ne'
  have hpow : 1 < (3 : ℕ) ^ j := by
    have hle : 3 ≤ (3 : ℕ) ^ j := Nat.le_of_dvd (by positivity) hdiv
    omega
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hpow] using
    (modEq_one_iff_dvd_sub_one (j := j) (n := n) hn)

theorem f3_prime_eq_pos_level_iff_mod_exact_above_three
    {p k : ℕ} (hp : p.Prime) (h3 : 3 < p) (hk : 0 < k) :
    f3 p = (k : ℤ) ↔
      p % (3 ^ k) = 3 ^ k - 1 ∧
        p % (3 ^ (k + 1)) ≠ 3 ^ (k + 1) - 1 := by
  rw [f3_prime_eq_pos_level_iff hp h3 hk,
    ← mod_pow_three_eq_sub_one_iff_dvd_add_one k p,
    ← mod_pow_three_eq_sub_one_iff_dvd_add_one (k + 1) p]

theorem f3_prime_eq_neg_level_iff_mod_exact_above_three
    {p k : ℕ} (hp : p.Prime) (h3 : 3 < p) (hk : 0 < k) :
    f3 p = -(k : ℤ) ↔
      p % (3 ^ k) = 1 ∧
        p % (3 ^ (k + 1)) ≠ 1 := by
  rw [f3_prime_eq_neg_level_iff hp h3 hk,
    ← mod_pow_three_eq_one_iff_dvd_sub_one k p hk (by omega),
    ← mod_pow_three_eq_one_iff_dvd_sub_one (k + 1) p (by omega) (by omega)]

end OmegaBalance
