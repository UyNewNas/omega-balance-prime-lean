import OmegaBalance.F3PrimeDensityConstants
import OmegaBalance.F3CorrelationPeriod

namespace OmegaBalance

/-- The positive exact-level divisibility criterion is valid for every prime,
including the small prime 2. The existing >3 theorem supplies the generic
case; the two small primes are discharged explicitly. -/
theorem f3_prime_eq_pos_level_iff_all
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    f3 p = (k : ℤ) ↔
      3 ^ k ∣ p + 1 ∧ ¬ 3 ^ (k + 1) ∣ p + 1 := by
  by_cases h3 : 3 < p
  · exact f3_prime_eq_pos_level_iff hp h3 hk
  · have hp23 : p = 2 ∨ p = 3 := by
      have hp2 := hp.two_le
      omega
    rcases hp23 with rfl | rfl
    · have hv3 : v3 3 = 1 := by simpa using v3_pow_three 1
      have hf2 : f3 2 = 1 := by
        simp [f3, neighborDiff, hv3, v3_one]
      rw [hf2]
      norm_cast
      simpa [hv3] using
        (v3_eq_iff_pow_three_dvd_not_succ (n := 3) (k := k) (by norm_num))
    · have hv2 : v3 2 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      have hv4 : v3 4 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      have hf3 : f3 3 = 0 := by simp [f3, neighborDiff, hv2, hv4]
      have h3pow : 3 ∣ (3 : ℕ) ^ k :=
        dvd_pow_self 3 (by omega : k ≠ 0)
      have hnot : ¬ (3 : ℕ) ^ k ∣ 4 := by
        intro hd
        have : 3 ∣ 4 := h3pow.trans hd
        norm_num at this
      constructor
      · intro he
        rw [hf3] at he
        have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
        omega
      · rintro ⟨hd, _⟩
        exact (hnot hd).elim

/-- Likewise, the negative exact-level criterion is valid for every prime. -/
theorem f3_prime_eq_neg_level_iff_all
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    f3 p = -(k : ℤ) ↔
      3 ^ k ∣ p - 1 ∧ ¬ 3 ^ (k + 1) ∣ p - 1 := by
  by_cases h3 : 3 < p
  · exact f3_prime_eq_neg_level_iff hp h3 hk
  · have hp23 : p = 2 ∨ p = 3 := by
      have hp2 := hp.two_le
      omega
    rcases hp23 with rfl | rfl
    · have hv3 : v3 3 = 1 := by simpa using v3_pow_three 1
      have hf2 : f3 2 = 1 := by
        simp [f3, neighborDiff, hv3, v3_one]
      have hnot : ¬ (3 : ℕ) ^ k ∣ 1 := by
        intro hd
        have hle := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hd
        have hpowgt : 1 < (3 : ℕ) ^ k :=
          Nat.one_lt_pow (Nat.ne_of_gt hk) (by norm_num)
        omega
      constructor
      · intro he
        rw [hf2] at he
        have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
        omega
      · rintro ⟨hd, _⟩
        exact (hnot hd).elim
    · have hv2 : v3 2 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      have hv4 : v3 4 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      have hf3 : f3 3 = 0 := by simp [f3, neighborDiff, hv2, hv4]
      have h3pow : 3 ∣ (3 : ℕ) ^ k :=
        dvd_pow_self 3 (by omega : k ≠ 0)
      have hnot : ¬ (3 : ℕ) ^ k ∣ 2 := by
        intro hd
        have : 3 ∣ 2 := h3pow.trans hd
        norm_num at this
      constructor
      · intro he
        rw [hf3] at he
        have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
        omega
      · rintro ⟨hd, _⟩
        exact (hnot hd).elim

/-- Exact positive F3 level as a difference of two nested power-three residue
classes. -/
theorem f3_prime_eq_pos_level_modEq_iff
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    f3 p = (k : ℤ) ↔
      (p ≡ 3 ^ k - 1 [MOD 3 ^ k]) ∧
        ¬ (p ≡ 3 ^ (k + 1) - 1 [MOD 3 ^ (k + 1)]) := by
  rw [f3_prime_eq_pos_level_iff_all hp hk,
    ← modEq_pow_three_sub_one_iff_dvd_add_one (j := k) (n := p),
    ← modEq_pow_three_sub_one_iff_dvd_add_one (j := k + 1) (n := p)]

/-- Exact negative F3 level as a difference of two nested plus-one residue
classes. -/
theorem f3_prime_eq_neg_level_modEq_iff
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    f3 p = -(k : ℤ) ↔
      (p ≡ 1 [MOD 3 ^ k]) ∧
        ¬ (p ≡ 1 [MOD 3 ^ (k + 1)]) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp.two_le
  rw [f3_prime_eq_neg_level_iff_all hp hk,
    ← modEq_one_iff_dvd_sub_one (j := k) (n := p) hp1,
    ← modEq_one_iff_dvd_sub_one (j := k + 1) (n := p) hp1]

end OmegaBalance
