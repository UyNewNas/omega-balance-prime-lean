import OmegaBalance.F3Infinitude

namespace OmegaBalance

theorem v3_eq_iff_pow_three_dvd_not_succ {n k : ℕ} (hn : n ≠ 0) :
    v3 n = k ↔ 3 ^ k ∣ n ∧ ¬ 3 ^ (k + 1) ∣ n := by
  have hdiv (j : ℕ) : 3 ^ j ∣ n ↔ j ≤ v3 n := by
    change 3 ^ j ∣ n ↔ j ≤ valuation 3 n
    rw [valuation_eq_padicValNat Nat.prime_three]
    exact padicValNat_dvd_iff_le hn
  constructor
  · intro hv
    constructor
    · exact (hdiv k).mpr (by omega)
    · intro hs
      have hks := (hdiv (k + 1)).mp hs
      omega
  · rintro ⟨hk, hs⟩
    have hle := (hdiv k).mp hk
    have hnle : ¬ k + 1 ≤ v3 n := by
      intro h
      exact hs ((hdiv (k + 1)).mpr h)
    omega

theorem f3_prime_eq_pos_level_iff
    {p k : ℕ} (hp : p.Prime) (h3 : 3 < p) (hk : 0 < k) :
    f3 p = (k : ℤ) ↔
      3 ^ k ∣ p + 1 ∧ ¬ 3 ^ (k + 1) ∣ p + 1 := by
  constructor
  · intro hf
    have hpos : 0 < f3 p := by
      rw [hf]
      exact_mod_cast hk
    have hm : p % 3 = 2 := (f3_pos_iff_mod_three hp h3).mp hpos
    have he := (f3_of_mod_three_two (n := p) (by omega) hm).1
    have hv : v3 (p + 1) = k := by
      rw [he] at hf
      exact_mod_cast hf
    exact (v3_eq_iff_pow_three_dvd_not_succ (n := p + 1) (k := k) (by omega)).mp hv
  · rintro h
    have hv : v3 (p + 1) = k :=
      (v3_eq_iff_pow_three_dvd_not_succ (n := p + 1) (k := k) (by omega)).mpr h
    have h3pow : 3 ∣ (3 : ℕ) ^ k :=
      dvd_pow_self 3 (by omega : k ≠ 0)
    have hdiv3 : 3 ∣ p + 1 := h3pow.trans h.1
    have hm : p % 3 = 2 := by
      have hz := Nat.mod_eq_zero_of_dvd hdiv3
      omega
    rw [(f3_of_mod_three_two (n := p) (by omega) hm).1, hv]

theorem f3_prime_eq_neg_level_iff
    {p k : ℕ} (hp : p.Prime) (h3 : 3 < p) (hk : 0 < k) :
    f3 p = -(k : ℤ) ↔
      3 ^ k ∣ p - 1 ∧ ¬ 3 ^ (k + 1) ∣ p - 1 := by
  constructor
  · intro hf
    have hneg : f3 p < 0 := by
      rw [hf]
      have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
      omega
    have hm : p % 3 = 1 := (f3_neg_iff_mod_three hp h3).mp hneg
    have he := (f3_of_mod_three_one (n := p) (by omega) hm).1
    have hv : v3 (p - 1) = k := by
      rw [he] at hf
      have hz : (v3 (p - 1) : ℤ) = (k : ℤ) := by omega
      exact_mod_cast hz
    exact (v3_eq_iff_pow_three_dvd_not_succ (n := p - 1) (k := k) (by omega)).mp hv
  · rintro h
    have hv : v3 (p - 1) = k :=
      (v3_eq_iff_pow_three_dvd_not_succ (n := p - 1) (k := k) (by omega)).mpr h
    have h3pow : 3 ∣ (3 : ℕ) ^ k :=
      dvd_pow_self 3 (by omega : k ≠ 0)
    have hdiv3 : 3 ∣ p - 1 := h3pow.trans h.1
    have hm : p % 3 = 1 := by
      have hz := Nat.mod_eq_zero_of_dvd hdiv3
      omega
    rw [(f3_of_mod_three_one (n := p) (by omega) hm).1, hv]

end OmegaBalance
