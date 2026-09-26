import OmegaBalance.F3Infinitude

/-!
# The second exact residue class for each nonzero F₃ level

For exact prime densities, one residue class is not enough.  At level `k>0`,
`F₃=+k` contains the two reduced classes
`3^k-1` and `2*3^k-1` modulo `3^(k+1)`; the negative level has the
corresponding `+1` classes.  The infinitude layer already formalized the first
class.  This module supplies the second class without making any asymptotic
prime-counting claim.
-/

namespace OmegaBalance

/-- The second positive-level residue is reduced modulo `3^(k+1)`. -/
theorem f3_pos_residue_two_coprime {k : ℕ} (hk : 0 < k) :
    (2 * 3 ^ k - 1).Coprime (3 ^ (k + 1)) := by
  have hd : 3 ∣ (3 : ℕ) ^ k := dvd_pow_self 3 (by omega)
  have hc : (2 * 3 ^ k - 1).Coprime 3 := by
    apply Nat.Coprime.symm
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro h
    have hm := Nat.mod_eq_zero_of_dvd hd
    have hm' := Nat.mod_eq_zero_of_dvd h
    omega
  exact hc.pow_right (k + 1)

/-- The second negative-level residue is reduced modulo `3^(k+1)`. -/
theorem f3_neg_residue_two_coprime {k : ℕ} (hk : 0 < k) :
    (2 * 3 ^ k + 1).Coprime (3 ^ (k + 1)) := by
  have hd : 3 ∣ (3 : ℕ) ^ k := dvd_pow_self 3 (by omega)
  have hc : (2 * 3 ^ k + 1).Coprime 3 := by
    apply Nat.Coprime.symm
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro h
    have hm := Nat.mod_eq_zero_of_dvd hd
    have hm' := Nat.mod_eq_zero_of_dvd h
    omega
  exact hc.pow_right (k + 1)

/-- The second explicit reduced residue gives the exact value `+k`. -/
theorem f3_pos_of_modEq_level_two {n k : ℕ} (hn : 1 < n) (hk : 0 < k)
    (hmod : n ≡ 2 * 3 ^ k - 1 [MOD 3 ^ (k + 1)]) :
    f3 n = (k : ℤ) := by
  have hp : 0 < (3 : ℕ) ^ k := pow_pos (by decide) _
  have hsmall : 2 * 3 ^ k - 1 < (3 : ℕ) ^ (k + 1) := by
    rw [pow_succ]
    omega
  have hr : n % 3 ^ (k + 1) = 2 * 3 ^ k - 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hsmall] using hmod
  have he := Nat.mod_add_div n (3 ^ (k + 1))
  rw [hr, pow_succ] at he
  have hsub : 2 * 3 ^ k - 1 + 1 = 2 * (3 : ℕ) ^ k := by omega
  have hf : n + 1 = 3 ^ k * (2 + 3 * (n / 3 ^ (k + 1))) := by
    rw [pow_succ]
    nlinarith [he, hsub]
  have hv0 : v3 (2 + 3 * (n / 3 ^ (k + 1))) = 0 := by
    apply v3_eq_zero_of_not_dvd
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  have hv : v3 (n + 1) = k := by
    rw [hf, v3_mul (by positivity) (by omega), v3_pow_three, hv0, add_zero]
  have hd : 3 ∣ n + 1 :=
    (dvd_pow_self 3 (by omega : k ≠ 0)).trans ⟨_, hf⟩
  have hm : n % 3 = 2 := by
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  rw [(f3_of_mod_three_two hn hm).1, hv]

/-- The second explicit reduced residue gives the exact value `-k`. -/
theorem f3_neg_of_modEq_level_two {n k : ℕ} (hn : 1 < n) (hk : 0 < k)
    (hmod : n ≡ 2 * 3 ^ k + 1 [MOD 3 ^ (k + 1)]) :
    f3 n = -(k : ℤ) := by
  have hp : 0 < (3 : ℕ) ^ k := pow_pos (by decide) _
  have hsmall : 2 * 3 ^ k + 1 < (3 : ℕ) ^ (k + 1) := by
    rw [pow_succ]
    have hk3 : 3 ≤ (3 : ℕ) ^ k := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      simp [pow_succ]
    omega
  have hr : n % 3 ^ (k + 1) = 2 * 3 ^ k + 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hsmall] using hmod
  have he := Nat.mod_add_div n (3 ^ (k + 1))
  rw [hr, pow_succ] at he
  have hf : n - 1 = 3 ^ k * (2 + 3 * (n / 3 ^ (k + 1))) := by
    rw [pow_succ]
    nlinarith
  have hv0 : v3 (2 + 3 * (n / 3 ^ (k + 1))) = 0 := by
    apply v3_eq_zero_of_not_dvd
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  have hv : v3 (n - 1) = k := by
    rw [hf, v3_mul (by positivity) (by omega), v3_pow_three, hv0, add_zero]
  have hd : 3 ∣ n - 1 :=
    (dvd_pow_self 3 (by omega : k ≠ 0)).trans ⟨_, hf⟩
  have hm : n % 3 = 1 := by
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  rw [(f3_of_mod_three_one hn hm).1, hv]

end OmegaBalance
