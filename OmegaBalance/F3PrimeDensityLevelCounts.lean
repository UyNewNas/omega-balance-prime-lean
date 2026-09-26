import OmegaBalance.F3PrimeDensityExact

open Filter
open scoped Topology

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


/-- Prime values up to `x` lying on the exact positive F₃ level `k`. -/
noncomputable def f3PrimePosLevelPrimes (k : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ f3 p = (k : ℤ)

/-- Prime values up to `x` lying on the exact negative F₃ level `-k`. -/
noncomputable def f3PrimeNegLevelPrimes (k : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ f3 p = -(k : ℤ)

/-- Real-valued exact positive-level prime count. -/
noncomputable def f3PrimePosLevelCountingReal (k : ℕ) (x : ℝ) : ℝ :=
  ((f3PrimePosLevelPrimes k x).card : ℝ)

/-- Real-valued exact negative-level prime count. -/
noncomputable def f3PrimeNegLevelCountingReal (k : ℕ) (x : ℝ) : ℝ :=
  ((f3PrimeNegLevelPrimes k x).card : ℝ)

lemma f3APPrimes_pow_three_sub_one_succ_subset (k : ℕ) (x : ℝ) :
    f3APPrimes (3 ^ (k + 1)) (3 ^ (k + 1) - 1) x ⊆
      f3APPrimes (3 ^ k) (3 ^ k - 1) x := by
  intro p hp
  simp only [f3APPrimes, Finset.mem_filter] at hp ⊢
  rcases hp with ⟨hIcc, hprime, hmod⟩
  refine ⟨hIcc, hprime, ?_⟩
  apply (mod_pow_three_eq_sub_one_iff_dvd_add_one (j := k) (n := p)).2
  have hhigh :
      3 ^ (k + 1) ∣ p + 1 :=
    (mod_pow_three_eq_sub_one_iff_dvd_add_one (j := k + 1) (n := p)).1 hmod
  exact (pow_dvd_pow 3 (by omega)).trans hhigh

lemma f3APPrimes_pow_three_one_succ_subset
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    f3APPrimes (3 ^ (k + 1)) 1 x ⊆
      f3APPrimes (3 ^ k) 1 x := by
  intro p hp
  simp only [f3APPrimes, Finset.mem_filter] at hp ⊢
  rcases hp with ⟨hIcc, hprime, hmod⟩
  refine ⟨hIcc, hprime, ?_⟩
  have hp1 : 1 ≤ p := hprime.one_lt.le
  apply (mod_pow_three_eq_one_iff_dvd_sub_one k p hk hp1).2
  have hhigh :
      3 ^ (k + 1) ∣ p - 1 :=
    (mod_pow_three_eq_one_iff_dvd_sub_one (k + 1) p (by omega) hp1).1 hmod
  exact (pow_dvd_pow 3 (by omega)).trans hhigh

lemma f3PrimePosLevelPrimes_eq_sdiff
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    f3PrimePosLevelPrimes k x =
      f3APPrimes (3 ^ k) (3 ^ k - 1) x \
        f3APPrimes (3 ^ (k + 1)) (3 ^ (k + 1) - 1) x := by
  classical
  ext p
  by_cases hI : p ∈ Finset.Icc 0 ⌊x⌋₊
  · by_cases hp : p.Prime
    · simp [f3PrimePosLevelPrimes, f3APPrimes, hI, hp,
        f3_prime_eq_pos_level_iff_mod_exact hp hk]
    · simp [f3PrimePosLevelPrimes, f3APPrimes, hI, hp]
  · simp [f3PrimePosLevelPrimes, f3APPrimes, hI]

lemma f3PrimeNegLevelPrimes_eq_sdiff
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    f3PrimeNegLevelPrimes k x =
      f3APPrimes (3 ^ k) 1 x \
        f3APPrimes (3 ^ (k + 1)) 1 x := by
  classical
  ext p
  by_cases hI : p ∈ Finset.Icc 0 ⌊x⌋₊
  · by_cases hp : p.Prime
    · simp [f3PrimeNegLevelPrimes, f3APPrimes, hI, hp,
        f3_prime_eq_neg_level_iff_mod_exact hp hk]
    · simp [f3PrimeNegLevelPrimes, f3APPrimes, hI, hp]
  · simp [f3PrimeNegLevelPrimes, f3APPrimes, hI]

theorem f3PrimePosLevelCountingReal_eq_residue
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    f3PrimePosLevelCountingReal k x =
      f3PrimePosExactResidueCountingReal k x := by
  rw [f3PrimePosLevelCountingReal, f3PrimePosLevelPrimes_eq_sdiff k hk x,
    f3PrimePosExactResidueCountingReal,
    f3PrimeAPCountingReal_eq_card_apPrimes,
    f3PrimeAPCountingReal_eq_card_apPrimes]
  simpa using
    (Finset.cast_card_sdiff (R := ℝ)
      (f3APPrimes_pow_three_sub_one_succ_subset k x))

theorem f3PrimeNegLevelCountingReal_eq_residue
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    f3PrimeNegLevelCountingReal k x =
      f3PrimeNegExactResidueCountingReal k x := by
  rw [f3PrimeNegLevelCountingReal, f3PrimeNegLevelPrimes_eq_sdiff k hk x,
    f3PrimeNegExactResidueCountingReal,
    f3PrimeAPCountingReal_eq_card_apPrimes,
    f3PrimeAPCountingReal_eq_card_apPrimes]
  simpa using
    (Finset.cast_card_sdiff (R := ℝ)
      (f3APPrimes_pow_three_one_succ_subset k hk x))

theorem f3PrimePosLevelCountingReal_normalized_tendsto
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimePosLevelCountingReal k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  simpa only [f3PrimePosLevelCountingReal_eq_residue k hk] using
    f3PrimePosExactResidueCountingReal_normalized_tendsto k hk

theorem f3PrimeNegLevelCountingReal_normalized_tendsto
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeNegLevelCountingReal k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  simpa only [f3PrimeNegLevelCountingReal_eq_residue k hk] using
    f3PrimeNegExactResidueCountingReal_normalized_tendsto k hk

end OmegaBalance
