import OmegaBalance.F3PrimeDensityExactNeg

open Filter Topology

namespace OmegaBalance

/-- For a positive power of three, the residue `-1` is equivalent to
divisibility of the successor. -/
lemma f3_mod_pow_three_eq_sub_one_iff_dvd_add_one
    {n k : ℕ} (hk : 0 < k) :
    n % (3 ^ k) = 3 ^ k - 1 ↔ 3 ^ k ∣ n + 1 := by
  have hmpos : 0 < (3 : ℕ) ^ k := by positivity
  have hmone : 1 ≤ (3 : ℕ) ^ k := by omega
  have hmlt : 3 ^ k - 1 < (3 : ℕ) ^ k :=
    Nat.sub_lt hmpos (by norm_num)
  constructor
  · intro hmod
    have hmeq : n ≡ 3 ^ k - 1 [MOD 3 ^ k] := by
      show n % (3 ^ k) = (3 ^ k - 1) % (3 ^ k)
      simpa [Nat.mod_eq_of_lt hmlt] using hmod
    have hadd := hmeq.add_right 1
    have hz : n + 1 ≡ 0 [MOD 3 ^ k] := by
      simpa [Nat.sub_add_cancel hmone] using hadd
    exact Nat.modEq_zero_iff_dvd.mp hz
  · intro hdiv
    have hz : n + 1 ≡ 0 [MOD 3 ^ k] :=
      Nat.modEq_zero_iff_dvd.mpr hdiv
    have hbase : (3 ^ k - 1) + 1 ≡ 0 [MOD 3 ^ k] := by
      simp [Nat.sub_add_cancel hmone]
    have heq : n + 1 ≡ (3 ^ k - 1) + 1 [MOD 3 ^ k] :=
      hz.trans hbase.symm
    have hmeq : n ≡ 3 ^ k - 1 [MOD 3 ^ k] :=
      Nat.ModEq.add_right_cancel' 1 heq
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hmlt] using hmeq

/-- For every prime, including the exceptional prime two, exact positive
F₃ level `+k` is the residue `-1 mod 3^k` with the next residue class
`-1 mod 3^(k+1)` removed. -/
theorem f3_prime_eq_pos_level_iff_nested_residue
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    f3 p = (k : ℤ) ↔
      p % (3 ^ k) = 3 ^ k - 1 ∧
        p % (3 ^ (k + 1)) ≠ 3 ^ (k + 1) - 1 := by
  constructor
  · intro hf
    have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
    have hpos : 0 < f3 p := by simpa [hf] using hkz
    have hm : p % 3 = 2 := by
      by_cases hp2 : p = 2
      · subst p
        norm_num
      · have h3p : 3 < p := by
          by_contra hnot
          have hp3 : p = 3 := by omega
          subst p
          rw [f3_three] at hf
          omega
        exact (f3_pos_iff_mod_three hp h3p).mp hpos
    have he := (f3_of_mod_three_two hp.one_lt hm).1
    have hv : v3 (p + 1) = k := by
      rw [he] at hf
      exact_mod_cast hf
    have hdepth :=
      (v3_eq_iff_pow_three_dvd_not_succ
        (n := p + 1) (k := k) (by omega)).mp hv
    constructor
    · exact (f3_mod_pow_three_eq_sub_one_iff_dvd_add_one hk).2 hdepth.1
    · intro hmod
      exact hdepth.2 <|
        (f3_mod_pow_three_eq_sub_one_iff_dvd_add_one (by omega)).1 hmod
  · rintro ⟨hmod, hmodsucc⟩
    have hdiv : 3 ^ k ∣ p + 1 :=
      (f3_mod_pow_three_eq_sub_one_iff_dvd_add_one hk).1 hmod
    have hnDiv : ¬ 3 ^ (k + 1) ∣ p + 1 := by
      intro hdivsucc
      exact hmodsucc <|
        (f3_mod_pow_three_eq_sub_one_iff_dvd_add_one (by omega)).2 hdivsucc
    have hv : v3 (p + 1) = k :=
      (v3_eq_iff_pow_three_dvd_not_succ
        (n := p + 1) (k := k) (by omega)).2 ⟨hdiv, hnDiv⟩
    have hthreepow : 3 ∣ (3 : ℕ) ^ k :=
      dvd_pow_self 3 hk.ne'
    have hthree : 3 ∣ p + 1 := hthreepow.trans hdiv
    have hm : p % 3 = 2 := by
      have hz := Nat.mod_eq_zero_of_dvd hthree
      omega
    rw [(f3_of_mod_three_two hp.one_lt hm).1, hv]

/-- Actual primes in the natural cutoff window with exact positive F₃ level. -/
noncomputable def f3PrimePosLevelPrimes (k : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).filter fun p =>
    p.Prime ∧ f3 p = (k : ℤ)

/-- Real-valued cardinality of the exact positive F₃ level. -/
noncomputable def f3PrimePosLevelCountingReal (k : ℕ) (x : ℝ) : ℝ :=
  (f3PrimePosLevelPrimes k x).card

/-- The next `-1` residue class is nested in the current one. -/
lemma f3APPrimes_pos_succ_subset (k : ℕ) (x : ℝ) (hk : 0 < k) :
    f3APPrimes (3 ^ (k + 1)) (3 ^ (k + 1) - 1) x ⊆
      f3APPrimes (3 ^ k) (3 ^ k - 1) x := by
  intro p hp
  rw [f3APPrimes] at hp ⊢
  rcases Finset.mem_filter.mp hp with ⟨hrange, hprime, hmod⟩
  refine Finset.mem_filter.mpr ⟨hrange, hprime, ?_⟩
  have hhigh : 3 ^ (k + 1) ∣ p + 1 :=
    (f3_mod_pow_three_eq_sub_one_iff_dvd_add_one (by omega)).1 hmod
  have hpow : 3 ^ k ∣ 3 ^ (k + 1) := by
    rw [pow_succ]
    exact dvd_mul_right _ _
  exact (f3_mod_pow_three_eq_sub_one_iff_dvd_add_one hk).2
    (hpow.trans hhigh)

/-- Removing the next `-1` residue class gives exactly the primes with
positive F₃ value `+k`, including the prime two when `k=1`. -/
theorem f3APPrimes_pos_sdiff_eq_pos_level
    (k : ℕ) (x : ℝ) (hk : 0 < k) :
    f3APPrimes (3 ^ k) (3 ^ k - 1) x \
        f3APPrimes (3 ^ (k + 1)) (3 ^ (k + 1) - 1) x =
      f3PrimePosLevelPrimes k x := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_sdiff.mp hp with ⟨hlow, hhigh⟩
    rw [f3APPrimes] at hlow
    rcases Finset.mem_filter.mp hlow with ⟨hrange, hprime, hmodk⟩
    have hmodks : p % (3 ^ (k + 1)) ≠ 3 ^ (k + 1) - 1 := by
      intro hm
      apply hhigh
      rw [f3APPrimes]
      exact Finset.mem_filter.mpr ⟨hrange, hprime, hm⟩
    rw [f3PrimePosLevelPrimes]
    exact Finset.mem_filter.mpr
      ⟨hrange, hprime,
        (f3_prime_eq_pos_level_iff_nested_residue hprime hk).2
          ⟨hmodk, hmodks⟩⟩
  · intro hp
    rw [f3PrimePosLevelPrimes] at hp
    rcases Finset.mem_filter.mp hp with ⟨hrange, hprime, hf⟩
    have hres :=
      (f3_prime_eq_pos_level_iff_nested_residue hprime hk).1 hf
    exact Finset.mem_sdiff.mpr ⟨by
      rw [f3APPrimes]
      exact Finset.mem_filter.mpr ⟨hrange, hprime, hres.1⟩, by
      intro hhigh
      rw [f3APPrimes] at hhigh
      exact hres.2 (Finset.mem_filter.mp hhigh).2.2⟩

/-- Nested AP-count proxy for the exact positive F₃ level. -/
noncomputable def f3PrimePosLevelAPDifference (k : ℕ) (x : ℝ) : ℝ :=
  f3PrimeAPCountingReal (3 ^ k) (3 ^ k - 1) x -
    f3PrimeAPCountingReal (3 ^ (k + 1)) (3 ^ (k + 1) - 1) x

/-- Before simplifying totients, the positive-level AP proxy has the same
successive-totient difference as the negative level. -/
theorem f3PrimePosLevelAPDifference_normalized_tendsto_totient
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimePosLevelAPDifference k x / (x / Real.log x))
      atTop
      (𝓝 (((Nat.totient (3 ^ k) : ℝ)⁻¹) -
        ((Nat.totient (3 ^ (k + 1)) : ℝ)⁻¹))) := by
  have hkpos : 0 < (3 : ℕ) ^ k := by positivity
  have hkspos : 0 < (3 : ℕ) ^ (k + 1) := by positivity
  have hkc :
      (3 ^ k - 1).Coprime (3 ^ k) := by
    rw [Nat.coprime_self_sub_left (by omega : 1 ≤ (3 : ℕ) ^ k)]
    simp
  have hksc :
      (3 ^ (k + 1) - 1).Coprime (3 ^ (k + 1)) := by
    rw [Nat.coprime_self_sub_left
      (by omega : 1 ≤ (3 : ℕ) ^ (k + 1))]
    simp
  have hklt : 3 ^ k - 1 < (3 : ℕ) ^ k :=
    Nat.sub_lt hkpos (by norm_num)
  have hkslt : 3 ^ (k + 1) - 1 < (3 : ℕ) ^ (k + 1) :=
    Nat.sub_lt hkspos (by norm_num)
  have h0 :=
    f3PrimeAPCountingReal_normalized_tendsto
      (A := 3 ^ k) (a := 3 ^ k - 1)
      hkpos hkc hklt
  have h1 :=
    f3PrimeAPCountingReal_normalized_tendsto
      (A := 3 ^ (k + 1)) (a := 3 ^ (k + 1) - 1)
      hkspos hksc hkslt
  simpa [f3PrimePosLevelAPDifference, sub_div] using h0.sub h1

/-- The positive exact-level AP proxy has normalized density `3⁻ᵏ`. -/
theorem f3PrimePosLevelAPDifference_normalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimePosLevelAPDifference k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  simpa [f3_totient_three_pow_inv_sub_succ hk] using
    f3PrimePosLevelAPDifference_normalized_tendsto_totient hk

/-- The actual positive-level prime count is exactly its nested AP difference. -/
theorem f3PrimePosLevelCountingReal_eq_APDifference
    (k : ℕ) (x : ℝ) (hk : 0 < k) :
    f3PrimePosLevelCountingReal k x =
      f3PrimePosLevelAPDifference k x := by
  rw [f3PrimePosLevelCountingReal, f3PrimePosLevelAPDifference,
    f3PrimeAPCountingReal_eq_card_apPrimes,
    f3PrimeAPCountingReal_eq_card_apPrimes,
    ← f3APPrimes_pos_sdiff_eq_pos_level k x hk]
  rw [Finset.card_sdiff_of_subset (f3APPrimes_pos_succ_subset k x hk),
    Nat.cast_sub (Finset.card_le_card (f3APPrimes_pos_succ_subset k x hk))]

/-- The actual primes with exact positive F₃ level `+k` have normalized
prime density constant `3⁻ᵏ` against the standard `x / log x` scale. -/
theorem f3PrimePosLevelCountingReal_normalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimePosLevelCountingReal k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  exact (f3PrimePosLevelAPDifference_normalized_tendsto hk).congr' <|
    Filter.Eventually.of_forall fun x => by
      exact congrArg (fun y : ℝ => y / (x / Real.log x))
        (f3PrimePosLevelCountingReal_eq_APDifference k x hk).symm

end OmegaBalance
