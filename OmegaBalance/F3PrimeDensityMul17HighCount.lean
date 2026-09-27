import OmegaBalance.F3PrimeDensityMul17High

open Filter Topology

namespace OmegaBalance

/-- For output levels at least three, exact multiplier-17 depth is exactly one
primitive residue modulo `3^k` with its unique lift modulo `3^(k+1)`
removed. -/
theorem f3_seventeen_mul_eq_level_iff_nested_residue
    {q k : ℕ} (hq : q.Prime) (hk : 3 ≤ k) :
    f3 (17 * q) = (k : ℤ) ↔
      q % (3 ^ k) = f3Mul17Residue k ∧
        q % (3 ^ (k + 1)) ≠ f3Mul17Residue (k + 1) := by
  constructor
  · intro hout
    have hf := f3_seventeen_mul_high_level_implies_neg_two hq hk hout
    have hmods := f3_prime_eq_neg_two_mod_twentyseven hq hf
    have hqmod3 : q % 3 = 1 := by
      rcases hmods with h10 | h19 <;> omega
    have hprodmod3 : (17 * q) % 3 = 2 := by
      norm_num [Nat.mul_mod, hqmod3]
    have hgt : 1 < 17 * q := by
      have := hq.two_le
      omega
    have he := (f3_of_mod_three_two hgt hprodmod3).1
    have hv : v3 (17 * q + 1) = k := by
      rw [he] at hout
      exact_mod_cast hout
    have hdepth :=
      (v3_eq_iff_pow_three_dvd_not_succ
        (n := 17 * q + 1) (k := k) (by omega)).1 hv
    constructor
    · exact
        (pow_three_dvd_seventeen_mul_add_one_iff_mod_eq_residue k q).1
          hdepth.1
    · intro hres
      exact hdepth.2 <|
        (pow_three_dvd_seventeen_mul_add_one_iff_mod_eq_residue (k + 1) q).2
          hres
  · rintro ⟨hres, hresSucc⟩
    have hdiv : 3 ^ k ∣ 17 * q + 1 :=
      (pow_three_dvd_seventeen_mul_add_one_iff_mod_eq_residue k q).2 hres
    have hnDiv : ¬ 3 ^ (k + 1) ∣ 17 * q + 1 := by
      intro hdivSucc
      exact hresSucc <|
        (pow_three_dvd_seventeen_mul_add_one_iff_mod_eq_residue (k + 1) q).1
          hdivSucc
    have hv : v3 (17 * q + 1) = k :=
      (v3_eq_iff_pow_three_dvd_not_succ
        (n := 17 * q + 1) (k := k) (by omega)).2 ⟨hdiv, hnDiv⟩
    have hthreePow : 3 ∣ (3 : ℕ) ^ k :=
      dvd_pow_self 3 (by omega : k ≠ 0)
    have hthree : 3 ∣ 17 * q + 1 := hthreePow.trans hdiv
    have hzero : 17 * q + 1 ≡ 0 [MOD 3] :=
      Nat.modEq_zero_iff_dvd.mpr hthree
    have htwo : 2 + 1 ≡ 0 [MOD 3] := by
      norm_num [Nat.ModEq]
    have hprod : 17 * q ≡ 2 [MOD 3] :=
      Nat.ModEq.add_right_cancel' 1 (hzero.trans htwo.symm)
    have hprodmod3 : (17 * q) % 3 = 2 := by
      simpa [Nat.ModEq] using hprod
    have hgt : 1 < 17 * q := by
      have := hq.two_le
      omega
    rw [(f3_of_mod_three_two hgt hprodmod3).1, hv]

/-- The distinguished multiplier-17 progression at the next depth is nested
inside the current one. -/
lemma f3APPrimes_mul17_succ_subset (k : ℕ) (x : ℝ) :
    f3APPrimes (3 ^ (k + 1)) (f3Mul17Residue (k + 1)) x ⊆
      f3APPrimes (3 ^ k) (f3Mul17Residue k) x := by
  intro q hq
  rw [f3APPrimes] at hq ⊢
  rcases Finset.mem_filter.mp hq with ⟨hrange, hprime, hres⟩
  refine Finset.mem_filter.mpr ⟨hrange, hprime, ?_⟩
  have hdivSucc : 3 ^ (k + 1) ∣ 17 * q + 1 :=
    (pow_three_dvd_seventeen_mul_add_one_iff_mod_eq_residue (k + 1) q).2
      hres
  have hpow : 3 ^ k ∣ 3 ^ (k + 1) := by
    rw [pow_succ]
    exact dvd_mul_right _ _
  exact (pow_three_dvd_seventeen_mul_add_one_iff_mod_eq_residue k q).1
    (hpow.trans hdivSucc)

/-- Genuine conditioned primes with multiplier-17 output exactly `+k`. -/
noncomputable def f3PrimeMul17LevelPrimes (k : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).filter fun q =>
    q.Prime ∧ f3 q = -2 ∧ f3 (17 * q) = (k : ℤ)

/-- The genuine conditioned event is exactly a nested AP difference. -/
theorem f3APPrimes_mul17_sdiff_eq_level
    (k : ℕ) (x : ℝ) (hk : 3 ≤ k) :
    f3APPrimes (3 ^ k) (f3Mul17Residue k) x \
        f3APPrimes (3 ^ (k + 1)) (f3Mul17Residue (k + 1)) x =
      f3PrimeMul17LevelPrimes k x := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_sdiff.mp hq with ⟨hlow, hhigh⟩
    rw [f3APPrimes] at hlow
    rcases Finset.mem_filter.mp hlow with ⟨hrange, hprime, hres⟩
    have hresSucc :
        q % (3 ^ (k + 1)) ≠ f3Mul17Residue (k + 1) := by
      intro hm
      apply hhigh
      rw [f3APPrimes]
      exact Finset.mem_filter.mpr ⟨hrange, hprime, hm⟩
    have hout : f3 (17 * q) = (k : ℤ) :=
      (f3_seventeen_mul_eq_level_iff_nested_residue hprime hk).2
        ⟨hres, hresSucc⟩
    have hf : f3 q = -2 :=
      f3_seventeen_mul_high_level_implies_neg_two hprime hk hout
    rw [f3PrimeMul17LevelPrimes]
    exact Finset.mem_filter.mpr ⟨hrange, hprime, hf, hout⟩
  · intro hq
    rw [f3PrimeMul17LevelPrimes] at hq
    rcases Finset.mem_filter.mp hq with ⟨hrange, hprime, hf, hout⟩
    have hres :=
      (f3_seventeen_mul_eq_level_iff_nested_residue hprime hk).1 hout
    exact Finset.mem_sdiff.mpr ⟨by
      rw [f3APPrimes]
      exact Finset.mem_filter.mpr ⟨hrange, hprime, hres.1⟩, by
      intro hnext
      rw [f3APPrimes] at hnext
      exact hres.2 (Finset.mem_filter.mp hnext).2.2⟩

noncomputable def f3PrimeMul17LevelCountingReal (k : ℕ) (x : ℝ) : ℝ :=
  (f3PrimeMul17LevelPrimes k x).card

noncomputable def f3PrimeMul17LevelAPDifference (k : ℕ) (x : ℝ) : ℝ :=
  f3PrimeAPCountingReal (3 ^ k) (f3Mul17Residue k) x -
    f3PrimeAPCountingReal (3 ^ (k + 1)) (f3Mul17Residue (k + 1)) x

/-- The multiplier-17 AP proxy at output level `k` has normalized density
`3^{-k}`. -/
theorem f3PrimeMul17LevelAPDifference_normalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeMul17LevelAPDifference k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  have h0 :=
    f3PrimeAPCountingReal_normalized_tendsto
      (A := 3 ^ k) (a := f3Mul17Residue k)
      (by positivity) (f3Mul17Residue_coprime k) (f3Mul17Residue_lt k)
  have h1 :=
    f3PrimeAPCountingReal_normalized_tendsto
      (A := 3 ^ (k + 1)) (a := f3Mul17Residue (k + 1))
      (by positivity) (f3Mul17Residue_coprime (k + 1))
      (f3Mul17Residue_lt (k + 1))
  simpa [f3PrimeMul17LevelAPDifference, sub_div,
    f3_totient_three_pow_inv_sub_succ hk] using h0.sub h1

theorem f3PrimeMul17LevelCountingReal_eq_APDifference
    (k : ℕ) (x : ℝ) (hk : 3 ≤ k) :
    f3PrimeMul17LevelCountingReal k x =
      f3PrimeMul17LevelAPDifference k x := by
  rw [f3PrimeMul17LevelCountingReal, f3PrimeMul17LevelAPDifference,
    f3PrimeAPCountingReal_eq_card_apPrimes,
    f3PrimeAPCountingReal_eq_card_apPrimes,
    ← f3APPrimes_mul17_sdiff_eq_level k x hk]
  rw [Finset.card_sdiff_of_subset (f3APPrimes_mul17_succ_subset k x),
    Nat.cast_sub
      (Finset.card_le_card (f3APPrimes_mul17_succ_subset k x))]

theorem f3PrimeMul17LevelCountingReal_normalized_tendsto
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeMul17LevelCountingReal k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  exact (f3PrimeMul17LevelAPDifference_normalized_tendsto
    (k := k) (by omega)).congr' <|
      Filter.Eventually.of_forall fun x => by
        exact congrArg (fun y : ℝ => y / (x / Real.log x))
          (f3PrimeMul17LevelCountingReal_eq_APDifference k x hk).symm

/-- Genuine relative count of the branch `F₃(17q)=2+j` inside
`F₃(q)=-2`. -/
noncomputable def f3PrimeMul17HighRelativeRatio (j : ℕ) (x : ℝ) : ℝ :=
  f3PrimeMul17LevelCountingReal (2 + j) x /
    f3PrimeNegLevelCountingReal 2 x

/-- For every `j≥1`, among primes with `F₃(q)=-2`, the exact branch
`F₃(17q)=2+j` has relative limiting proportion `3^{-j}`. -/
theorem f3PrimeMul17HighRelativeRatio_tendsto
    {j : ℕ} (hj : 0 < j) :
    Tendsto (f3PrimeMul17HighRelativeRatio j) atTop
      (𝓝 (1 / (3 : ℝ) ^ j)) := by
  have hnum :=
    f3PrimeMul17LevelCountingReal_normalized_tendsto
      (k := 2 + j) (by omega)
  have hden :=
    f3PrimeNegLevelCountingReal_normalized_tendsto
      (k := 2) (by norm_num)
  have hratio :=
    hnum.div hden (by norm_num : (1 / (3 : ℝ) ^ 2) ≠ 0)
  have hconst :
      (1 / (3 : ℝ) ^ (2 + j)) / (1 / (3 : ℝ) ^ 2) =
        1 / (3 : ℝ) ^ j := by
    rw [pow_add]
    field_simp
  rw [hconst] at hratio
  refine hratio.congr' ?_
  have hden_ne :
      ∀ᶠ x : ℝ in atTop,
        f3PrimeNegLevelCountingReal 2 x / (x / Real.log x) ≠ 0 :=
    hden.eventually_ne (by norm_num : (1 / (3 : ℝ) ^ 2) ≠ 0)
  filter_upwards [hden_ne] with x hx
  have hscale : x / Real.log x ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  simpa [f3PrimeMul17HighRelativeRatio] using
    (div_div_div_cancel_right₀ hscale
      (f3PrimeMul17LevelCountingReal (2 + j) x)
      (f3PrimeNegLevelCountingReal 2 x))

end OmegaBalance
