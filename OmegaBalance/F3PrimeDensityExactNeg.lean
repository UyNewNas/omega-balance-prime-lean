import OmegaBalance.F3PrimeDensityAPLimit

namespace OmegaBalance

/-- For a positive power of three, residue one is the same as divisibility of
the predecessor.  This is the small congruence bridge needed to turn the
valuation description of exact negative F₃ levels into AP predicates. -/
lemma f3_mod_pow_three_eq_one_iff_dvd_sub_one
    {p k : ℕ} (hp : 1 ≤ p) (hk : 0 < k) :
    p % (3 ^ k) = 1 ↔ 3 ^ k ∣ p - 1 := by
  have hm : 1 < 3 ^ k :=
    Nat.one_lt_pow hk.ne' (by norm_num : 1 < (3 : ℕ))
  have h := Nat.modEq_iff_dvd'
    (n := 3 ^ k) (a := 1) (b := p) hp
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hm, eq_comm] using h

/-- On primes above three, an exact negative F₃ level is exactly the residue-one
class modulo `3^k` with the residue-one class modulo `3^(k+1)` removed. -/
theorem f3_prime_eq_neg_level_iff_nested_residue
    {p k : ℕ} (hp : p.Prime) (h3 : 3 < p) (hk : 0 < k) :
    f3 p = -(k : ℤ) ↔
      p % (3 ^ k) = 1 ∧ p % (3 ^ (k + 1)) ≠ 1 := by
  rw [f3_prime_eq_neg_level_iff hp h3 hk]
  constructor
  · rintro ⟨hkdiv, hksdiv⟩
    constructor
    · exact (f3_mod_pow_three_eq_one_iff_dvd_sub_one hp.one_lt.le hk).2 hkdiv
    · intro hmod
      exact hksdiv <|
        (f3_mod_pow_three_eq_one_iff_dvd_sub_one hp.one_lt.le (by omega)).1 hmod
  · rintro ⟨hkmod, hksmod⟩
    constructor
    · exact (f3_mod_pow_three_eq_one_iff_dvd_sub_one hp.one_lt.le hk).1 hkmod
    · intro hdiv
      exact hksmod <|
        (f3_mod_pow_three_eq_one_iff_dvd_sub_one hp.one_lt.le (by omega)).2 hdiv


/-- Actual primes in the natural cutoff window with exact negative F₃ level. -/
noncomputable def f3PrimeNegLevelPrimes (k : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).filter fun p =>
    p.Prime ∧ 3 < p ∧ f3 p = -(k : ℤ)

/-- Real-valued cardinality of the exact negative F₃ level. -/
noncomputable def f3PrimeNegLevelCountingReal (k : ℕ) (x : ℝ) : ℝ :=
  (f3PrimeNegLevelPrimes k x).card

/-- The residue-one class modulo the next power of three is nested in the
current residue-one class.  The positivity assumption excludes modulus one. -/
lemma f3APPrimes_succ_subset (k : ℕ) (x : ℝ) (hk : 0 < k) :
    f3APPrimes (3 ^ (k + 1)) 1 x ⊆ f3APPrimes (3 ^ k) 1 x := by
  intro p hp
  rw [f3APPrimes] at hp ⊢
  rcases Finset.mem_filter.mp hp with ⟨hrange, hprime, hmod⟩
  refine Finset.mem_filter.mpr ⟨hrange, hprime, ?_⟩
  have hklt : 1 < 3 ^ k :=
    Nat.one_lt_pow hk.ne' (by norm_num : 1 < (3 : ℕ))
  have hkslt : 1 < 3 ^ (k + 1) :=
    Nat.one_lt_pow (by omega : k + 1 ≠ 0) (by norm_num : 1 < (3 : ℕ))
  have hmodeq : p ≡ 1 [MOD 3 ^ (k + 1)] := by
    show p % (3 ^ (k + 1)) = 1 % (3 ^ (k + 1))
    simpa [Nat.mod_eq_of_lt hkslt] using hmod
  have hdiv : 3 ^ k ∣ 3 ^ (k + 1) := by
    rw [pow_succ]
    exact dvd_mul_right _ _
  have hlow := hmodeq.of_dvd hdiv
  show p % (3 ^ k) = 1
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hklt] using hlow

/-- Removing the next residue-one class from the current one gives exactly the
primes with F₃ value `-k`. -/
theorem f3APPrimes_sdiff_eq_neg_level
    (k : ℕ) (x : ℝ) (hk : 0 < k) :
    f3APPrimes (3 ^ k) 1 x \ f3APPrimes (3 ^ (k + 1)) 1 x =
      f3PrimeNegLevelPrimes k x := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_sdiff.mp hp with ⟨hlow, hhigh⟩
    rw [f3APPrimes] at hlow
    rcases Finset.mem_filter.mp hlow with ⟨hrange, hprime, hmodk⟩
    have hmodks : p % (3 ^ (k + 1)) ≠ 1 := by
      intro hm
      apply hhigh
      rw [f3APPrimes]
      exact Finset.mem_filter.mpr ⟨hrange, hprime, hm⟩
    have hdivk : 3 ^ k ∣ p - 1 :=
      (f3_mod_pow_three_eq_one_iff_dvd_sub_one hprime.one_lt.le hk).1 hmodk
    have hthreepow : 3 ∣ 3 ^ k :=
      dvd_pow_self 3 hk.ne'
    have hthree : 3 ∣ p - 1 := hthreepow.trans hdivk
    have hsubpos : 0 < p - 1 := Nat.sub_pos_of_lt hprime.one_lt
    have hle : 3 ≤ p - 1 := Nat.le_of_dvd hsubpos hthree
    have h3 : 3 < p := by omega
    rw [f3PrimeNegLevelPrimes]
    exact Finset.mem_filter.mpr
      ⟨hrange, hprime, h3,
        (f3_prime_eq_neg_level_iff_nested_residue hprime h3 hk).2
          ⟨hmodk, hmodks⟩⟩
  · intro hp
    rw [f3PrimeNegLevelPrimes] at hp
    rcases Finset.mem_filter.mp hp with ⟨hrange, hprime, h3, hf⟩
    have hres :=
      (f3_prime_eq_neg_level_iff_nested_residue hprime h3 hk).1 hf
    exact Finset.mem_sdiff.mpr ⟨by
      rw [f3APPrimes]
      exact Finset.mem_filter.mpr ⟨hrange, hprime, hres.1⟩, by
      intro hhigh
      rw [f3APPrimes] at hhigh
      exact hres.2 (Finset.mem_filter.mp hhigh).2.2⟩

/-- The actual exact negative-level prime count is exactly the nested AP-count
difference, with no asymptotic replacement and no exceptional-prime error. -/
theorem f3PrimeNegLevelCountingReal_eq_APDifference
    (k : ℕ) (x : ℝ) (hk : 0 < k) :
    f3PrimeNegLevelCountingReal k x =
      f3PrimeNegLevelAPDifference k x := by
  rw [f3PrimeNegLevelCountingReal, f3PrimeNegLevelAPDifference,
    f3PrimeAPCountingReal_eq_card_apPrimes,
    f3PrimeAPCountingReal_eq_card_apPrimes,
    ← f3APPrimes_sdiff_eq_neg_level k x hk]
  exact Finset.cast_card_sdiff (f3APPrimes_succ_subset k x hk)

end OmegaBalance
