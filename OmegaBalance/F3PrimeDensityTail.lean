import OmegaBalance.F3PrimeDensityExactPos

open Filter Topology

namespace OmegaBalance

theorem f3_prime_natAbs_ge_iff_residue
    {p K : ℕ} (hp : p.Prime) (hK : 0 < K) :
    K ≤ (f3 p).natAbs ↔
      p % (3 ^ K) = 3 ^ K - 1 ∨ p % (3 ^ K) = 1 := by
  by_cases h3 : 3 < p
  · rw [f3_prime_natAbs_ge_iff hp h3 hK,
      ← f3_mod_pow_three_eq_sub_one_iff_dvd_add_one hK,
      ← f3_mod_pow_three_eq_one_iff_dvd_sub_one hp.one_lt.le hK]
  · have hp23 : p = 2 ∨ p = 3 := by
      have hp2 : 2 ≤ p := hp.two_le
      omega
    rcases hp23 with rfl | rfl
    · have hf2 : f3 2 = 1 := by
        have h := (f3_of_mod_three_two (n := 2) (by omega) (by norm_num)).1
        rw [h]
        simpa using v3_pow_three 1
      have hv3 : v3 3 = 1 := by simpa using v3_pow_three 1
      rw [hf2]
      norm_num only [Int.natAbs_one]
      rw [f3_mod_pow_three_eq_sub_one_iff_dvd_add_one hK,
        f3_mod_pow_three_eq_one_iff_dvd_sub_one (p := 2) (by norm_num) hK]
      norm_num only [Nat.reduceAdd, Nat.reduceSub]
      rw [pow_three_dvd_iff_le_v3 (n := 3) (k := K) (by norm_num),
        pow_three_dvd_iff_le_v3 (n := 1) (k := K) (by norm_num),
        hv3, v3_one]
      omega
    · have hv4 : v3 4 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      have hv2 : v3 2 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      have hf3 : f3 3 = 0 := by simp [f3, neighborDiff, hv4, hv2]
      rw [hf3]
      norm_num only [Int.natAbs_zero]
      rw [f3_mod_pow_three_eq_sub_one_iff_dvd_add_one hK,
        f3_mod_pow_three_eq_one_iff_dvd_sub_one (p := 3) (by norm_num) hK]
      norm_num only [Nat.reduceAdd, Nat.reduceSub]
      rw [pow_three_dvd_iff_le_v3 (n := 4) (k := K) (by norm_num),
        pow_three_dvd_iff_le_v3 (n := 2) (k := K) (by norm_num),
        hv4, hv2]
      omega

noncomputable def f3PrimeTailPrimes (K : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ K ≤ (f3 p).natAbs

noncomputable def f3PrimeTailCountingReal (K : ℕ) (x : ℝ) : ℝ :=
  (f3PrimeTailPrimes K x).card

lemma f3APPrimes_tail_disjoint (K : ℕ) (x : ℝ) (hK : 0 < K) :
    Disjoint
      (f3APPrimes (3 ^ K) (3 ^ K - 1) x)
      (f3APPrimes (3 ^ K) 1 x) := by
  refine Finset.disjoint_left.mpr ?_
  intro p hminus hone
  rw [f3APPrimes] at hminus hone
  have hmminus := (Finset.mem_filter.mp hminus).2.2
  have hmone := (Finset.mem_filter.mp hone).2.2
  have hdiv : 3 ∣ (3 : ℕ) ^ K := dvd_pow_self 3 hK.ne'
  have hpow : 3 ≤ (3 : ℕ) ^ K := Nat.le_of_dvd (by positivity) hdiv
  omega

theorem f3APPrimes_tail_union_eq
    (K : ℕ) (x : ℝ) (hK : 0 < K) :
    f3APPrimes (3 ^ K) (3 ^ K - 1) x ∪
        f3APPrimes (3 ^ K) 1 x =
      f3PrimeTailPrimes K x := by
  ext p
  simp only [Finset.mem_union, f3APPrimes, f3PrimeTailPrimes,
    Finset.mem_filter]
  constructor
  · rintro (⟨hrange, hprime, hminus⟩ | ⟨hrange, hprime, hone⟩)
    · exact ⟨hrange, hprime,
        (f3_prime_natAbs_ge_iff_residue hprime hK).2 (Or.inl hminus)⟩
    · exact ⟨hrange, hprime,
        (f3_prime_natAbs_ge_iff_residue hprime hK).2 (Or.inr hone)⟩
  · rintro ⟨hrange, hprime, htail⟩
    rcases (f3_prime_natAbs_ge_iff_residue hprime hK).1 htail with hminus | hone
    · exact Or.inl ⟨hrange, hprime, hminus⟩
    · exact Or.inr ⟨hrange, hprime, hone⟩

theorem f3PrimeTailCountingReal_eq_APSum
    (K : ℕ) (x : ℝ) (hK : 0 < K) :
    f3PrimeTailCountingReal K x =
      f3PrimeAPCountingReal (3 ^ K) (3 ^ K - 1) x +
        f3PrimeAPCountingReal (3 ^ K) 1 x := by
  rw [f3PrimeTailCountingReal,
    ← f3APPrimes_tail_union_eq K x hK,
    Finset.card_union_of_disjoint (f3APPrimes_tail_disjoint K x hK),
    f3PrimeAPCountingReal_eq_card_apPrimes,
    f3PrimeAPCountingReal_eq_card_apPrimes]
  norm_num

lemma f3_pow_three_minus_one_coprime (K : ℕ) :
    (3 ^ K - 1).Coprime (3 ^ K) := by
  rw [Nat.coprime_self_sub_left (by omega : 1 ≤ (3 : ℕ) ^ K)]
  simp

lemma f3_totient_pow_three (K : ℕ) (hK : 0 < K) :
    (3 ^ K).totient = 3 ^ (K - 1) * 2 := by
  simpa using (Nat.totient_prime_pow Nat.prime_three hK)

lemma f3_two_inv_totient_pow_three (K : ℕ) (hK : 0 < K) :
    ((((3 ^ K).totient : ℕ) : ℝ)⁻¹ +
        (((3 ^ K).totient : ℕ) : ℝ)⁻¹) =
      1 / (3 : ℝ) ^ (K - 1) := by
  rw [f3_totient_pow_three K hK]
  push_cast
  field_simp <;> ring

theorem f3PrimeTailAPSum_normalized_tendsto
    (K : ℕ) (hK : 0 < K) :
    Tendsto
      (fun x : ℝ =>
        (f3PrimeAPCountingReal (3 ^ K) (3 ^ K - 1) x +
          f3PrimeAPCountingReal (3 ^ K) 1 x) /
          (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ (K - 1))) := by
  have hpowpos : 0 < (3 : ℕ) ^ K := by positivity
  have hpowgt : 1 < (3 : ℕ) ^ K :=
    Nat.one_lt_pow hK.ne' (by norm_num : 1 < (3 : ℕ))
  have hminus :=
    f3PrimeAPCountingReal_normalized_tendsto
      (A := 3 ^ K) (a := 3 ^ K - 1)
      hpowpos (f3_pow_three_minus_one_coprime K)
      (Nat.sub_lt hpowpos (by norm_num))
  have hone :=
    f3PrimeAPCountingReal_normalized_tendsto
      (A := 3 ^ K) (a := 1)
      hpowpos (by simp) hpowgt
  simpa [add_div, f3_two_inv_totient_pow_three K hK] using hminus.add hone

theorem f3PrimeTailCountingReal_normalized_tendsto
    {K : ℕ} (hK : 0 < K) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeTailCountingReal K x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ (K - 1))) := by
  exact (f3PrimeTailAPSum_normalized_tendsto K hK).congr' <|
    Filter.Eventually.of_forall fun x => by
      exact congrArg (fun y : ℝ => y / (x / Real.log x))
        (f3PrimeTailCountingReal_eq_APSum K x hK).symm

end OmegaBalance
