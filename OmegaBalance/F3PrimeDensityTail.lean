import OmegaBalance.F3PrimeDensityLevelCounts
import Mathlib.Data.Finset.CastCard

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

/-- The natAbs tail criterion is valid for every prime, including the two
small primes omitted by the >3 formulation. -/
theorem f3_prime_natAbs_ge_iff_all
    {p K : ℕ} (hp : p.Prime) (hK : 0 < K) :
    K ≤ (f3 p).natAbs ↔
      3 ^ K ∣ p + 1 ∨ 3 ^ K ∣ p - 1 := by
  by_cases h3 : 3 < p
  · exact f3_prime_natAbs_ge_iff hp h3 hK
  · have hp23 : p = 2 ∨ p = 3 := by
      have hp2 := hp.two_le
      omega
    rcases hp23 with rfl | rfl
    · have hv3 : v3 3 = 1 := by simpa using v3_pow_three 1
      have hf2 : f3 2 = 1 := by
        simp [f3, neighborDiff, hv3, v3_one]
      have hnot1 : ¬ (3 : ℕ) ^ K ∣ 1 := by
        intro hd
        have hle := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hd
        have hpowgt : 1 < (3 : ℕ) ^ K :=
          Nat.one_lt_pow (Nat.ne_of_gt hK) (by norm_num)
        omega
      have hdiv3 :
          (3 : ℕ) ^ K ∣ 3 ↔ K ≤ 1 := by
        simpa [hv3] using
          (pow_three_dvd_iff_le_v3 (n := 3) (k := K) (by norm_num))
      simpa [hf2, hnot1] using hdiv3.symm
    · have hv2 : v3 2 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      have hv4 : v3 4 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
      have hf3 : f3 3 = 0 := by simp [f3, neighborDiff, hv2, hv4]
      have h3pow : 3 ∣ (3 : ℕ) ^ K :=
        dvd_pow_self 3 (by omega : K ≠ 0)
      have hnot4 : ¬ (3 : ℕ) ^ K ∣ 4 := by
        intro hd
        have : 3 ∣ 4 := h3pow.trans hd
        norm_num at this
      have hnot2 : ¬ (3 : ℕ) ^ K ∣ 2 := by
        intro hd
        have : 3 ∣ 2 := h3pow.trans hd
        norm_num at this
      simp [hf3, hnot4, hnot2, hK]

/-- Tail event on primes as the union of the two reduced residue classes
minus one and plus one modulo 3^K. -/
theorem f3_prime_natAbs_ge_mod_iff
    {p K : ℕ} (hp : p.Prime) (hK : 0 < K) :
    K ≤ (f3 p).natAbs ↔
      p % (3 ^ K) = 3 ^ K - 1 ∨ p % (3 ^ K) = 1 := by
  have hp1 : 1 ≤ p := by omega
  have hpow : 1 < (3 : ℕ) ^ K :=
    Nat.one_lt_pow (Nat.ne_of_gt hK) (by norm_num)
  have hminus : 3 ^ K - 1 < (3 : ℕ) ^ K := by omega
  rw [f3_prime_natAbs_ge_iff_all hp hK,
    ← modEq_pow_three_sub_one_iff_dvd_add_one (j := K) (n := p),
    ← modEq_one_iff_dvd_sub_one (j := K) (n := p) hp1]
  simp only [Nat.ModEq, Nat.mod_eq_of_lt hminus, Nat.mod_eq_of_lt hpow]

/-- Prime count in the tail event |F3(p)| >= K. -/
noncomputable def f3PrimeAbsTailCountingReal (K : ℕ) (x : ℝ) : ℝ :=
  (((Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ K ≤ (f3 p).natAbs).card : ℝ)

/-- The tail count is exactly the sum of the two disjoint AP counts. -/
theorem f3PrimeAbsTailCountingReal_eq_apSum
    {K : ℕ} (hK : 0 < K) (x : ℝ) :
    f3PrimeAbsTailCountingReal K x =
      f3PrimeAPCountingReal (3 ^ K) (3 ^ K - 1) x +
        f3PrimeAPCountingReal (3 ^ K) 1 x := by
  let U : Finset ℕ := Icc 0 ⌊x⌋₊
  let S : Finset ℕ :=
    U.filter fun p => p.Prime ∧ p % (3 ^ K) = 3 ^ K - 1
  let T : Finset ℕ :=
    U.filter fun p => p.Prime ∧ p % (3 ^ K) = 1
  have hlevel :
      (U.filter fun p => p.Prime ∧ K ≤ (f3 p).natAbs) = S ∪ T := by
    ext p
    by_cases hpU : p ∈ U
    · by_cases hp : p.Prime
      · simp [S, T, hpU, hp, f3_prime_natAbs_ge_mod_iff hp hK]
      · simp [S, T, hpU, hp]
    · simp [S, T, hpU]
  have hpow : 2 < (3 : ℕ) ^ K := by
    have h3le : 3 ≤ (3 : ℕ) ^ K := by
      exact Nat.le_pow hK
    omega
  have hinter : S ∩ T = ∅ := by
    ext p
    by_cases hpS : p ∈ S
    · have hs := hpS
      simp only [S, Finset.mem_filter] at hs
      have hnotT : p ∉ T := by
        intro hpT
        have ht := hpT
        simp only [T, Finset.mem_filter] at ht
        omega
      simp [hpS, hnotT]
    · simp [hpS]
  unfold f3PrimeAbsTailCountingReal
  change (((U.filter fun p => p.Prime ∧ K ≤ (f3 p).natAbs).card : ℕ) : ℝ) = _
  rw [hlevel, Finset.cast_card_union, hinter]
  simp [S, T, U, f3PrimeAPCountingReal]

lemma two_mul_inv_totient_pow_three {K : ℕ} (hK : 0 < K) :
    2 * (((3 ^ K).totient : ℝ)⁻¹) =
      1 / (3 : ℝ) ^ (K - 1) := by
  rw [totient_pow_three hK]
  push_cast
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (K - 1) := by positivity
  field_simp
  ring

/-- Fixed positive depth threshold has prime density 3^(1-K), written with
a natural exponent as 1 / 3^(K-1). -/
theorem f3PrimeAbsTailCountingReal_normalized_tendsto
    {K : ℕ} (hK : 0 < K) :
    Tendsto
      (fun x : ℝ => f3PrimeAbsTailCountingReal K x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ (K - 1))) := by
  have hsum :=
    (f3PrimeAP_pow_three_minus_one_normalized_tendsto hK).add
      (f3PrimeAP_pow_three_one_normalized_tendsto hK)
  have hsum' :
      Tendsto
        (fun x : ℝ =>
          (f3PrimeAPCountingReal (3 ^ K) (3 ^ K - 1) x +
            f3PrimeAPCountingReal (3 ^ K) 1 x) / (x / Real.log x))
        atTop (𝓝 (2 * (((3 ^ K).totient : ℝ)⁻¹))) := by
    simpa [add_div, two_mul] using hsum
  simpa [f3PrimeAbsTailCountingReal_eq_apSum hK,
    two_mul_inv_totient_pow_three hK] using hsum'

end OmegaBalance
