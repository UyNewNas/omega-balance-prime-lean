import OmegaBalance.F3PrimeDensityAPLimit

open Filter
open scoped Topology

namespace OmegaBalance

lemma pow_three_minus_one_coprime (k : ℕ) :
    (3 ^ k - 1).Coprime (3 ^ k) := by
  have hpos : 0 < 3 ^ k := by positivity
  have hdiff : 3 ^ k - (3 ^ k - 1) = 1 := by omega
  refine (Nat.coprime_sub_self_right
    (m := 3 ^ k - 1) (n := 3 ^ k) (by omega)).mp ?_
  simpa [hdiff]

lemma totient_pow_three (k : ℕ) (hk : 0 < k) :
    (3 ^ k).totient = 3 ^ (k - 1) * 2 := by
  simpa using (Nat.totient_prime_pow Nat.prime_three hk)

lemma f3PrimeAP_pow_three_minus_one_normalized_tendsto
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeAPCountingReal (3 ^ k) (3 ^ k - 1) x /
          (x / Real.log x))
      atTop (𝓝 ((((3 ^ k).totient : ℕ) : ℝ)⁻¹)) := by
  apply f3PrimeAPCountingReal_normalized_tendsto
  · positivity
  · exact pow_three_minus_one_coprime k
  · have hpos : 0 < 3 ^ k := by positivity
    omega

lemma f3PrimeAP_pow_three_one_normalized_tendsto
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeAPCountingReal (3 ^ k) 1 x /
          (x / Real.log x))
      atTop (𝓝 ((((3 ^ k).totient : ℕ) : ℝ)⁻¹)) := by
  apply f3PrimeAPCountingReal_normalized_tendsto
  · positivity
  · simp
  · have hdiv : 3 ∣ 3 ^ k := dvd_pow_self 3 hk.ne'
    have hle : 3 ≤ 3 ^ k := Nat.le_of_dvd (by positivity) hdiv
    omega

lemma inv_totient_pow_three_sub_succ (k : ℕ) (hk : 0 < k) :
    ((((3 ^ k).totient : ℕ) : ℝ)⁻¹ -
        (((3 ^ (k + 1)).totient : ℕ) : ℝ)⁻¹) =
      1 / (3 : ℝ) ^ k := by
  rw [totient_pow_three k hk, totient_pow_three (k + 1) (by omega)]
  norm_num only [Nat.add_sub_cancel]
  push_cast
  have hk_eq : k = k - 1 + 1 := by omega
  have hpow : (3 : ℝ) ^ k = (3 : ℝ) ^ (k - 1) * 3 := by
    calc
      (3 : ℝ) ^ k = (3 : ℝ) ^ (k - 1 + 1) :=
        congrArg (fun n : ℕ => (3 : ℝ) ^ n) hk_eq
      _ = (3 : ℝ) ^ (k - 1) * 3 := by rw [pow_succ]
  rw [hpow]
  field_simp <;> ring

lemma two_inv_totient_pow_three (K : ℕ) (hK : 0 < K) :
    ((((3 ^ K).totient : ℕ) : ℝ)⁻¹ +
        (((3 ^ K).totient : ℕ) : ℝ)⁻¹) =
      1 / (3 : ℝ) ^ (K - 1) := by
  rw [totient_pow_three K hK]
  push_cast
  field_simp <;> ring

noncomputable def f3PrimePosExactResidueCountingReal (k : ℕ) (x : ℝ) : ℝ :=
  f3PrimeAPCountingReal (3 ^ k) (3 ^ k - 1) x -
    f3PrimeAPCountingReal (3 ^ (k + 1)) (3 ^ (k + 1) - 1) x

noncomputable def f3PrimeNegExactResidueCountingReal (k : ℕ) (x : ℝ) : ℝ :=
  f3PrimeAPCountingReal (3 ^ k) 1 x -
    f3PrimeAPCountingReal (3 ^ (k + 1)) 1 x

noncomputable def f3PrimeTailResidueCountingReal (K : ℕ) (x : ℝ) : ℝ :=
  f3PrimeAPCountingReal (3 ^ K) (3 ^ K - 1) x +
    f3PrimeAPCountingReal (3 ^ K) 1 x

theorem f3PrimePosExactResidueCountingReal_normalized_tendsto
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimePosExactResidueCountingReal k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  simpa [f3PrimePosExactResidueCountingReal, sub_div,
    inv_totient_pow_three_sub_succ k hk] using
    (f3PrimeAP_pow_three_minus_one_normalized_tendsto k hk).sub
      (f3PrimeAP_pow_three_minus_one_normalized_tendsto (k + 1) (by omega))

theorem f3PrimeNegExactResidueCountingReal_normalized_tendsto
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeNegExactResidueCountingReal k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  simpa [f3PrimeNegExactResidueCountingReal, sub_div,
    inv_totient_pow_three_sub_succ k hk] using
    (f3PrimeAP_pow_three_one_normalized_tendsto k hk).sub
      (f3PrimeAP_pow_three_one_normalized_tendsto (k + 1) (by omega))

theorem f3PrimeTailResidueCountingReal_normalized_tendsto
    (K : ℕ) (hK : 0 < K) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeTailResidueCountingReal K x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ (K - 1))) := by
  simpa [f3PrimeTailResidueCountingReal, add_div,
    two_inv_totient_pow_three K hK] using
    (f3PrimeAP_pow_three_minus_one_normalized_tendsto K hK).add
      (f3PrimeAP_pow_three_one_normalized_tendsto K hK)

end OmegaBalance
