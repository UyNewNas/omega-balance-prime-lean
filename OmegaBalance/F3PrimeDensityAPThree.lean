import OmegaBalance.F3PrimeDensityAPLimit

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

lemma pow_three_sub_one_coprime_pow_three {k : ℕ} (hk : 0 < k) :
    (3 ^ k - 1).Coprime (3 ^ k) := by
  apply (f3_pos_residue_coprime hk).coprime_dvd_right
  rw [pow_succ]
  exact dvd_mul_right _ _

theorem f3PrimeAP_pow_three_minus_one_normalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeAPCountingReal (3 ^ k) (3 ^ k - 1) x / (x / Real.log x))
      atTop (𝓝 (((3 ^ k).totient : ℝ)⁻¹)) := by
  apply f3PrimeAPCountingReal_normalized_tendsto
  · positivity
  · exact pow_three_sub_one_coprime_pow_three hk
  · have hq : 0 < (3 : ℕ) ^ k := by positivity
    omega

theorem f3PrimeAP_pow_three_one_normalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeAPCountingReal (3 ^ k) 1 x / (x / Real.log x))
      atTop (𝓝 (((3 ^ k).totient : ℝ)⁻¹)) := by
  apply f3PrimeAPCountingReal_normalized_tendsto
  · positivity
  · simp
  · exact Nat.one_lt_pow (Nat.ne_of_gt hk) (by norm_num)

theorem f3PosLevelAPDiff_normalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        (f3PrimeAPCountingReal (3 ^ k) (3 ^ k - 1) x -
          f3PrimeAPCountingReal (3 ^ (k + 1)) (3 ^ (k + 1) - 1) x) /
          (x / Real.log x))
      atTop
      (𝓝 (((3 ^ k).totient : ℝ)⁻¹ -
        (((3 ^ (k + 1)).totient : ℝ)⁻¹))) := by
  simpa only [sub_div] using
    (f3PrimeAP_pow_three_minus_one_normalized_tendsto hk).sub
      (f3PrimeAP_pow_three_minus_one_normalized_tendsto (by omega : 0 < k + 1))

theorem f3NegLevelAPDiff_normalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        (f3PrimeAPCountingReal (3 ^ k) 1 x -
          f3PrimeAPCountingReal (3 ^ (k + 1)) 1 x) /
          (x / Real.log x))
      atTop
      (𝓝 (((3 ^ k).totient : ℝ)⁻¹ -
        (((3 ^ (k + 1)).totient : ℝ)⁻¹))) := by
  simpa only [sub_div] using
    (f3PrimeAP_pow_three_one_normalized_tendsto hk).sub
      (f3PrimeAP_pow_three_one_normalized_tendsto (by omega : 0 < k + 1))

end OmegaBalance
