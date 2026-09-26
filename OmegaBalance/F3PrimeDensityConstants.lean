import OmegaBalance.F3PrimeDensityAPThree

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

lemma totient_pow_three {k : ℕ} (hk : 0 < k) :
    (3 ^ k).totient = 2 * 3 ^ (k - 1) := by
  rw [Nat.totient_prime_pow Nat.prime_three hk]
  norm_num
  ring

lemma inv_totient_pow_three_sub_succ {k : ℕ} (hk : 0 < k) :
    (((3 ^ k).totient : ℝ)⁻¹ -
      (((3 ^ (k + 1)).totient : ℝ)⁻¹)) =
      1 / (3 : ℝ) ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [totient_pow_three (by omega), totient_pow_three (by omega)]
  push_cast
  simp only [Nat.add_sub_cancel, Nat.add_assoc, pow_succ]
  field_simp
  ring

theorem f3PosLevelAPDiff_normalized_tendsto_exact
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        (f3PrimeAPCountingReal (3 ^ k) (3 ^ k - 1) x -
          f3PrimeAPCountingReal (3 ^ (k + 1)) (3 ^ (k + 1) - 1) x) /
          (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  simpa [inv_totient_pow_three_sub_succ hk] using
    f3PosLevelAPDiff_normalized_tendsto hk

theorem f3NegLevelAPDiff_normalized_tendsto_exact
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        (f3PrimeAPCountingReal (3 ^ k) 1 x -
          f3PrimeAPCountingReal (3 ^ (k + 1)) 1 x) /
          (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  simpa [inv_totient_pow_three_sub_succ hk] using
    f3NegLevelAPDiff_normalized_tendsto hk

end OmegaBalance
