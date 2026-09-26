import OmegaBalance.F3PrimeDensityLevelResidues
import Mathlib.Data.Finset.CastCard

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

/-- Actual prime count at the exact positive F3 level +k. -/
noncomputable def f3PrimePosLevelCountingReal (k : ℕ) (x : ℝ) : ℝ :=
  (((Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ f3 p = (k : ℤ)).card : ℝ)

/-- Actual prime count at the exact negative F3 level -k. -/
noncomputable def f3PrimeNegLevelCountingReal (k : ℕ) (x : ℝ) : ℝ :=
  (((Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ f3 p = -(k : ℤ)).card : ℝ)

/-- Replace the canonical remainder test in the AP counter by Nat.ModEq. -/
lemma f3PrimeAPCountingReal_eq_modEq_card
    {A a : ℕ} (ha : a < A) (x : ℝ) :
    f3PrimeAPCountingReal A a x =
      (((Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ p ≡ a [MOD A]).card : ℝ) := by
  unfold f3PrimeAPCountingReal
  congr 1
  ext p
  simp [Nat.ModEq, Nat.mod_eq_of_lt ha]

theorem f3PrimePosLevelCountingReal_eq_apDiff
    {k : ℕ} (hk : 0 < k) (x : ℝ) :
    f3PrimePosLevelCountingReal k x =
      f3PrimeAPCountingReal (3 ^ k) (3 ^ k - 1) x -
        f3PrimeAPCountingReal (3 ^ (k + 1)) (3 ^ (k + 1) - 1) x := by
  let U : Finset ℕ := Icc 0 ⌊x⌋₊
  let S : Finset ℕ :=
    U.filter fun p => p.Prime ∧ p ≡ 3 ^ k - 1 [MOD 3 ^ k]
  let T : Finset ℕ :=
    U.filter fun p => p.Prime ∧ p ≡ 3 ^ (k + 1) - 1 [MOD 3 ^ (k + 1)]
  have hdiv : (3 : ℕ) ^ k ∣ 3 ^ (k + 1) := by
    rw [pow_succ]
    exact dvd_mul_right _ _
  have hTS : T ⊆ S := by
    intro p hpT
    simp only [T, S, Finset.mem_filter] at hpT ⊢
    rcases hpT with ⟨hpU, hp, hdeep⟩
    refine ⟨hpU, hp, ?_⟩
    exact modEq_pow_three_sub_one_iff_dvd_add_one.mpr <|
      hdiv.trans (modEq_pow_three_sub_one_iff_dvd_add_one.mp hdeep)
  have hlevel :
      (U.filter fun p => p.Prime ∧ f3 p = (k : ℤ)) = S \ T := by
    ext p
    by_cases hpU : p ∈ U
    · by_cases hp : p.Prime
      · simp [S, T, hpU, hp, f3_prime_eq_pos_level_modEq_iff hp hk]
      · simp [S, T, hpU, hp]
    · simp [S, T, hpU]
  have hlowlt : 3 ^ k - 1 < (3 : ℕ) ^ k := by positivity
  have hhighlt : 3 ^ (k + 1) - 1 < (3 : ℕ) ^ (k + 1) := by positivity
  have hlow := f3PrimeAPCountingReal_eq_modEq_card
    (A := 3 ^ k) (a := 3 ^ k - 1) hlowlt x
  have hhigh := f3PrimeAPCountingReal_eq_modEq_card
    (A := 3 ^ (k + 1)) (a := 3 ^ (k + 1) - 1) hhighlt x
  unfold f3PrimePosLevelCountingReal
  change (((U.filter fun p => p.Prime ∧ f3 p = (k : ℤ)).card : ℕ) : ℝ) = _
  rw [hlevel]
  calc
    (((S \ T).card : ℕ) : ℝ) =
        (S.card : ℝ) - (T.card : ℝ) :=
      Finset.cast_card_sdiff hTS
    _ = _ := by
      rw [← hlow, ← hhigh]
      rfl

theorem f3PrimeNegLevelCountingReal_eq_apDiff
    {k : ℕ} (hk : 0 < k) (x : ℝ) :
    f3PrimeNegLevelCountingReal k x =
      f3PrimeAPCountingReal (3 ^ k) 1 x -
        f3PrimeAPCountingReal (3 ^ (k + 1)) 1 x := by
  let U : Finset ℕ := Icc 0 ⌊x⌋₊
  let S : Finset ℕ :=
    U.filter fun p => p.Prime ∧ p ≡ 1 [MOD 3 ^ k]
  let T : Finset ℕ :=
    U.filter fun p => p.Prime ∧ p ≡ 1 [MOD 3 ^ (k + 1)]
  have hdiv : (3 : ℕ) ^ k ∣ 3 ^ (k + 1) := by
    rw [pow_succ]
    exact dvd_mul_right _ _
  have hTS : T ⊆ S := by
    intro p hpT
    simp only [T, S, Finset.mem_filter] at hpT ⊢
    rcases hpT with ⟨hpU, hp, hdeep⟩
    have hp1 : 1 ≤ p := le_trans (by norm_num) hp.two_le
    refine ⟨hpU, hp, ?_⟩
    exact (modEq_one_iff_dvd_sub_one (j := k) (n := p) hp1).mpr <|
      hdiv.trans ((modEq_one_iff_dvd_sub_one
        (j := k + 1) (n := p) hp1).mp hdeep)
  have hlevel :
      (U.filter fun p => p.Prime ∧ f3 p = -(k : ℤ)) = S \ T := by
    ext p
    by_cases hpU : p ∈ U
    · by_cases hp : p.Prime
      · simp [S, T, hpU, hp, f3_prime_eq_neg_level_modEq_iff hp hk]
      · simp [S, T, hpU, hp]
    · simp [S, T, hpU]
  have honeLow : 1 < (3 : ℕ) ^ k :=
    Nat.one_lt_pow (Nat.ne_of_gt hk) (by norm_num)
  have honeHigh : 1 < (3 : ℕ) ^ (k + 1) :=
    Nat.one_lt_pow (by omega : k + 1 ≠ 0) (by norm_num)
  have hlow := f3PrimeAPCountingReal_eq_modEq_card
    (A := 3 ^ k) (a := 1) honeLow x
  have hhigh := f3PrimeAPCountingReal_eq_modEq_card
    (A := 3 ^ (k + 1)) (a := 1) honeHigh x
  unfold f3PrimeNegLevelCountingReal
  change (((U.filter fun p => p.Prime ∧ f3 p = -(k : ℤ)).card : ℕ) : ℝ) = _
  rw [hlevel]
  calc
    (((S \ T).card : ℕ) : ℝ) =
        (S.card : ℝ) - (T.card : ℝ) :=
      Finset.cast_card_sdiff hTS
    _ = _ := by
      rw [← hlow, ← hhigh]
      rfl

/-- Fixed positive F3 level +k has prime density 3^(-k), normalized by x/log x. -/
theorem f3PrimePosLevelCountingReal_normalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ => f3PrimePosLevelCountingReal k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  simpa only [f3PrimePosLevelCountingReal_eq_apDiff hk] using
    f3PosLevelAPDiff_normalized_tendsto_exact hk

/-- Fixed negative F3 level -k has the same prime density 3^(-k). -/
theorem f3PrimeNegLevelCountingReal_normalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ => f3PrimeNegLevelCountingReal k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  simpa only [f3PrimeNegLevelCountingReal_eq_apDiff hk] using
    f3NegLevelAPDiff_normalized_tendsto_exact hk

end OmegaBalance
