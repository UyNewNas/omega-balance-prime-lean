import OmegaBalance.F3CorrelationTail
import Mathlib.Data.Int.CardIntervalMod

/-!
# Finite counting lemmas for the F₃ L² tail

This module connects the pointwise excess-layer decomposition to exact counts of
multiples of powers of three, and records the weighted geometric sum that controls
the resulting layer series.  It does not yet assert the full Cesàro L² tail limit.
-/

namespace OmegaBalance

/-- Among `1, ..., N`, exactly `N / 3^a` integers are divisible by `3^a`. -/
theorem card_filter_Icc_dvd_pow_three (N a : ℕ) :
    ((Finset.Icc 1 N).filter fun m => 3 ^ a ∣ m).card = N / 3 ^ a := by
  have hset :
      ((Finset.Icc 1 N).filter fun m => 3 ^ a ∣ m) =
        ((Finset.Ioc 0 N).filter fun m => m ≡ 0 [MOD 3 ^ a]) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc,
      Nat.modEq_zero_iff_dvd]
    omega
  rw [hset]
  have hcount := Nat.Ioc_filter_modEq_card (a := 0) (b := N) (r := 3 ^ a)
    (pow_pos (by decide) a) 0
  have hcount' :
      (((Finset.Ioc 0 N).filter fun m => m ≡ 0 [MOD 3 ^ a]).card : ℤ) =
        ((N / 3 ^ a : ℕ) : ℤ) := by
    rw [Rat.floor_natCast_div_natCast] at hcount
    have hnonneg : (0 : ℤ) ≤ ((N / 3 ^ a : ℕ) : ℤ) := by positivity
    rw [max_eq_left hnonneg] at hcount
    exact hcount
  exact_mod_cast hcount'

/-- The `t`-th excess layer occurs exactly at the positive multiples of
`3^(R+t+1)`, hence exactly `N / 3^(R+t+1)` times in `1, ..., N`. -/
theorem card_filter_Icc_lt_v3Excess (R N t : ℕ) :
    ((Finset.Icc 1 N).filter fun m => t < v3Excess R m).card =
      N / 3 ^ (R + t + 1) := by
  have hfilter :
      ((Finset.Icc 1 N).filter fun m => t < v3Excess R m) =
        ((Finset.Icc 1 N).filter fun m => 3 ^ (R + t + 1) ∣ m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hm, ht⟩
      refine ⟨hm, (pow_three_dvd_iff_lt_v3Excess (R := R) (t := t)
        (n := m) (by omega)).2 ht⟩
    · rintro ⟨hm, hd⟩
      refine ⟨hm, (pow_three_dvd_iff_lt_v3Excess (R := R) (t := t)
        (n := m) (by omega)).1 hd⟩
  rw [hfilter, card_filter_Icc_dvd_pow_three]

/-- The first `T` odd geometric weights have the exact closed form
`1 - (T+1)/3^T`.  Their infinite sum is therefore `1`. -/
theorem odd_geometric_partial_sum_real (T : ℕ) :
    (∑ t ∈ Finset.range T,
      (2 * (t : ℝ) + 1) / (3 : ℝ) ^ (t + 1)) =
      1 - ((T : ℝ) + 1) / (3 : ℝ) ^ T := by
  induction T with
  | zero => norm_num
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [pow_succ]
      field_simp
      ring

/-- Every finite initial segment of the odd geometric weights is at most `1`. -/
theorem odd_geometric_partial_sum_le_one (T : ℕ) :
    (∑ t ∈ Finset.range T,
      (2 * (t : ℝ) + 1) / (3 : ℝ) ^ (t + 1)) ≤ 1 := by
  rw [odd_geometric_partial_sum_real]
  have hnonneg :
      0 ≤ ((T : ℝ) + 1) / (3 : ℝ) ^ T := by positivity
  linarith

/-- After counting each retained excess layer, every finite weighted floor sum is
bounded by `N / 3^R`.  This is the quantitative estimate used for the L² tail. -/
theorem odd_weighted_floor_sum_le (R N T : ℕ) :
    (∑ t ∈ Finset.range T,
      (2 * (t : ℝ) + 1) * ((N / 3 ^ (R + t + 1) : ℕ) : ℝ)) ≤
      (N : ℝ) / (3 : ℝ) ^ R := by
  calc
    _ ≤ ∑ t ∈ Finset.range T,
        (2 * (t : ℝ) + 1) *
          ((N : ℝ) / (((3 ^ (R + t + 1) : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_left
      · exact Nat.cast_div_le
      · positivity
    _ = ((N : ℝ) / (3 : ℝ) ^ R) *
        ∑ t ∈ Finset.range T,
          (2 * (t : ℝ) + 1) / (3 : ℝ) ^ (t + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have hcast :
          (((3 ^ (R + t + 1) : ℕ) : ℝ)) = (3 : ℝ) ^ (R + t + 1) := by
        norm_cast
      rw [hcast, show R + t + 1 = R + (t + 1) by omega, pow_add]
      field_simp
    _ ≤ ((N : ℝ) / (3 : ℝ) ^ R) * 1 :=
      mul_le_mul_of_nonneg_left (odd_geometric_partial_sum_le_one T) (by positivity)
    _ = (N : ℝ) / (3 : ℝ) ^ R := by ring

end OmegaBalance
