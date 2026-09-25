import OmegaBalance.F3CorrelationTail
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PadicValNat
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite counting lemmas for the F₃ L² tail

This module connects the pointwise excess-layer decomposition to exact counts of
multiples of powers of three, and records the weighted geometric sum that controls
the resulting layer series.  It does not yet assert the full Cesàro L² tail limit.
-/

namespace OmegaBalance

open Filter Topology

/-- Among `1, ..., N`, exactly `N / 3^a` integers are divisible by `3^a`. -/
theorem card_filter_Icc_dvd_pow_three (N a : ℕ) :
    ((Finset.Icc 1 N).filter fun m => 3 ^ a ∣ m).card = N / 3 ^ a := by
  have hset :
      ((Finset.Icc 1 N).filter fun m => 3 ^ a ∣ m) =
        ((Finset.Ioc 0 N).filter fun m => 3 ^ a ∣ m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  exact Nat.Ioc_filter_dvd_card_eq_div N (3 ^ a)

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

/-- The excess depth never exceeds its positive integer argument. -/
theorem v3Excess_le_self (R n : ℕ) : v3Excess R n ≤ n := by
  unfold v3Excess
  exact (Nat.sub_le _ _).trans <| by
    rw [v3_eq_padic]
    exact Nat.padicValNat_le_self n

/-- Real-valued version of the odd-number expansion of an excess square. -/
theorem v3Excess_sq_eq_odd_sum_real (R n : ℕ) :
    (v3Excess R n : ℝ) ^ 2 =
      ∑ t ∈ Finset.range (v3Excess R n), (2 * (t : ℝ) + 1) := by
  exact_mod_cast v3Excess_sq_eq_odd_sum R n

/-- On `1 ≤ m ≤ N`, the odd-number expansion can be extended to the fixed range
`0 ≤ t < N` by inserting zero outside the active excess layers. -/
theorem v3Excess_sq_eq_indicator_sum (R N m : ℕ)
    (hm : m ∈ Finset.Icc 1 N) :
    (v3Excess R m : ℝ) ^ 2 =
      ∑ t ∈ Finset.range N,
        if t < v3Excess R m then (2 * (t : ℝ) + 1) else 0 := by
  rw [v3Excess_sq_eq_odd_sum_real]
  have hm' := Finset.mem_Icc.mp hm
  have hexle : v3Excess R m ≤ N := (v3Excess_le_self R m).trans hm'.2
  have hfilter :
      (Finset.range N).filter (fun t => t < v3Excess R m) =
        Finset.range (v3Excess R m) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← hfilter, Finset.sum_filter]

/-- Exact finite double-counting identity for the excess-square mass on `1, ..., N`. -/
theorem sum_Icc_v3Excess_sq_eq_weighted_floor (R N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (v3Excess R m : ℝ) ^ 2) =
      ∑ t ∈ Finset.range N,
        (2 * (t : ℝ) + 1) * ((N / 3 ^ (R + t + 1) : ℕ) : ℝ) := by
  calc
    _ = ∑ m ∈ Finset.Icc 1 N,
        ∑ t ∈ Finset.range N,
          if t < v3Excess R m then (2 * (t : ℝ) + 1) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      exact v3Excess_sq_eq_indicator_sum R N m hm
    _ = ∑ t ∈ Finset.range N,
        ∑ m ∈ Finset.Icc 1 N,
          if t < v3Excess R m then (2 * (t : ℝ) + 1) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ Finset.range N,
        (2 * (t : ℝ) + 1) *
          (((Finset.Icc 1 N).filter fun m => t < v3Excess R m).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      calc
        (∑ m ∈ Finset.Icc 1 N,
            if t < v3Excess R m then (2 * (t : ℝ) + 1) else 0) =
            ∑ m ∈ Finset.Icc 1 N,
              (2 * (t : ℝ) + 1) *
                (if t < v3Excess R m then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro m hm
          by_cases h : t < v3Excess R m <;> simp [h]
        _ = (2 * (t : ℝ) + 1) *
            ∑ m ∈ Finset.Icc 1 N,
              (if t < v3Excess R m then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
        _ = (2 * (t : ℝ) + 1) *
            (((Finset.Icc 1 N).filter fun m => t < v3Excess R m).card : ℝ) := by
          rw [Finset.sum_boole]
    _ = ∑ t ∈ Finset.range N,
        (2 * (t : ℝ) + 1) * ((N / 3 ^ (R + t + 1) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [card_filter_Icc_lt_v3Excess]

/-- Uniform finite L² bound for a single excess coordinate. -/
theorem sum_Icc_v3Excess_sq_le (R N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (v3Excess R m : ℝ) ^ 2) ≤
      (N : ℝ) / (3 : ℝ) ^ R := by
  rw [sum_Icc_v3Excess_sq_eq_weighted_floor]
  exact odd_weighted_floor_sum_le R N N


/-- Reindex the right-neighbor excess square from centers `2 ≤ n ≤ N` to
the interval `3 ≤ m ≤ N+1`. -/
theorem sum_Icc_v3Excess_sq_add_one (R N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, (v3Excess R (n + 1) : ℝ) ^ 2) =
      ∑ m ∈ Finset.Icc 3 (N + 1), (v3Excess R m : ℝ) ^ 2 := by
  refine Finset.sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro a ha b hb hab
    exact Nat.add_right_cancel hab
  · intro m hm
    have hmBounds := Finset.mem_Icc.mp hm
    have hm3 : 3 ≤ m := hmBounds.1
    have hmN : m ≤ N + 1 := hmBounds.2
    refine ⟨m - 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · exact Nat.sub_add_cancel (by omega)
  · intro n hn
    rfl


/-- Reindex the left-neighbor excess square from centers `2 ≤ n ≤ N` to
the interval `1 ≤ m ≤ N-1`. -/
theorem sum_Icc_v3Excess_sq_sub_one (R N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, (v3Excess R (n - 1) : ℝ) ^ 2) =
      ∑ m ∈ Finset.Icc 1 (N - 1), (v3Excess R m : ℝ) ^ 2 := by
  refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    calc
      a = (a - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
      _ = (b - 1) + 1 := by rw [hab]
      _ = b := Nat.sub_add_cancel (by omega)
  · intro m hm
    refine ⟨m + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hm ⊢
      omega
    · omega
  · intro n hn
    rfl

/-- Finite squared-tail mass is exactly the sum of the two shifted excess-square
masses. -/
theorem sum_Icc_f3Tail_sq_eq_neighbor_excess (R N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, (f3Tail R n : ℝ) ^ 2) =
      (∑ n ∈ Finset.Icc 2 N, (v3Excess R (n + 1) : ℝ) ^ 2) +
      (∑ n ∈ Finset.Icc 2 N, (v3Excess R (n - 1) : ℝ) ^ 2) := by
  calc
    _ = ∑ n ∈ Finset.Icc 2 N,
        ((v3Excess R (n + 1) : ℝ) ^ 2 +
          (v3Excess R (n - 1) : ℝ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : 1 < n := by
        simp only [Finset.mem_Icc] at hn
        omega
      exact_mod_cast f3Tail_sq_eq_neighbor_excess R hn'
    _ = _ := by
      rw [Finset.sum_add_distrib]

/-- Uniform finite L² bound for the full `F₃ - F₃,R` tail. -/
theorem sum_Icc_f3Tail_sq_le (R N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, (f3Tail R n : ℝ) ^ 2) ≤
      ((N + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R +
      (N : ℝ) / (3 : ℝ) ^ R := by
  rw [sum_Icc_f3Tail_sq_eq_neighbor_excess,
    sum_Icc_v3Excess_sq_add_one, sum_Icc_v3Excess_sq_sub_one]
  apply add_le_add
  · calc
      (∑ m ∈ Finset.Icc 3 (N + 1), (v3Excess R m : ℝ) ^ 2) ≤
          ∑ m ∈ Finset.Icc 1 (N + 1), (v3Excess R m : ℝ) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro m hm
          simp only [Finset.mem_Icc] at hm ⊢
          omega
        · intro m hm hnot
          positivity
      _ ≤ ((N + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R :=
        sum_Icc_v3Excess_sq_le R (N + 1)
  · calc
      (∑ m ∈ Finset.Icc 1 (N - 1), (v3Excess R m : ℝ) ^ 2) ≤
          ∑ m ∈ Finset.Icc 1 N, (v3Excess R m : ℝ) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro m hm
          simp only [Finset.mem_Icc] at hm ⊢
          omega
        · intro m hm hnot
          positivity
      _ ≤ (N : ℝ) / (3 : ℝ) ^ R :=
        sum_Icc_v3Excess_sq_le R N


/-- Uniform normalized finite L² bound for the full truncation tail.
The bound is intentionally coarse but decays geometrically in the cutoff. -/
theorem f3Tail_sq_cesaro_le (R N : ℕ) (hN : 0 < N) :
    ((∑ n ∈ Finset.Icc 2 N, (f3Tail R n : ℝ) ^ 2) / (N : ℝ)) ≤
      3 / (3 : ℝ) ^ R := by
  have hs := sum_Icc_f3Tail_sq_le R N
  have hNr : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hp : (0 : ℝ) < (3 : ℝ) ^ R := by
    positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hnum :
      (((N + 1 : ℕ) : ℝ) + (N : ℝ)) ≤ 3 * (N : ℝ) := by
    push_cast
    nlinarith
  have hsum :
      ((N + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R +
          (N : ℝ) / (3 : ℝ) ^ R ≤
        (3 * (N : ℝ)) / (3 : ℝ) ^ R := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hnum hp.le
  calc
    ((∑ n ∈ Finset.Icc 2 N, (f3Tail R n : ℝ) ^ 2) / (N : ℝ)) ≤
        ((((N + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R +
          (N : ℝ) / (3 : ℝ) ^ R) / (N : ℝ)) :=
      div_le_div_of_nonneg_right hs hNr.le
    _ ≤ (((3 * (N : ℝ)) / (3 : ℝ) ^ R) / (N : ℝ)) :=
      div_le_div_of_nonneg_right hsum hNr.le
    _ = 3 / (3 : ℝ) ^ R := by
      field_simp [ne_of_gt hNr, ne_of_gt hp]

/-- The uniform normalized L² tail majorant vanishes as the cutoff tends to infinity. -/
theorem tendsto_f3Tail_sq_cesaro_majorant :
    Filter.Tendsto (fun R : ℕ => 3 / (3 : ℝ) ^ R) Filter.atTop (𝓝 0) := by
  have hpow :
      Filter.Tendsto (fun R : ℕ => ((1 : ℝ) / 3) ^ R) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa [div_pow, div_eq_mul_inv] using hpow.const_mul 3

/-- Finite Cauchy-Schwarz control with the established L² tail bound inserted. -/
theorem sum_Icc_f3Tail_mul_sq_le (R N : ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 2 N, (f3Tail R n : ℝ) * g n) ^ 2 ≤
      (((N + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R +
        (N : ℝ) / (3 : ℝ) ^ R) *
        ∑ n ∈ Finset.Icc 2 N, (g n) ^ 2 := by
  calc
    (∑ n ∈ Finset.Icc 2 N, (f3Tail R n : ℝ) * g n) ^ 2 ≤
        (∑ n ∈ Finset.Icc 2 N, (f3Tail R n : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc 2 N, (g n) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 2 N)
        (fun n => (f3Tail R n : ℝ)) g
    _ ≤ (((N + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R +
          (N : ℝ) / (3 : ℝ) ^ R) *
          ∑ n ∈ Finset.Icc 2 N, (g n) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (sum_Icc_f3Tail_sq_le R N)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Reindex a shifted tail square over the natural correlation interval. -/
theorem sum_Icc_f3Tail_sq_add_shift (R h N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, (f3Tail R (n + h) : ℝ) ^ 2) =
      ∑ m ∈ Finset.Icc (2 + h) (N + h), (f3Tail R m : ℝ) ^ 2 := by
  refine Finset.sum_bij (fun n _ => n + h) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro a ha b hb hab
    exact Nat.add_right_cancel hab
  · intro m hm
    have hmBounds := Finset.mem_Icc.mp hm
    refine ⟨m - h, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · exact Nat.sub_add_cancel (by omega)
  · intro n hn
    rfl

/-- The finite L² tail estimate remains valid after any fixed nonnegative shift,
at the cost of enlarging the terminal interval to N+h. -/
theorem sum_Icc_f3Tail_sq_shift_le (R h N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, (f3Tail R (n + h) : ℝ) ^ 2) ≤
      (((N + h + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R) +
      (((N + h : ℕ) : ℝ) / (3 : ℝ) ^ R) := by
  rw [sum_Icc_f3Tail_sq_add_shift]
  calc
    (∑ m ∈ Finset.Icc (2 + h) (N + h), (f3Tail R m : ℝ) ^ 2) ≤
        ∑ m ∈ Finset.Icc 2 (N + h), (f3Tail R m : ℝ) ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        simp only [Finset.mem_Icc] at hm ⊢
        omega
      · intro m hm hnot
        positivity
    _ ≤ (((N + h + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R) +
        (((N + h : ℕ) : ℝ) / (3 : ℝ) ^ R) :=
      sum_Icc_f3Tail_sq_le R (N + h)

/-- At cutoff zero the truncation vanishes, so the tail is the full statistic. -/
theorem f3Tail_zero (n : ℕ) : f3Tail 0 n = f3 n := by
  simp [f3Tail, f3Trunc, v3Trunc]

/-- Uniform finite second-moment bound for the shifted raw F₃ statistic. -/
theorem sum_Icc_f3_sq_shift_le (h N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, (f3 (n + h) : ℝ) ^ 2) ≤
      (((N + h + 1 : ℕ) : ℝ) + ((N + h : ℕ) : ℝ)) := by
  simpa [f3Tail_zero] using (sum_Icc_f3Tail_sq_shift_le 0 h N)

end OmegaBalance
