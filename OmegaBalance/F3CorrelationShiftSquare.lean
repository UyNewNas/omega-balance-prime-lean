import OmegaBalance.F3CorrelationApproxPeriod

/-!
# Mean-square approximate periods for F₃

This module closes the analytic part of COR-2. The first step proves that a fixed
shift does not change the limiting square mean. It then expands the mean square
of a fixed difference into the two square means and the already-proved raw
correlation. Finally the power-of-three kernel evaluation from
`F3CorrelationApproxPeriod` gives the target `4 / 3^r` for `r > 0`.
-/

namespace OmegaBalance

open Filter Topology

/-- A fixed initial square mass, used only as the finite boundary removed when
reindexing a shifted square average. -/
noncomputable def f3SquarePrefix (h : ℕ) : ℝ :=
  ∑ i ∈ Finset.range h, (f3 (i + 2) : ℝ) ^ 2

/-- Real-valued version of the standard `Icc 2 N` to `range (N-1)`
reindexing. -/
theorem sum_Icc_two_eq_sum_range_sub_one_real (g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, g n) =
      ∑ i ∈ Finset.range (N - 1), g (i + 2) := by
  refine Finset.sum_bij (fun n _ => n - 2) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    refine ⟨i + 2, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    congr 1
    omega

/-- Reindex the square mass after a fixed shift. For `N ≥ 2`, it is the full
square mass through `N+h` minus the fixed prefix omitted by the shift. -/
theorem sum_Icc_f3_sq_shift_eq_full_sub_prefix
    (h N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, (f3 (n + h) : ℝ) ^ 2) =
      (∑ m ∈ Finset.Icc 2 (N + h), (f3 m : ℝ) ^ 2) -
        f3SquarePrefix h := by
  rw [sum_Icc_two_eq_sum_range_sub_one_real,
    sum_Icc_two_eq_sum_range_sub_one_real]
  have hlen : N + h - 1 = h + (N - 1) := by omega
  rw [hlen, Finset.sum_range_add]
  unfold f3SquarePrefix
  have htail :
      (∑ i ∈ Finset.range (N - 1), (f3 (h + i + 2) : ℝ) ^ 2) =
        ∑ i ∈ Finset.range (N - 1), (f3 (i + 2 + h) : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [htail]
  ring

/-- The square average after a fixed shift, on the same natural center window as
the correlation theorem. -/
noncomputable def f3ShiftSquareIccAverage (h N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 2 N, (f3 (n + h) : ℝ) ^ 2) / (N : ℝ)

/-- The zero-shift correlation average is exactly the unshifted square average. -/
theorem f3CorrelationIccAverage_zero_eq_square (N : ℕ) :
    f3CorrelationIccAverage 0 N =
      (∑ n ∈ Finset.Icc 2 N, (f3 n : ℝ) ^ 2) / (N : ℝ) := by
  unfold f3CorrelationIccAverage
  simp [pow_two]

/-- Exact boundary formula expressing the shifted square average through the
zero-shift correlation average at the enlarged endpoint. -/
theorem f3ShiftSquareIccAverage_eq
    (h N : ℕ) (hN : 2 ≤ N) :
    f3ShiftSquareIccAverage h N =
      f3CorrelationIccAverage 0 (N + h) *
          (((N + h : ℕ) : ℝ) / (N : ℝ)) -
        f3SquarePrefix h / (N : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hNh0 : ((N + h : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show N + h ≠ 0 by omega)
  unfold f3ShiftSquareIccAverage
  rw [sum_Icc_f3_sq_shift_eq_full_sub_prefix h N hN,
    f3CorrelationIccAverage_zero_eq_square]
  field_simp [hN0, hNh0]

/-- A fixed shift does not change the limiting raw F₃ square mean. -/
theorem tendsto_f3ShiftSquareIccAverage (h : ℕ) :
    Tendsto (fun N : ℕ => f3ShiftSquareIccAverage h N) atTop (𝓝 2) := by
  have hcorr :
      Tendsto (fun N : ℕ => f3CorrelationIccAverage 0 (N + h))
        atTop (𝓝 2) :=
    tendsto_f3CorrelationIccAverage_zero.comp (tendsto_add_atTop_nat h)
  have hratio :
      Tendsto (fun N : ℕ => (((N + h : ℕ) : ℝ) / (N : ℝ)))
        atTop (𝓝 (1 : ℝ)) := by
    simpa [add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (h : ℝ) 0 1 (d := 1) (by norm_num))
  have hprefix :
      Tendsto (fun N : ℕ => f3SquarePrefix h / (N : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim := (hcorr.mul hratio).sub hprefix
  have hlim' :
      Tendsto (fun N : ℕ => f3ShiftSquareIccAverage h N)
        atTop (𝓝 (2 * 1 - 0)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (f3ShiftSquareIccAverage_eq h N hN).symm
  simpa using hlim'

/-- Mean square of the fixed shift difference on the natural center window. -/
noncomputable def f3MeanSquareShiftIccAverage (h N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 2 N,
    ((f3 (n + h) : ℝ) - (f3 n : ℝ)) ^ 2) / (N : ℝ)

/-- Exact finite decomposition of a shift mean square into two square averages
and one correlation average. -/
theorem f3MeanSquareShiftIccAverage_eq (h N : ℕ) :
    f3MeanSquareShiftIccAverage h N =
      f3ShiftSquareIccAverage h N +
        f3CorrelationIccAverage 0 N -
        2 * f3CorrelationIccAverage h N := by
  have hsum :
      (∑ n ∈ Finset.Icc 2 N,
        ((f3 (n + h) : ℝ) - (f3 n : ℝ)) ^ 2) =
        (∑ n ∈ Finset.Icc 2 N, (f3 (n + h) : ℝ) ^ 2) +
        (∑ n ∈ Finset.Icc 2 N, (f3 n : ℝ) ^ 2) -
        2 * (∑ n ∈ Finset.Icc 2 N,
          (f3 n : ℝ) * (f3 (n + h) : ℝ)) := by
    calc
      _ = ∑ n ∈ Finset.Icc 2 N,
          ((f3 (n + h) : ℝ) ^ 2 + (f3 n : ℝ) ^ 2 -
            2 * ((f3 n : ℝ) * (f3 (n + h) : ℝ))) := by
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
  unfold f3MeanSquareShiftIccAverage f3ShiftSquareIccAverage
    f3CorrelationIccAverage
  rw [hsum]
  simp only [Nat.add_zero, Nat.add_comm h]
  ring

/-- The required mean-square approximate period theorem. The hypothesis
`r > 0` is essential: the shift-one case (`r = 0`) is governed separately by
the full correlation kernel and is not asserted here. -/
theorem tendsto_f3MeanSquareShiftIccAverage_pow_three
    {r : ℕ} (hr : 0 < r) :
    Tendsto
      (fun N : ℕ => f3MeanSquareShiftIccAverage (3 ^ r) N)
      atTop (𝓝 (4 / (3 : ℝ) ^ r)) := by
  have hshift := tendsto_f3ShiftSquareIccAverage (3 ^ r)
  have hraw := tendsto_f3CorrelationIccAverage_zero
  have hcross := tendsto_f3CorrelationIccAverage_pow_three hr
  have hlim :
      Tendsto
        (fun N : ℕ =>
          f3ShiftSquareIccAverage (3 ^ r) N +
            f3CorrelationIccAverage 0 N -
            2 * f3CorrelationIccAverage (3 ^ r) N)
        atTop
        (𝓝 (2 + 2 - 2 * (2 - 2 / (3 : ℝ) ^ r))) := by
    exact (hshift.add hraw).sub (hcross.const_mul 2)
  have hlim' :
      Tendsto
        (fun N : ℕ => f3MeanSquareShiftIccAverage (3 ^ r) N)
        atTop
        (𝓝 (2 + 2 - 2 * (2 - 2 / (3 : ℝ) ^ r))) := by
    refine hlim.congr' ?_
    filter_upwards [] with N
    exact (f3MeanSquareShiftIccAverage_eq (3 ^ r) N).symm
  have hvalue :
      2 + 2 - 2 * (2 - 2 / (3 : ℝ) ^ r) =
        4 / (3 : ℝ) ^ r := by
    ring
  rwa [hvalue] at hlim'

end OmegaBalance
