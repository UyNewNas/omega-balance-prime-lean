import OmegaBalance.F3CorrelationTailError

/-!
# Fixed-cutoff Cesàro limit on the natural F₃ domain

The periodic cutoff correlation is naturally summed from zero, whereas the original
F₃ statistic is used on centers `2 ≤ n ≤ N`. This module bridges those conventions.
-/

namespace OmegaBalance

open Filter Topology

def f3TruncCorrelationIccSum (R h N : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 2 N, f3Trunc R n * f3Trunc R (n + h)

noncomputable def f3TruncCorrelationIccAverage (R h N : ℕ) : ℝ :=
  (f3TruncCorrelationIccSum R h N : ℝ) / (N : ℝ)

theorem sum_Icc_two_eq_sum_range_sub_one (f : ℕ → ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, f n) =
      ∑ i ∈ Finset.range (N - 1), f (i + 2) := by
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

theorem f3PeriodicCorrelationTerm_eq_trunc {R h n : ℕ} (hn : 1 < n) :
    f3PeriodicCorrelationTerm R h n =
      f3Trunc R n * f3Trunc R (n + h) := by
  simp only [f3PeriodicCorrelationTerm]
  rw [f3PeriodicTrunc_eq_f3Trunc hn,
    f3PeriodicTrunc_eq_f3Trunc (by omega : 1 < n + h)]

theorem f3TruncCorrelationIccSum_eq_periodic_sub_boundary
    (R h N : ℕ) (hN : 1 ≤ N) :
    f3TruncCorrelationIccSum R h N =
      f3PeriodicCorrelationPartialSum R h (N + 1) -
        f3PeriodicCorrelationTerm R h 0 -
        f3PeriodicCorrelationTerm R h 1 := by
  have hterms :
      f3TruncCorrelationIccSum R h N =
        ∑ n ∈ Finset.Icc 2 N, f3PeriodicCorrelationTerm R h n := by
    unfold f3TruncCorrelationIccSum
    apply Finset.sum_congr rfl
    intro n hn
    symm
    exact f3PeriodicCorrelationTerm_eq_trunc
      (by
        simp only [Finset.mem_Icc] at hn
        omega)
  rw [hterms, sum_Icc_two_eq_sum_range_sub_one]
  unfold f3PeriodicCorrelationPartialSum
  have hlen : N + 1 = 2 + (N - 1) := by omega
  rw [hlen, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Nat.add_comm 2]
  ring

theorem f3TruncCorrelationIccAverage_eq (R h N : ℕ) (hN : 0 < N) :
    f3TruncCorrelationIccAverage R h N =
      (f3PeriodicCorrelationPartialSum R h (N + 1) : ℝ) / (N : ℝ) -
      (f3PeriodicCorrelationTerm R h 0 : ℝ) / (N : ℝ) -
      (f3PeriodicCorrelationTerm R h 1 : ℝ) / (N : ℝ) := by
  have hs := f3TruncCorrelationIccSum_eq_periodic_sub_boundary R h N (by omega)
  have hsR :
      (f3TruncCorrelationIccSum R h N : ℝ) =
        (f3PeriodicCorrelationPartialSum R h (N + 1) : ℝ) -
          (f3PeriodicCorrelationTerm R h 0 : ℝ) -
          (f3PeriodicCorrelationTerm R h 1 : ℝ) := by
    exact_mod_cast hs
  rw [f3TruncCorrelationIccAverage, hsR]
  ring

theorem tendsto_f3PeriodicCorrelationPartialSum_succ_div (R h : ℕ) :
    Tendsto
      (fun N : ℕ =>
        (f3PeriodicCorrelationPartialSum R h (N + 1) : ℝ) / (N : ℝ))
      atTop (𝓝 (f3PeriodicCorrelationAverage R h)) := by
  have havg :
      Tendsto
        (fun N : ℕ => f3PeriodicCorrelationCesaroAverage R h (N + 1))
        atTop (𝓝 (f3PeriodicCorrelationAverage R h)) :=
    (tendsto_f3PeriodicCorrelationCesaroAverage R h).comp (tendsto_add_atTop_nat 1)
  have hratio :
      Tendsto (fun N : ℕ => (((N : ℝ) + 1) / (N : ℝ)))
        atTop (𝓝 (1 : ℝ)) := by
    simpa [add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ) 1 0 1 (d := 1) (by norm_num))
  have hmul := havg.mul hratio
  have hmul' :
      Tendsto
        (fun N : ℕ =>
          (f3PeriodicCorrelationPartialSum R h (N + 1) : ℝ) / (N : ℝ))
        atTop (𝓝 (f3PeriodicCorrelationAverage R h * 1)) := by
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [f3PeriodicCorrelationCesaroAverage]
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hN1r : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    push_cast
    field_simp [ne_of_gt hNr, ne_of_gt hN1r]
    ring
  simpa using hmul'

theorem tendsto_f3TruncCorrelationIccAverage (R h : ℕ) :
    Tendsto (fun N : ℕ => f3TruncCorrelationIccAverage R h N)
      atTop (𝓝 (f3PeriodicCorrelationAverage R h)) := by
  have hmain := tendsto_f3PeriodicCorrelationPartialSum_succ_div R h
  have hzero :
      Tendsto
        (fun N : ℕ => (f3PeriodicCorrelationTerm R h 0 : ℝ) / (N : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hone :
      Tendsto
        (fun N : ℕ => (f3PeriodicCorrelationTerm R h 1 : ℝ) / (N : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim := (hmain.sub hzero).sub hone
  have hlim' :
      Tendsto (fun N : ℕ => f3TruncCorrelationIccAverage R h N)
        atTop (𝓝 (f3PeriodicCorrelationAverage R h - 0 - 0)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (f3TruncCorrelationIccAverage_eq R h N hN).symm
  simpa using hlim'

end OmegaBalance
