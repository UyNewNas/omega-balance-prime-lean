import OmegaBalance.F3CorrelationLimitExchange

/-!
# Shifted square averages for the F₃ approximate period

This module begins COR-2.  It proves that any fixed translate of the square
sequence has the same Cesàro mean as the unshifted square sequence.  The argument
uses an exact finite prefix correction, so no boundedness assumption on `F₃`
is smuggled in.
-/

namespace OmegaBalance

open Filter Topology

/-- Real-valued version of the natural-window/range reindexing used by the
correlation bridge. -/
theorem sum_Icc_two_eq_sum_range_sub_one_real (f : ℕ → ℝ) (N : ℕ) :
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

/-- The fixed initial square mass removed when an average is translated by `s`. -/
noncomputable def f3SquarePrefix (s : ℕ) : ℝ :=
  ∑ i ∈ Finset.range s, (f3 (i + 2) : ℝ) ^ 2

/-- Square average after translating every center by a fixed `s`. -/
noncomputable def f3ShiftSquareIccAverage (s N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 2 N, (f3 (n + s) : ℝ) ^ 2) / (N : ℝ)

/-- A translated square sum is the longer unshifted square sum minus one fixed
initial prefix. -/
theorem sum_Icc_f3_sq_add_shift_eq (s N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc 2 N, (f3 (n + s) : ℝ) ^ 2) =
      (∑ n ∈ Finset.Icc 2 (N + s), (f3 n : ℝ) ^ 2) -
        f3SquarePrefix s := by
  rw [sum_Icc_two_eq_sum_range_sub_one_real,
    sum_Icc_two_eq_sum_range_sub_one_real]
  unfold f3SquarePrefix
  have hlen : N + s - 1 = s + (N - 1) := by omega
  rw [hlen, Finset.sum_range_add]
  have htail :
      (∑ i ∈ Finset.range (N - 1), (f3 (i + 2 + s) : ℝ) ^ 2) =
        ∑ i ∈ Finset.range (N - 1), (f3 (s + i + 2) : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    omega
  rw [htail]
  ring

/-- Exact relation between a translated square average and the unshifted
correlation average at lag zero. -/
theorem f3ShiftSquareIccAverage_eq (s N : ℕ) (hN : 0 < N) :
    f3ShiftSquareIccAverage s N =
      (((N + s : ℕ) : ℝ) / (N : ℝ)) *
        f3CorrelationIccAverage 0 (N + s) -
      f3SquarePrefix s / (N : ℝ) := by
  rw [f3ShiftSquareIccAverage, sum_Icc_f3_sq_add_shift_eq s N hN]
  unfold f3CorrelationIccAverage
  simp only [Nat.add_zero]
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNsr : (0 : ℝ) < ((N + s : ℕ) : ℝ) := by positivity
  simp_rw [pow_two]
  field_simp [ne_of_gt hNr, ne_of_gt hNsr]
  ring

@[simp] theorem f3PadicKernel_two : f3PadicKernel 2 = 1 := by
  rw [f3PadicKernel, if_neg (by norm_num)]
  rw [v3_eq_zero_of_not_dvd (by norm_num)]
  norm_num

/-- The raw square Cesàro mean is two. -/
theorem tendsto_f3CorrelationIccAverage_zero :
    Tendsto (fun N : ℕ => f3CorrelationIccAverage 0 N) atTop (𝓝 (2 : ℝ)) := by
  simpa using (tendsto_f3CorrelationIccAverage 0)

/-- Translating the square sequence by any fixed amount preserves its Cesàro
mean.  The proof uses the exact fixed-prefix correction above. -/
theorem tendsto_f3ShiftSquareIccAverage (s : ℕ) :
    Tendsto (fun N : ℕ => f3ShiftSquareIccAverage s N) atTop (𝓝 (2 : ℝ)) := by
  have hcorr :
      Tendsto (fun N : ℕ => f3CorrelationIccAverage 0 (N + s))
        atTop (𝓝 (2 : ℝ)) :=
    tendsto_f3CorrelationIccAverage_zero.comp (tendsto_add_atTop_nat s)
  have hratio :
      Tendsto (fun N : ℕ => (((N + s : ℕ) : ℝ) / (N : ℝ)))
        atTop (𝓝 (1 : ℝ)) := by
    simpa [add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ)
        (s : ℝ) 0 1 (d := 1) (by norm_num))
  have hmain := hratio.mul hcorr
  have hpref :
      Tendsto (fun N : ℕ => f3SquarePrefix s / (N : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim := hmain.sub hpref
  have hlim' :
      Tendsto (fun N : ℕ => f3ShiftSquareIccAverage s N)
        atTop (𝓝 ((1 : ℝ) * 2 - 0)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (f3ShiftSquareIccAverage_eq s N hN).symm
  simpa using hlim'

end OmegaBalance
