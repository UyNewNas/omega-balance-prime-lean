import OmegaBalance.F3CorrelationTruncCesaro

/-!
# Exchange the F₃ cutoff and Cesàro limits

The previous layers provide, on the natural window `2 ≤ n ≤ N`:

* fixed-cutoff Cesàro convergence of the truncated correlation;
* a square error bound uniform in the averaging length;
* geometric decay of that uniform error majorant as the cutoff tends to infinity.

This module combines those three ingredients with an explicit epsilon argument.  In
particular, the proof does not identify a pointwise cutoff equality with a limit
exchange and does not pass to any prime subsequence.
-/

namespace OmegaBalance

open Filter Topology

/-- The raw F₃ correlation average on the natural center window.  The denominator
is exactly `N`, matching the stated Cesàro normalization. -/
noncomputable def f3CorrelationIccAverage (h N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 2 N, (f3 n : ℝ) * (f3 (n + h) : ℝ)) / (N : ℝ)

/-- Exact difference between the raw and fixed-cutoff natural-window averages. -/
theorem f3CorrelationIccAverage_sub_trunc (R h N : ℕ) :
    f3CorrelationIccAverage h N - f3TruncCorrelationIccAverage R h N =
      (∑ n ∈ Finset.Icc 2 N,
        ((f3 n : ℝ) * (f3 (n + h) : ℝ) -
          (f3Trunc R n : ℝ) * (f3Trunc R (n + h) : ℝ))) / (N : ℝ) := by
  unfold f3CorrelationIccAverage f3TruncCorrelationIccAverage
    f3TruncCorrelationIccSum
  rw [Finset.sum_sub_distrib]
  push_cast
  ring

/-- The normalized raw/cutoff correlation difference inherits the uniform square
majorant already proved for its finite numerator. -/
theorem f3CorrelationIccAverage_sub_trunc_sq_le_majorant
    (R h N : ℕ) (hN : 0 < N) :
    (f3CorrelationIccAverage h N -
        f3TruncCorrelationIccAverage R h N) ^ 2 ≤
      f3CorrelationErrorSqMajorant R h := by
  rw [f3CorrelationIccAverage_sub_trunc]
  exact f3_correlation_cesaro_error_sq_le_majorant R h N hN

/-- The full untruncated F₃ correlation kernel on all integer centers.

For fixed `h`, the proof first chooses a cutoff whose uniform raw/cutoff error and
complete-period cutoff error are both small, and only then chooses the averaging
length for that fixed cutoff.  Thus the cutoff/Cesàro interchange is explicit. -/
theorem tendsto_f3CorrelationIccAverage (h : ℕ) :
    Tendsto (fun N : ℕ => f3CorrelationIccAverage h N) atTop
      (𝓝 (f3PadicKernel (Nat.dist h 2) + f3PadicKernel (h + 2) -
        2 * f3PadicKernel h)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hδsq : 0 < δ ^ 2 := by positivity
  obtain ⟨RM, hRM⟩ :=
    Metric.tendsto_atTop.1 (tendsto_f3CorrelationErrorSqMajorant h)
      (δ ^ 2) hδsq
  obtain ⟨RP, hRP⟩ :=
    Metric.tendsto_atTop.1 (tendsto_f3PeriodicCorrelationAverage h) δ hδ
  let R : ℕ := max RM RP
  have hmajorDist :
      dist (f3CorrelationErrorSqMajorant R h) 0 < δ ^ 2 :=
    hRM R (by
      dsimp [R]
      exact le_max_left _ _)
  have hperiod :
      dist (f3PeriodicCorrelationAverage R h)
        (f3PadicKernel (Nat.dist h 2) + f3PadicKernel (h + 2) -
          2 * f3PadicKernel h) < δ :=
    hRP R (by
      dsimp [R]
      exact le_max_right _ _)
  have hmajorNonneg : 0 ≤ f3CorrelationErrorSqMajorant R h := by
    unfold f3CorrelationErrorSqMajorant
    positivity
  have hmajor : f3CorrelationErrorSqMajorant R h < δ ^ 2 := by
    simpa [Real.dist_eq, abs_of_nonneg hmajorNonneg] using hmajorDist
  obtain ⟨N₀, hN₀⟩ :=
    Metric.tendsto_atTop.1 (tendsto_f3TruncCorrelationIccAverage R h) δ hδ
  refine ⟨max N₀ 1, ?_⟩
  intro N hN
  have hNN₀ : N₀ ≤ N :=
    le_trans (le_max_left N₀ 1) hN
  have hNpos : 0 < N :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N₀ 1) hN)
  have hcut :
      dist (f3TruncCorrelationIccAverage R h N)
        (f3PeriodicCorrelationAverage R h) < δ :=
    hN₀ N hNN₀
  have hsq :
      (f3CorrelationIccAverage h N -
          f3TruncCorrelationIccAverage R h N) ^ 2 <
        δ ^ 2 :=
    lt_of_le_of_lt
      (f3CorrelationIccAverage_sub_trunc_sq_le_majorant R h N hNpos)
      hmajor
  have herr :
      dist (f3CorrelationIccAverage h N)
        (f3TruncCorrelationIccAverage R h N) < δ := by
    rw [Real.dist_eq]
    have habs :=
      (sq_lt_sq.mp hsq :
        |f3CorrelationIccAverage h N -
            f3TruncCorrelationIccAverage R h N| < |δ|)
    simpa [abs_of_pos hδ] using habs
  have htri :
      dist (f3TruncCorrelationIccAverage R h N)
          (f3PadicKernel (Nat.dist h 2) + f3PadicKernel (h + 2) -
            2 * f3PadicKernel h) ≤
        dist (f3TruncCorrelationIccAverage R h N)
            (f3PeriodicCorrelationAverage R h) +
          dist (f3PeriodicCorrelationAverage R h)
            (f3PadicKernel (Nat.dist h 2) + f3PadicKernel (h + 2) -
              2 * f3PadicKernel h) :=
    dist_triangle _ _ _
  calc
    dist (f3CorrelationIccAverage h N)
        (f3PadicKernel (Nat.dist h 2) + f3PadicKernel (h + 2) -
          2 * f3PadicKernel h) ≤
      dist (f3CorrelationIccAverage h N)
          (f3TruncCorrelationIccAverage R h N) +
        dist (f3TruncCorrelationIccAverage R h N)
          (f3PadicKernel (Nat.dist h 2) + f3PadicKernel (h + 2) -
            2 * f3PadicKernel h) :=
      dist_triangle _ _ _
    _ ≤
      dist (f3CorrelationIccAverage h N)
          (f3TruncCorrelationIccAverage R h N) +
        (dist (f3TruncCorrelationIccAverage R h N)
            (f3PeriodicCorrelationAverage R h) +
          dist (f3PeriodicCorrelationAverage R h)
            (f3PadicKernel (Nat.dist h 2) + f3PadicKernel (h + 2) -
              2 * f3PadicKernel h)) :=
      add_le_add_left htri _
    _ < ε := by
      dsimp [δ] at herr hcut hperiod
      linarith

end OmegaBalance
