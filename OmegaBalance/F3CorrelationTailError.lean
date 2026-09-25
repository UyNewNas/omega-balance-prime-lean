import OmegaBalance.F3CorrelationTailMean

/-!
# Combined finite error bound for the F₃ correlation

This module combines the three Cauchy–Schwarz components of the raw-minus-truncated
correlation error.  It remains a finite estimate; no cutoff/Cesàro interchange is
claimed here.
-/

namespace OmegaBalance

/-- Convenient upper bound for the unshifted tail square-mass. -/
noncomputable def f3TailMassUpper (R N : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R + (N : ℝ) / (3 : ℝ) ^ R

/-- Convenient upper bound for the tail square-mass after a fixed shift. -/
noncomputable def f3TailShiftMassUpper (R h N : ℕ) : ℝ :=
  ((N + h + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R +
    ((N + h : ℕ) : ℝ) / (3 : ℝ) ^ R

/-- Convenient upper bound for the shifted raw F₃ second moment. -/
def f3RawShiftMassUpper (h N : ℕ) : ℝ :=
  ((N + h + 1 : ℕ) : ℝ) + ((N + h : ℕ) : ℝ)

/-- Combined square-error upper bound obtained from the three tail terms. -/
noncomputable def f3CorrelationErrorSqUpper (R h N : ℕ) : ℝ :=
  3 * (f3TailMassUpper R N * f3RawShiftMassUpper h N +
    f3TailShiftMassUpper R h N * f3RawShiftMassUpper 0 N +
    f3TailShiftMassUpper R h N * f3TailMassUpper R N)

/-- A three-term square is bounded by three times the sum of the individual squares. -/
theorem sq_add_sub_le_three_sq (a b c : ℝ) :
    (a + b - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + c), sq_nonneg (b + c)]

/-- Finite square bound for the complete raw-minus-truncated correlation error. -/
theorem sum_Icc_f3_correlation_error_sq_le (R h N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N,
      ((f3 n : ℝ) * (f3 (n + h) : ℝ) -
        (f3Trunc R n : ℝ) * (f3Trunc R (n + h) : ℝ))) ^ 2 ≤
      f3CorrelationErrorSqUpper R h N := by
  let A : ℝ := ∑ n ∈ Finset.Icc 2 N,
    (f3Tail R n : ℝ) * (f3 (n + h) : ℝ)
  let B : ℝ := ∑ n ∈ Finset.Icc 2 N,
    (f3 n : ℝ) * (f3Tail R (n + h) : ℝ)
  let C : ℝ := ∑ n ∈ Finset.Icc 2 N,
    (f3Tail R n : ℝ) * (f3Tail R (n + h) : ℝ)
  have hdecomp :
      (∑ n ∈ Finset.Icc 2 N,
        ((f3 n : ℝ) * (f3 (n + h) : ℝ) -
          (f3Trunc R n : ℝ) * (f3Trunc R (n + h) : ℝ))) =
        A + B - C := by
    simpa [A, B, C] using sum_Icc_f3_correlation_sub_trunc_eq_tails R h N
  have hA : A ^ 2 ≤
      f3TailMassUpper R N * f3RawShiftMassUpper h N := by
    simpa [A, f3TailMassUpper, f3RawShiftMassUpper] using
      sum_Icc_f3Tail_mul_f3_shift_sq_le R h N
  have hB : B ^ 2 ≤
      f3TailShiftMassUpper R h N * f3RawShiftMassUpper 0 N := by
    simpa [B, f3TailShiftMassUpper, f3RawShiftMassUpper] using
      sum_Icc_f3_mul_f3Tail_shift_sq_le R h N
  have hC : C ^ 2 ≤
      f3TailShiftMassUpper R h N * f3TailMassUpper R N := by
    simpa [C, f3TailShiftMassUpper, f3TailMassUpper] using
      sum_Icc_f3Tail_mul_f3Tail_shift_sq_le R h N
  calc
    (∑ n ∈ Finset.Icc 2 N,
      ((f3 n : ℝ) * (f3 (n + h) : ℝ) -
        (f3Trunc R n : ℝ) * (f3Trunc R (n + h) : ℝ))) ^ 2 =
        (A + B - C) ^ 2 := by rw [hdecomp]
    _ ≤ 3 * (A ^ 2 + B ^ 2 + C ^ 2) :=
      sq_add_sub_le_three_sq A B C
    _ ≤ 3 * (
        f3TailMassUpper R N * f3RawShiftMassUpper h N +
        f3TailShiftMassUpper R h N * f3RawShiftMassUpper 0 N +
        f3TailShiftMassUpper R h N * f3TailMassUpper R N) := by
      nlinarith [hA, hB, hC]
    _ = f3CorrelationErrorSqUpper R h N := by
      rfl

/-- The complete finite correlation-error estimate after dividing by the square of
the averaging length.  The positivity hypothesis keeps this interface restricted
to genuine Cesàro averages rather than totalized division by zero. -/
theorem f3_correlation_cesaro_error_sq_le (R h N : ℕ) (hN : 0 < N) :
    (((∑ n ∈ Finset.Icc 2 N,
      ((f3 n : ℝ) * (f3 (n + h) : ℝ) -
        (f3Trunc R n : ℝ) * (f3Trunc R (n + h) : ℝ))) / (N : ℝ)) ^ 2) ≤
      f3CorrelationErrorSqUpper R h N / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := pow_pos hNr 2
  rw [div_pow]
  exact div_le_div_of_nonneg_right
    (sum_Icc_f3_correlation_error_sq_le R h N) hN2.le


/-- An averaging-length independent square-error majorant. For fixed shift `h`,
this decays geometrically with the truncation cutoff `R`. -/
noncomputable def f3CorrelationErrorSqMajorant (R h : ℕ) : ℝ :=
  9 * ((2 * h + 3 : ℕ) : ℝ) *
    (2 / (3 : ℝ) ^ R + 1 / ((3 : ℝ) ^ R) ^ 2)

/-- After normalization by `N²`, the finite correlation-error upper bound is
controlled uniformly in every genuine averaging length `N > 0`. -/
theorem f3CorrelationErrorSqUpper_div_sq_le_majorant
    (R h N : ℕ) (hN : 0 < N) :
    f3CorrelationErrorSqUpper R h N / (N : ℝ) ^ 2 ≤
      f3CorrelationErrorSqMajorant R h := by
  let A : ℝ := 2 * (N : ℝ) + 1
  let B : ℝ := 2 * (N : ℝ) + 2 * (h : ℝ) + 1
  let C : ℝ := 2 * (h : ℝ) + 3
  have hNr : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (0 : ℝ) < (3 : ℝ) ^ R := by
    positivity
  have hA : A ≤ 3 * (N : ℝ) := by
    dsimp [A]
    nlinarith
  have hNm1 : 0 ≤ (N : ℝ) - 1 := sub_nonneg.mpr hN1
  have hh1 : 0 ≤ 2 * (h : ℝ) + 1 := by
    positivity
  have hprod : 0 ≤ (2 * (h : ℝ) + 1) * ((N : ℝ) - 1) :=
    mul_nonneg hh1 hNm1
  have hB : B ≤ C * (N : ℝ) := by
    dsimp [B, C]
    nlinarith
  have hAB : A * B ≤ 3 * C * (N : ℝ) ^ 2 := by
    calc
      A * B ≤ (3 * (N : ℝ)) * B := by
        exact mul_le_mul_of_nonneg_right hA (by dsimp [B]; positivity)
      _ ≤ (3 * (N : ℝ)) * (C * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hB (by positivity)
      _ = 3 * C * (N : ℝ) ^ 2 := by ring
  have hN2 : 0 < (N : ℝ) ^ 2 := pow_pos hNr 2
  have hABdiv : A * B / (N : ℝ) ^ 2 ≤ 3 * C := by
    rw [div_le_iff₀ hN2]
    simpa [mul_assoc] using hAB
  have hfactor :
      0 ≤ 2 / (3 : ℝ) ^ R + 1 / ((3 : ℝ) ^ R) ^ 2 := by
    positivity
  have hexp :
      f3CorrelationErrorSqUpper R h N / (N : ℝ) ^ 2 =
        3 * (A * B / (N : ℝ) ^ 2) *
          (2 / (3 : ℝ) ^ R + 1 / ((3 : ℝ) ^ R) ^ 2) := by
    dsimp [A, B]
    unfold f3CorrelationErrorSqUpper f3TailMassUpper
      f3TailShiftMassUpper f3RawShiftMassUpper
    push_cast
    field_simp [ne_of_gt hNr, ne_of_gt hpow]
    ring
  calc
    f3CorrelationErrorSqUpper R h N / (N : ℝ) ^ 2 =
        3 * (A * B / (N : ℝ) ^ 2) *
          (2 / (3 : ℝ) ^ R + 1 / ((3 : ℝ) ^ R) ^ 2) := hexp
    _ ≤ 3 * (3 * C) *
          (2 / (3 : ℝ) ^ R + 1 / ((3 : ℝ) ^ R) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hABdiv (by norm_num)) hfactor
    _ = f3CorrelationErrorSqMajorant R h := by
      dsimp [C, f3CorrelationErrorSqMajorant]
      push_cast
      ring

/-- Uniform-in-`N` finite square bound for the normalized raw/truncated
correlation error. -/
theorem f3_correlation_cesaro_error_sq_le_majorant
    (R h N : ℕ) (hN : 0 < N) :
    (((∑ n ∈ Finset.Icc 2 N,
      ((f3 n : ℝ) * (f3 (n + h) : ℝ) -
        (f3Trunc R n : ℝ) * (f3Trunc R (n + h) : ℝ))) / (N : ℝ)) ^ 2) ≤
      f3CorrelationErrorSqMajorant R h := by
  exact (f3_correlation_cesaro_error_sq_le R h N hN).trans
    (f3CorrelationErrorSqUpper_div_sq_le_majorant R h N hN)

end OmegaBalance
