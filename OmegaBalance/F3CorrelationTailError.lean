import OmegaBalance.F3CorrelationTailMean

/-!
# Combined finite error bound for the F₃ correlation

This module combines the three Cauchy–Schwarz components of the raw-minus-truncated
correlation error.  It remains a finite estimate; no cutoff/Cesàro interchange is
claimed here.
-/

namespace OmegaBalance

/-- Convenient upper bound for the unshifted tail square-mass. -/
def f3TailMassUpper (R N : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R + (N : ℝ) / (3 : ℝ) ^ R

/-- Convenient upper bound for the tail square-mass after a fixed shift. -/
def f3TailShiftMassUpper (R h N : ℕ) : ℝ :=
  ((N + h + 1 : ℕ) : ℝ) / (3 : ℝ) ^ R +
    ((N + h : ℕ) : ℝ) / (3 : ℝ) ^ R

/-- Convenient upper bound for the shifted raw F₃ second moment. -/
def f3RawShiftMassUpper (h N : ℕ) : ℝ :=
  ((N + h + 1 : ℕ) : ℝ) + ((N + h : ℕ) : ℝ)

/-- Combined square-error upper bound obtained from the three tail terms. -/
def f3CorrelationErrorSqUpper (R h N : ℕ) : ℝ :=
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

end OmegaBalance
