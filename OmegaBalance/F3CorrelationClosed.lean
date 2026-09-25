import OmegaBalance.F3CorrelationDepth

/-!
# Closed finite-period formula for the truncated F₃ correlation

This module substitutes the geometric weight formula into the exact complete-period
correlation.  It remains entirely finite: no Cesàro limit or truncation-limit exchange
is asserted here.
-/

namespace OmegaBalance

/-- Every capped depth is bounded by its cutoff, including the special zero value. -/
theorem f3CappedDepth_le (R n : ℕ) : f3CappedDepth R n ≤ R := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [f3CappedDepth_eq_min hn]
    exact min_le_left _ _

@[simp] theorem f3CappedDepth_two (R : ℕ) : f3CappedDepth R 2 = 0 := by
  rw [f3CappedDepth_eq_min (by decide) R,
    v3_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]
  simp

@[simp] theorem f3CappedDepth_four (R : ℕ) : f3CappedDepth R 4 = 0 := by
  rw [f3CappedDepth_eq_min (by decide) R,
    v3_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 4)]
  simp

/-- Exact closed form for one complete `3^R` period of the retained-layer
correlation.  The first three terms are the geometric kernel; the last three
are the finite-period boundary correction. -/
theorem f3PeriodicCorrelationSum_eq_closed (R h : ℕ) :
    f3PeriodicCorrelationSum R h =
      (3 : ℤ) ^ (R - f3CappedDepth R (Nat.dist h 2)) +
      (3 : ℤ) ^ (R - f3CappedDepth R (h + 2)) -
      2 * (3 : ℤ) ^ (R - f3CappedDepth R h) +
      (f3CappedDepth R (Nat.dist h 2) : ℤ) +
      (f3CappedDepth R (h + 2) : ℤ) -
      2 * (f3CappedDepth R h : ℤ) := by
  have h0 := f3CappedDepth_le R h
  have h1 := f3CappedDepth_le R (Nat.dist h 2)
  have h2 := f3CappedDepth_le R (h + 2)
  rw [f3PeriodicCorrelationSum_eq_weights,
    f3CorrelationWeight_eq, f3CorrelationWeight_eq, f3CorrelationWeight_eq,
    min_eq_right h0, min_eq_right h1, min_eq_right h2]
  ring

/-- The zero-shift finite correlation keeps both self-correlation layers.  The
`-1-R` correction is exactly what later disappears after normalization. -/
theorem f3PeriodicCorrelationSum_zero_shift (R : ℕ) :
    f3PeriodicCorrelationSum R 0 =
      2 * ((3 : ℤ) ^ R - 1 - (R : ℤ)) := by
  rw [f3PeriodicCorrelationSum_eq_closed]
  simp [Nat.dist]
  ring

/-- The shift-two boundary is the other exceptional capped-depth case: the
cross term has zero distance and therefore retains every layer. -/
theorem f3PeriodicCorrelationSum_two_shift (R : ℕ) :
    f3PeriodicCorrelationSum R 2 =
      -((3 : ℤ) ^ R - 1 - (R : ℤ)) := by
  rw [f3PeriodicCorrelationSum_eq_closed]
  simp [Nat.dist]
  ring

end OmegaBalance
