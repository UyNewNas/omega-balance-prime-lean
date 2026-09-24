import OmegaBalance.F3CorrelationPeriod

/-!
# Geometric weight behind the finite F₃ correlation

The explicit complete-period formula depends on a double sum whose summand only
sees `min (j+1) (k+1)` through a depth cutoff and `max (j+1) (k+1)` through a
power of three.  This module isolates that finite combinatorics.  It does not
assert an infinite limit.
-/

namespace OmegaBalance

/-- Generic depth-cutoff weight for the complete-period correlation.  The
layers are numbered `1,...,R`; `d` is the number of compatible retained
layers. -/
def f3CorrelationWeight (R d : ℕ) : ℤ :=
  ∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
    if min (j + 1) (k + 1) ≤ d then
      (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0

private theorem f3CorrelationWeight_old_term {R d j k : ℕ}
    (hj : j < R) (hk : k < R) :
    (if min (j + 1) (k + 1) ≤ d then
        (3 : ℤ) ^ ((R + 1) - max (j + 1) (k + 1)) else 0) =
      3 * (if min (j + 1) (k + 1) ≤ d then
        (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) := by
  have hm : max (j + 1) (k + 1) ≤ R := by omega
  have hs : (R + 1) - max (j + 1) (k + 1) =
      (R - max (j + 1) (k + 1)) + 1 := by omega
  by_cases h : min (j + 1) (k + 1) ≤ d
  · simp [h, hs, pow_succ, mul_comm]
  · simp [h]

private theorem f3CorrelationWeight_boundary_sum (R d : ℕ) :
    (∑ j ∈ Finset.range R,
      if min (j + 1) (R + 1) ≤ d then
        (3 : ℤ) ^ ((R + 1) - max (j + 1) (R + 1)) else 0) =
      (min R d : ℕ) := by
  calc
    _ = ∑ j ∈ Finset.range R, if j < d then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjR : j < R := Finset.mem_range.mp hj
      have hmin : min (j + 1) (R + 1) = j + 1 := min_eq_left (by omega)
      have hmax : max (j + 1) (R + 1) = R + 1 := max_eq_right (by omega)
      rw [hmin, hmax]
      have hiff : j + 1 ≤ d ↔ j < d := by omega
      simp [hiff]
    _ = (min R d : ℕ) := sum_initial_indicator R d

private theorem f3CorrelationWeight_old_block (R d : ℕ) :
    (∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
      if min (j + 1) (k + 1) ≤ d then
        (3 : ℤ) ^ ((R + 1) - max (j + 1) (k + 1)) else 0) =
      3 * f3CorrelationWeight R d := by
  unfold f3CorrelationWeight
  calc
    _ = ∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
        3 * (if min (j + 1) (k + 1) ≤ d then
          (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjR : j < R := Finset.mem_range.mp hj
      apply Finset.sum_congr rfl
      intro k hk
      exact f3CorrelationWeight_old_term hjR (Finset.mem_range.mp hk)
    _ = ∑ j ∈ Finset.range R,
        3 * (∑ k ∈ Finset.range R,
          if min (j + 1) (k + 1) ≤ d then
            (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = _ := by rw [Finset.mul_sum]

/-- Adding one retained layer triples the old block and adds the two boundary
rows plus the new corner. -/
theorem f3CorrelationWeight_succ (R d : ℕ) :
    f3CorrelationWeight (R + 1) d =
      3 * f3CorrelationWeight R d + 2 * (min R d : ℕ) +
        (if R + 1 ≤ d then 1 else 0) := by
  unfold f3CorrelationWeight
  rw [Finset.sum_range_succ]
  have hleft :
      (∑ j ∈ Finset.range R, ∑ k ∈ Finset.range (R + 1),
        if min (j + 1) (k + 1) ≤ d then
          (3 : ℤ) ^ ((R + 1) - max (j + 1) (k + 1)) else 0) =
        (∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
          if min (j + 1) (k + 1) ≤ d then
            (3 : ℤ) ^ ((R + 1) - max (j + 1) (k + 1)) else 0) +
        (∑ j ∈ Finset.range R,
          if min (j + 1) (R + 1) ≤ d then
            (3 : ℤ) ^ ((R + 1) - max (j + 1) (R + 1)) else 0) := by
    calc
      _ = ∑ j ∈ Finset.range R,
          ((∑ k ∈ Finset.range R,
            if min (j + 1) (k + 1) ≤ d then
              (3 : ℤ) ^ ((R + 1) - max (j + 1) (k + 1)) else 0) +
          (if min (j + 1) (R + 1) ≤ d then
            (3 : ℤ) ^ ((R + 1) - max (j + 1) (R + 1)) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_range_succ]
      _ = _ := by rw [Finset.sum_add_distrib]
  rw [hleft, f3CorrelationWeight_old_block, f3CorrelationWeight_boundary_sum]
  rw [Finset.sum_range_succ]
  have hrow :
      (∑ k ∈ Finset.range R,
        if min (R + 1) (k + 1) ≤ d then
          (3 : ℤ) ^ ((R + 1) - max (R + 1) (k + 1)) else 0) =
        (min R d : ℕ) := by
    simpa [min_comm, max_comm] using f3CorrelationWeight_boundary_sum R d
  rw [hrow]
  have hcorner :
      (if min (R + 1) (R + 1) ≤ d then
        (3 : ℤ) ^ ((R + 1) - max (R + 1) (R + 1)) else 0) =
      (if R + 1 ≤ d then 1 else 0) := by simp
  rw [hcorner]
  ring

/-- Closed finite geometric formula for the depth-cutoff weight.  The final
`- min R d` is the finite-period boundary correction; after division by
`3^R` it disappears as `R → ∞` for fixed depth. -/
theorem f3CorrelationWeight_eq (R d : ℕ) :
    f3CorrelationWeight R d =
      (3 : ℤ) ^ R - (3 : ℤ) ^ (R - min R d) - (min R d : ℕ) := by
  induction R with
  | zero => simp [f3CorrelationWeight]
  | succ R ih =>
      rw [show Nat.succ R = R + 1 by omega, f3CorrelationWeight_succ, ih]
      by_cases hd : d ≤ R
      · have hminR : min R d = d := min_eq_right hd
        have hminS : min (R + 1) d = d := min_eq_right (by omega)
        have hnot : ¬ R + 1 ≤ d := by omega
        rw [hminR, hminS, if_neg hnot]
        have hs : (R + 1) - d = (R - d) + 1 := by omega
        rw [hs, pow_succ, pow_succ]
        push_cast
        ring
      · have hRd : R < d := lt_of_not_ge hd
        have hminR : min R d = R := min_eq_left (by omega)
        have hminS : min (R + 1) d = R + 1 := min_eq_left (by omega)
        have hyes : R + 1 ≤ d := by omega
        rw [hminR, hminS, if_pos hyes]
        simp [pow_succ]
        ring

end OmegaBalance
