import OmegaBalance.F3CorrelationCesaro
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Fixed-cutoff Cesàro limit for the periodic F₃ correlation

For each fixed cutoff `R`, the retained correlation is exactly periodic with period
`3^R`.  The preceding module decomposes every partial sum into complete periods plus
a uniformly bounded terminal block.  Here we normalize that decomposition and prove
that arbitrary initial Cesàro averages converge to the complete-period average.

This module still does **not** exchange the cutoff limit with the untruncated `F₃`
correlation.  That requires the separate `L²` tail estimate.
-/

namespace OmegaBalance

open Filter Topology

/-- The arbitrary-length normalized correlation average at fixed cutoff.  At `N = 0`
Lean's totalized division gives zero; this does not affect the `atTop` limit. -/
noncomputable def f3PeriodicCorrelationCesaroAverage (R h N : ℕ) : ℝ :=
  (f3PeriodicCorrelationPartialSum R h N : ℝ) / (N : ℝ)

/-- Exact real quotient/remainder form of the normalized partial sum.  The factor
`1 - (N mod 3^R)/N` is the proportion covered by complete periods. -/
theorem f3PeriodicCorrelationCesaroAverage_eq (R h N : ℕ) (hN : 0 < N) :
    f3PeriodicCorrelationCesaroAverage R h N =
      f3PeriodicCorrelationAverage R h *
          (1 - ((N % 3 ^ R : ℕ) : ℝ) / (N : ℝ)) +
        (f3PeriodicCorrelationPartialSum R h (N % 3 ^ R) : ℝ) / (N : ℝ) := by
  rw [f3PeriodicCorrelationCesaroAverage,
    f3PeriodicCorrelationPartialSum_eq_div_mod,
    f3PeriodicCorrelationAverage]
  push_cast
  have hP : (0 : ℝ) < ((3 : ℕ) ^ R : ℝ) := by positivity
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdecompNat :
      N / 3 ^ R * 3 ^ R + N % 3 ^ R = N := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod N (3 ^ R)
  have hdecomp :
      (N : ℝ) = ((N / 3 ^ R : ℕ) : ℝ) * ((3 : ℕ) ^ R : ℝ) +
        ((N % 3 ^ R : ℕ) : ℝ) := by
    exact_mod_cast hdecompNat.symm
  field_simp [ne_of_gt hP, ne_of_gt hNr]
  nlinarith

/-- The bounded terminal block divided by the total length tends to zero. -/
theorem tendsto_f3PeriodicCorrelationRemainder_div (R h : ℕ) :
    Tendsto
      (fun N : ℕ ↦
        (f3PeriodicCorrelationPartialSum R h (N % 3 ^ R) : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero
  · filter_upwards with N
    have hb := abs_f3PeriodicCorrelationRemainder_le R h N
    have hz :
        -(((3 : ℕ) ^ R : ℤ) * (R : ℤ) ^ 2) ≤
          f3PeriodicCorrelationPartialSum R h (N % 3 ^ R) :=
      neg_le_of_abs_le hb
    exact_mod_cast hz
  · filter_upwards with N
    have hb := abs_f3PeriodicCorrelationRemainder_le R h N
    have hz :
        f3PeriodicCorrelationPartialSum R h (N % 3 ^ R) ≤
          ((3 : ℕ) ^ R : ℤ) * (R : ℤ) ^ 2 :=
      le_of_abs_le hb
    exact_mod_cast hz
  · exact tendsto_natCast_atTop_atTop

/-- For fixed cutoff `R`, arbitrary-length Cesàro correlation averages converge to
exactly the average over one complete `3^R` period. -/
theorem tendsto_f3PeriodicCorrelationCesaroAverage (R h : ℕ) :
    Tendsto (fun N : ℕ ↦ f3PeriodicCorrelationCesaroAverage R h N) atTop
      (𝓝 (f3PeriodicCorrelationAverage R h)) := by
  have hP : 0 < (3 : ℕ) ^ R := pow_pos (by decide) R
  have hmod :
      Tendsto (fun N : ℕ ↦ ((N % 3 ^ R : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat hP
  have hmain :
      Tendsto
        (fun N : ℕ ↦
          f3PeriodicCorrelationAverage R h *
            (1 - ((N % 3 ^ R : ℕ) : ℝ) / (N : ℝ)))
        atTop (𝓝 (f3PeriodicCorrelationAverage R h)) := by
    simpa using tendsto_const_nhds.mul (tendsto_const_nhds.sub hmod)
  have hsum := hmain.add (tendsto_f3PeriodicCorrelationRemainder_div R h)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (f3PeriodicCorrelationCesaroAverage_eq R h N hN).symm

end OmegaBalance
