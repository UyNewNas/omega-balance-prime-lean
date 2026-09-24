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
  let P : ℕ := 3 ^ R
  let q : ℕ := N / P
  let r : ℕ := N % P
  have hsumZ := f3PeriodicCorrelationPartialSum_eq_div_mod R h N
  have hsumR :
      (f3PeriodicCorrelationPartialSum R h N : ℝ) =
        (q : ℝ) * (f3PeriodicCorrelationSum R h : ℝ) +
          (f3PeriodicCorrelationPartialSum R h r : ℝ) := by
    exact_mod_cast hsumZ
  have hPnat : 0 < P := by simp [P]
  have hPreal : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPnat
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdecompNat : q * P + r = N := by
    simp only [q, r]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod N P
  have hdecomp : (N : ℝ) = (q : ℝ) * (P : ℝ) + (r : ℝ) := by
    exact_mod_cast hdecompNat.symm
  have hminus : (N : ℝ) - (r : ℝ) = (q : ℝ) * (P : ℝ) := by
    linarith [hdecomp]
  have hq :
      (q : ℝ) / (N : ℝ) = (1 - (r : ℝ) / (N : ℝ)) / (P : ℝ) := by
    field_simp [ne_of_gt hPreal, ne_of_gt hNreal]
    rw [hminus]
  rw [f3PeriodicCorrelationCesaroAverage, hsumR, add_div, f3PeriodicCorrelationAverage]
  simp only [P, r] at hq ⊢
  rw [show (q : ℝ) * (f3PeriodicCorrelationSum R h : ℝ) / (N : ℝ) =
      (f3PeriodicCorrelationSum R h : ℝ) * ((q : ℝ) / (N : ℝ)) by ring, hq]
  ring

/-- The bounded terminal block divided by the total length tends to zero. -/
theorem tendsto_f3PeriodicCorrelationRemainder_div (R h : ℕ) :
    Tendsto
      (fun N : ℕ ↦
        (f3PeriodicCorrelationPartialSum R h (N % 3 ^ R) : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  refine tendsto_bdd_div_atTop_nhds_zero
    (b := -((((3 : ℕ) ^ R : ℕ) : ℝ) * (R : ℝ) ^ 2))
    (B := ((((3 : ℕ) ^ R : ℕ) : ℝ) * (R : ℝ) ^ 2)) ?_ ?_
    tendsto_natCast_atTop_atTop
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

/-- For fixed cutoff `R`, arbitrary-length Cesàro correlation averages converge to
exactly the average over one complete `3^R` period. -/
theorem tendsto_f3PeriodicCorrelationCesaroAverage (R h : ℕ) :
    Tendsto (fun N : ℕ ↦ f3PeriodicCorrelationCesaroAverage R h N) atTop
      (𝓝 (f3PeriodicCorrelationAverage R h)) := by
  have hP : 0 < (3 : ℕ) ^ R := pow_pos (by decide) R
  have hmod :
      Tendsto (fun N : ℕ ↦ ((N % 3 ^ R : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat hP
  have hone :
      Tendsto (fun N : ℕ ↦ 1 - ((N % 3 ^ R : ℕ) : ℝ) / (N : ℝ))
        atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hmod :
      Tendsto (fun N : ℕ ↦ 1 - ((N % 3 ^ R : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 (1 - 0)))
  have hmain :
      Tendsto
        (fun N : ℕ ↦
          f3PeriodicCorrelationAverage R h *
            (1 - ((N % 3 ^ R : ℕ) : ℝ) / (N : ℝ)))
        atTop (𝓝 (f3PeriodicCorrelationAverage R h)) := by
    simpa using (tendsto_const_nhds.mul hone :
      Tendsto
        (fun N : ℕ ↦
          f3PeriodicCorrelationAverage R h *
            (1 - ((N % 3 ^ R : ℕ) : ℝ) / (N : ℝ)))
        atTop (𝓝 (f3PeriodicCorrelationAverage R h * 1)))
  have hsum :
      Tendsto
        (fun N : ℕ ↦
          f3PeriodicCorrelationAverage R h *
              (1 - ((N % 3 ^ R : ℕ) : ℝ) / (N : ℝ)) +
            (f3PeriodicCorrelationPartialSum R h (N % 3 ^ R) : ℝ) / (N : ℝ))
        atTop (𝓝 (f3PeriodicCorrelationAverage R h)) := by
    simpa using hmain.add (tendsto_f3PeriodicCorrelationRemainder_div R h)
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (f3PeriodicCorrelationCesaroAverage_eq R h N hN).symm

end OmegaBalance
