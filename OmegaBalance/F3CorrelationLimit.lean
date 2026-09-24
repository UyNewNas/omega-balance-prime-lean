import OmegaBalance.F3CorrelationClosed
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Normalized complete-period limit for the truncated F₃ correlation

This module is the first genuinely limiting layer of the correlation argument.  It
normalizes the exact complete `3^R`-period formula and proves its limit as the cutoff
`R` tends to infinity.  It still does not exchange the cutoff limit with an arbitrary
Cesàro average of the untruncated function.
-/

namespace OmegaBalance

open Filter Topology

/-- Real-valued three-adic kernel on natural numbers.  The zero convention is the
usual absolute-value convention `|0|₃ = 0`, unlike the finite capped depth. -/
def f3PadicKernel (n : ℕ) : ℝ :=
  if n = 0 then 0 else 1 / (3 : ℝ) ^ v3 n

@[simp] theorem f3PadicKernel_zero : f3PadicKernel 0 = 0 := by
  simp [f3PadicKernel]

/-- The normalized geometric term attached to one capped depth. -/
def f3NormalizedCappedKernel (R n : ℕ) : ℝ :=
  (3 : ℝ) ^ (R - f3CappedDepth R n) / (3 : ℝ) ^ R

/-- Away from zero, once the cutoff exceeds the true valuation depth, the normalized
finite kernel has already stabilized to the three-adic kernel. -/
theorem f3NormalizedCappedKernel_eq_padicKernel_of_le {R n : ℕ}
    (hn : n ≠ 0) (hR : v3 n ≤ R) :
    f3NormalizedCappedKernel R n = f3PadicKernel n := by
  rw [f3NormalizedCappedKernel, f3CappedDepth_eq_min hn, min_eq_right hR,
    f3PadicKernel, if_neg hn]
  have hpow :
      (3 : ℝ) ^ (R - v3 n) * (3 : ℝ) ^ v3 n = (3 : ℝ) ^ R :=
    pow_sub_mul_pow _ hR
  field_simp
  exact hpow

/-- At zero, the retained depth equals the cutoff, so normalization leaves exactly
`(1/3)^R`. -/
theorem f3NormalizedCappedKernel_zero (R : ℕ) :
    f3NormalizedCappedKernel R 0 = (1 / 3 : ℝ) ^ R := by
  simp [f3NormalizedCappedKernel, div_pow]

/-- Each normalized capped geometric term converges to the genuine three-adic
kernel, including the special zero case. -/
theorem tendsto_f3NormalizedCappedKernel (n : ℕ) :
    Tendsto (fun R : ℕ ↦ f3NormalizedCappedKernel R n) atTop
      (𝓝 (f3PadicKernel n)) := by
  by_cases hn : n = 0
  · subst n
    have hpow : Tendsto (fun R : ℕ ↦ (1 / 3 : ℝ) ^ R) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [f3NormalizedCappedKernel_zero] using hpow
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (v3 n)] with R hR
    symm
    exact f3NormalizedCappedKernel_eq_padicKernel_of_le hn hR

/-- The normalized retained depth is the finite-period boundary correction scale. -/
def f3CappedDepthRatio (R n : ℕ) : ℝ :=
  (f3CappedDepth R n : ℝ) / (3 : ℝ) ^ R

/-- Every normalized retained depth vanishes exponentially, uniformly under the
trivial bound `depth ≤ R`. -/
theorem tendsto_f3CappedDepthRatio_zero (n : ℕ) :
    Tendsto (fun R : ℕ ↦ f3CappedDepthRatio R n) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun R : ℕ ↦ (R : ℝ) / (3 : ℝ) ^ R) atTop (𝓝 0) := by
    simpa only [pow_one] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 3))
  apply squeeze_zero'
  · filter_upwards with R
    exact div_nonneg (by positivity) (by positivity)
  · filter_upwards with R
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast f3CappedDepth_le R n) (by positivity)
  · exact hmajor

/-- Complete-period correlation normalized by its period length. -/
def f3PeriodicCorrelationAverage (R h : ℕ) : ℝ :=
  (f3PeriodicCorrelationSum R h : ℝ) / (3 : ℝ) ^ R

/-- Exact normalized closed form: three geometric kernels plus the three finite-depth
boundary corrections. -/
theorem f3PeriodicCorrelationAverage_eq (R h : ℕ) :
    f3PeriodicCorrelationAverage R h =
      f3NormalizedCappedKernel R (Nat.dist h 2) +
      f3NormalizedCappedKernel R (h + 2) -
      2 * f3NormalizedCappedKernel R h +
      f3CappedDepthRatio R (Nat.dist h 2) +
      f3CappedDepthRatio R (h + 2) -
      2 * f3CappedDepthRatio R h := by
  rw [f3PeriodicCorrelationAverage, f3PeriodicCorrelationSum_eq_closed]
  simp only [f3NormalizedCappedKernel, f3CappedDepthRatio]
  push_cast
  ring

/-- The exact normalized complete-period limit.  This is the finite-cutoff kernel
that later feeds the arbitrary-length Cesàro and `L²` tail arguments. -/
theorem tendsto_f3PeriodicCorrelationAverage (h : ℕ) :
    Tendsto (fun R : ℕ ↦ f3PeriodicCorrelationAverage R h) atTop
      (𝓝 (f3PadicKernel (Nat.dist h 2) + f3PadicKernel (h + 2) -
        2 * f3PadicKernel h)) := by
  rw [show (fun R : ℕ ↦ f3PeriodicCorrelationAverage R h) =
      (fun R : ℕ ↦
        f3NormalizedCappedKernel R (Nat.dist h 2) +
        f3NormalizedCappedKernel R (h + 2) -
        2 * f3NormalizedCappedKernel R h +
        f3CappedDepthRatio R (Nat.dist h 2) +
        f3CappedDepthRatio R (h + 2) -
        2 * f3CappedDepthRatio R h) by
      funext R
      exact f3PeriodicCorrelationAverage_eq R h]
  exact (((((tendsto_f3NormalizedCappedKernel (Nat.dist h 2)).add
      (tendsto_f3NormalizedCappedKernel (h + 2))).sub
      ((tendsto_const_nhds.mul (tendsto_f3NormalizedCappedKernel h)))).add
      (tendsto_f3CappedDepthRatio_zero (Nat.dist h 2))).add
      (tendsto_f3CappedDepthRatio_zero (h + 2))).sub
      (tendsto_const_nhds.mul (tendsto_f3CappedDepthRatio_zero h))

end OmegaBalance
