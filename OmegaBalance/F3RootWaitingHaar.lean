import OmegaBalance.F3RootBatchHaar
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Process.HittingTime
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual one-based waiting time for a fixed root-pair certificate

The stream has the genuine infinite product of the previously constructed unit
Haar measure. The waiting variable is mathlib's actual first hitting time plus
one, retaining infinity on a stream that never produces a certificate. Its tail
and expectation are derived from actual cylinder probabilities. No geometric
distribution, waiting law or independent-root assumption is a premise.

This file treats fixed genuine roots and a fixed original configuration. Moving
random configurations, joint matrix waiting bounds and prime sampling remain
separate tasks.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Independent complete sample parameters; root labels within each observation
all receive the same coordinate of this stream. -/
def f3UnitHaarStream : Measure (ℕ → ℤ_[3]) :=
  Measure.infinitePi (fun _ : ℕ => f3UnitHaar)

instance f3UnitHaarStream_isProbabilityMeasure : IsProbabilityMeasure f3UnitHaarStream := by
  unfold f3UnitHaarStream
  infer_instance

/-- One-based first actual unequal-depth observation, with infinity if none occurs. -/
def f3RootWait (a b : ℤ_[3]) (ω : ℕ → ℤ_[3]) : ℕ∞ :=
  (show ℕ∞ from hittingAfter (fun n (x : ℕ → ℤ_[3]) => x n)
    {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠
      rootDepth (d : ℚ_[3]) (b : ℚ_[3])} 0 ω) + 1

/-- The actual one-based first-hit count exceeds T exactly after T failures. -/
theorem f3RootWait_gt_iff (a b : ℤ_[3]) (ω : ℕ → ℤ_[3]) (T : ℕ) :
    (T : ℕ∞) < f3RootWait a b ω ↔ ∀ n < T,
      rootDepth (ω n : ℚ_[3]) (a : ℚ_[3]) =
        rootDepth (ω n : ℚ_[3]) (b : ℚ_[3]) := by
  have hshift (u : ℕ∞) : (T : ℕ∞) < u + 1 ↔ (T : ℕ∞) ≤ u := by
    cases u using ENat.recTopCoe with
    | top => simp
    | coe n => norm_cast <;> omega
  change (T : ℕ∞) < (show ℕ∞ from hittingAfter
    (fun n (x : ℕ → ℤ_[3]) => x n)
    {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠
      rootDepth (d : ℚ_[3]) (b : ℚ_[3])} 0 ω) + 1 ↔ _
  rw [hshift]
  change (T : WithTop ℕ) ≤ hittingAfter (fun n (x : ℕ → ℤ_[3]) => x n)
    {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠
      rootDepth (d : ℚ_[3]) (b : ℚ_[3])} 0 ω ↔ _
  rw [← not_lt, hittingAfter_lt_iff]
  simp only [Set.mem_Ico, Nat.zero_le, true_and, Set.mem_setOf_eq,
    not_exists, not_and, not_not]

/-- A never-ending wait means every actual observation has equal depths. -/
theorem f3RootWait_eq_top_iff (a b : ℤ_[3]) (ω : ℕ → ℤ_[3]) :
    f3RootWait a b ω = ⊤ ↔ ∀ n : ℕ,
      rootDepth (ω n : ℚ_[3]) (a : ℚ_[3]) =
        rootDepth (ω n : ℚ_[3]) (b : ℚ_[3]) := by
  rw [ENat.eq_top_iff_forall_gt]
  simp_rw [f3RootWait_gt_iff]
  constructor
  · intro h n
    exact h (n + 1) n (by omega)
  · intro h T n _hn
    exact h n

/-- The first-hit convention counts at least one observation, including infinite waits. -/
theorem f3RootWait_pos (a b : ℤ_[3]) (ω : ℕ → ℤ_[3]) :
    0 < f3RootWait a b ω := by
  simpa using (f3RootWait_gt_iff a b ω 0).mpr (by simp)

/-- A waiting tail is an actual finite cylinder in the infinite product space. -/
theorem f3RootWait_tail_eq_pi (a b : ℤ_[3]) (T : ℕ) :
    {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3RootWait a b ω} =
      Set.pi (↑(Finset.range T) : Set ℕ) (fun _ =>
        {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (a : ℚ_[3]) =
          rootDepth (d : ℚ_[3]) (b : ℚ_[3])}) := by
  ext ω
  simpa only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
    using f3RootWait_gt_iff a b ω T

/-- The actual first-hit tail events are measurable. -/
theorem f3RootWait_tail_measurable {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (T : ℕ) :
    MeasurableSet {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3RootWait a b ω} := by
  have hevent : {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3RootWait a b ω} =
      ⋂ (n : ℕ) (_hn : n < T), {ω : ℕ → ℤ_[3] |
        rootDepth (ω n : ℚ_[3]) (a : ℚ_[3]) =
          rootDepth (ω n : ℚ_[3]) (b : ℚ_[3])} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, f3RootWait_gt_iff]
  rw [hevent]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    (f3RootDepth_equal_measurable hL).preimage (measurable_pi_apply n)

/-- The one-based actual waiting time has the geometric tail derived from Haar cylinders. -/
theorem f3UnitHaarStream_rootWait_gt {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (T : ℕ) :
    f3UnitHaarStream {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3RootWait a b ω} =
      (1 - ((3 : ℝ≥0∞) ^ L)⁻¹) ^ T := by
  rw [f3UnitHaarStream, f3RootWait_tail_eq_pi,
    Measure.infinitePi_pi _ (fun _ _ => f3RootDepth_equal_measurable hL)]
  simp only [f3UnitHaar_rootDepth_equal ha hb hLpos hL,
    Finset.prod_const, Finset.card_range]

/-- A pointwise count identity for the actual first hit, including a never-hit stream. -/
theorem f3RootWait_toENNReal_eq_tsum (a b : ℤ_[3]) (ω : ℕ → ℤ_[3]) :
    (f3RootWait a b ω : ℝ≥0∞) = ∑' T : ℕ,
      ({x : ℕ → ℤ_[3] | (T : ℕ∞) < f3RootWait a b x}.indicator
        (fun _ => (1 : ℝ≥0∞))) ω := by
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  cases h : f3RootWait a b ω using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, ENat.natCast_lt_top, if_true]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)).symm
  | coe k =>
    simp only [ENat.toENNReal_coe, ENat.natCast_lt_natCast]
    rw [tsum_eq_sum (s := Finset.range k) (fun n hn =>
      if_neg (by simpa only [Finset.mem_range] using hn))]
    have hsum : (∑ n ∈ Finset.range k, if n < k then (1 : ℝ≥0∞) else 0) =
        ∑ _n ∈ Finset.range k, (1 : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact if_pos (Finset.mem_range.mp hn)
    rw [hsum]
    simp

/-- The actual waiting variable is measurable as an extended nonnegative count. -/
theorem f3RootWait_measurable_toENNReal {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    Measurable (fun ω : ℕ → ℤ_[3] => (f3RootWait a b ω : ℝ≥0∞)) := by
  have heq : (fun ω : ℕ → ℤ_[3] => (f3RootWait a b ω : ℝ≥0∞)) =
      (fun ω => ∑' T : ℕ,
        ({x : ℕ → ℤ_[3] | (T : ℕ∞) < f3RootWait a b x}.indicator
          (fun _ => (1 : ℝ≥0∞))) ω) :=
    funext (f3RootWait_toENNReal_eq_tsum a b)
  rw [heq]
  exact Measurable.ennreal_tsum fun T =>
    measurable_const.indicator (f3RootWait_tail_measurable hL T)

/-- The true nonnegative expectation of the one-based waiting time is `3^L`. -/
theorem f3UnitHaarStream_rootWait_mean {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    (∫⁻ ω, (f3RootWait a b ω : ℝ≥0∞) ∂f3UnitHaarStream) = (3 : ℝ≥0∞) ^ L := by
  classical
  have hp : ((3 : ℝ≥0∞) ^ L)⁻¹ ≤ 1 := by
    rw [← f3UnitHaar_rootDepth_ne ha hb hLpos hL]
    exact prob_le_one
  simp_rw [f3RootWait_toENNReal_eq_tsum]
  rw [lintegral_tsum (fun T =>
    (measurable_const.indicator (f3RootWait_tail_measurable hL T)).aemeasurable)]
  simp_rw [lintegral_indicator_fun_one (f3RootWait_tail_measurable hL _),
    f3UnitHaarStream_rootWait_gt ha hb hLpos hL]
  rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hp, inv_inv]

/-- A certificate occurs after finitely many actual observations almost surely. -/
theorem f3UnitHaarStream_rootWait_finite_ae {a b : ℤ_[3]} (ha : IsUnit a)
    (hb : IsUnit b) {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    ∀ᵐ ω ∂f3UnitHaarStream, f3RootWait a b ω < ⊤ := by
  have hmean : (∫⁻ ω, (f3RootWait a b ω : ℝ≥0∞) ∂f3UnitHaarStream) ≠ ⊤ := by
    rw [f3UnitHaarStream_rootWait_mean ha hb hLpos hL]
    simp
  filter_upwards [ae_lt_top (f3RootWait_measurable_toENNReal hL) hmean] with ω hω
  exact ENat.toENNReal_lt_top.mp hω

/-- The same first-hit count on one fixed original shared-root configuration. -/
def f3SharedRootWait {m : ℕ} (C : F3SharedRootConfig m) (i j : Fin m) :
    (ℕ → ℤ_[3]) → ℕ∞ :=
  f3RootWait (f3SharedRootUnit C i) (f3SharedRootUnit C j)

/-- The original fixed configuration has the actual one-based waiting tail. -/
theorem f3SharedRootConfig_unitHaar_wait_gt {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L : ℕ}
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) (T : ℕ) :
    f3UnitHaarStream {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3SharedRootWait C i j ω} =
      (1 - ((3 : ℝ≥0∞) ^ L)⁻¹) ^ T := by
  have hLpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  have hdist : rootDistance (f3SharedRootUnit C i : ℚ_[3])
      (f3SharedRootUnit C j : ℚ_[3]) = (L : WithTop ℤ) := by
    simpa only [f3SharedRootUnit_coe] using hL
  exact f3UnitHaarStream_rootWait_gt (f3SharedRootUnit_isUnit C i)
    (f3SharedRootUnit_isUnit C j) hLpos hdist T

/-- The original fixed configuration has actual waiting expectation `3^L`. -/
theorem f3SharedRootConfig_unitHaar_wait_mean {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L : ℕ}
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) :
    (∫⁻ ω, (f3SharedRootWait C i j ω : ℝ≥0∞) ∂f3UnitHaarStream) =
      (3 : ℝ≥0∞) ^ L := by
  have hLpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  have hdist : rootDistance (f3SharedRootUnit C i : ℚ_[3])
      (f3SharedRootUnit C j : ℚ_[3]) = (L : WithTop ℤ) := by
    simpa only [f3SharedRootUnit_coe] using hL
  exact f3UnitHaarStream_rootWait_mean (f3SharedRootUnit_isUnit C i)
    (f3SharedRootUnit_isUnit C j) hLpos hdist

end

end OmegaBalance
