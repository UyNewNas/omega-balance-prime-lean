import OmegaBalance.F3JointWaitingHaar
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Actual joint certificate waiting expectation

REC-L7 / theorem 2.3, equation (2.8), logarithmic mean. This bounds the
nonnegative expectation of the existing actual ENat maximum, including infinite
never-hit streams. The analytic envelope is only an upper bound on its proved
Haar tail, not a prescribed distribution. Moving configurations, signed
root-depth differences and prime transfer remain separate.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory Set
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The analytic majorant of the already proved joint waiting tail. -/
def f3JointTailEnvelope (B p x : ℝ) : ℝ := min 1 (B * Real.exp (-p * x))

/-- Nonnegativity of the tail majorant. -/
theorem f3JointTailEnvelope_nonneg {B : ℝ} (hB : 0 ≤ B) (p x : ℝ) :
    0 ≤ f3JointTailEnvelope B p x :=
  le_min zero_le_one (mul_nonneg hB (Real.exp_pos _).le)

/-- The analytic majorant decreases with elapsed time. -/
theorem f3JointTailEnvelope_antitone {B p : ℝ} (hB : 0 ≤ B) (hp : 0 ≤ p) :
    Antitone (f3JointTailEnvelope B p) := by
  intro x y hxy
  apply min_le_min le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr hp))

/-- Integrability follows by domination by the existing exponential integral. -/
theorem f3JointTailEnvelope_integrable {B p : ℝ} (hB : 0 ≤ B) (hp : 0 < p) :
    IntegrableOn (f3JointTailEnvelope B p) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => B * Real.exp (-p * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hp) 0).const_mul B
  have hc : Continuous (f3JointTailEnvelope B p) := by
    unfold f3JointTailEnvelope
    fun_prop
  apply hg.mono_nonneg hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => f3JointTailEnvelope_nonneg hB p x)
  · exact Filter.Eventually.of_forall (fun x => min_le_right _ _)

/-- Splitting at log(B)/p bounds the envelope integral without a piecewise formula. -/
theorem f3JointTailEnvelope_integral_le {B p : ℝ} (hB : 1 ≤ B) (hp : 0 < p) :
    (∫ x in Ioi (0 : ℝ), f3JointTailEnvelope B p x) ≤ (Real.log B + 1) / p := by
  let c : ℝ := Real.log B / p
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hpne : p ≠ 0 := ne_of_gt hp
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hc : 0 ≤ c := div_nonneg (Real.log_nonneg hB) hp.le
  have hf := f3JointTailEnvelope_integrable (le_trans zero_le_one hB) hp
  have hleft : Ioc (0 : ℝ) c ⊆ Ioi 0 := fun _ hx => hx.1
  have hright : Ioi c ⊆ Ioi (0 : ℝ) := fun _ hx => lt_of_le_of_lt hc hx
  have hunion : Ioc (0 : ℝ) c ∪ Ioi c = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · exact lt_of_le_of_lt hc hx
    · intro hx
      by_cases hxc : x ≤ c
      · exact Or.inl ⟨hx, hxc⟩
      · exact Or.inr (lt_of_not_ge hxc)
  have hdisj : Disjoint (Ioc (0 : ℝ) c) (Ioi c) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) c) :=
    integrableOn_const
  have hexp : IntegrableOn (fun x : ℝ => B * Real.exp (-p * x)) (Ioi c) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hp) c).const_mul B
  have hexpValue : (∫ x in Ioi c, B * Real.exp (-p * x)) = 1 / p := by
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hp)]
    have hpc : -p * c = -Real.log B := by
      dsimp [c]
      field_simp [hpne]
      <;> ring
    rw [hpc, Real.exp_neg, Real.exp_log hBpos]
    field_simp [hpne, hBne]
    <;> ring
  calc
    (∫ x in Ioi (0 : ℝ), f3JointTailEnvelope B p x) =
        (∫ x in Ioc (0 : ℝ) c, f3JointTailEnvelope B p x) +
        ∫ x in Ioi c, f3JointTailEnvelope B p x := by
      rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
        (hf.mono_set hleft) (hf.mono_set hright)]
    _ ≤ (∫ _x in Ioc (0 : ℝ) c, (1 : ℝ)) +
        ∫ x in Ioi c, B * Real.exp (-p * x) := by
      apply add_le_add
      · exact setIntegral_mono_on (hf.mono_set hleft) hconst measurableSet_Ioc
          (fun _ _ => min_le_left _ _)
      · exact setIntegral_mono_on (hf.mono_set hright) hexp measurableSet_Ioi
          (fun _ _ => min_le_right _ _)
    _ = c + 1 / p := by
      rw [hexpValue, setIntegral_const, Real.volume_real_Ioc_of_le hc]
      simp
    _ = (Real.log B + 1) / p := by dsimp [c]; ring

/-- The locked integral test yields the logarithmic sum bound. -/
theorem f3JointTailEnvelope_tsum_le {B p : ℝ} (hB : 1 ≤ B) (hp : 0 < p) :
    (∑' n : ℕ, f3JointTailEnvelope B p n) ≤ 1 + (Real.log B + 1) / p := by
  have hB0 := le_trans zero_le_one hB
  have ha : AntitoneOn (f3JointTailEnvelope B p) (Ici 0) :=
    (f3JointTailEnvelope_antitone hB0 hp.le).antitoneOn
  have hi := f3JointTailEnvelope_integrable hB0 hp
  have hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f3JointTailEnvelope B p x :=
    fun x _ => f3JointTailEnvelope_nonneg hB0 p x
  calc
    (∑' n : ℕ, f3JointTailEnvelope B p n) ≤
        f3JointTailEnvelope B p 0 + ∫ x in Ioi (0 : ℝ), f3JointTailEnvelope B p x :=
      ha.tsum_le_integral hi hn
    _ ≤ 1 + (Real.log B + 1) / p := by
      apply add_le_add
      · exact min_le_left _ _
      · exact f3JointTailEnvelope_integral_le hB hp

/-- Every actual joint tail event is measurable as the finite union of genuine pair tails. -/
theorem f3JointRootWait_tail_measurable {m : ℕ} (C : F3SharedRootConfig m) (T : ℕ) :
    MeasurableSet {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3JointRootWait C ω} := by
  rw [f3JointRootWait_tail_eq_union]
  apply MeasurableSet.iUnion
  intro ij
  apply MeasurableSet.iUnion
  intro hij
  have hne := ne_of_lt ((f3RootPairs_mem ij).mp hij)
  have hd : rootDistance (f3SharedRootUnit C ij.1 : ℚ_[3])
      (f3SharedRootUnit C ij.2 : ℚ_[3]) =
        (f3RootDistanceExponent C ij.1 ij.2 : WithTop ℤ) := by
    simpa only [f3SharedRootUnit_coe] using f3RootDistanceExponent_eq C hne
  simpa only [f3SharedRootWait] using f3RootWait_tail_measurable hd T

/-- Pointwise tail counting for the actual maximum, including an infinite wait. -/
theorem f3JointRootWait_toENNReal_eq_tsum {m : ℕ} (C : F3SharedRootConfig m)
    (ω : ℕ → ℤ_[3]) :
    (f3JointRootWait C ω : ℝ≥0∞) = ∑' T : ℕ,
      ({x : ℕ → ℤ_[3] | (T : ℕ∞) < f3JointRootWait C x}.indicator
        (fun _ => (1 : ℝ≥0∞))) ω := by
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  cases h : f3JointRootWait C ω using ENat.recTopCoe with
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

/-- The actual extended maximum is measurable, without removing never-hit streams. -/
theorem f3JointRootWait_measurable_toENNReal {m : ℕ} (C : F3SharedRootConfig m) :
    Measurable (fun ω : ℕ → ℤ_[3] => (f3JointRootWait C ω : ℝ≥0∞)) := by
  have heq : (fun ω : ℕ → ℤ_[3] => (f3JointRootWait C ω : ℝ≥0∞)) =
      (fun ω => ∑' T : ℕ,
        ({x : ℕ → ℤ_[3] | (T : ℕ∞) < f3JointRootWait C x}.indicator
          (fun _ => (1 : ℝ≥0∞))) ω) :=
    funext (f3JointRootWait_toENNReal_eq_tsum C)
  rw [heq]
  exact Measurable.ennreal_tsum fun T =>
    measurable_const.indicator (f3JointRootWait_tail_measurable C T)

/-- The nonnegative expectation is the sum of the actual maximum's tail probabilities. -/
theorem f3JointRootWait_lintegral_eq_tsum {m : ℕ} (C : F3SharedRootConfig m) :
    (∫⁻ ω, (f3JointRootWait C ω : ℝ≥0∞) ∂f3UnitHaarStream) =
      ∑' T : ℕ, f3UnitHaarStream {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3JointRootWait C ω} := by
  classical
  simp_rw [f3JointRootWait_toENNReal_eq_tsum]
  rw [lintegral_tsum (fun T =>
    (measurable_const.indicator (f3JointRootWait_tail_measurable C T)).aemeasurable)]
  simp_rw [lintegral_indicator_fun_one (f3JointRootWait_tail_measurable C _)]

/-- REC-L7's logarithmic bound for the actual maximum of all certificate waits. -/
theorem f3SharedRootConfig_unitHaar_jointWait_mean_le {m : ℕ} (C : F3SharedRootConfig m) :
    (∫⁻ ω, (f3JointRootWait C ω : ℝ≥0∞) ∂f3UnitHaarStream) ≤
      ENNReal.ofReal (1 + (3 : ℝ) ^ f3RootMaxDistance C * (1 + Real.log (m.choose 2))) := by
  let B : ℝ := m.choose 2
  let p : ℝ := ((3 : ℝ) ^ f3RootMaxDistance C)⁻¹
  have hB : 1 ≤ B := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.choose_pos C.two_le_card))
  have hp : 0 < p := by dsimp [p]; positivity
  have hB0 := le_trans zero_le_one hB
  have ha : AntitoneOn (f3JointTailEnvelope B p) (Ici 0) :=
    (f3JointTailEnvelope_antitone hB0 hp.le).antitoneOn
  have hi := f3JointTailEnvelope_integrable hB0 hp
  have hs := ha.summable_of_integrableOn_Ioi_zero hi
    (fun x _ => f3JointTailEnvelope_nonneg hB0 p x)
  rw [f3JointRootWait_lintegral_eq_tsum]
  calc
    (∑' T : ℕ, f3UnitHaarStream {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3JointRootWait C ω}) ≤
        ∑' T : ℕ, ENNReal.ofReal (f3JointTailEnvelope B p T) := by
      apply ENNReal.tsum_le_tsum
      intro T
      have h := ENNReal.ofReal_le_ofReal (f3SharedRootConfig_unitHaar_jointWait_gt C T)
      simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
        f3JointTailEnvelope, B, p, neg_mul, mul_comm] using h
    _ = ENNReal.ofReal (∑' T : ℕ, f3JointTailEnvelope B p T) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun T => f3JointTailEnvelope_nonneg hB0 p T) hs).symm
    _ ≤ ENNReal.ofReal (1 + (Real.log B + 1) / p) :=
      ENNReal.ofReal_le_ofReal (f3JointTailEnvelope_tsum_le hB hp)
    _ = ENNReal.ofReal (1 + (3 : ℝ) ^ f3RootMaxDistance C * (1 + Real.log (m.choose 2))) := by
      congr 1
      dsimp [p, B]
      rw [div_inv_eq_mul]
      ring

/-- The complete certificate matrix is obtained after finite actual waiting almost surely. -/
theorem f3SharedRootConfig_unitHaar_jointWait_finite_ae {m : ℕ} (C : F3SharedRootConfig m) :
    ∀ᵐ ω ∂f3UnitHaarStream, f3JointRootWait C ω < ⊤ := by
  have hmean : (∫⁻ ω, (f3JointRootWait C ω : ℝ≥0∞) ∂f3UnitHaarStream) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (f3SharedRootConfig_unitHaar_jointWait_mean_le C)
  filter_upwards [ae_lt_top (f3JointRootWait_measurable_toENNReal C) hmean] with ω hω
  exact ENat.toENNReal_lt_top.mp hω

/-- Almost every actual stream eventually makes the existing scan recover the true matrix. -/
theorem f3SharedRootConfig_unitHaar_matrix_recover_ae {m : ℕ} (C : F3SharedRootConfig m) :
    ∀ᵐ ω ∂f3UnitHaarStream, ∃ T : ℕ,
      depthCertificateMatrix (List.finRange T)
          (fun t k => rootDepth (ω t.val : ℚ_[3]) (C.root k)) =
        (fun i j => some (rootDistance (C.root i) (C.root j))) := by
  filter_upwards [f3SharedRootConfig_unitHaar_jointWait_finite_ae C] with ω hω
  obtain ⟨T, hT⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hω)
  exact ⟨T, (f3JointRootWait_le_iff_matrix_recover C ω T).mp hT.symm.le⟩

end

end OmegaBalance
