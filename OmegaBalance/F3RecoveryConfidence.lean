import OmegaBalance.F3JointWaitingMean
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit confidence for the actual certificate matrix

The confidence threshold in REC theorem 2.3 is applied to the genuine joint
waiting tail and then to the complement event of the existing matrix scan.
The original fixed configuration and whole-sample Haar stream are unchanged.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Elementary inversion of the proved exponential envelope at a positive confidence level. -/
theorem f3Recovery_exponential_confidence {A B δ t : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (ht : A * Real.log (B / δ) ≤ t) :
    B * Real.exp (-t / A) ≤ δ := by
  have hlog : Real.log (B / δ) ≤ t / A :=
    (le_div_iff₀ hA).mpr (by simpa only [mul_comm] using ht)
  have he : Real.exp (-t / A) ≤ Real.exp (-Real.log (B / δ)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hlog
  calc
    B * Real.exp (-t / A) ≤ B * Real.exp (-Real.log (B / δ)) :=
      mul_le_mul_of_nonneg_left he hB.le
    _ = δ := by
      rw [Real.exp_neg, Real.exp_log (div_pos hB hδ)]
      field_simp [ne_of_gt hB, ne_of_gt hδ]
      <;> ring

/-- The paper's explicit sample threshold bounds the actual joint failure probability. -/
theorem f3SharedRootConfig_unitHaar_jointWait_confidence {m : ℕ}
    (C : F3SharedRootConfig m) {δ : ℝ} (hδ : 0 < δ) (_hδone : δ < 1) (T : ℕ)
    (hT : (3 : ℝ) ^ f3RootMaxDistance C * Real.log ((m.choose 2 : ℝ) / δ) ≤ (T : ℝ)) :
    f3UnitHaarStream.real {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3JointRootWait C ω} ≤ δ := by
  have hB : (0 : ℝ) < (m.choose 2 : ℝ) := by
    exact_mod_cast (Nat.choose_pos C.two_le_card)
  have he := f3Recovery_exponential_confidence
    (by positivity : (0 : ℝ) < 3 ^ f3RootMaxDistance C) hB hδ hT
  calc
    f3UnitHaarStream.real {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3JointRootWait C ω} ≤
        min 1 ((m.choose 2 : ℝ) *
          Real.exp (-(T : ℝ) * ((3 : ℝ) ^ f3RootMaxDistance C)⁻¹)) :=
      f3SharedRootConfig_unitHaar_jointWait_gt C T
    _ ≤ (m.choose 2 : ℝ) *
        Real.exp (-(T : ℝ) * ((3 : ℝ) ^ f3RootMaxDistance C)⁻¹) := min_le_right _ _
    _ ≤ δ := by simpa only [div_eq_mul_inv] using he

/-- At the stated threshold the existing scan actually recovers every true matrix entry
with probability at least one minus delta, including the true infinite diagonal. -/
theorem f3SharedRootConfig_unitHaar_matrix_recovery_confidence {m : ℕ}
    (C : F3SharedRootConfig m) {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) (T : ℕ)
    (hT : (3 : ℝ) ^ f3RootMaxDistance C * Real.log ((m.choose 2 : ℝ) / δ) ≤ (T : ℝ)) :
    1 - δ ≤ f3UnitHaarStream.real {ω : ℕ → ℤ_[3] |
      depthCertificateMatrix (List.finRange T)
          (fun t k => rootDepth (ω t.val : ℚ_[3]) (C.root k)) =
        (fun i j => some (rootDistance (C.root i) (C.root j)))} := by
  have hevent : {ω : ℕ → ℤ_[3] |
      depthCertificateMatrix (List.finRange T)
          (fun t k => rootDepth (ω t.val : ℚ_[3]) (C.root k)) =
        (fun i j => some (rootDistance (C.root i) (C.root j)))} =
      {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3JointRootWait C ω}ᶜ := by
    ext ω
    simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt] using
      (f3JointRootWait_le_iff_matrix_recover C ω T).symm
  rw [hevent, measureReal_compl (f3JointRootWait_tail_measurable C T)]
  have hu : f3UnitHaarStream.real Set.univ = 1 := by simp [Measure.real]
  rw [hu]
  exact sub_le_sub_left (f3SharedRootConfig_unitHaar_jointWait_confidence C hδ hδone T hT) 1

end

end OmegaBalance
