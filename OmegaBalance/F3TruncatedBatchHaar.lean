import OmegaBalance.F3TruncatedCertificateHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real

/-!
# Actual finite-batch recovery of the truncated distance matrix

REC-L12 / theorem 2.6, equation (2.14). Complete parameters are independently
sampled under the genuine finite product of normalized unit Haar measures.
Every root label receives the same parameter at each time. Pair failure is a
product rectangle across times, while matrix failure is a union across pairs.
No independence between root pairs is assumed.

The algorithm is the existing truncatedDepthCertificateMatrix. Its target is
min(L,H), with diagonal H, never the untruncated matrix above the cutoff.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- All T actual observations fail the existing finite-precision certificate rule. -/
def f3TruncatedCertificateBatchFailure (a b : ℤ_[3]) (H T : ℕ) :
    Set (Fin T → ℤ_[3]) :=
  {d | ∀ t : Fin T, d t ∉ f3TruncatedCertificateEvent a b H}

/-- Time independence is represented by the actual complement rectangle. -/
theorem f3TruncatedCertificateBatchFailure_eq_pi (a b : ℤ_[3]) (H T : ℕ) :
    f3TruncatedCertificateBatchFailure a b H T =
      Set.pi Set.univ (fun _ : Fin T => (f3TruncatedCertificateEvent a b H)ᶜ) := by
  ext d
  simp only [f3TruncatedCertificateBatchFailure, Set.mem_setOf_eq, Set.mem_pi,
    Set.mem_univ, forall_const, Set.mem_compl_iff]

/-- No observation means no off-diagonal certificate, including at finite precision. -/
theorem f3TruncatedCertificateBatchFailure_zero (a b : ℤ_[3]) (H : ℕ) :
    f3TruncatedCertificateBatchFailure a b H 0 = Set.univ := by
  ext d
  simp [f3TruncatedCertificateBatchFailure]

/-- Actual finite-batch failure is measurable. -/
theorem f3TruncatedCertificateBatchFailure_measurable {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (H T : ℕ) :
    MeasurableSet (f3TruncatedCertificateBatchFailure a b H T) := by
  rw [f3TruncatedCertificateBatchFailure_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => (f3TruncatedCertificateEvent_measurable hL H).compl)

/-- The genuine product measure gives the exact power of the actual failure mass. -/
theorem f3UnitHaar_truncated_batch_failure (a b : ℤ_[3]) (H T : ℕ) :
    Measure.pi (fun _ : Fin T => f3UnitHaar) (f3TruncatedCertificateBatchFailure a b H T) =
      (f3UnitHaar (f3TruncatedCertificateEvent a b H)ᶜ) ^ T := by
  rw [f3TruncatedCertificateBatchFailure_eq_pi, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The real pair-failure probability uses the measured success complement. -/
theorem f3UnitHaar_truncated_batch_failure_real {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (H T : ℕ) :
    (Measure.pi (fun _ : Fin T => f3UnitHaar)).real
        (f3TruncatedCertificateBatchFailure a b H T) =
      (1 - f3UnitHaar.real (f3TruncatedCertificateEvent a b H)) ^ T := by
  change (Measure.pi (fun _ : Fin T => f3UnitHaar)
    (f3TruncatedCertificateBatchFailure a b H T)).toReal = _
  rw [f3UnitHaar_truncated_batch_failure, ENNReal.toReal_pow]
  change (f3UnitHaar.real (f3TruncatedCertificateEvent a b H)ᶜ) ^ T = _
  rw [measureReal_compl (f3TruncatedCertificateEvent_measurable hL H)]
  have hu : f3UnitHaar.real Set.univ = 1 := by simp [Measure.real]
  rw [hu]

/-- The actual single-event inclusion bound gives a uniform exponential pair tail. -/
theorem f3UnitHaar_truncated_batch_failure_le_exp {a b : ℤ_[3]} (ha : IsUnit a)
    {L H : ℕ} (hH : 1 ≤ H)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (T : ℕ) :
    (Measure.pi (fun _ : Fin T => f3UnitHaar)).real
        (f3TruncatedCertificateBatchFailure a b H T) ≤
      Real.exp (-(T : ℝ) / (2 * (3 : ℝ) ^ (H - 1))) := by
  have hr : f3UnitHaar.real (f3TruncatedCertificateEvent a b H) ≤ 1 := measureReal_le_one
  have hq : (2 * (3 : ℝ) ^ (H - 1))⁻¹ ≤
      f3UnitHaar.real (f3TruncatedCertificateEvent a b H) := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _)
      (f3UnitHaar_truncatedCertificate_lower_bound (b := b) ha hH)
    simpa [Measure.real, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_pow] using h
  rw [f3UnitHaar_truncated_batch_failure_real hL]
  calc
    (1 - f3UnitHaar.real (f3TruncatedCertificateEvent a b H)) ^ T ≤
        (1 - (2 * (3 : ℝ) ^ (H - 1))⁻¹) ^ T :=
      pow_le_pow_left₀ (sub_nonneg.mpr hr) (sub_le_sub_left hq 1) T
    _ ≤ (Real.exp (-(2 * (3 : ℝ) ^ (H - 1))⁻¹)) ^ T :=
      pow_le_pow_left₀ (sub_nonneg.mpr (hq.trans hr)) (Real.one_sub_le_exp_neg _) T
    _ = Real.exp (-(T : ℝ) / (2 * (3 : ℝ) ^ (H - 1))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      simp only [div_eq_mul_inv]
      ring

/-- Both finite-precision witness alternatives are invariant under label reversal. -/
theorem truncatedDepthWitness_comm (H : ℕ) (x y : WithTop ℤ) :
    truncatedDepthWitness H x y ↔ truncatedDepthWitness H y x := by
  constructor <;> rintro (hne | ⟨hx, hy⟩)
  · exact Or.inl hne.symm
  · exact Or.inr ⟨hy, hx⟩
  · exact Or.inl hne.symm
  · exact Or.inr ⟨hy, hx⟩

/-- Full algorithmic failure is exactly a union of actual canonical pair failures. -/
theorem f3TruncatedMatrixFailure_eq_union {m : ℕ} (C : F3SharedRootConfig m) (H T : ℕ) :
    {d : Fin T → ℤ_[3] |
      truncatedDepthCertificateMatrix H (List.finRange T)
          (fun t k => truncatedRootDepth H (d t : ℚ_[3]) (C.root k)) ≠
        (fun i j => some (truncatedRootDistance H (C.root i) (C.root j)))} =
      ⋃ ij ∈ f3RootPairs m, f3TruncatedCertificateBatchFailure
        (f3SharedRootUnit C ij.1) (f3SharedRootUnit C ij.2) H T := by
  classical
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop,
    f3TruncatedCertificateBatchFailure, f3TruncatedCertificateEvent, f3SharedRootUnit_coe]
  have hrec := truncatedDepthCertificateMatrix_recover_iff (H := H)
    (samples := List.finRange T) (d := fun t : Fin T => (d t : ℚ_[3]))
    (α := fun _ => C.root) (α₀ := C.root) (fun _ _ _ _ => rfl)
  constructor
  · intro hfail
    by_contra hnone
    apply hfail
    apply hrec.mpr
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · by_contra hw
      have hall : ∀ t : Fin T, ¬truncatedDepthWitness H
          (truncatedRootDepth H (d t : ℚ_[3]) (C.root i))
          (truncatedRootDepth H (d t : ℚ_[3]) (C.root j)) := by
        intro t ht
        exact hw ⟨t, by simp, ht⟩
      exact hnone ⟨(i, j), (f3RootPairs_mem (i, j)).mpr hlt, hall⟩
    · by_contra hw
      have hall : ∀ t : Fin T, ¬truncatedDepthWitness H
          (truncatedRootDepth H (d t : ℚ_[3]) (C.root j))
          (truncatedRootDepth H (d t : ℚ_[3]) (C.root i)) := by
        intro t ht
        exact hw ⟨t, by simp, (truncatedDepthWitness_comm H _ _).mp ht⟩
      exact hnone ⟨(j, i), (f3RootPairs_mem (j, i)).mpr hgt, hall⟩
  · rintro ⟨ij, hij, hall⟩ hmatrix
    obtain ⟨t, _ht, hw⟩ := hrec.mp hmatrix ij.1 ij.2
      (ne_of_lt ((f3RootPairs_mem ij).mp hij))
    exact hall t hw

/-- The actual matrix-failure event is measurable. -/
theorem f3TruncatedMatrixFailure_measurable {m : ℕ} (C : F3SharedRootConfig m) (H T : ℕ) :
    MeasurableSet {d : Fin T → ℤ_[3] |
      truncatedDepthCertificateMatrix H (List.finRange T)
          (fun t k => truncatedRootDepth H (d t : ℚ_[3]) (C.root k)) ≠
        (fun i j => some (truncatedRootDistance H (C.root i) (C.root j)))} := by
  rw [f3TruncatedMatrixFailure_eq_union]
  apply MeasurableSet.iUnion
  intro ij
  apply MeasurableSet.iUnion
  intro hij
  have hne := ne_of_lt ((f3RootPairs_mem ij).mp hij)
  have hd : rootDistance (f3SharedRootUnit C ij.1 : ℚ_[3])
      (f3SharedRootUnit C ij.2 : ℚ_[3]) =
        (f3RootDistanceExponent C ij.1 ij.2 : WithTop ℤ) := by
    simpa only [f3SharedRootUnit_coe] using f3RootDistanceExponent_eq C hne
  exact f3TruncatedCertificateBatchFailure_measurable hd H T

/-- Each genuine original-model pair has the same precision-uniform batch envelope. -/
theorem f3SharedRootConfig_truncated_pair_failure_le_exp {m : ℕ}
    (C : F3SharedRootConfig m) {i j : Fin m} (hij : i ≠ j) {H : ℕ} (hH : 1 ≤ H) (T : ℕ) :
    (Measure.pi (fun _ : Fin T => f3UnitHaar)).real
        (f3TruncatedCertificateBatchFailure (f3SharedRootUnit C i) (f3SharedRootUnit C j) H T) ≤
      Real.exp (-(T : ℝ) / (2 * (3 : ℝ) ^ (H - 1))) := by
  have hd : rootDistance (f3SharedRootUnit C i : ℚ_[3])
      (f3SharedRootUnit C j : ℚ_[3]) = (f3RootDistanceExponent C i j : WithTop ℤ) := by
    simpa only [f3SharedRootUnit_coe] using f3RootDistanceExponent_eq C hij
  exact f3UnitHaar_truncated_batch_failure_le_exp (f3SharedRootUnit_isUnit C i) hH hd T

/-- REC-L12 / (2.14): actual finite-batch truncated matrix failure has the stated tail bound. -/
theorem f3SharedRootConfig_unitHaar_truncated_matrix_failure {m : ℕ}
    (C : F3SharedRootConfig m) {H : ℕ} (hH : 1 ≤ H) (T : ℕ) :
    (Measure.pi (fun _ : Fin T => f3UnitHaar)).real {d : Fin T → ℤ_[3] |
      truncatedDepthCertificateMatrix H (List.finRange T)
          (fun t k => truncatedRootDepth H (d t : ℚ_[3]) (C.root k)) ≠
        (fun i j => some (truncatedRootDistance H (C.root i) (C.root j)))} ≤
      min 1 ((m.choose 2 : ℝ) * Real.exp (-(T : ℝ) / (2 * (3 : ℝ) ^ (H - 1)))) := by
  apply le_min measureReal_le_one
  rw [f3TruncatedMatrixFailure_eq_union]
  calc
    (Measure.pi (fun _ : Fin T => f3UnitHaar)).real
        (⋃ ij ∈ f3RootPairs m, f3TruncatedCertificateBatchFailure
          (f3SharedRootUnit C ij.1) (f3SharedRootUnit C ij.2) H T) ≤
        ∑ ij ∈ f3RootPairs m, (Measure.pi (fun _ : Fin T => f3UnitHaar)).real
          (f3TruncatedCertificateBatchFailure (f3SharedRootUnit C ij.1)
            (f3SharedRootUnit C ij.2) H T) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _ij ∈ f3RootPairs m,
        Real.exp (-(T : ℝ) / (2 * (3 : ℝ) ^ (H - 1))) := by
      apply Finset.sum_le_sum
      intro ij hij
      exact f3SharedRootConfig_truncated_pair_failure_le_exp C
        (ne_of_lt ((f3RootPairs_mem ij).mp hij)) hH T
    _ = (m.choose 2 : ℝ) * Real.exp (-(T : ℝ) / (2 * (3 : ℝ) ^ (H - 1))) := by
      rw [Finset.sum_const, nsmul_eq_mul, f3RootPairs_card]

end

end OmegaBalance
