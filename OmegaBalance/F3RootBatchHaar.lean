import OmegaBalance.F3SharedRootHaar
import OmegaBalance.F3RootReconstruction
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.List.FinRange

/-!
# Fixed-root finite-batch certificate probability under actual unit Haar

This is the finite-batch part of REC-L6 / proof (2.7). A batch has the actual
product law `Measure.pi (fun _ : Fin T => f3UnitHaar)`. Each time coordinate
is one sample `d`; every root label in that observation uses that same `d`.
Only different observations are sampled independently. The failure event is
exactly `none` from the existing ordered `depthCertificateScan`.

All finite batch sizes, including zero, are covered. Roots and depths remain
actual three-adic objects, with a root hit having depth infinity. The roots
are fixed throughout the batch. This file does not construct an infinite
one-based waiting time, prove its expectation, generalize to moving random
configurations, or transfer the law to prime sampling.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The actual unequal-depth event is measurable, via its two next-level balls. -/
theorem f3RootDepth_ne_measurable {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    MeasurableSet {d : ℤ_[3] |
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠ rootDepth (d : ℚ_[3]) (b : ℚ_[3])} := by
  have hevent : {d : ℤ_[3] |
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠ rootDepth (d : ℚ_[3]) (b : ℚ_[3])} =
      f3RootDepthTail a (L + 1) ∪ f3RootDepthTail b (L + 1) := by
    ext d
    exact rootDepth_ne_iff_mem_tail_union hL d
  rw [hevent]
  exact (f3RootDepthTail_measurable a (L + 1)).union
    (f3RootDepthTail_measurable b (L + 1))

/-- The actual equal-depth event is the measurable complement of certificate success. -/
theorem f3RootDepth_equal_measurable {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    MeasurableSet {d : ℤ_[3] |
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = rootDepth (d : ℚ_[3]) (b : ℚ_[3])} := by
  simpa only [Set.compl_setOf, not_not] using (f3RootDepth_ne_measurable hL).compl

/-- One actual observation fails to give a certificate with probability `1 - 3^(-L)`.
This is a complement of the already proved unequal-depth law, not a model assumption. -/
theorem f3UnitHaar_rootDepth_equal {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnitHaar {d : ℤ_[3] |
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = rootDepth (d : ℚ_[3]) (b : ℚ_[3])} =
        1 - ((3 : ℝ≥0∞) ^ L)⁻¹ := by
  have hcompl := prob_compl_eq_one_sub (μ := f3UnitHaar)
    (f3RootDepth_ne_measurable hL)
  simpa only [Set.compl_setOf, not_not, f3UnitHaar_rootDepth_ne ha hb hLpos hL]
    using hcompl

/-- Failure for a fixed pair means that all `T` complete observations have equal
extended depths at this pair. The same sample is used at both roots each time. -/
def f3RootDepthBatchFailure (a b : ℤ_[3]) (T : ℕ) : Set (Fin T → ℤ_[3]) :=
  {d | ∀ t : Fin T,
    rootDepth (d t : ℚ_[3]) (a : ℚ_[3]) = rootDepth (d t : ℚ_[3]) (b : ℚ_[3])}

/-- The all-failures event is the genuine product rectangle of the equal-depth event. -/
theorem f3RootDepthBatchFailure_eq_pi (a b : ℤ_[3]) (T : ℕ) :
    f3RootDepthBatchFailure a b T = Set.pi Set.univ (fun _ : Fin T =>
      {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (a : ℚ_[3]) =
        rootDepth (d : ℚ_[3]) (b : ℚ_[3])}) := by
  ext d
  simp only [f3RootDepthBatchFailure, Set.mem_setOf_eq, Set.mem_pi,
    Set.mem_univ, forall_const]

/-- An empty batch has not produced a certificate, for every possible empty sample. -/
theorem f3RootDepthBatchFailure_zero (a b : ℤ_[3]) :
    f3RootDepthBatchFailure a b 0 = Set.univ := by
  ext d
  simp [f3RootDepthBatchFailure]

/-- Every fixed-pair finite-batch failure event is measurable. -/
theorem f3RootDepthBatchFailure_measurable {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (T : ℕ) :
    MeasurableSet (f3RootDepthBatchFailure a b T) := by
  rw [f3RootDepthBatchFailure_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => f3RootDepth_equal_measurable hL)

/-- REC-L6, finite-batch slice: the actual product measure gives the exact failure
probability. No independence among the labels within an observation is assumed. -/
theorem f3UnitHaar_batch_failure {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (T : ℕ) :
    Measure.pi (fun _ : Fin T => f3UnitHaar) (f3RootDepthBatchFailure a b T) =
      (1 - ((3 : ℝ≥0∞) ^ L)⁻¹) ^ T := by
  rw [f3RootDepthBatchFailure_eq_pi, Measure.pi_pi]
  simp only [f3UnitHaar_rootDepth_equal ha hb hLpos hL, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The existing ordered scan is unknown exactly on the all-failures event.
This bridge uses all time indices in their `List.finRange T` order. -/
theorem depthCertificateScan_finRange_eq_none_iff {ι : Type*} {T : ℕ}
    (α : ι → ℤ_[3]) (d : Fin T → ℤ_[3]) (i j : ι) :
    depthCertificateScan (List.finRange T)
        (fun t k => rootDepth (d t : ℚ_[3]) (α k : ℚ_[3])) i j = none ↔
      d ∈ f3RootDepthBatchFailure (α i) (α j) T := by
  rw [depthCertificateScan_eq_none_iff]
  simp only [List.mem_finRange, forall_const, f3RootDepthBatchFailure, Set.mem_setOf_eq]

/-- Exact probability that the actual certificate algorithm is still unknown
for a fixed labelled pair after a finite batch, including the empty batch. -/
theorem f3UnitHaar_depthCertificateScan_none {ι : Type*} (α : ι → ℤ_[3])
    (i j : ι) (hi : IsUnit (α i)) (hj : IsUnit (α j)) {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (α i : ℚ_[3]) (α j : ℚ_[3]) = (L : WithTop ℤ)) (T : ℕ) :
    Measure.pi (fun _ : Fin T => f3UnitHaar) {d : Fin T → ℤ_[3] |
      depthCertificateScan (List.finRange T)
        (fun t k => rootDepth (d t : ℚ_[3]) (α k : ℚ_[3])) i j = none} =
      (1 - ((3 : ℝ≥0∞) ^ L)⁻¹) ^ T := by
  have hevent : {d : Fin T → ℤ_[3] |
      depthCertificateScan (List.finRange T)
        (fun t k => rootDepth (d t : ℚ_[3]) (α k : ℚ_[3])) i j = none} =
        f3RootDepthBatchFailure (α i) (α j) T := by
    ext d
    exact depthCertificateScan_finRange_eq_none_iff α d i j
  rw [hevent]
  exact f3UnitHaar_batch_failure hi hj hLpos hL T

/-- The finite-batch law on one fixed original shared-root configuration.
Its positive base depth, cardinality, distinct unit roots and common first
residue are retained. The scan observes excess depths `R`, not raw depths `D`. -/
theorem f3SharedRootConfig_unitHaar_scan_none {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L : ℕ}
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) (T : ℕ) :
    Measure.pi (fun _ : Fin T => f3UnitHaar) {d : Fin T → ℤ_[3] |
      depthCertificateScan (List.finRange T)
        (fun t k => rootDepth (d t : ℚ_[3]) (C.root k)) i j = none} =
      (1 - ((3 : ℝ≥0∞) ^ L)⁻¹) ^ T := by
  have hLpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  have hdist : rootDistance (f3SharedRootUnit C i : ℚ_[3])
      (f3SharedRootUnit C j : ℚ_[3]) = (L : WithTop ℤ) := by
    simpa only [f3SharedRootUnit_coe] using hL
  simpa only [f3SharedRootUnit_coe] using
    (f3UnitHaar_depthCertificateScan_none (f3SharedRootUnit C) i j
      (f3SharedRootUnit_isUnit C i) (f3SharedRootUnit_isUnit C j) hLpos hdist T)

end

end OmegaBalance
