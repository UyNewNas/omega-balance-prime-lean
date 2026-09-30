import OmegaBalance.F3RootWaitingHaar
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Complex.Exponential

/-!
# Actual joint certificate waiting time under unit Haar sampling

REC-L7 / theorem 2.3, equation (2.8), tail only. The waiting variable is the
finite maximum of the existing actual first-certificate times, over one
canonical representative `i < j` of each distinct unordered label pair. The
maximum distance is computed from the same fixed original configuration.

The event of stopping by T is exactly recovery by the existing matrix scan on
the first T complete observations. This equivalence is pointwise, including
root hits, never-hit streams, and T = 0. Each observation uses one shared
stream coordinate for every label; no independence between pairs is assumed.
The logarithmic mean, moving configurations and prime transfer remain open.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Exactly one ordered representative of each unordered distinct label pair. -/
def f3RootPairs (m : ℕ) : Finset (Fin m × Fin m) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun ij => ij.1 < ij.2)

/-- Membership in the canonical pair set is precisely strict label order. -/
theorem f3RootPairs_mem {m : ℕ} (ij : Fin m × Fin m) :
    ij ∈ f3RootPairs m ↔ ij.1 < ij.2 := by
  simp [f3RootPairs]

/-- The union coefficient is choose-two, without counting both orientations. -/
theorem f3RootPairs_card (m : ℕ) : (f3RootPairs m).card = m.choose 2 := by
  simpa only [f3RootPairs, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_product_filter_lt (s := Finset.univ : Finset (Fin m)))

/-- Natural exponent of the actual finite off-diagonal root distance.
Only off-diagonal uses are identified with extended rootDistance below. -/
def f3RootDistanceExponent {m : ℕ} (C : F3SharedRootConfig m) (i j : Fin m) : ℕ :=
  (C.root i - C.root j).valuation.toNat

/-- Distinct roots have exactly this finite distance; no diagonal infinity is lost. -/
theorem f3RootDistanceExponent_eq {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (hij : i ≠ j) :
    rootDistance (C.root i) (C.root j) = (f3RootDistanceExponent C i j : WithTop ℤ) := by
  have hne : C.root i ≠ C.root j := fun h => hij (C.root_injective h)
  have hv : rootDistance (C.root i) (C.root j) =
      ((C.root i - C.root j).valuation : WithTop ℤ) := rootDepth_eq_valuation hne
  have hpos : (1 : ℤ) ≤ (C.root i - C.root j).valuation := by
    have h := C.roots_same_residue i j
    rw [hv] at h
    exact_mod_cast h
  rw [hv]
  exact congrArg (fun z : ℤ => (z : WithTop ℤ))
    (Int.toNat_of_nonneg (by omega : 0 ≤ (C.root i - C.root j).valuation)).symm

/-- The common first residue gives a positive finite off-diagonal exponent. -/
theorem f3RootDistanceExponent_pos {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (hij : i ≠ j) : 1 ≤ f3RootDistanceExponent C i j := by
  have h := C.roots_same_residue i j
  rw [f3RootDistanceExponent_eq C hij] at h
  exact_mod_cast h

/-- The actual maximum finite pair-distance exponent of the original configuration. -/
def f3RootMaxDistance {m : ℕ} (C : F3SharedRootConfig m) : ℕ :=
  (f3RootPairs m).sup (fun ij => f3RootDistanceExponent C ij.1 ij.2)

/-- Every canonical actual pair exponent is bounded by the actual maximum. -/
theorem f3RootDistanceExponent_le_max {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (hij : i < j) :
    f3RootDistanceExponent C i j ≤ f3RootMaxDistance C :=
  Finset.le_sup ((f3RootPairs_mem (i, j)).mpr hij)

/-- Actual first observation count at which every unordered pair has a certificate. -/
def f3JointRootWait {m : ℕ} (C : F3SharedRootConfig m) (ω : ℕ → ℤ_[3]) : ℕ∞ :=
  (f3RootPairs m).sup (fun ij => f3SharedRootWait C ij.1 ij.2 ω)

/-- The original-root pair wait retains the exact all-failures interpretation. -/
theorem f3SharedRootWait_gt_iff {m : ℕ} (C : F3SharedRootConfig m)
    (i j : Fin m) (ω : ℕ → ℤ_[3]) (T : ℕ) :
    (T : ℕ∞) < f3SharedRootWait C i j ω ↔ ∀ n < T,
      rootDepth (ω n : ℚ_[3]) (C.root i) = rootDepth (ω n : ℚ_[3]) (C.root j) := by
  simpa only [f3SharedRootWait, f3SharedRootUnit_coe] using
    (f3RootWait_gt_iff (f3SharedRootUnit C i) (f3SharedRootUnit C j) ω T)

/-- A pair stops by T exactly when one of those T actual observations is unequal. -/
theorem f3SharedRootWait_le_iff {m : ℕ} (C : F3SharedRootConfig m)
    (i j : Fin m) (ω : ℕ → ℤ_[3]) (T : ℕ) :
    f3SharedRootWait C i j ω ≤ (T : ℕ∞) ↔ ∃ n < T,
      rootDepth (ω n : ℚ_[3]) (C.root i) ≠ rootDepth (ω n : ℚ_[3]) (C.root j) := by
  have h := not_congr (f3SharedRootWait_gt_iff C i j ω T)
  simpa only [not_lt, not_forall, not_implies, not_not] using h

/-- Joint failure means that some canonical pair failed at every prior time. -/
theorem f3JointRootWait_gt_iff {m : ℕ} (C : F3SharedRootConfig m)
    (ω : ℕ → ℤ_[3]) (T : ℕ) :
    (T : ℕ∞) < f3JointRootWait C ω ↔ ∃ ij ∈ f3RootPairs m, ∀ n < T,
      rootDepth (ω n : ℚ_[3]) (C.root ij.1) =
        rootDepth (ω n : ℚ_[3]) (C.root ij.2) := by
  simp only [f3JointRootWait, Finset.lt_sup_iff, f3SharedRootWait_gt_iff]

/-- Joint success is exactly one actual unequal observation for every distinct pair.
Reversing labels does not require a new independent observation. -/
theorem f3JointRootWait_le_iff {m : ℕ} (C : F3SharedRootConfig m)
    (ω : ℕ → ℤ_[3]) (T : ℕ) :
    f3JointRootWait C ω ≤ (T : ℕ∞) ↔ ∀ i j : Fin m, i ≠ j → ∃ n < T,
      rootDepth (ω n : ℚ_[3]) (C.root i) ≠ rootDepth (ω n : ℚ_[3]) (C.root j) := by
  rw [f3JointRootWait, Finset.sup_le_iff]
  constructor
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (f3SharedRootWait_le_iff C i j ω T).mp
        (h (i, j) ((f3RootPairs_mem (i, j)).mpr hlt))
    · obtain ⟨n, hn, hne⟩ := (f3SharedRootWait_le_iff C j i ω T).mp
        (h (j, i) ((f3RootPairs_mem (j, i)).mpr hgt))
      exact ⟨n, hn, hne.symm⟩
  · intro h ij hij
    exact (f3SharedRootWait_le_iff C ij.1 ij.2 ω T).mpr
      (h ij.1 ij.2 (ne_of_lt ((f3RootPairs_mem ij).mp hij)))

/-- The actual maximum wait is exactly the existing full-matrix scan's stopping time.
This holds on every stream, with the true infinite diagonal and root-hit depths. -/
theorem f3JointRootWait_le_iff_matrix_recover {m : ℕ} (C : F3SharedRootConfig m)
    (ω : ℕ → ℤ_[3]) (T : ℕ) :
    f3JointRootWait C ω ≤ (T : ℕ∞) ↔
      depthCertificateMatrix (List.finRange T)
          (fun t k => rootDepth (ω t.val : ℚ_[3]) (C.root k)) =
        (fun i j => some (rootDistance (C.root i) (C.root j))) := by
  constructor
  · intro h
    apply depthCertificateMatrix_recover (α₀ := C.root)
      (fun _ _ _ _ => rfl)
    intro i j hij
    obtain ⟨n, hn, hne⟩ := (f3JointRootWait_le_iff C ω T).mp h i j hij
    exact ⟨⟨n, hn⟩, by simp, hne⟩
  · intro h
    apply (f3JointRootWait_le_iff C ω T).mpr
    intro i j hij
    have hentry := congrFun (congrFun h i) j
    have hscan : depthCertificateScan (List.finRange T)
        (fun t k => rootDepth (ω t.val : ℚ_[3]) (C.root k)) i j =
        some (rootDistance (C.root i) (C.root j)) := by
      simpa only [depthCertificateMatrix, if_neg hij] using hentry
    obtain ⟨t, _ht, hne⟩ :=
      (depthCertificateScan_recover_iff (samples := List.finRange T)
        (d := fun t : Fin T => (ω t.val : ℚ_[3]))
        (α := fun _ => C.root) (α₀ := C.root) i j (fun _ _ => rfl)).mp hscan
    exact ⟨t.val, t.isLt, hne⟩

/-- The actual joint tail event is a finite union, not a product across root pairs. -/
theorem f3JointRootWait_tail_eq_union {m : ℕ} (C : F3SharedRootConfig m) (T : ℕ) :
    {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3JointRootWait C ω} =
      ⋃ ij ∈ f3RootPairs m,
        {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3SharedRootWait C ij.1 ij.2 ω} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, f3JointRootWait, Finset.lt_sup_iff]

/-- The real-valued pair tail follows from the already proved actual ENNReal law. -/
theorem f3SharedRootConfig_unitHaar_wait_gt_real {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (hij : i ≠ j) (T : ℕ) :
    f3UnitHaarStream.real {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3SharedRootWait C i j ω} =
      (1 - ((3 : ℝ) ^ f3RootDistanceExponent C i j)⁻¹) ^ T := by
  have hp : ((3 : ℝ≥0∞) ^ f3RootDistanceExponent C i j)⁻¹ ≤ 1 := by
    rw [← f3SharedRootConfig_unitHaar_depth_ne C hij (f3RootDistanceExponent_eq C hij)]
    exact prob_le_one
  change (f3UnitHaarStream _).toReal = _
  rw [f3SharedRootConfig_unitHaar_wait_gt C hij (f3RootDistanceExponent_eq C hij) T,
    ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top]
  norm_num [ENNReal.toReal_inv, ENNReal.toReal_pow]

/-- A genuine pair's tail is at most the exponential envelope for any upper bound K. -/
theorem f3SharedRootConfig_unitHaar_wait_gt_le_exp {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (hij : i ≠ j) {K : ℕ}
    (hK : f3RootDistanceExponent C i j ≤ K) (T : ℕ) :
    f3UnitHaarStream.real {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3SharedRootWait C i j ω} ≤
      Real.exp (-(T : ℝ) * ((3 : ℝ) ^ K)⁻¹) := by
  rw [f3SharedRootConfig_unitHaar_wait_gt_real C hij T]
  have hp : ((3 : ℝ) ^ f3RootDistanceExponent C i j)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))
  have hrate : ((3 : ℝ) ^ K)⁻¹ ≤
      ((3 : ℝ) ^ f3RootDistanceExponent C i j)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) hK
  calc
    (1 - ((3 : ℝ) ^ f3RootDistanceExponent C i j)⁻¹) ^ T ≤
        (Real.exp (-((3 : ℝ) ^ f3RootDistanceExponent C i j)⁻¹)) ^ T :=
      pow_le_pow_left₀ (sub_nonneg.mpr hp) (Real.one_sub_le_exp_neg _) T
    _ = Real.exp (-(T : ℝ) * ((3 : ℝ) ^ f3RootDistanceExponent C i j)⁻¹) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-(T : ℝ) * ((3 : ℝ) ^ K)⁻¹) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hrate (neg_nonpos.mpr (Nat.cast_nonneg T))

/-- REC-L7's actual joint recovery tail, with the exact choose-two coefficient and
actual maximum distance. Only complete observations are sampled independently. -/
theorem f3SharedRootConfig_unitHaar_jointWait_gt {m : ℕ} (C : F3SharedRootConfig m)
    (T : ℕ) :
    f3UnitHaarStream.real {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3JointRootWait C ω} ≤
      min 1 ((m.choose 2 : ℝ) *
        Real.exp (-(T : ℝ) * ((3 : ℝ) ^ f3RootMaxDistance C)⁻¹)) := by
  apply le_min measureReal_le_one
  rw [f3JointRootWait_tail_eq_union]
  calc
    f3UnitHaarStream.real (⋃ ij ∈ f3RootPairs m,
        {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3SharedRootWait C ij.1 ij.2 ω}) ≤
        ∑ ij ∈ f3RootPairs m, f3UnitHaarStream.real
          {ω : ℕ → ℤ_[3] | (T : ℕ∞) < f3SharedRootWait C ij.1 ij.2 ω} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _ij ∈ f3RootPairs m,
        Real.exp (-(T : ℝ) * ((3 : ℝ) ^ f3RootMaxDistance C)⁻¹) := by
      apply Finset.sum_le_sum
      intro ij hij
      have hlt := (f3RootPairs_mem ij).mp hij
      exact f3SharedRootConfig_unitHaar_wait_gt_le_exp C (ne_of_lt hlt)
        (f3RootDistanceExponent_le_max C hlt) T
    _ = (m.choose 2 : ℝ) *
        Real.exp (-(T : ℝ) * ((3 : ℝ) ^ f3RootMaxDistance C)⁻¹) := by
      rw [Finset.sum_const, nsmul_eq_mul, f3RootPairs_card]

end

end OmegaBalance
