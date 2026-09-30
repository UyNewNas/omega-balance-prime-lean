import OmegaBalance.F3SignedDepthLaw
import Mathlib.Probability.ConditionalProbability

/-!
# Conditional laws under the actual certificate-success event

The conditional measure is mathlib's normalized restriction of actual unit Haar
measure to unequal extended depths. Its positive normalization is proved from
the existing certificate law. Signed atoms retain finite integer depths, while
absolute continuity transfers the proved null-root exception treatment.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory Set
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Every nonzero genuine signed atom is an actual unequal-depth observation. -/
theorem f3SignedDepthEvent_subset_ne (a b : ℤ_[3]) {h : ℤ} (hh : h ≠ 0) :
    f3SignedDepthEvent a b h ⊆ {d : ℤ_[3] |
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠ rootDepth (d : ℚ_[3]) (b : ℚ_[3])} := by
  rintro d ⟨r, s, hr, hs, hdiff⟩ heq
  have hrs : r = s := by exact_mod_cast (hr.symm.trans (heq.trans hs))
  apply hh
  omega

/-- Distinct integer signed atoms are disjoint, without totalizing root hits. -/
theorem f3SignedDepthEvent_disjoint (a b : ℤ_[3]) {h k : ℤ} (hk : h ≠ k) :
    Disjoint (f3SignedDepthEvent a b h) (f3SignedDepthEvent a b k) := by
  apply Set.disjoint_left.mpr
  rintro d ⟨r, s, hr, hs, hd⟩ ⟨r', s', hr', hs', hd'⟩
  have hrr : r = r' := by exact_mod_cast (hr.symm.trans hr')
  have hss : s = s' := by exact_mod_cast (hs.symm.trans hs')
  apply hk
  omega

/-- Actual unit Haar measure conditioned on producing an unequal-depth certificate. -/
def f3UnequalDepthHaar (a b : ℤ_[3]) : Measure ℤ_[3] :=
  ProbabilityTheory.cond f3UnitHaar {d : ℤ_[3] |
    rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠ rootDepth (d : ℚ_[3]) (b : ℚ_[3])}

/-- The conditioning event has proved positive mass, so this is a probability measure. -/
theorem f3UnequalDepthHaar_isProbability {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    IsProbabilityMeasure (f3UnequalDepthHaar a b) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  rw [f3UnitHaar_rootDepth_ne ha hb hLpos hL]
  simp

/-- Conditioning preserves the already proved null sets of actual Haar measure. -/
theorem f3UnequalDepthHaar_absolutelyContinuous (a b : ℤ_[3]) :
    f3UnequalDepthHaar a b ≪ f3UnitHaar :=
  ProbabilityTheory.cond_absolutelyContinuous

/-- Genuine finite signed atoms still cover almost every conditioned observation. -/
theorem f3UnequalDepthHaar_signedDepth_defined_ae (a b : ℤ_[3]) :
    ∀ᵐ d ∂f3UnequalDepthHaar a b, ∃ h : ℤ, d ∈ f3SignedDepthEvent a b h :=
  (f3UnequalDepthHaar_absolutelyContinuous a b).ae_le
    (f3UnitHaar_signedDepth_defined_ae a b)

/-- Every positive conditional signed atom has mass `3^(-h)`, independent of L. -/
theorem f3UnequalDepthHaar_signed_pos {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L h : ℕ} (hLpos : 1 ≤ L) (hh : 1 ≤ h)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnequalDepthHaar a b (f3SignedDepthEvent a b (h : ℤ)) = ((3 : ℝ≥0∞) ^ h)⁻¹ := by
  have hsub := f3SignedDepthEvent_subset_ne a b (h := (h : ℤ)) (by omega)
  rw [f3UnequalDepthHaar, ProbabilityTheory.cond_apply (f3RootDepth_ne_measurable hL),
    Set.inter_eq_right.mpr hsub, f3UnitHaar_rootDepth_ne ha hb hLpos hL,
    f3UnitHaar_signedDepth_pos ha hb hLpos hh hL, inv_inv, pow_add]
  have h0 : (3 : ℝ≥0∞) ^ L ≠ 0 := by simp
  have ht : (3 : ℝ≥0∞) ^ L ≠ ⊤ := by simp
  rw [ENNReal.mul_inv (Or.inl h0) (Or.inl ht), ← mul_assoc,
    ENNReal.mul_inv_cancel h0 ht, one_mul]

/-- The corresponding negative conditional atom has exactly the same probability. -/
theorem f3UnequalDepthHaar_signed_neg {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L h : ℕ} (hLpos : 1 ≤ L) (hh : 1 ≤ h)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnequalDepthHaar a b (f3SignedDepthEvent a b (-(h : ℤ))) = ((3 : ℝ≥0∞) ^ h)⁻¹ := by
  have hsub := f3SignedDepthEvent_subset_ne a b (h := -(h : ℤ)) (by omega)
  rw [f3UnequalDepthHaar, ProbabilityTheory.cond_apply (f3RootDepth_ne_measurable hL),
    Set.inter_eq_right.mpr hsub, f3UnitHaar_rootDepth_ne ha hb hLpos hL,
    f3UnitHaar_signedDepth_neg ha hb hLpos hh hL, inv_inv, pow_add]
  have h0 : (3 : ℝ≥0∞) ^ L ≠ 0 := by simp
  have ht : (3 : ℝ≥0∞) ^ L ≠ ⊤ := by simp
  rw [ENNReal.mul_inv (Or.inl h0) (Or.inl ht), ← mul_assoc,
    ENNReal.mul_inv_cancel h0 ht, one_mul]

/-- A successful unequal-depth observation cannot have genuine signed difference zero. -/
theorem f3UnequalDepthHaar_signed_zero {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnequalDepthHaar a b (f3SignedDepthEvent a b 0) = 0 := by
  have he : {d : ℤ_[3] |
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠ rootDepth (d : ℚ_[3]) (b : ℚ_[3])} ∩
      f3SignedDepthEvent a b 0 = ∅ := by
    rw [f3SignedDepthEvent_zero_eq_equal hL]
    ext d
    simp
  rw [f3UnequalDepthHaar, ProbabilityTheory.cond_apply (f3RootDepth_ne_measurable hL),
    he, measure_empty, mul_zero]

/-- A finite absolute-difference atom is the union of its two signed atoms. -/
def f3AbsDepthEvent (a b : ℤ_[3]) (h : ℕ) : Set ℤ_[3] :=
  f3SignedDepthEvent a b (h : ℤ) ∪ f3SignedDepthEvent a b (-(h : ℤ))

/-- The union definition is exactly the absolute value of two genuine finite integer depths. -/
theorem f3AbsDepthEvent_iff (a b d : ℤ_[3]) (h : ℕ) :
    d ∈ f3AbsDepthEvent a b h ↔ ∃ r s : ℤ,
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = (r : WithTop ℤ) ∧
      rootDepth (d : ℚ_[3]) (b : ℚ_[3]) = (s : WithTop ℤ) ∧ (r - s).natAbs = h := by
  constructor
  · rintro (⟨r, s, hr, hs, hd⟩ | ⟨r, s, hr, hs, hd⟩)
    · exact ⟨r, s, hr, hs, Int.natAbs_eq_iff.mpr (Or.inl hd)⟩
    · exact ⟨r, s, hr, hs, Int.natAbs_eq_iff.mpr (Or.inr hd)⟩
  · rintro ⟨r, s, hr, hs, hd⟩
    rcases Int.natAbs_eq_iff.mp hd with hp | hn
    · exact Or.inl ⟨r, s, hr, hs, hp⟩
    · exact Or.inr ⟨r, s, hr, hs, hn⟩

/-- Positive absolute-difference atoms are measurable events of the genuine observations. -/
theorem f3AbsDepthEvent_measurable {a b : ℤ_[3]} {L h : ℕ} (hh : 1 ≤ h)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    MeasurableSet (f3AbsDepthEvent a b h) :=
  (f3SignedDepthEvent_pos_measurable hh hL).union
    (f3SignedDepthEvent_neg_measurable hh hL)

/-- Actual conditional absolute differences have geometric mass `2·3^(-h)`. -/
theorem f3UnequalDepthHaar_abs_eq {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L h : ℕ} (hLpos : 1 ≤ L) (hh : 1 ≤ h)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnequalDepthHaar a b (f3AbsDepthEvent a b h) = 2 * ((3 : ℝ≥0∞) ^ h)⁻¹ := by
  rw [f3AbsDepthEvent, measure_union (f3SignedDepthEvent_disjoint a b (by omega))
    (f3SignedDepthEvent_neg_measurable hh hL),
    f3UnequalDepthHaar_signed_pos ha hb hLpos hh hL,
    f3UnequalDepthHaar_signed_neg ha hb hLpos hh hL, two_mul]

/-- Original-model positive conditional law with unchanged actual roots and hypotheses. -/
theorem f3SharedRootConfig_conditional_signed_pos {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L h : ℕ} (hh : 1 ≤ h)
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) :
    f3UnequalDepthHaar (f3SharedRootUnit C i) (f3SharedRootUnit C j)
      (f3SignedDepthEvent (f3SharedRootUnit C i) (f3SharedRootUnit C j) (h : ℤ)) =
      ((3 : ℝ≥0∞) ^ h)⁻¹ := by
  have hpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  apply f3UnequalDepthHaar_signed_pos (f3SharedRootUnit_isUnit C i)
    (f3SharedRootUnit_isUnit C j) hpos hh
  simpa only [f3SharedRootUnit_coe] using hL

/-- Original-model negative conditional law, independent of the finite root distance. -/
theorem f3SharedRootConfig_conditional_signed_neg {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L h : ℕ} (hh : 1 ≤ h)
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) :
    f3UnequalDepthHaar (f3SharedRootUnit C i) (f3SharedRootUnit C j)
      (f3SignedDepthEvent (f3SharedRootUnit C i) (f3SharedRootUnit C j) (-(h : ℤ))) =
      ((3 : ℝ≥0∞) ^ h)⁻¹ := by
  have hpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  apply f3UnequalDepthHaar_signed_neg (f3SharedRootUnit_isUnit C i)
    (f3SharedRootUnit_isUnit C j) hpos hh
  simpa only [f3SharedRootUnit_coe] using hL

/-- Original-model actual conditional absolute-difference law. -/
theorem f3SharedRootConfig_conditional_abs_eq {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L h : ℕ} (hh : 1 ≤ h)
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) :
    f3UnequalDepthHaar (f3SharedRootUnit C i) (f3SharedRootUnit C j)
      (f3AbsDepthEvent (f3SharedRootUnit C i) (f3SharedRootUnit C j) h) =
      2 * ((3 : ℝ≥0∞) ^ h)⁻¹ := by
  have hpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  apply f3UnequalDepthHaar_abs_eq (f3SharedRootUnit_isUnit C i)
    (f3SharedRootUnit_isUnit C j) hpos hh
  simpa only [f3SharedRootUnit_coe] using hL

end

end OmegaBalance
