import OmegaBalance.F3RootTruncatedReconstruction
import OmegaBalance.F3JointWaitingHaar

/-!
# Actual Haar probabilities of finite-precision certificates

REC-L12 / theorem 2.6, equation (2.13), single-observation slice. The observed
values are the existing normalized depths min(R,H), not min(b+R,H). Success
uses the existing unequal-or-jointly-saturated certificate rule. Raw root hits
retain infinity before truncation. The target remains min(L,H).

The finite-batch matrix probability and prime transfer are separate tasks.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Below precision, a truncated certificate occurs exactly at raw unequal depths. -/
theorem truncatedDepthWitness_iff_raw_ne_of_distance_lt {H : ℕ} {d a b : ℚ_[3]}
    (hL : rootDistance a b < (H : WithTop ℤ)) :
    truncatedDepthWitness H (truncatedRootDepth H d a) (truncatedRootDepth H d b) ↔
      rootDepth d a ≠ rootDepth d b := by
  constructor
  · rintro (hne | hsat)
    · intro heq
      apply hne
      exact congrArg (fun z => min z (H : WithTop ℤ)) heq
    · have hge := (truncatedRootDepth_saturated_certificate hsat.1 hsat.2).1
      exact False.elim ((not_lt_of_ge hge) hL)
  · intro hne
    have hd := rootDepth_min_eq_distance_of_ne hne
    have hsmall : min (rootDepth d a) (rootDepth d b) < (H : WithTop ℤ) :=
      hd.symm.trans_lt hL
    rcases lt_or_gt_of_ne hne with hab | hba
    · have ha : rootDepth d a < (H : WithTop ℤ) := by
        simpa only [min_eq_left hab.le] using hsmall
      exact Or.inl (ne_of_lt (min_lt_min_left_iff.mpr ⟨hab, ha⟩))
    · have hb : rootDepth d b < (H : WithTop ℤ) := by
        simpa only [min_eq_right hba.le] using hsmall
      exact Or.inl (ne_of_gt (min_lt_min_left_iff.mpr ⟨hba, hb⟩))

/-- At or above precision, success is exactly the common saturated root ball. -/
theorem truncatedDepthWitness_iff_ge_of_le_distance {H : ℕ} {d a b : ℚ_[3]}
    (hL : (H : WithTop ℤ) ≤ rootDistance a b) :
    truncatedDepthWitness H (truncatedRootDepth H d a) (truncatedRootDepth H d b) ↔
      (H : WithTop ℤ) ≤ rootDepth d a := by
  constructor
  · rintro (hne | hsat)
    · have hc := truncatedRootDepth_ne_certificate hne
      exact False.elim ((not_lt_of_ge hL) (hc.1.trans_lt hc.2))
    · exact min_eq_right_iff.mp hsat.1
  · intro ha
    have hasym : (H : WithTop ℤ) ≤ rootDepth a d := by
      change (H : WithTop ℤ) ≤ Padic.addValuation (a - d)
      rw [AddValuation.map_sub_swap]
      exact ha
    have hb : (H : WithTop ℤ) ≤ rootDepth d b :=
      (le_min hasym hL).trans (rootDepth_min_le_distance a d b)
    exact Or.inr ⟨min_eq_right ha, min_eq_right hb⟩

/-- The actual success event of the existing finite-precision certificate rule. -/
def f3TruncatedCertificateEvent (a b : ℤ_[3]) (H : ℕ) : Set ℤ_[3] :=
  {d | truncatedDepthWitness H (truncatedRootDepth H (d : ℚ_[3]) (a : ℚ_[3]))
    (truncatedRootDepth H (d : ℚ_[3]) (b : ℚ_[3]))}

/-- The low-distance success event is the existing raw unequal-depth event. -/
theorem f3TruncatedCertificateEvent_eq_ne {a b : ℤ_[3]} {L H : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (hLH : L < H) :
    f3TruncatedCertificateEvent a b H =
      {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠
        rootDepth (d : ℚ_[3]) (b : ℚ_[3])} := by
  have hlt : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) < (H : WithTop ℤ) := by
    rw [hL]
    exact_mod_cast hLH
  ext d
  exact truncatedDepthWitness_iff_raw_ne_of_distance_lt hlt

/-- The high-distance success event is the actual first-root threshold ball. -/
theorem f3TruncatedCertificateEvent_eq_tail {a b : ℤ_[3]} {H : ℕ}
    (hL : (H : WithTop ℤ) ≤ rootDistance (a : ℚ_[3]) (b : ℚ_[3])) :
    f3TruncatedCertificateEvent a b H = f3RootDepthTail a H := by
  ext d
  exact truncatedDepthWitness_iff_ge_of_le_distance hL

/-- Saturating the first observed coordinate always supplies a valid certificate. -/
theorem f3RootDepthTail_subset_truncatedCertificate (a b : ℤ_[3]) (H : ℕ) :
    f3RootDepthTail a H ⊆ f3TruncatedCertificateEvent a b H := by
  intro d hd
  have ha : truncatedRootDepth H (d : ℚ_[3]) (a : ℚ_[3]) = (H : WithTop ℤ) :=
    min_eq_right hd
  by_cases hb : truncatedRootDepth H (d : ℚ_[3]) (b : ℚ_[3]) = (H : WithTop ℤ)
  · exact Or.inr ⟨ha, hb⟩
  · exact Or.inl (fun heq => hb (heq.symm.trans ha))

/-- The true certificate event is measurable in either distance regime. -/
theorem f3TruncatedCertificateEvent_measurable {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (H : ℕ) :
    MeasurableSet (f3TruncatedCertificateEvent a b H) := by
  by_cases hLH : L < H
  · rw [f3TruncatedCertificateEvent_eq_ne hL hLH]
    exact f3RootDepth_ne_measurable hL
  · have hge : (H : WithTop ℤ) ≤ rootDistance (a : ℚ_[3]) (b : ℚ_[3]) := by
      rw [hL]
      exact_mod_cast (Nat.le_of_not_gt hLH)
    rw [f3TruncatedCertificateEvent_eq_tail hge]
    exact f3RootDepthTail_measurable a H

/-- Low-distance certificates have the already proved actual unequal-depth mass. -/
theorem f3UnitHaar_truncatedCertificate_of_lt {a b : ℤ_[3]} (ha : IsUnit a)
    (hb : IsUnit b) {L H : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (hLH : L < H) :
    f3UnitHaar (f3TruncatedCertificateEvent a b H) = ((3 : ℝ≥0∞) ^ L)⁻¹ := by
  rw [f3TruncatedCertificateEvent_eq_ne hL hLH]
  exact f3UnitHaar_rootDepth_ne ha hb hLpos hL

/-- At or above precision, the actual normalized unit-root ball supplies the mass. -/
theorem f3UnitHaar_truncatedCertificate_of_ge {a b : ℤ_[3]} (ha : IsUnit a)
    {H : ℕ} (hH : 1 ≤ H)
    (hL : (H : WithTop ℤ) ≤ rootDistance (a : ℚ_[3]) (b : ℚ_[3])) :
    f3UnitHaar (f3TruncatedCertificateEvent a b H) =
      (2 * (3 : ℝ≥0∞) ^ (H - 1))⁻¹ := by
  rw [f3TruncatedCertificateEvent_eq_tail hL]
  exact f3UnitHaar_rootDepth_ge ha hH

/-- REC-L12's exact single-observation law, including the boundary L=H. -/
theorem f3UnitHaar_truncatedCertificate_probability {a b : ℤ_[3]} (ha : IsUnit a)
    (hb : IsUnit b) {L H : ℕ} (hLpos : 1 ≤ L) (hH : 1 ≤ H)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnitHaar (f3TruncatedCertificateEvent a b H) =
      if L < H then ((3 : ℝ≥0∞) ^ L)⁻¹ else (2 * (3 : ℝ≥0∞) ^ (H - 1))⁻¹ := by
  split_ifs with hLH
  · exact f3UnitHaar_truncatedCertificate_of_lt ha hb hLpos hL hLH
  · apply f3UnitHaar_truncatedCertificate_of_ge ha hH
    rw [hL]
    exact_mod_cast (Nat.le_of_not_gt hLH)

/-- A uniform positive rate follows from actual event inclusion, not inverse estimates. -/
theorem f3UnitHaar_truncatedCertificate_lower_bound {a b : ℤ_[3]} (ha : IsUnit a)
    {H : ℕ} (hH : 1 ≤ H) :
    (2 * (3 : ℝ≥0∞) ^ (H - 1))⁻¹ ≤
      f3UnitHaar (f3TruncatedCertificateEvent a b H) := by
  rw [← f3UnitHaar_rootDepth_ge ha hH]
  exact measure_mono (f3RootDepthTail_subset_truncatedCertificate a b H)

/-- The original fixed model has this law for normalized truncated observations. -/
theorem f3SharedRootConfig_unitHaar_truncatedCertificate_probability {m : ℕ}
    (C : F3SharedRootConfig m) {i j : Fin m} (hij : i ≠ j) {H : ℕ} (hH : 1 ≤ H) :
    f3UnitHaar {d : ℤ_[3] | truncatedDepthWitness H
      (truncatedRootDepth H (d : ℚ_[3]) (C.root i))
      (truncatedRootDepth H (d : ℚ_[3]) (C.root j))} =
      if f3RootDistanceExponent C i j < H then
        ((3 : ℝ≥0∞) ^ f3RootDistanceExponent C i j)⁻¹
      else (2 * (3 : ℝ≥0∞) ^ (H - 1))⁻¹ := by
  have hd : rootDistance (f3SharedRootUnit C i : ℚ_[3])
      (f3SharedRootUnit C j : ℚ_[3]) = (f3RootDistanceExponent C i j : WithTop ℤ) := by
    simpa only [f3SharedRootUnit_coe] using f3RootDistanceExponent_eq C hij
  simpa only [f3TruncatedCertificateEvent, f3SharedRootUnit_coe] using
    f3UnitHaar_truncatedCertificate_probability (f3SharedRootUnit_isUnit C i)
      (f3SharedRootUnit_isUnit C j) (f3RootDistanceExponent_pos C hij) hH hd

/-- The same original-model event has the uniform precision-dependent lower bound. -/
theorem f3SharedRootConfig_unitHaar_truncatedCertificate_lower_bound {m : ℕ}
    (C : F3SharedRootConfig m) (i j : Fin m) {H : ℕ} (hH : 1 ≤ H) :
    (2 * (3 : ℝ≥0∞) ^ (H - 1))⁻¹ ≤
      f3UnitHaar {d : ℤ_[3] | truncatedDepthWitness H
        (truncatedRootDepth H (d : ℚ_[3]) (C.root i))
        (truncatedRootDepth H (d : ℚ_[3]) (C.root j))} := by
  simpa only [f3TruncatedCertificateEvent, f3SharedRootUnit_coe] using
    (f3UnitHaar_truncatedCertificate_lower_bound
      (b := f3SharedRootUnit C j) (f3SharedRootUnit_isUnit C i) hH)

end

end OmegaBalance
