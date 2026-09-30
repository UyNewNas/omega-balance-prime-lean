import OmegaBalance.F3TruncatedNonidentifiability

/-!
# Actual signed atoms of two root depths

A signed atom is defined only when both genuine extended depths are finite
integers. Root hits are not assigned a fictitious signed value. They form a
proved null exceptional set, so these atoms cover almost every actual unit-Haar
sample. The atom laws below are the unconditional signed part of REC-L3;
conditional absolute-value/sign independence remains separate work.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory Set
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- A strict excess above the root distance forces the other actual depth. -/
theorem rootDepth_eq_distance_of_lt {d a b : ℚ_[3]}
    (h : rootDistance a b < rootDepth d a) :
    rootDepth d b = rootDistance a b := by
  change Padic.addValuation (a - b) < Padic.addValuation (d - a) at h
  change Padic.addValuation (d - b) = Padic.addValuation (a - b)
  calc
    Padic.addValuation (d - b) = Padic.addValuation ((d - a) + (a - b)) := by
      congr 1
      ring
    _ = Padic.addValuation (a - b) := Padic.addValuation.map_add_eq_of_lt_right h

/-- The genuine signed atom, with explicit finite integer depths at both roots. -/
def f3SignedDepthEvent (a b : ℤ_[3]) (h : ℤ) : Set ℤ_[3] :=
  {d | ∃ r s : ℤ, rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = (r : WithTop ℤ) ∧
    rootDepth (d : ℚ_[3]) (b : ℚ_[3]) = (s : WithTop ℤ) ∧ r - s = h}

/-- Swapping the roots reverses the genuine signed difference. -/
theorem f3SignedDepthEvent_neg_swap (a b : ℤ_[3]) (h : ℤ) :
    f3SignedDepthEvent a b (-h) = f3SignedDepthEvent b a h := by
  ext d
  constructor
  · rintro ⟨r, s, hr, hs, hdiff⟩
    exact ⟨s, r, hs, hr, by omega⟩
  · rintro ⟨r, s, hr, hs, hdiff⟩
    exact ⟨s, r, hs, hr, by omega⟩

/-- A positive signed atom is exactly one actual finite layer at the first root. -/
theorem f3SignedDepthEvent_pos_eq_layer {a b : ℤ_[3]} {L h : ℕ} (hh : 1 ≤ h)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3SignedDepthEvent a b (h : ℤ) = f3RootDepthLayer a (L + h) := by
  ext d
  constructor
  · rintro ⟨r, s, hr, hs, hdiff⟩
    have hsr : s < r := by omega
    have hsr' : (s : WithTop ℤ) < (r : WithTop ℤ) := by exact_mod_cast hsr
    have hne : rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠
        rootDepth (d : ℚ_[3]) (b : ℚ_[3]) := by
      rw [hr, hs]
      exact ne_of_gt hsr'
    have hm := rootDepth_min_eq_distance_of_ne hne
    rw [hL, hr, hs, min_eq_right hsr'.le] at hm
    have hsL : (L : ℤ) = s := by exact_mod_cast hm
    change rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = ((L + h : ℕ) : WithTop ℤ)
    rw [hr]
    norm_cast
    omega
  · intro hd
    have hr : rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = ((L + h : ℕ) : WithTop ℤ) := hd
    have hgt : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) <
        rootDepth (d : ℚ_[3]) (a : ℚ_[3]) := by
      rw [hL, hr]
      exact_mod_cast (show L < L + h by omega)
    have hs := rootDepth_eq_distance_of_lt hgt
    rw [hL] at hs
    refine ⟨(L + h : ℕ), L, ?_, ?_, ?_⟩
    · exact_mod_cast hr
    · exact_mod_cast hs
    · omega

/-- A negative signed atom is the corresponding finite layer at the second root. -/
theorem f3SignedDepthEvent_neg_eq_layer {a b : ℤ_[3]} {L h : ℕ} (hh : 1 ≤ h)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3SignedDepthEvent a b (-(h : ℤ)) = f3RootDepthLayer b (L + h) := by
  rw [f3SignedDepthEvent_neg_swap]
  apply f3SignedDepthEvent_pos_eq_layer hh
  simpa only [rootDistance, AddValuation.map_sub_swap] using hL

/-- With finite root distance, equal depths are already finite, so zero loses no points. -/
theorem f3SignedDepthEvent_zero_eq_equal {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3SignedDepthEvent a b 0 = {d : ℤ_[3] |
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = rootDepth (d : ℚ_[3]) (b : ℚ_[3])} := by
  ext d
  constructor
  · rintro ⟨r, s, hr, hs, hdiff⟩
    have hrs : r = s := by omega
    change rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = rootDepth (d : ℚ_[3]) (b : ℚ_[3])
    rw [hr, hs, hrs]
  · intro heq
    have hm := rootDepth_min_le_distance (d : ℚ_[3]) (a : ℚ_[3]) (b : ℚ_[3])
    rw [← heq, min_self, hL] at hm
    cases hd : rootDepth (d : ℚ_[3]) (a : ℚ_[3]) using WithTop.recTopCoe with
    | top => simp only [hd, top_le_iff, WithTop.natCast_ne_top] at hm
    | coe r => exact ⟨r, r, hd, heq.symm.trans hd, sub_self r⟩

/-- Positive signed atoms are genuinely measurable. -/
theorem f3SignedDepthEvent_pos_measurable {a b : ℤ_[3]} {L h : ℕ} (hh : 1 ≤ h)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    MeasurableSet (f3SignedDepthEvent a b (h : ℤ)) := by
  rw [f3SignedDepthEvent_pos_eq_layer hh hL]
  exact f3RootDepthLayer_measurable a (L + h)

/-- Negative signed atoms are genuinely measurable. -/
theorem f3SignedDepthEvent_neg_measurable {a b : ℤ_[3]} {L h : ℕ} (hh : 1 ≤ h)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    MeasurableSet (f3SignedDepthEvent a b (-(h : ℤ))) := by
  rw [f3SignedDepthEvent_neg_eq_layer hh hL]
  exact f3RootDepthLayer_measurable b (L + h)

/-- The zero signed atom is the existing measurable equal-depth event. -/
theorem f3SignedDepthEvent_zero_measurable {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    MeasurableSet (f3SignedDepthEvent a b 0) := by
  rw [f3SignedDepthEvent_zero_eq_equal hL]
  exact f3RootDepth_equal_measurable hL

/-- Actual positive signed differences have mass `3^(-(L+h))`. -/
theorem f3UnitHaar_signedDepth_pos {a b : ℤ_[3]} (ha : IsUnit a) (_hb : IsUnit b)
    {L h : ℕ} (_hLpos : 1 ≤ L) (hh : 1 ≤ h)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnitHaar (f3SignedDepthEvent a b (h : ℤ)) = ((3 : ℝ≥0∞) ^ (L + h))⁻¹ := by
  rw [f3SignedDepthEvent_pos_eq_layer hh hL]
  exact f3UnitHaar_rootDepth_eq ha (by omega)

/-- Actual negative signed differences have exactly the same mass. -/
theorem f3UnitHaar_signedDepth_neg {a b : ℤ_[3]} (_ha : IsUnit a) (hb : IsUnit b)
    {L h : ℕ} (_hLpos : 1 ≤ L) (hh : 1 ≤ h)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnitHaar (f3SignedDepthEvent a b (-(h : ℤ))) = ((3 : ℝ≥0∞) ^ (L + h))⁻¹ := by
  rw [f3SignedDepthEvent_neg_eq_layer hh hL]
  exact f3UnitHaar_rootDepth_eq hb (by omega)

/-- The genuine zero difference has the complementary certificate probability. -/
theorem f3UnitHaar_signedDepth_zero {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnitHaar (f3SignedDepthEvent a b 0) = 1 - ((3 : ℝ≥0∞) ^ L)⁻¹ := by
  rw [f3SignedDepthEvent_zero_eq_equal hL]
  exact f3UnitHaar_rootDepth_equal ha hb hLpos hL

/-- The genuine finite signed atoms cover almost every sample; root exceptions are null. -/
theorem f3UnitHaar_signedDepth_defined_ae (a b : ℤ_[3]) :
    ∀ᵐ d ∂f3UnitHaar, ∃ h : ℤ, d ∈ f3SignedDepthEvent a b h := by
  have hn (x : ℤ_[3]) : ∀ᵐ d ∂f3UnitHaar, d ≠ x := by
    apply ae_iff.mpr
    have he : {d : ℤ_[3] | ¬d ≠ x} = {x} := by ext d; simp
    rw [he]
    exact f3UnitHaar_singleton x
  filter_upwards [hn a, hn b] with d hda hdb
  have hda' : (d : ℚ_[3]) ≠ (a : ℚ_[3]) := fun h => hda (PadicInt.ext h)
  have hdb' : (d : ℚ_[3]) ≠ (b : ℚ_[3]) := fun h => hdb (PadicInt.ext h)
  exact ⟨((d : ℚ_[3]) - a).valuation - ((d : ℚ_[3]) - b).valuation,
    ((d : ℚ_[3]) - a).valuation, ((d : ℚ_[3]) - b).valuation,
    rootDepth_eq_valuation hda', rootDepth_eq_valuation hdb', rfl⟩

/-- The original model's positive signed law, without changing its actual roots. -/
theorem f3SharedRootConfig_unitHaar_signedDepth_pos {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L h : ℕ} (hh : 1 ≤ h)
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) :
    f3UnitHaar (f3SignedDepthEvent (f3SharedRootUnit C i) (f3SharedRootUnit C j) (h : ℤ)) =
      ((3 : ℝ≥0∞) ^ (L + h))⁻¹ := by
  have hpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  apply f3UnitHaar_signedDepth_pos (f3SharedRootUnit_isUnit C i)
    (f3SharedRootUnit_isUnit C j) hpos hh
  simpa only [f3SharedRootUnit_coe] using hL

/-- The original model's negative signed law with the same finite-distance domain. -/
theorem f3SharedRootConfig_unitHaar_signedDepth_neg {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L h : ℕ} (hh : 1 ≤ h)
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) :
    f3UnitHaar (f3SignedDepthEvent (f3SharedRootUnit C i) (f3SharedRootUnit C j) (-(h : ℤ))) =
      ((3 : ℝ≥0∞) ^ (L + h))⁻¹ := by
  have hpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  apply f3UnitHaar_signedDepth_neg (f3SharedRootUnit_isUnit C i)
    (f3SharedRootUnit_isUnit C j) hpos hh
  simpa only [f3SharedRootUnit_coe] using hL

/-- The original model's zero signed law retains the positive common-root distance. -/
theorem f3SharedRootConfig_unitHaar_signedDepth_zero {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L : ℕ}
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) :
    f3UnitHaar (f3SignedDepthEvent (f3SharedRootUnit C i) (f3SharedRootUnit C j) 0) =
      1 - ((3 : ℝ≥0∞) ^ L)⁻¹ := by
  have hpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  apply f3UnitHaar_signedDepth_zero (f3SharedRootUnit_isUnit C i)
    (f3SharedRootUnit_isUnit C j) hpos
  simpa only [f3SharedRootUnit_coe] using hL

end

end OmegaBalance
