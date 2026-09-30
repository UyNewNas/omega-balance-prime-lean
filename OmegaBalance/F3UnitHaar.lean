import OmegaBalance.PadicIntHaar
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.NormNum

/-!
# The actual Haar probability on three-adic units

The ambient measure is mathlib's additive Haar measure, normalized on the compact
whole space `ℤ_[3]`. The sampling measure is its normalized restriction to the
actual set `IsUnit`, as in F3-REC §1 and prime_product_correlations §3.
No residue or ball masses are assumptions.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory Measure TopologicalSpace
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

instance f3PadicIntMeasurableSpace : MeasurableSpace ℤ_[3] := borel _
instance f3PadicIntBorelSpace : BorelSpace ℤ_[3] := ⟨rfl⟩

/-- Additive Haar measure normalized on the whole compact ring of three-adic integers. -/
def f3PadicHaar : Measure ℤ_[3] := addHaarMeasure ⊤

/-- The chosen ambient Haar normalization has total mass one. -/
theorem f3PadicHaar_univ : f3PadicHaar Set.univ = 1 :=
  addHaarMeasure_self

instance f3PadicHaar_isProbabilityMeasure : IsProbabilityMeasure f3PadicHaar :=
  ⟨f3PadicHaar_univ⟩

instance f3PadicHaar_isAddHaarMeasure : f3PadicHaar.IsAddHaarMeasure :=
  isAddHaarMeasure_addHaarMeasure _

/-- The actual three-adic unit domain. -/
def f3PadicUnitSet : Set ℤ_[3] := {x | IsUnit x}

/-- Nonunits are exactly the zero residue class modulo three. -/
theorem f3PadicInt_not_isUnit_iff (x : ℤ_[3]) :
    ¬IsUnit x ↔ PadicInt.toZModPow 1 x = 0 := by
  rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd,
    ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one]

/-- The complement of the unit domain is a genuine residue fiber. -/
theorem f3PadicUnitSet_compl :
    f3PadicUnitSetᶜ = (PadicInt.toZModPow 1) ⁻¹' {0} := by
  ext x
  exact f3PadicInt_not_isUnit_iff x

/-- The unit domain is Borel measurable. -/
theorem f3PadicUnitSet_measurable : MeasurableSet f3PadicUnitSet := by
  have h := (padicInt_measurable_fiber (p := 3) 1 0).compl
  simpa only [← f3PadicUnitSet_compl, compl_compl] using h

/-- The additive Haar mass of the actual unit domain is `2/3`. -/
theorem f3PadicHaar_units : f3PadicHaar f3PadicUnitSet = 2 / 3 := by
  have h := prob_compl_eq_one_sub (μ := f3PadicHaar)
    (padicInt_measurable_fiber (p := 3) 1 0)
  rw [padicInt_haar_fiber, ← f3PadicUnitSet_compl, compl_compl] at h
  convert h using 1 <;> norm_num

/-- The paper's normalized additive Haar probability on the units, represented
as a measure on `ℤ_[3]` supported on its actual unit set. -/
def f3UnitHaar : Measure ℤ_[3] :=
  (f3PadicHaar f3PadicUnitSet)⁻¹ • f3PadicHaar.restrict f3PadicUnitSet

/-- Normalizing the actual restriction gives mass one on the whole sample space. -/
theorem f3UnitHaar_univ : f3UnitHaar Set.univ = 1 := by
  simp only [f3UnitHaar, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel (by rw [f3PadicHaar_units]; norm_num)
    (measure_ne_top _ _)

instance f3UnitHaar_isProbabilityMeasure : IsProbabilityMeasure f3UnitHaar :=
  ⟨f3UnitHaar_univ⟩

/-- The sampling probability is supported on genuine units. -/
theorem f3UnitHaar_units : f3UnitHaar f3PadicUnitSet = 1 := by
  rw [f3UnitHaar, Measure.smul_apply, Measure.restrict_apply f3PadicUnitSet_measurable,
    Set.inter_self, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by rw [f3PadicHaar_units]; norm_num)
    (measure_ne_top _ _)

/-- Nonunits have probability zero in the normalized unit model. -/
theorem f3UnitHaar_nonunits : f3UnitHaar f3PadicUnitSetᶜ = 0 := by
  rw [prob_compl_eq_one_sub f3PadicUnitSet_measurable, f3UnitHaar_units, tsub_self]

/-- A positive-precision fiber around a unit remains in the unit domain. -/
theorem f3PadicInt_unit_fiber_subset {a : ℤ_[3]} (ha : IsUnit a)
    {t : ℕ} (ht : 1 ≤ t) :
    (PadicInt.toZModPow t) ⁻¹' {PadicInt.toZModPow t a} ⊆ f3PadicUnitSet := by
  intro d hd
  change PadicInt.toZModPow t d = PadicInt.toZModPow t a at hd
  change IsUnit d
  by_contra hdu
  have hd0 := (f3PadicInt_not_isUnit_iff d).mp hdu
  have hmod : PadicInt.toZModPow 1 d = PadicInt.toZModPow 1 a := by
    simpa only [PadicInt.cast_toZModPow 1 t ht] using
      congrArg (ZMod.cast : ZMod (3 ^ t) → ZMod (3 ^ 1)) hd
  exact ((f3PadicInt_not_isUnit_iff a).mpr (hmod.symm.trans hd0)) ha

/-- Actual unit-fiber mass before cancelling the adjacent powers of three. -/
theorem f3UnitHaar_fiber {a : ℤ_[3]} (ha : IsUnit a) {t : ℕ} (ht : 1 ≤ t) :
    f3UnitHaar ((PadicInt.toZModPow t) ⁻¹' {PadicInt.toZModPow t a}) =
      (2 / 3 : ℝ≥0∞)⁻¹ * ((3 : ℝ≥0∞) ^ t)⁻¹ := by
  rw [f3UnitHaar, Measure.smul_apply,
    Measure.restrict_apply (padicInt_measurable_fiber t _),
    Set.inter_eq_left.mpr (f3PadicInt_unit_fiber_subset ha ht),
    f3PadicHaar_units, smul_eq_mul, padicInt_haar_fiber]
  norm_num

end

end OmegaBalance
